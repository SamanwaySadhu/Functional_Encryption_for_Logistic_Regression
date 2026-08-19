#include <pbc.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <iostream>
#include <cstring>
#include <cmath>
#include <vector>
#include <algorithm>
#include <random>
#include <chrono>
#include <limits>
#include <cstdint>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/hmac.h>

#ifdef _OPENMP
#include <omp.h>
#endif

// --- Finetuning-layer encrypted forward pass: 784 -> 196 -> 16, ReLU LUTs ---
//
// This is a dynamic-dimension generalization of encrypted_forward_prop_kim.cpp's
// single-neuron IPFE+LUT design, run twice (fan-in 784 then fan-in 196) to build
// a two-hidden-layer encrypted ReLU network. Two design decisions carry over
// verbatim from that file's fix-up:
//
//   1. Every neuron's ReLU LUT domain is the single-TERM product range
//      [MIN_X*MAX_X, MIN_X*MIN_X], never scaled by fan-in. Row *count* is
//      therefore constant (does not grow with 784 or 196); row *payload*
//      still scales with fan-in because each row carries a
//      fan_in x (BATCH_SIZE+1) tensor of G1 elements for the next stage.
//
//   2. Because the domain is deliberately not scaled by fan-in, a neuron's
//      true pre-activation (a sum of up to `fan_in` per-term products) will
//      very often land outside [min_x, max_x] -- expected, not a bug. The
//      lookup function falls back to drawing a value uniformly from its own
//      declared range and masking it exactly as a real row would be, using
//      the masks already in scope at the call site (see MapReLULUT below).
//      For the 784-wide layer this fallback is not an edge case: it is the
//      common case (see the printed fallback-rate stats at the end of main).
//
// BATCH_SIZE is fixed at 1 here (one sample flows through the whole trunk).
// The upstream repo's per-neuron LUT ties its row *keys* to one specific
// (alpha, beta) pair from one specific KeyGen/Encrypt call, so a LUT cannot
// be safely shared across multiple ciphertexts with different `beta` without
// rederiving the scheme's batching protocol from scratch; keeping
// BATCH_SIZE=1 sidesteps that instead of guessing at an unverified variant.
// Bump it and re-thread `idx` per sample if you want genuine minibatching.
//
// The 16-dim output of the second hidden layer becomes the shared pseudo-
// feature vector `y` for NUM_HEADS=20 independent downstream classifiers.
// This file produces, per head and per class, the Setup/KeyGen/Encrypt
// artifacts (function key + ciphertext) over that pseudo-feature vector --
// exactly the inputs encrypted_forward_prop_kim_multiclass.cpp (compiled
// with FEATURE_SIZE=16) and encrypted_backward_prop_kim_multiclass.cpp
// (same) expect to consume for that head's Stage-A/B softmax LUT and
// gradient LUTs respectively. It does not re-implement those LUTs itself.
//
// Implementation note: pbc's element_t is `typedef struct element_s
// element_t[1]` (an array type, GMP-style). std::vector<element_t> does not
// compile under libstdc++ (resize()/nested-vector construction hit a
// static_assert on array value_types), so every element_t that needs to
// live inside a std::vector is wrapped in `struct Elem { element_t v; };`
// below and accessed via `.v`. Plain (non-container) element_t locals and
// struct fields are unaffected and used exactly as in the rest of the repo.

#define QUANTIZATION_BITS 6
#define MIN_X (-(1 << (QUANTIZATION_BITS - 1)))
#define MAX_X ((1 << (QUANTIZATION_BITS - 1)) - 1)
#define BATCH_SIZE 1

#define INPUT_DIM 784
#define HIDDEN1_DIM 196
#define HIDDEN2_DIM 16
#define NUM_HEADS 20
#define HEAD_CLASSES 3

struct Elem {
    element_t v;
};
typedef std::vector<std::vector<Elem>> ElemMatrix;

// --- LUT plumbing (dimension-agnostic; copied from encrypted_forward_prop_kim.cpp) ---

struct EncryptedLookupRow {
    std::vector<unsigned char> nonce;
    std::vector<unsigned char> ciphertext;
    std::vector<unsigned char> tag;
};

struct EncryptedLookupTable {
    int min_x = 0;
    int max_x = 0;
    size_t num_entries = 0;
    size_t table_size = 0;
    std::vector<EncryptedLookupRow> slots;
    std::vector<unsigned char> occupied;
};

static const int GCM_NONCE_LEN = 12;
static const int GCM_TAG_LEN = 16;
static const int HKDF_KEY_LEN = 32;
static const uint64_t LUT_HASH_SEED_1 = 1469598103934665603ULL;
static const uint64_t LUT_HASH_SEED_2 = 1099511628211ULL;
static const int LUT_MAX_REBUILDS = 8;
static const int LUT_MAX_KICKS = 512;

struct LookupBuildEntry {
    EncryptedLookupRow row;
    std::vector<unsigned char> key;
};

int generate_random_int(int min_val, int max_val) {
    try {
        std::random_device rd;
        std::mt19937_64 gen(rd());
        std::uniform_int_distribution<int> dist(min_val, max_val);
        return dist(gen);
    } catch (const std::exception& e) {
        std::cerr << "Error generating random number: " << e.what() << "\n";
        return min_val;
    }
}

uint64_t fnv1a64(const std::vector<unsigned char>& data, uint64_t seed) {
    uint64_t h = seed;
    for (unsigned char b : data) {
        h ^= static_cast<uint64_t>(b);
        h *= 1099511628211ULL;
    }
    return h;
}

size_t next_power_of_two(size_t x) {
    size_t p = 1;
    while (p < x) p <<= 1;
    return p;
}

size_t lut_hash_idx1(const std::vector<unsigned char>& key, size_t table_size) {
    return static_cast<size_t>(fnv1a64(key, LUT_HASH_SEED_1) & (table_size - 1));
}
size_t lut_hash_idx2(const std::vector<unsigned char>& key, size_t table_size) {
    return static_cast<size_t>(fnv1a64(key, LUT_HASH_SEED_2) & (table_size - 1));
}
unsigned char lut_permute_bit(const std::vector<unsigned char>& key) {
    return static_cast<unsigned char>(fnv1a64(key, LUT_HASH_SEED_1 ^ LUT_HASH_SEED_2) & 0x1ULL);
}

bool build_point_permute_cuckoo(const std::vector<LookupBuildEntry>& entries,
                                 EncryptedLookupTable& lut, size_t table_size) {
    lut.table_size = table_size;
    lut.num_entries = entries.size();
    lut.slots.assign(table_size, EncryptedLookupRow());
    lut.occupied.assign(table_size, 0);
    std::vector<std::vector<unsigned char>> slot_keys(table_size);

    for (const auto& entry : entries) {
        EncryptedLookupRow cur_row = entry.row;
        std::vector<unsigned char> cur_key = entry.key;
        size_t idx1 = lut_hash_idx1(cur_key, table_size);
        size_t idx2 = lut_hash_idx2(cur_key, table_size);
        size_t idx = lut_permute_bit(cur_key) ? idx2 : idx1;

        bool inserted = false;
        for (int kick = 0; kick < LUT_MAX_KICKS; kick++) {
            if (!lut.occupied[idx]) {
                lut.slots[idx] = std::move(cur_row);
                slot_keys[idx] = std::move(cur_key);
                lut.occupied[idx] = 1;
                inserted = true;
                break;
            }
            std::swap(cur_row, lut.slots[idx]);
            std::swap(cur_key, slot_keys[idx]);
            idx1 = lut_hash_idx1(cur_key, table_size);
            idx2 = lut_hash_idx2(cur_key, table_size);
            idx = (idx == idx1) ? idx2 : idx1;
        }
        if (!inserted) return false;
    }
    return true;
}

std::vector<unsigned char> serialize_element_to_bytes(element_t e) {
    int len = element_length_in_bytes(e);
    std::vector<unsigned char> out(len);
    element_to_bytes(out.data(), e);
    return out;
}
std::vector<unsigned char> serialize_g1_element_to_compressed_bytes(element_t e) {
    int len = element_length_in_bytes_compressed(e);
    std::vector<unsigned char> out(len);
    element_to_bytes_compressed(out.data(), e);
    return out;
}

bool hkdf_sha256(const std::vector<unsigned char>& ikm,
                  const std::vector<unsigned char>& salt,
                  const std::vector<unsigned char>& info,
                  size_t out_len,
                  std::vector<unsigned char>& out_key) {
    const EVP_MD* md = EVP_sha256();
    const size_t hash_len = EVP_MD_size(md);
    std::vector<unsigned char> effective_salt = salt;
    if (effective_salt.empty()) effective_salt.assign(hash_len, 0);

    unsigned char prk[EVP_MAX_MD_SIZE];
    unsigned int prk_len = 0;
    if (!HMAC(md, effective_salt.data(), static_cast<int>(effective_salt.size()),
              ikm.data(), ikm.size(), prk, &prk_len)) {
        return false;
    }

    out_key.clear();
    out_key.reserve(out_len);
    std::vector<unsigned char> previous_block;
    unsigned char counter = 1;
    while (out_key.size() < out_len) {
        std::vector<unsigned char> hmac_input;
        hmac_input.insert(hmac_input.end(), previous_block.begin(), previous_block.end());
        hmac_input.insert(hmac_input.end(), info.begin(), info.end());
        hmac_input.push_back(counter);

        unsigned char block[EVP_MAX_MD_SIZE];
        unsigned int block_len = 0;
        if (!HMAC(md, prk, prk_len, hmac_input.data(), hmac_input.size(), block, &block_len)) {
            return false;
        }
        previous_block.assign(block, block + block_len);
        size_t remaining = out_len - out_key.size();
        size_t to_copy = remaining < previous_block.size() ? remaining : previous_block.size();
        out_key.insert(out_key.end(), previous_block.begin(), previous_block.begin() + to_copy);
        counter++;
    }
    return true;
}

bool aes_gcm_encrypt(const std::vector<unsigned char>& key,
                      const std::vector<unsigned char>& nonce,
                      const std::vector<unsigned char>& plaintext,
                      std::vector<unsigned char>& ciphertext,
                      std::vector<unsigned char>& tag) {
    EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
    if (!ctx) return false;
    bool ok = false;
    int len = 0, ciphertext_len = 0;
    ciphertext.assign(plaintext.size(), 0);
    tag.assign(GCM_TAG_LEN, 0);
    if (EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL) != 1) goto cleanup;
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, nonce.size(), NULL) != 1) goto cleanup;
    if (EVP_EncryptInit_ex(ctx, NULL, NULL, key.data(), nonce.data()) != 1) goto cleanup;
    if (EVP_EncryptUpdate(ctx, ciphertext.data(), &len, plaintext.data(), plaintext.size()) != 1) goto cleanup;
    ciphertext_len = len;
    if (EVP_EncryptFinal_ex(ctx, ciphertext.data() + len, &len) != 1) goto cleanup;
    ciphertext_len += len;
    ciphertext.resize(ciphertext_len);
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, GCM_TAG_LEN, tag.data()) != 1) goto cleanup;
    ok = true;
cleanup:
    EVP_CIPHER_CTX_free(ctx);
    return ok;
}

bool aes_gcm_decrypt(const std::vector<unsigned char>& key,
                      const std::vector<unsigned char>& nonce,
                      const std::vector<unsigned char>& ciphertext,
                      const std::vector<unsigned char>& tag,
                      std::vector<unsigned char>& plaintext) {
    EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
    if (!ctx) return false;
    bool ok = false;
    int len = 0, plaintext_len = 0;
    plaintext.assign(ciphertext.size(), 0);
    if (EVP_DecryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL) != 1) goto cleanup;
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, nonce.size(), NULL) != 1) goto cleanup;
    if (EVP_DecryptInit_ex(ctx, NULL, NULL, key.data(), nonce.data()) != 1) goto cleanup;
    if (EVP_DecryptUpdate(ctx, plaintext.data(), &len, ciphertext.data(), ciphertext.size()) != 1) goto cleanup;
    plaintext_len = len;
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_TAG, tag.size(), (void*)tag.data()) != 1) goto cleanup;
    if (EVP_DecryptFinal_ex(ctx, plaintext.data() + len, &len) != 1) goto cleanup;
    plaintext_len += len;
    plaintext.resize(plaintext_len);
    ok = true;
cleanup:
    EVP_CIPHER_CTX_free(ctx);
    return ok;
}

size_t estimate_lut_size_bytes(const EncryptedLookupTable& lut) {
    size_t total = lut.occupied.capacity() / 8;
    for (const auto& row : lut.slots) total += row.ciphertext.capacity();
    return total;
}

// --- Dynamic-dimension Kim-et-al. IPFE primitives (dim_m = fan_in + 1) ---

struct PublicKey {
    element_t g1, g2, gT_base, g1_base;
};

struct MasterSecretKey {
    int dim_m = 0;
    ElemMatrix B, B_star;
    element_t det_B;
};

struct DecryptionKey {
    int dim_m = 0;
    element_t K1;
    std::vector<Elem> K2;
};

struct Ciphertext {
    int dim_m = 0;
    element_t C1;
    std::vector<Elem> C2;
};

void ClearPublicKey(PublicKey* pk) {
    element_clear(pk->g1); element_clear(pk->g2);
    element_clear(pk->gT_base); element_clear(pk->g1_base);
}
void ClearMasterSecretKey(MasterSecretKey* msk) {
    element_clear(msk->det_B);
    for (auto& row : msk->B) for (auto& e : row) element_clear(e.v);
    for (auto& row : msk->B_star) for (auto& e : row) element_clear(e.v);
}
void ClearDecryptionKey(DecryptionKey* sk) {
    element_clear(sk->K1);
    for (auto& e : sk->K2) element_clear(e.v);
}
void ClearCiphertext(Ciphertext* ct) {
    element_clear(ct->C1);
    for (auto& e : ct->C2) element_clear(e.v);
}

int invert_and_det_matrix_Fq(pairing_t pairing, int dim_m, ElemMatrix& M, ElemMatrix& inverse, element_t det) {
    ElemMatrix aug(dim_m, std::vector<Elem>(2 * dim_m));
    element_t temp, pivot_inv;
    element_init_Zr(temp, pairing);
    element_init_Zr(pivot_inv, pairing);
    element_set1(det);
    int sign = 1;

    for (int i = 0; i < dim_m; i++) {
        for (int j = 0; j < dim_m; j++) {
            element_init_Zr(aug[i][j].v, pairing);
            element_set(aug[i][j].v, M[i][j].v);
            element_init_Zr(aug[i][j + dim_m].v, pairing);
            if (i == j) element_set1(aug[i][j + dim_m].v); else element_set0(aug[i][j + dim_m].v);
        }
    }

    for (int i = 0; i < dim_m; i++) {
        int pivot_row = i;
        for (int k = i + 1; k < dim_m; k++) {
            if (!element_is0(aug[k][i].v)) { pivot_row = k; break; }
        }
        if (element_is0(aug[pivot_row][i].v)) {
            element_set0(det);
            for (int r = 0; r < dim_m; r++) for (int c = 0; c < 2 * dim_m; c++) element_clear(aug[r][c].v);
            element_clear(temp); element_clear(pivot_inv);
            return 0;
        }
        if (pivot_row != i) {
            for (int j = 0; j < 2 * dim_m; j++) {
                element_set(temp, aug[i][j].v);
                element_set(aug[i][j].v, aug[pivot_row][j].v);
                element_set(aug[pivot_row][j].v, temp);
            }
            sign = -sign;
        }
        element_mul(det, det, aug[i][i].v);
        element_invert(pivot_inv, aug[i][i].v);
        for (int j = 0; j < 2 * dim_m; j++) element_mul(aug[i][j].v, aug[i][j].v, pivot_inv);

#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
        for (int k = 0; k < dim_m; k++) {
            if (k != i) {
                element_t factor, local_temp;
                element_init_Zr(factor, pairing);
                element_init_Zr(local_temp, pairing);
                element_set(factor, aug[k][i].v);
                for (int j = 0; j < 2 * dim_m; j++) {
                    element_mul(local_temp, factor, aug[i][j].v);
                    element_sub(aug[k][j].v, aug[k][j].v, local_temp);
                }
                element_clear(factor);
                element_clear(local_temp);
            }
        }
    }

    if (sign == -1) element_neg(det, det);
    for (int i = 0; i < dim_m; i++) for (int j = 0; j < dim_m; j++) element_set(inverse[i][j].v, aug[i][j + dim_m].v);
    element_clear(temp); element_clear(pivot_inv);
    for (int i = 0; i < dim_m; i++) for (int j = 0; j < 2 * dim_m; j++) element_clear(aug[i][j].v);
    return 1;
}

void Setup(pairing_t pairing, PublicKey* pk, MasterSecretKey* msk, int dim_m) {
    element_init_G1(pk->g1, pairing);
    element_init_G2(pk->g2, pairing);
    element_random(pk->g1);
    element_random(pk->g2);
    element_init_GT(pk->gT_base, pairing);
    element_pairing(pk->gT_base, pk->g1, pk->g2);
    element_init_G1(pk->g1_base, pairing);
    element_set(pk->g1_base, pk->g1);

    msk->dim_m = dim_m;
    element_init_Zr(msk->det_B, pairing);
    msk->B.assign(dim_m, std::vector<Elem>(dim_m));
    msk->B_star.assign(dim_m, std::vector<Elem>(dim_m));
    ElemMatrix B_inv(dim_m, std::vector<Elem>(dim_m));

    for (int i = 0; i < dim_m; i++) {
        for (int j = 0; j < dim_m; j++) {
            element_init_Zr(msk->B[i][j].v, pairing);
            element_init_Zr(msk->B_star[i][j].v, pairing);
            element_init_Zr(B_inv[i][j].v, pairing);
        }
    }

    int is_invertible = 0;
    while (!is_invertible) {
#ifdef _OPENMP
#pragma omp parallel for collapse(2) schedule(static)
#endif
        for (int i = 0; i < dim_m; i++) {
            for (int j = 0; j < dim_m; j++) element_random(msk->B[i][j].v);
        }
        is_invertible = invert_and_det_matrix_Fq(pairing, dim_m, msk->B, B_inv, msk->det_B);
    }

#ifdef _OPENMP
#pragma omp parallel for collapse(2) schedule(static)
#endif
    for (int i = 0; i < dim_m; i++) {
        for (int j = 0; j < dim_m; j++) {
            element_t local_temp;
            element_init_Zr(local_temp, pairing);
            element_mul(local_temp, msk->det_B, B_inv[j][i].v);
            element_set(msk->B_star[i][j].v, local_temp);
            element_clear(local_temp);
        }
    }
    for (int i = 0; i < dim_m; i++) for (int j = 0; j < dim_m; j++) element_clear(B_inv[i][j].v);
}

void KeyGen(pairing_t pairing, PublicKey* pk, MasterSecretKey* msk,
            std::vector<Elem>& x, DecryptionKey* sk, element_t alpha_out) {
    int dim_m = msk->dim_m;
    element_t alpha, temp_scalar;
    element_init_Zr(alpha, pairing);
    element_init_Zr(temp_scalar, pairing);
    element_random(alpha);
    element_set(alpha_out, alpha);

    sk->dim_m = dim_m;
    element_init_G1(sk->K1, pairing);
    element_mul(temp_scalar, alpha, msk->det_B);
    element_pow_zn(sk->K1, pk->g1, temp_scalar);

    sk->K2.assign(dim_m, Elem());
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (int i = 0; i < dim_m; i++) {
        element_t dot_product, term;
        element_init_Zr(dot_product, pairing);
        element_init_Zr(term, pairing);
        element_set0(dot_product);
        for (int j = 0; j < dim_m; j++) {
            element_mul(term, x[j].v, msk->B[j][i].v);
            element_add(dot_product, dot_product, term);
        }
        element_mul(dot_product, dot_product, alpha);
        element_init_G1(sk->K2[i].v, pairing);
        element_pow_zn(sk->K2[i].v, pk->g1, dot_product);
        element_clear(dot_product);
        element_clear(term);
    }
    element_clear(alpha);
    element_clear(temp_scalar);
}

void Encrypt(pairing_t pairing, PublicKey* pk, MasterSecretKey* msk,
             std::vector<Elem>& y, Ciphertext* ct, element_t beta_out) {
    int dim_m = msk->dim_m;
    element_t beta;
    element_init_Zr(beta, pairing);
    element_random(beta);
    element_set(beta_out, beta);

    ct->dim_m = dim_m;
    element_init_G2(ct->C1, pairing);
    element_pow_zn(ct->C1, pk->g2, beta);

    ct->C2.assign(dim_m, Elem());
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (int i = 0; i < dim_m; i++) {
        element_t dot_product, term;
        element_init_Zr(dot_product, pairing);
        element_init_Zr(term, pairing);
        element_set0(dot_product);
        for (int j = 0; j < dim_m; j++) {
            element_mul(term, y[j].v, msk->B_star[j][i].v);
            element_add(dot_product, dot_product, term);
        }
        element_mul(dot_product, dot_product, beta);
        element_init_G2(ct->C2[i].v, pairing);
        element_pow_zn(ct->C2[i].v, pk->g2, dot_product);
        element_clear(dot_product);
        element_clear(term);
    }
    element_clear(beta);
}

// --- ReLU non-linearity + requantization into the next layer's [0, MAX_X] input domain ---

int quantized_relu(int pre_activation, int domain_max) {
    int r = pre_activation > 0 ? pre_activation : 0;
    if (domain_max <= 0) return 0;
    if (r > domain_max) r = domain_max;
    long double frac = static_cast<long double>(r) / static_cast<long double>(domain_max);
    int q = static_cast<int>(std::llround(frac * static_cast<long double>(MAX_X)));
    if (q < 0) q = 0;
    if (q > MAX_X) q = MAX_X;
    return q;
}

// --- Per-neuron ReLU LUT: build (unscaled range) + lookup (known-mask fallback) ---
//
// Domain is [MIN_X*MAX_X, MIN_X*MIN_X] regardless of fan_in -- see file header.
// Row payload is fan_in x (BATCH_SIZE+1) G1 elements, matching
// encrypted_forward_prop_kim.cpp's BuildEncryptedLookupTable exactly, just with
// fan_in threaded through as a runtime parameter instead of the FEATURE_SIZE macro.

EncryptedLookupTable BuildReLULUT(pairing_t pairing, PublicKey* pk, int fan_in,
                                   int min_x, int max_x, int r3, int r2,
                                   element_t alpha, element_t beta, element_t det_B,
                                   int z1, int z4,
                                   std::vector<Elem>& betad,
                                   std::vector<std::vector<std::vector<Elem>>>& Bstar,
                                   int idx) {
    EncryptedLookupTable lut;
    lut.min_x = min_x;
    lut.max_x = max_x;

    std::vector<unsigned char> salt = {'F','I','N','E','T','U','N','E','-','R','E','L','U','-','S','A','L','T'};
    std::vector<unsigned char> info = {'H','K','D','F','-','S','H','A','2','5','6','-','R','O','W'};
    const size_t candidate_count = static_cast<size_t>(max_x - min_x + 1);
    std::vector<LookupBuildEntry> entries;
    entries.reserve(candidate_count);

    int thread_count = 1;
#ifdef _OPENMP
    thread_count = omp_get_max_threads();
#endif
    std::vector<std::vector<LookupBuildEntry>> entries_by_thread(static_cast<size_t>(thread_count));

#pragma omp parallel
    {
        int tid = 0;
#ifdef _OPENMP
        tid = omp_get_thread_num();
#endif
        std::vector<LookupBuildEntry>& local_entries = entries_by_thread[static_cast<size_t>(tid)];
        local_entries.reserve((candidate_count / static_cast<size_t>(thread_count)) + 1);

#pragma omp for schedule(static)
        for (int x = min_x; x <= max_x; x++) {
            element_t expt, exp1, gt_val;
            element_init_Zr(expt, pairing);
            element_init_Zr(exp1, pairing);
            element_init_GT(gt_val, pairing);

            element_set_si(expt, r2 * x + r3);
            element_mul(expt, expt, alpha);
            element_mul(expt, expt, beta);
            element_mul(expt, expt, det_B);
            element_set_si(exp1, z1 * quantized_relu(x, max_x) + z4);
            element_pow_zn(gt_val, pk->gT_base, expt);

            std::vector<unsigned char> gt_bytes = serialize_element_to_bytes(gt_val);
            std::vector<unsigned char> plaintext;

            element_t base_exp, slot_exp, slot_g1;
            element_init_Zr(base_exp, pairing);
            element_init_Zr(slot_exp, pairing);
            element_init_G1(slot_g1, pairing);

            for (int feature_idx = 0; feature_idx < fan_in; feature_idx++) {
                for (int batch_idx = 0; batch_idx < BATCH_SIZE + 1; batch_idx++) {
                    element_mul(base_exp, betad[feature_idx].v, Bstar[feature_idx][idx][batch_idx].v);
                    element_mul(slot_exp, base_exp, exp1);
                    element_pow_zn(slot_g1, pk->g1_base, slot_exp);
                    std::vector<unsigned char> slot_bytes = serialize_g1_element_to_compressed_bytes(slot_g1);
                    plaintext.insert(plaintext.end(), slot_bytes.begin(), slot_bytes.end());
                }
            }
            element_clear(base_exp);
            element_clear(slot_exp);
            element_clear(slot_g1);

            std::vector<unsigned char> key;
            if (hkdf_sha256(gt_bytes, salt, info, HKDF_KEY_LEN, key)) {
                EncryptedLookupRow row;
                row.nonce.assign(GCM_NONCE_LEN, 0);
                if (RAND_bytes(row.nonce.data(), row.nonce.size()) == 1 &&
                    aes_gcm_encrypt(key, row.nonce, plaintext, row.ciphertext, row.tag)) {
                    local_entries.push_back({std::move(row), std::move(key)});
                }
            }
            element_clear(expt);
            element_clear(exp1);
            element_clear(gt_val);
        }
    }

    for (auto& local_entries : entries_by_thread) {
        if (!local_entries.empty()) {
            entries.insert(entries.end(), std::make_move_iterator(local_entries.begin()),
                            std::make_move_iterator(local_entries.end()));
        }
    }

    if (!entries.empty()) {
        size_t table_size = next_power_of_two(entries.size() * 2);
        bool built = false;
        for (int rebuild = 0; rebuild < LUT_MAX_REBUILDS; rebuild++) {
            if (build_point_permute_cuckoo(entries, lut, table_size)) { built = true; break; }
            table_size <<= 1;
        }
        if (!built) {
            lut.num_entries = 0;
            lut.table_size = 0;
            lut.slots.clear();
            lut.occupied.clear();
        }
    }
    return lut;
}

// Looks up D2 in the neuron's ReLU LUT. On a hit, decodes the row's G1 tensor
// into L_in_G1 (the caller already knows the true x that produced D2, so it
// does not need to be returned here). On a miss (the expected common case
// for wide layers, since the domain is not scaled by fan-in), falls back:
// draw a value uniformly from [lut.min_x, lut.max_x] using the masks already
// in scope (z1, z4, betad, Bstar), mask it exactly as a real row would be,
// and report that draw via `recovered_x` so the caller propagates a value
// consistent with what was actually produced.
bool MapReLULUT(pairing_t pairing, element_t D2, const EncryptedLookupTable& lut,
                 int fan_in, PublicKey* pk, int z1, int z4,
                 std::vector<Elem>& betad,
                 std::vector<std::vector<std::vector<Elem>>>& Bstar,
                 int idx,
                 std::vector<std::vector<Elem>>& L_in_G1,
                 int* recovered_x, bool* used_fallback,
                 bool verbose = true) {
    std::vector<unsigned char> salt = {'F','I','N','E','T','U','N','E','-','R','E','L','U','-','S','A','L','T'};
    std::vector<unsigned char> info = {'H','K','D','F','-','S','H','A','2','5','6','-','R','O','W'};

    std::vector<unsigned char> d2_bytes = serialize_element_to_bytes(D2);
    std::vector<unsigned char> key;
    *used_fallback = false;

    if (hkdf_sha256(d2_bytes, salt, info, HKDF_KEY_LEN, key) &&
        lut.table_size != 0 && !lut.slots.empty() && !lut.occupied.empty()) {
        size_t idx1 = lut_hash_idx1(key, lut.table_size);
        size_t idx2 = lut_hash_idx2(key, lut.table_size);
        unsigned char permute = lut_permute_bit(key);
        size_t candidates[2] = {permute ? idx2 : idx1, permute ? idx1 : idx2};

        for (size_t slot : candidates) {
            if (slot >= lut.occupied.size() || !lut.occupied[slot]) continue;
            const EncryptedLookupRow& row = lut.slots[slot];
            std::vector<unsigned char> plaintext;
            if (!aes_gcm_decrypt(key, row.nonce, row.ciphertext, row.tag, plaintext)) continue;
            if (plaintext.empty()) continue;

            element_t g1_probe;
            element_init_G1(g1_probe, pairing);
            int g1_comp_len = element_length_in_bytes_compressed(g1_probe);
            element_clear(g1_probe);

            size_t expected_len = static_cast<size_t>(fan_in) * static_cast<size_t>(BATCH_SIZE + 1) *
                                   static_cast<size_t>(g1_comp_len);
            if (plaintext.size() != expected_len) continue;

            L_in_G1.assign(fan_in, std::vector<Elem>(BATCH_SIZE + 1));
            size_t offset = 0;
            for (int f = 0; f < fan_in; f++) {
                for (int b = 0; b < BATCH_SIZE + 1; b++) {
                    element_init_G1(L_in_G1[f][b].v, pairing);
                    element_from_bytes_compressed(L_in_G1[f][b].v,
                                                   const_cast<unsigned char*>(plaintext.data() + offset));
                    offset += static_cast<size_t>(g1_comp_len);
                }
            }
            if (verbose) printf("  lookup hit\n");
            return true;
        }
    }

    // Fallback: masks are already known here, so draw a value in-range and
    // mask it exactly as a genuine row would have been built.
    *used_fallback = true;
    int fallback_x = generate_random_int(lut.min_x, lut.max_x);
    *recovered_x = fallback_x;

    element_t exp1, base_exp, slot_exp;
    element_init_Zr(exp1, pairing);
    element_init_Zr(base_exp, pairing);
    element_init_Zr(slot_exp, pairing);
    element_set_si(exp1, z1 * quantized_relu(fallback_x, lut.max_x) + z4);

    L_in_G1.assign(fan_in, std::vector<Elem>(BATCH_SIZE + 1));
    for (int f = 0; f < fan_in; f++) {
        for (int b = 0; b < BATCH_SIZE + 1; b++) {
            element_mul(base_exp, betad[f].v, Bstar[f][idx][b].v);
            element_mul(slot_exp, base_exp, exp1);
            element_init_G1(L_in_G1[f][b].v, pairing);
            element_pow_zn(L_in_G1[f][b].v, pk->g1_base, slot_exp);
        }
    }
    element_clear(exp1);
    element_clear(base_exp);
    element_clear(slot_exp);
    if (verbose) printf("  lookup miss -> fallback x=%d\n", fallback_x);
    return true;
}

// --- Stats ---
struct LayerStats {
    double setup_ms = 0.0;
    double lut_build_ms = 0.0;
    double decrypt_ms = 0.0;
    long long lut_bytes = 0;
    int neurons_total = 0;
    int neurons_fallback = 0;
};

// --- One dense encrypted ReLU layer: fan_in -> num_neurons ---
std::vector<int> RunDenseReLULayer(pairing_t pairing, int fan_in, int num_neurons,
                                    const std::vector<int>& x_in, LayerStats& stats) {
    std::vector<int> y_out(num_neurons, 0);
    const int dim_m = fan_in + 1;
    const int min_x = MIN_X * MAX_X;
    const int max_x = MIN_X * MIN_X;

    for (int n = 0; n < num_neurons; n++) {
        std::vector<long> w(fan_in), r1(fan_in);
        std::vector<long> x_values(dim_m), y_values(dim_m);
        long r3 = generate_random_int(-(1 << 15), (1 << 15) - 1);
        long r2 = generate_random_int(-(1 << 15), (1 << 15) - 1);

        long output_value = 0;
        for (int i = 0; i < fan_in; i++) {
            w[i] = generate_random_int(MIN_X, MAX_X);
            output_value += w[i] * static_cast<long>(x_in[i]);
        }

        y_values[dim_m - 1] = r3;
        x_values[dim_m - 1] = 1;
        for (int i = 0; i < fan_in; i++) {
            r1[i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
            y_values[dim_m - 1] -= static_cast<long>(x_in[i]) * r1[i];
        }
        long expected_output = 0;
        for (int i = 0; i < fan_in; i++) {
            x_values[i] = r2 * w[i] + r1[i];
            y_values[i] = x_in[i];
        }

        std::vector<Elem> x_vec(dim_m), y_vec(dim_m);
        for (int j = 0; j < dim_m; j++) {
            element_init_Zr(x_vec[j].v, pairing);
            element_init_Zr(y_vec[j].v, pairing);
            element_set_si(x_vec[j].v, x_values[j]);
            element_set_si(y_vec[j].v, y_values[j]);
            expected_output += x_values[j] * y_values[j];
        }
        if (expected_output != (r2 * output_value + r3)) {
            printf("[ASSERTION FAILED] expected_output mismatch at neuron %d\n", n);
        }

        PublicKey pk;
        MasterSecretKey msk;
        DecryptionKey sk;
        Ciphertext ct;
        element_t alpha, beta;
        element_init_Zr(alpha, pairing);
        element_init_Zr(beta, pairing);

        auto t0 = std::chrono::steady_clock::now();
        Setup(pairing, &pk, &msk, dim_m);
        auto t1 = std::chrono::steady_clock::now();
        stats.setup_ms += std::chrono::duration<double, std::milli>(t1 - t0).count();

        KeyGen(pairing, &pk, &msk, x_vec, &sk, alpha);
        Encrypt(pairing, &pk, &msk, y_vec, &ct, beta);

        int z1 = generate_random_int(-(1 << 15), (1 << 15) - 1);
        int z4 = generate_random_int(-(1 << 15), (1 << 15) - 1);
        std::vector<Elem> betad(fan_in);
        std::vector<std::vector<std::vector<Elem>>> Bstar(
            fan_in, std::vector<std::vector<Elem>>(BATCH_SIZE + 1, std::vector<Elem>(BATCH_SIZE + 1)));

        for (int f = 0; f < fan_in; f++) {
            element_init_Zr(betad[f].v, pairing);
            element_random(betad[f].v);

            ElemMatrix B(BATCH_SIZE + 1, std::vector<Elem>(BATCH_SIZE + 1));
            ElemMatrix B_inv(BATCH_SIZE + 1, std::vector<Elem>(BATCH_SIZE + 1));
            element_t det_Bf, tmp;
            element_init_Zr(det_Bf, pairing);
            element_init_Zr(tmp, pairing);
            for (int i = 0; i <= BATCH_SIZE; i++) {
                for (int j = 0; j <= BATCH_SIZE; j++) {
                    element_init_Zr(B[i][j].v, pairing);
                    element_init_Zr(B_inv[i][j].v, pairing);
                    element_init_Zr(Bstar[f][i][j].v, pairing);
                }
            }
            int is_invertible = 0;
            while (!is_invertible) {
                for (int i = 0; i <= BATCH_SIZE; i++)
                    for (int j = 0; j <= BATCH_SIZE; j++) element_random(B[i][j].v);
                is_invertible = invert_and_det_matrix_Fq(pairing, BATCH_SIZE + 1, B, B_inv, det_Bf);
            }
            for (int i = 0; i <= BATCH_SIZE; i++) {
                for (int j = 0; j <= BATCH_SIZE; j++) {
                    element_mul(tmp, det_Bf, B_inv[j][i].v);
                    element_set(Bstar[f][i][j].v, tmp);
                }
            }
            element_clear(det_Bf);
            element_clear(tmp);
            for (int i = 0; i <= BATCH_SIZE; i++)
                for (int j = 0; j <= BATCH_SIZE; j++) { element_clear(B[i][j].v); element_clear(B_inv[i][j].v); }
        }

        auto t2 = std::chrono::steady_clock::now();
        EncryptedLookupTable lut = BuildReLULUT(pairing, &pk, fan_in, min_x, max_x, r3, r2,
                                                 alpha, beta, msk.det_B, z1, z4, betad, Bstar, 0);
        auto t3 = std::chrono::steady_clock::now();
        stats.lut_build_ms += std::chrono::duration<double, std::milli>(t3 - t2).count();
        stats.lut_bytes += static_cast<long long>(estimate_lut_size_bytes(lut));

        element_t D1, D2, temp_pairing;
        element_init_GT(D1, pairing);
        element_init_GT(D2, pairing);
        element_init_GT(temp_pairing, pairing);

        auto t4 = std::chrono::steady_clock::now();
        element_pairing(D1, sk.K1, ct.C1);
        element_set1(D2);
        for (int i = 0; i < dim_m; i++) {
            element_pairing(temp_pairing, sk.K2[i].v, ct.C2[i].v);
            element_mul(D2, D2, temp_pairing);
        }
        auto t5 = std::chrono::steady_clock::now();
        stats.decrypt_ms += std::chrono::duration<double, std::milli>(t5 - t4).count();

        element_t expected_exp, D1_expected;
        element_init_Zr(expected_exp, pairing);
        element_init_GT(D1_expected, pairing);
        element_set_si(expected_exp, expected_output);
        element_pow_zn(D1_expected, D1, expected_exp);
        if (element_cmp(D1_expected, D2) != 0) {
            printf("[ASSERTION FAILED] D1^expected_output != D2 at neuron %d\n", n);
        }
        element_clear(expected_exp);
        element_clear(D1_expected);

        std::vector<std::vector<Elem>> L_in_G1;
        int recovered_x = 0;
        bool used_fallback = false;
        MapReLULUT(pairing, D2, lut, fan_in, &pk, z1, z4, betad, Bstar, 0,
                   L_in_G1, &recovered_x, &used_fallback, false);
        if (!used_fallback) recovered_x = static_cast<int>(output_value);

        stats.neurons_total++;
        if (used_fallback) stats.neurons_fallback++;
        y_out[n] = quantized_relu(recovered_x, max_x);

        for (auto& row : L_in_G1) for (auto& e : row) element_clear(e.v);
        element_clear(D1); element_clear(D2); element_clear(temp_pairing);
        for (int j = 0; j < dim_m; j++) { element_clear(x_vec[j].v); element_clear(y_vec[j].v); }
        for (auto& e : betad) element_clear(e.v);
        for (auto& plane : Bstar) for (auto& row : plane) for (auto& e : row) element_clear(e.v);
        element_clear(alpha); element_clear(beta);
        ClearDecryptionKey(&sk);
        ClearCiphertext(&ct);
        ClearMasterSecretKey(&msk);
        ClearPublicKey(&pk);
    }
    return y_out;
}

// --- Per-head hand-off: Setup/KeyGen/Encrypt for each of HEAD_CLASSES weight
//     vectors, all encrypting the shared 16-dim pseudo-feature vector. These
//     (sk, ct) pairs are exactly what encrypted_forward_prop_kim_multiclass.cpp
//     (Stage-A/B softmax LUT) and encrypted_backward_prop_kim_multiclass.cpp
//     (gradient LUTs), both compiled with FEATURE_SIZE=16, expect as input.

struct HeadStats {
    double setup_ms = 0.0;
    long long keygen_us = 0;
    long long encrypt_us = 0;
    long long ciphertext_bytes = 0;
};

void RunHeadEncrypt(pairing_t pairing, int head_id, int feature_dim,
                     const std::vector<int>& pseudo_features, HeadStats& stats) {
    const int dim_m = feature_dim + 1;
    for (int c = 0; c < HEAD_CLASSES; c++) {
        std::vector<long> w(feature_dim), r1(feature_dim);
        std::vector<long> x_values(dim_m), y_values(dim_m);
        long r3 = generate_random_int(-(1 << 15), (1 << 15) - 1);
        long r2 = generate_random_int(-(1 << 15), (1 << 15) - 1);

        for (int i = 0; i < feature_dim; i++) w[i] = generate_random_int(MIN_X, MAX_X);
        y_values[dim_m - 1] = r3;
        x_values[dim_m - 1] = 1;
        for (int i = 0; i < feature_dim; i++) {
            r1[i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
            y_values[dim_m - 1] -= static_cast<long>(pseudo_features[i]) * r1[i];
        }
        for (int i = 0; i < feature_dim; i++) {
            x_values[i] = r2 * w[i] + r1[i];
            y_values[i] = pseudo_features[i];
        }

        std::vector<Elem> x_vec(dim_m), y_vec(dim_m);
        for (int j = 0; j < dim_m; j++) {
            element_init_Zr(x_vec[j].v, pairing);
            element_init_Zr(y_vec[j].v, pairing);
            element_set_si(x_vec[j].v, x_values[j]);
            element_set_si(y_vec[j].v, y_values[j]);
        }

        PublicKey pk;
        MasterSecretKey msk;
        DecryptionKey sk;
        Ciphertext ct;
        element_t alpha, beta;
        element_init_Zr(alpha, pairing);
        element_init_Zr(beta, pairing);

        auto t0 = std::chrono::steady_clock::now();
        Setup(pairing, &pk, &msk, dim_m);
        auto t1 = std::chrono::steady_clock::now();
        stats.setup_ms += std::chrono::duration<double, std::milli>(t1 - t0).count();

        auto t2 = std::chrono::steady_clock::now();
        KeyGen(pairing, &pk, &msk, x_vec, &sk, alpha);
        auto t3 = std::chrono::steady_clock::now();
        stats.keygen_us += std::chrono::duration_cast<std::chrono::microseconds>(t3 - t2).count();

        auto t4 = std::chrono::steady_clock::now();
        Encrypt(pairing, &pk, &msk, y_vec, &ct, beta);
        auto t5 = std::chrono::steady_clock::now();
        stats.encrypt_us += std::chrono::duration_cast<std::chrono::microseconds>(t5 - t4).count();

        long long ct_bytes = element_length_in_bytes(ct.C1);
        for (auto& e : ct.C2) ct_bytes += element_length_in_bytes(e.v);
        stats.ciphertext_bytes += ct_bytes;

        for (int j = 0; j < dim_m; j++) { element_clear(x_vec[j].v); element_clear(y_vec[j].v); }
        element_clear(alpha); element_clear(beta);
        ClearDecryptionKey(&sk);
        ClearCiphertext(&ct);
        ClearMasterSecretKey(&msk);
        ClearPublicKey(&pk);
    }
    (void)head_id;
}

int main() {
    srand(static_cast<unsigned>(time(NULL)));
#ifdef _OPENMP
    omp_set_dynamic(0);
    omp_set_num_threads(omp_get_max_threads());
#endif

    pairing_t pairing;
    pbc_param_t pbc_param;
    pbc_param_init_a_gen(pbc_param, 80, 256);
    pairing_init_pbc_param(pairing, pbc_param);
    pbc_param_clear(pbc_param);

    printf("=== Finetuning encrypted forward pass: %d -> %d -> %d, ReLU LUTs (unscaled range) ===\n",
           INPUT_DIM, HIDDEN1_DIM, HIDDEN2_DIM);
    printf("QUANTIZATION_BITS=%d (MIN_X=%d, MAX_X=%d), BATCH_SIZE=%d, NUM_HEADS=%d, HEAD_CLASSES=%d\n\n",
           QUANTIZATION_BITS, MIN_X, MAX_X, BATCH_SIZE, NUM_HEADS, HEAD_CLASSES);

    std::vector<int> input_features(INPUT_DIM);
    for (int i = 0; i < INPUT_DIM; i++) input_features[i] = generate_random_int(MIN_X, MAX_X);

    LayerStats l1_stats, l2_stats;

    auto layer1_start = std::chrono::steady_clock::now();
    std::vector<int> hidden1 = RunDenseReLULayer(pairing, INPUT_DIM, HIDDEN1_DIM, input_features, l1_stats);
    auto layer1_stop = std::chrono::steady_clock::now();
    double layer1_wall_ms = std::chrono::duration<double, std::milli>(layer1_stop - layer1_start).count();

    printf("Layer 1 (%d -> %d): wall %.1f ms | Setup %.1f ms | LUT build %.1f ms | Decrypt %.1f ms\n",
           INPUT_DIM, HIDDEN1_DIM, layer1_wall_ms, l1_stats.setup_ms, l1_stats.lut_build_ms, l1_stats.decrypt_ms);
    printf("  LUT bytes: %lld | fallback rate: %d / %d neurons\n\n",
           l1_stats.lut_bytes, l1_stats.neurons_fallback, l1_stats.neurons_total);

    auto layer2_start = std::chrono::steady_clock::now();
    std::vector<int> hidden2 = RunDenseReLULayer(pairing, HIDDEN1_DIM, HIDDEN2_DIM, hidden1, l2_stats);
    auto layer2_stop = std::chrono::steady_clock::now();
    double layer2_wall_ms = std::chrono::duration<double, std::milli>(layer2_stop - layer2_start).count();

    printf("Layer 2 (%d -> %d): wall %.1f ms | Setup %.1f ms | LUT build %.1f ms | Decrypt %.1f ms\n",
           HIDDEN1_DIM, HIDDEN2_DIM, layer2_wall_ms, l2_stats.setup_ms, l2_stats.lut_build_ms, l2_stats.decrypt_ms);
    printf("  LUT bytes: %lld | fallback rate: %d / %d neurons\n\n",
           l2_stats.lut_bytes, l2_stats.neurons_fallback, l2_stats.neurons_total);

    printf("Pseudo-feature vector (%d-dim), fed to %d heads: [", HIDDEN2_DIM, NUM_HEADS);
    for (int i = 0; i < HIDDEN2_DIM; i++) printf("%d%s", hidden2[i], (i + 1 < HIDDEN2_DIM) ? ", " : "");
    printf("]\n\n");

    HeadStats head_stats;
    auto heads_start = std::chrono::steady_clock::now();
    for (int h = 0; h < NUM_HEADS; h++) {
        RunHeadEncrypt(pairing, h, HIDDEN2_DIM, hidden2, head_stats);
    }
    auto heads_stop = std::chrono::steady_clock::now();
    double heads_wall_ms = std::chrono::duration<double, std::milli>(heads_stop - heads_start).count();

    printf("Heads (%d heads x %d classes, feature_dim=%d): wall %.1f ms | Setup %.1f ms | "
           "KeyGen %lld us | Encrypt %lld us\n",
           NUM_HEADS, HEAD_CLASSES, HIDDEN2_DIM, heads_wall_ms, head_stats.setup_ms,
           head_stats.keygen_us, head_stats.encrypt_us);
    printf("  Total ciphertext bytes handed to the %d forward/backward heads: %lld\n",
           NUM_HEADS, head_stats.ciphertext_bytes);
    printf("  (Each head's own Stage-A/B softmax LUT and gradient LUTs are built by\n"
           "   encrypted_forward_prop_kim_multiclass.cpp / encrypted_backward_prop_kim_multiclass.cpp\n"
           "   compiled with FEATURE_SIZE=%d, consuming the sk/ct pairs produced above.)\n",
           HIDDEN2_DIM);

    pairing_clear(pairing);
    return 0;
}
