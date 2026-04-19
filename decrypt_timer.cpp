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

#define FEATURE_SIZE 30
#define NUM_SAMPLES 569
#define DIM_M (FEATURE_SIZE + 2)

long long total_decrypt_ms = 0;
double total_lookup_us = 0.0;

// --- Struct Definitions for Kim et al. Scheme ---
typedef struct {
    element_t g1;
    element_t g2;
    element_t gT_base; // Retained for compatibility with existing LUT builder
    element_t g1_base; // Retained for compatibility with existing LUT builder
} PublicKey;

typedef struct {
    element_t B[DIM_M][DIM_M];
    element_t B_star[DIM_M][DIM_M];
    element_t det_B;
} MasterSecretKey;

typedef struct {
    element_t K1;
    element_t K2[DIM_M];
} DecryptionKey;

typedef struct {
    element_t C1;
    element_t C2[DIM_M];
} Ciphertext;

struct EncryptedLookupRow {
    std::vector<unsigned char> nonce;
    std::vector<unsigned char> ciphertext;
    std::vector<unsigned char> tag;
};

struct EncryptedLookupTable {
    int min_x;
    int max_x;
    size_t num_entries;
    size_t table_size;
    std::vector<EncryptedLookupRow> slots;
    std::vector<unsigned char> occupied;
};

struct SampleArtifacts {
    PublicKey pk;
    DecryptionKey sk;
    Ciphertext ct;
    EncryptedLookupTable lut;
    long r4 = 0;
    long r3 = 0;
    long expected_output = 0;
    long output_values = 0;
    bool has_pk = false;
    bool has_sk = false;
    bool has_ct = false;
};

struct DecryptPhaseArtifacts {
    element_t D1;
    element_t D2;
    element_t L_in_G1;
    bool has_D1 = false;
    bool has_D2 = false;
    bool has_L_in_G1 = false;
};

size_t estimate_lut_size_bytes(const EncryptedLookupTable& lut) {
    size_t total = sizeof(EncryptedLookupTable);
    total += lut.slots.capacity() * sizeof(EncryptedLookupRow);
    total += lut.occupied.capacity() * sizeof(unsigned char);

    for (const auto& row : lut.slots) {
        total += row.nonce.capacity() * sizeof(unsigned char);
        total += row.ciphertext.capacity() * sizeof(unsigned char);
        total += row.tag.capacity() * sizeof(unsigned char);
    }

    return total;
}

size_t estimate_lut_row_size_bytes(const EncryptedLookupRow& row) {
    size_t total = sizeof(EncryptedLookupRow);
    total += row.nonce.capacity() * sizeof(unsigned char);
    total += row.ciphertext.capacity() * sizeof(unsigned char);
    total += row.tag.capacity() * sizeof(unsigned char);
    return total;
}

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
    while (p < x) {
        p <<= 1;
    }
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
                                EncryptedLookupTable& lut,
                                size_t table_size) {
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

        if (!inserted) {
            return false;
        }
    }

    return true;
}

std::vector<unsigned char> serialize_element_to_bytes(element_t e) {
    int len = element_length_in_bytes(e);
    std::vector<unsigned char> out(len);
    element_to_bytes(out.data(), e);
    return out;
}

void append_u32_be(std::vector<unsigned char>& buffer, uint32_t value) {
    buffer.push_back((value >> 24) & 0xFF);
    buffer.push_back((value >> 16) & 0xFF);
    buffer.push_back((value >> 8) & 0xFF);
    buffer.push_back(value & 0xFF);
}

uint32_t read_u32_be(const std::vector<unsigned char>& buffer, size_t offset) {
    return (static_cast<uint32_t>(buffer[offset]) << 24) |
           (static_cast<uint32_t>(buffer[offset + 1]) << 16) |
           (static_cast<uint32_t>(buffer[offset + 2]) << 8) |
           static_cast<uint32_t>(buffer[offset + 3]);
}

bool hkdf_sha256(const std::vector<unsigned char>& ikm,
                 const std::vector<unsigned char>& salt,
                 const std::vector<unsigned char>& info,
                 size_t out_len,
                 std::vector<unsigned char>& out_key) {
    const EVP_MD* md = EVP_sha256();
    const size_t hash_len = EVP_MD_size(md);

    std::vector<unsigned char> effective_salt = salt;
    if (effective_salt.empty()) {
        effective_salt.assign(hash_len, 0);
    }

    unsigned char prk[EVP_MAX_MD_SIZE];
    unsigned int prk_len = 0;
    if (!HMAC(md,
              effective_salt.data(), static_cast<int>(effective_salt.size()),
              ikm.data(), ikm.size(),
              prk, &prk_len)) {
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
    int len = 0;
    int ciphertext_len = 0;
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
    int len = 0;
    int plaintext_len = 0;
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

long double sigmoid(long double x) {
    return 1.0L / (1.0L + std::exp(-x));
}

int non_linear_transform(long double x) {
    return static_cast<int>(sigmoid(x / (1 << 14)) * (1 << 7));
}

EncryptedLookupTable BuildEncryptedLookupTable(pairing_t pairing, PublicKey* pk, int min_x, int max_x, int r3, int r4, element_t alpha, element_t beta, element_t det_B) {
    EncryptedLookupTable lut;
    lut.min_x = min_x;
    lut.max_x = max_x;
    lut.num_entries = 0;
    lut.table_size = 0;

    std::vector<unsigned char> salt = {'G','T','2','G','1','-','L','U','T','-','S','A','L','T'};
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
            element_t expt, exp1, gt_val, g1_val;
            element_init_Zr(expt, pairing);
            element_init_Zr(exp1, pairing);
            element_init_GT(gt_val, pairing);
            element_init_G1(g1_val, pairing);

            element_set_si(expt, r4 * x + r3);
            element_mul(expt, expt, alpha);
            element_mul(expt, expt, beta);
            element_mul(expt, expt, det_B);
            element_set_si(exp1, r4 * non_linear_transform((long double)x) + r3);
            element_pow_zn(gt_val, pk->gT_base, expt);
            element_pow_zn(g1_val, pk->g1_base, exp1);

            std::vector<unsigned char> gt_bytes = serialize_element_to_bytes(gt_val);
            std::vector<unsigned char> g1_bytes = serialize_element_to_bytes(g1_val);

            std::vector<unsigned char> plaintext = g1_bytes;

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
            element_clear(g1_val);
        }
    }

    for (auto& local_entries : entries_by_thread) {
        if (!local_entries.empty()) {
            entries.insert(entries.end(),
                           std::make_move_iterator(local_entries.begin()),
                           std::make_move_iterator(local_entries.end()));
        }
    }

    if (!entries.empty()) {
        size_t table_size = next_power_of_two(entries.size() * 2);
        bool built = false;
        for (int rebuild = 0; rebuild < LUT_MAX_REBUILDS; rebuild++) {
            if (build_point_permute_cuckoo(entries, lut, table_size)) {
                built = true;
                break;
            }
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

bool MapLTinGTtoG1WithEncryptedLUT(pairing_t pairing,
                                   element_t L_T,
                                   const EncryptedLookupTable& lut,
                                   element_t L_in_G1,
                                   bool verbose = true) {
    std::vector<unsigned char> salt = {'G','T','2','G','1','-','L','U','T','-','S','A','L','T'};
    std::vector<unsigned char> info = {'H','K','D','F','-','S','H','A','2','5','6','-','R','O','W'};

    std::vector<unsigned char> lt_bytes = serialize_element_to_bytes(L_T);
    std::vector<unsigned char> key;
    if (!hkdf_sha256(lt_bytes, salt, info, HKDF_KEY_LEN, key)) {
        return false;
    }

    if (lut.table_size == 0 || lut.slots.empty() || lut.occupied.empty()) {
        return false;
    }

    size_t idx1 = lut_hash_idx1(key, lut.table_size);
    size_t idx2 = lut_hash_idx2(key, lut.table_size);
    unsigned char permute = lut_permute_bit(key);
    size_t candidates[2] = {
        permute ? idx2 : idx1,
        permute ? idx1 : idx2
    };

    for (size_t idx : candidates) {
        if (idx >= lut.occupied.size() || !lut.occupied[idx]) {
            continue;
        }

        const EncryptedLookupRow& row = lut.slots[idx];
        std::vector<unsigned char> plaintext;
        if (!aes_gcm_decrypt(key, row.nonce, row.ciphertext, row.tag, plaintext)) {
            continue;
        }

        if (plaintext.empty()) {
            continue;
        }

        std::vector<unsigned char> row_g1_bytes = plaintext;
        element_init_G1(L_in_G1, pairing);
        element_from_bytes(L_in_G1, row_g1_bytes.data());
        if (verbose) {
            printf("Lookup completed with success\n");
        }
        return true;
    }
    if (verbose) {
        printf("Lookup completed with failure\n");
    }
    return false;
}

// --- Modified Matrix Inversion over Fq using Gaussian Elimination (Simultaneous Inv & Det) ---
int invert_and_det_matrix_Fq(pairing_t pairing, element_t M[DIM_M][DIM_M], element_t inverse[DIM_M][DIM_M], element_t det) {
    element_t aug[DIM_M][2 * DIM_M];
    element_t temp, pivot_inv, factor;
    
    element_init_Zr(temp, pairing);
    element_init_Zr(pivot_inv, pairing);
    element_init_Zr(factor, pairing);
    
    element_set1(det);
    int sign = 1;

    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_init_Zr(aug[i][j], pairing);
            element_set(aug[i][j], M[i][j]);
            
            element_init_Zr(aug[i][j + DIM_M], pairing);
            if (i == j) {
                element_set1(aug[i][j + DIM_M]);
            } else {
                element_set0(aug[i][j + DIM_M]);
            }
        }
    }

    for (int i = 0; i < DIM_M; i++) {
        int pivot_row = i;
        for (int k = i + 1; k < DIM_M; k++) {
            if (!element_is0(aug[k][i])) {
                pivot_row = k;
                break;
            }
        }
        if (element_is0(aug[pivot_row][i])) {
            element_set0(det);
            for (int r = 0; r < DIM_M; r++) {
                for (int c = 0; c < 2 * DIM_M; c++) {
                    element_clear(aug[r][c]);
                }
            }
            element_clear(temp);
            element_clear(pivot_inv);
            element_clear(factor);
            return 0; // Singular matrix encountered
        }

        if (pivot_row != i) {
            for (int j = 0; j < 2 * DIM_M; j++) {
                element_set(temp, aug[i][j]);
                element_set(aug[i][j], aug[pivot_row][j]);
                element_set(aug[pivot_row][j], temp);
            }
            sign = -sign;
        }

        element_mul(det, det, aug[i][i]);
        element_invert(pivot_inv, aug[i][i]);
        for (int j = 0; j < 2 * DIM_M; j++) {
            element_mul(aug[i][j], aug[i][j], pivot_inv);
        }

        for (int k = 0; k < DIM_M; k++) {
            if (k != i) {
                element_set(factor, aug[k][i]);
                for (int j = 0; j < 2 * DIM_M; j++) {
                    element_mul(temp, factor, aug[i][j]);
                    element_sub(aug[k][j], aug[k][j], temp);
                }
            }
        }
    }

    if (sign == -1) {
        element_neg(det, det);
    }

    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_set(inverse[i][j], aug[i][j + DIM_M]);
        }
    }

    element_clear(temp);
    element_clear(pivot_inv);
    element_clear(factor);
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < 2 * DIM_M; j++) {
            element_clear(aug[i][j]);
        }
    }

    return 1;
}

// --- 1. Setup Algorithm (Kim et al. Section 3) ---
void Setup(pairing_t pairing, PublicKey* pk, MasterSecretKey* msk) {
    element_init_G1(pk->g1, pairing);
    element_init_G2(pk->g2, pairing);
    element_random(pk->g1);
    element_random(pk->g2);

    // Initializing LUT target bases
    element_init_GT(pk->gT_base, pairing);
    element_pairing(pk->gT_base, pk->g1, pk->g2); 
    
    element_init_G1(pk->g1_base, pairing);
    element_set(pk->g1_base, pk->g1);

    element_init_Zr(msk->det_B, pairing);

    element_t B_inv[DIM_M][DIM_M];
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_init_Zr(msk->B[i][j], pairing);
            element_init_Zr(msk->B_star[i][j], pairing);
            element_init_Zr(B_inv[i][j], pairing);
        }
    }

    int is_invertible = 0;
    while (!is_invertible) {
        for (int i = 0; i < DIM_M; i++) {
            for (int j = 0; j < DIM_M; j++) {
                element_random(msk->B[i][j]);
            }
        }
        is_invertible = invert_and_det_matrix_Fq(pairing, msk->B, B_inv, msk->det_B);
    }

    element_t temp;
    element_init_Zr(temp, pairing);
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_mul(temp, msk->det_B, B_inv[j][i]);
            element_set(msk->B_star[i][j], temp);
        }
    }
    
    element_clear(temp);
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_clear(B_inv[i][j]);
        }
    }
}

// --- 2. Key Generation Algorithm (Kim et al. Section 3) ---
void KeyGen(pairing_t pairing, PublicKey* pk, MasterSecretKey* msk, element_t x[DIM_M], DecryptionKey* sk, element_t alpha_out) {
    element_t alpha, temp_scalar;
    element_init_Zr(alpha, pairing);
    element_init_Zr(temp_scalar, pairing);
    element_random(alpha);
    element_set(alpha_out, alpha);

    // K1 = g1^(alpha * det_B)
    element_init_G1(sk->K1, pairing);
    element_mul(temp_scalar, alpha, msk->det_B);
    element_pow_zn(sk->K1, pk->g1, temp_scalar);

    // K2 = g1^(alpha * x * B)
    element_t dot_product, term;
    element_init_Zr(dot_product, pairing);
    element_init_Zr(term, pairing);

    for (int i = 0; i < DIM_M; i++) {
        element_set0(dot_product);
        for (int j = 0; j < DIM_M; j++) {
            element_mul(term, x[j], msk->B[j][i]);
            element_add(dot_product, dot_product, term);
        }
        element_mul(dot_product, dot_product, alpha);
        
        element_init_G1(sk->K2[i], pairing);
        element_pow_zn(sk->K2[i], pk->g1, dot_product);
    }

    element_clear(alpha);
    element_clear(temp_scalar);
    element_clear(dot_product);
    element_clear(term);
}

// --- 3. Encrypt Algorithm (Kim et al. Section 3) ---
void Encrypt(pairing_t pairing, PublicKey* pk, MasterSecretKey* msk, element_t y[DIM_M], Ciphertext* ct, element_t beta_out) {
    element_t beta;
    element_init_Zr(beta, pairing);
    element_random(beta);
    element_set(beta_out, beta);

    // C1 = g2^beta
    element_init_G2(ct->C1, pairing);
    element_pow_zn(ct->C1, pk->g2, beta);

    // C2 = g2^(beta * y * B_star)
    element_t dot_product, term;
    element_init_Zr(dot_product, pairing);
    element_init_Zr(term, pairing);

    for (int i = 0; i < DIM_M; i++) {
        element_set0(dot_product);
        for (int j = 0; j < DIM_M; j++) {
            element_mul(term, y[j], msk->B_star[j][i]);
            element_add(dot_product, dot_product, term);
        }
        element_mul(dot_product, dot_product, beta);

        element_init_G2(ct->C2[i], pairing);
        element_pow_zn(ct->C2[i], pk->g2, dot_product);
    }

    element_clear(beta);
    element_clear(dot_product);
    element_clear(term);
}

void ClearDecryptionKey(DecryptionKey* sk) {
    element_clear(sk->K1);
    for (int i = 0; i < DIM_M; i++) {
        element_clear(sk->K2[i]);
    }
}

void ClearCiphertexts(Ciphertext* ct) {
    element_clear(ct->C1);
    for (int i = 0; i < DIM_M; i++) {
        element_clear(ct->C2[i]);
    }
}

void ClearPublicKey(PublicKey* pk) {
    element_clear(pk->g1);
    element_clear(pk->g2);
    element_clear(pk->gT_base);
    element_clear(pk->g1_base);
}

void ClearMasterSecretKey(MasterSecretKey* msk) {
    element_clear(msk->det_B);
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_clear(msk->B[i][j]);
            element_clear(msk->B_star[i][j]);
        }
    }
}

void ClearSampleArtifacts(SampleArtifacts* sample) {
    if (sample->has_sk) {
        ClearDecryptionKey(&sample->sk);
        sample->has_sk = false;
    }
    if (sample->has_ct) {
        ClearCiphertexts(&sample->ct);
        sample->has_ct = false;
    }
    if (sample->has_pk) {
        ClearPublicKey(&sample->pk);
        sample->has_pk = false;
    }
    sample->lut = EncryptedLookupTable();
}

void ClearDecryptPhaseArtifacts(DecryptPhaseArtifacts* artifacts) {
    if (artifacts->has_L_in_G1) {
        element_clear(artifacts->L_in_G1);
        artifacts->has_L_in_G1 = false;
    }
    if (artifacts->has_D2) {
        element_clear(artifacts->D2);
        artifacts->has_D2 = false;
    }
    if (artifacts->has_D1) {
        element_clear(artifacts->D1);
        artifacts->has_D1 = false;
    }
}

// --- 4. Decrypt Algorithm (Kim et al. Section 3) ---
bool Decrypt(pairing_t pairing, PublicKey* pk, DecryptionKey* sk, Ciphertext* ct, const EncryptedLookupTable& lut,
             long r4, long r3, long expected_output, long output_value, bool verbose = true) {
    element_t D1, D2, temp_pairing;
    element_init_GT(D1, pairing);
    element_init_GT(D2, pairing);
    element_init_GT(temp_pairing, pairing);

    // D1 = e(K1, C1)
    element_pairing(D1, sk->K1, ct->C1);

    // D2 = product e(K2[i], C2[i])
    auto start = std::chrono::steady_clock::now();
    element_set1(D2);
    for (int i = 0; i < DIM_M; i++) {
        element_pairing(temp_pairing, sk->K2[i], ct->C2[i]);
        element_mul(D2, D2, temp_pairing);
    }

    auto stop = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
#ifdef _OPENMP
    #pragma omp atomic update
#endif
    total_decrypt_ms += duration.count();

    if (verbose) {
        printf("Decrypt pairings completed in %lld ms\n", duration.count());
    }

    element_t expected_exp, D1_expected;
    element_init_Zr(expected_exp, pairing);
    element_init_GT(D1_expected, pairing);
    element_set_si(expected_exp, expected_output);
    element_pow_zn(D1_expected, D1, expected_exp);
    if (element_cmp(D1_expected, D2) != 0) {
        printf("[ASSERTION FAILED] D1^expected_output != D2\n");
        element_clear(expected_exp);
        element_clear(D1_expected);
        element_clear(D1);
        element_clear(D2);
        element_clear(temp_pairing);
        return false;
    }
    element_clear(expected_exp);
    element_clear(D1_expected);

    // Pass D2 off to the LUT. In a fully symmetric system where D1 changes organically, 
    // LUT structure would hash a pairing derived value or be modified, but we pass D2 
    // seamlessly directly down here.
    element_t L_in_G1;
    if (!MapLTinGTtoG1WithEncryptedLUT(pairing, D2, lut, L_in_G1, verbose)) {
        printf("Failed to map D2 from GT to G1 using encrypted LUT.\n");
        element_clear(D1);
        element_clear(D2);
        element_clear(temp_pairing);
        return false;
    }

    element_t lut_exp, expected_L_in_G1;
    element_init_Zr(lut_exp, pairing);
    element_init_G1(expected_L_in_G1, pairing);
    element_set_si(lut_exp, r4 * non_linear_transform((long double)output_value) + r3);
    element_pow_zn(expected_L_in_G1, pk->g1, lut_exp);
    if (element_cmp(L_in_G1, expected_L_in_G1) != 0) {
        printf("[ASSERTION FAILED] L_in_G1 != g1^(r4 * non_linear_transform(output_value) + r3)\n");
        element_clear(lut_exp);
        element_clear(expected_L_in_G1);
        element_clear(L_in_G1);
        element_clear(D1);
        element_clear(D2);
        element_clear(temp_pairing);
        return false;
    }

    if (verbose) {
        printf("Mapped D2 from GT to G1 using encrypted LUT.\n");
    }

    element_clear(lut_exp);
    element_clear(expected_L_in_G1);
    element_clear(L_in_G1);

    element_clear(D1);
    element_clear(D2);
    element_clear(temp_pairing);
    return true;
}

int generate_random_int(int min_val, int max_val) {
    try {
        std::random_device rd;
        std::mt19937_64 gen(rd());
        std::uniform_int_distribution<int> dist(min_val, max_val);
        int randomValue = dist(gen);
        return randomValue;
    } catch (const std::exception &e) {
        std::cerr << "Error generating random number: " << e.what() << "\n";
        return 1;
    }
    return 0;
}

int main() {
    srand(time(NULL));

#ifdef _OPENMP
    omp_set_dynamic(0);
    omp_set_num_threads(32);
#endif

    pairing_t pairing;
    pbc_param_t pbc_param;
    // pbc_param_init_a_gen(pbc_param, 80, 256);
    pbc_param_init_a_gen(pbc_param, 160, 512);
    pairing_init_pbc_param(pairing, pbc_param);
    pbc_param_clear(pbc_param);

    double total_setup_ms = 0.0;
    double total_lut_build_ms = 0.0;
    long double total_lut_size_bytes = 0.0L;
    long long total_keygen_ms = 0;
    long long total_encrypt_ms = 0;
    double decrypt_bilinear_parallel_ms = 0.0;
    double decrypt_expected_cmp_ms = 0.0;
    double decrypt_lookup_parallel_ms = 0.0;
    double decrypt_final_cmp_ms = 0.0;
    bool failed = false;
    int failed_sample = -1;

    std::vector<SampleArtifacts> samples(NUM_SAMPLES);

    // Phase 1: setup, keygen, encrypt, LUT build, and store all artifacts.
    for (int sample = 0; sample < NUM_SAMPLES; sample++) {
        SampleArtifacts& sample_data = samples[static_cast<size_t>(sample)];
        auto sample_phase1_start = std::chrono::steady_clock::now();

        MasterSecretKey msk;
        auto start = std::chrono::steady_clock::now();
        Setup(pairing, &sample_data.pk, &msk);
        sample_data.has_pk = true;
        auto stop = std::chrono::steady_clock::now();
        total_setup_ms += std::chrono::duration<double, std::milli>(stop - start).count();

        element_t alpha_sample, beta_sample;
        element_init_Zr(alpha_sample, pairing);
        element_init_Zr(beta_sample, pairing);

        
        // Single flat vector of DIM_M dimension
        element_t x_vec[DIM_M];
        element_t y_vec[DIM_M];

        long w[FEATURE_SIZE];
        long x[FEATURE_SIZE];
        long bias;
        long r2[FEATURE_SIZE + 1];
        long x_values[DIM_M];
        long y_values[DIM_M];
        long r3 = generate_random_int(-(1 << 15), (1 << 15) - 1);
        long r4 = generate_random_int(-(1 << 15), (1 << 15) - 1);

        long output_values = 0;
        for (int i = 0; i < FEATURE_SIZE; i++) {
            w[i] = generate_random_int(-128, 127);
            x[i] = generate_random_int(-128, 127);
            output_values += w[i] * x[i];
        }

        y_values[DIM_M - 1] = r3;
        for (int i = 0; i < FEATURE_SIZE + 1; i++) {
            r2[i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
            if (i < FEATURE_SIZE) {
                y_values[DIM_M - 1] -= x[i] * r2[i];
            } else {
                y_values[DIM_M - 1] -= 128 * r2[i];
            }
        }

        bias = generate_random_int(-128, 127);
        output_values += bias * 128;

        long expected_output = 0;
        for (int i = 0; i < FEATURE_SIZE; i++) {
            x_values[i] = r4 * w[i] + r2[i];
        }
        x_values[DIM_M - 2] = r4 * bias + r2[DIM_M - 2];
        x_values[DIM_M - 1] = 1;

        for (int i = 0; i < FEATURE_SIZE; i++) {
            y_values[i] = x[i];
        }
        y_values[DIM_M - 2] = 128;

        for (int j = 0; j < DIM_M; j++) {
            element_init_Zr(x_vec[j], pairing);
            element_init_Zr(y_vec[j], pairing);
            element_set_si(x_vec[j], x_values[j]);
            element_set_si(y_vec[j], y_values[j]);
            expected_output += x_values[j] * y_values[j];
        }

        if (expected_output != (r4 * output_values + r3)) {
            printf("\n[ASSERTION FAILED] expected_output != r4 * output_values + r3 at sample %d\n", sample);
            for (int i = 0; i < FEATURE_SIZE; i++) {
                printf("index=%d, x=%ld, w=%ld, r2=%ld\n", i, x[i], w[i], r2[i]);
            }
            printf("index=%d, r2=%ld (bias slot)\n", FEATURE_SIZE, r2[FEATURE_SIZE]);
            printf("bias=%ld, r3=%ld, r4=%ld\n", bias, r3, r4);
            printf("output_value=%ld, expected_output=%ld\n", output_values, expected_output);

            for (int i = 0; i < DIM_M; i++) {
                element_clear(x_vec[i]);
                element_clear(y_vec[i]);
            }
            element_clear(alpha_sample);
            element_clear(beta_sample);
            ClearMasterSecretKey(&msk);
            ClearSampleArtifacts(&sample_data);
            failed = true;
            failed_sample = sample;
            break;
        }

        start = std::chrono::steady_clock::now();
        KeyGen(pairing, &sample_data.pk, &msk, y_vec, &sample_data.sk, alpha_sample);
        sample_data.has_sk = true;
        stop = std::chrono::steady_clock::now();
        total_keygen_ms += std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count();

        start = std::chrono::steady_clock::now();
        Encrypt(pairing, &sample_data.pk, &msk, x_vec, &sample_data.ct, beta_sample);
        sample_data.has_ct = true;
        stop = std::chrono::steady_clock::now();
        total_encrypt_ms += std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count();

        start = std::chrono::steady_clock::now();
        sample_data.lut = BuildEncryptedLookupTable(pairing, &sample_data.pk, -(FEATURE_SIZE + 1) * 128 * 127, (FEATURE_SIZE + 1) * 127 * 127, r3, r4, alpha_sample, beta_sample, msk.det_B);
        stop = std::chrono::steady_clock::now();
        total_lut_build_ms += std::chrono::duration<double, std::milli>(stop - start).count();
        size_t lut_size_bytes = estimate_lut_size_bytes(sample_data.lut);
        total_lut_size_bytes += static_cast<long double>(lut_size_bytes);

        sample_data.r3 = r3;
        sample_data.r4 = r4;
        sample_data.expected_output = expected_output;
        sample_data.output_values = output_values;

        if (sample == 0) {
            size_t one_row_size_bytes = 0;
            for (size_t idx = 0; idx < sample_data.lut.table_size; idx++) {
                if (idx < sample_data.lut.occupied.size() && sample_data.lut.occupied[idx]) {
                    one_row_size_bytes = estimate_lut_row_size_bytes(sample_data.lut.slots[idx]);
                    break;
                }
            }

            printf("\n=== Single LUT Stats (sample 0) ===\n");
            printf("Total table size: %.6f MB\n", lut_size_bytes / (1024.0 * 1024.0));
            printf("One row size: %zu bytes\n", one_row_size_bytes);
            printf("Number of rows: %zu\n", sample_data.lut.num_entries);
        }

        for (int i = 0; i < DIM_M; i++) {
            element_clear(x_vec[i]);
            element_clear(y_vec[i]);
        }
        element_clear(alpha_sample);
        element_clear(beta_sample);
        ClearMasterSecretKey(&msk);

        auto sample_phase1_stop = std::chrono::steady_clock::now();
        double sample_phase1_ms = std::chrono::duration<double, std::milli>(sample_phase1_stop - sample_phase1_start).count();
        printf("Sample %d precompute time: %.3f s\n", sample, sample_phase1_ms / 1000.0);
        break;
    }

    if (!failed) {
        // Phase 2.1.1: bilinear operations initialization in parallel (wall-clock timed).
        std::vector<DecryptPhaseArtifacts> decrypt_artifacts(static_cast<size_t>(NUM_SAMPLES));

        element_t temp_pairing[NUM_SAMPLES];
        for (int sample = 0; sample < NUM_SAMPLES; sample++) {
            SampleArtifacts& sample_data = samples[static_cast<size_t>(0)];
            DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];

            element_init_GT(phase_data.D1, pairing);
            element_init_GT(phase_data.D2, pairing);
            phase_data.has_D1 = true;
            phase_data.has_D2 = true;

            element_pairing(phase_data.D1, sample_data.sk.K1, sample_data.ct.C1);

            element_init_GT(temp_pairing[sample], pairing);
            element_set1(phase_data.D2);
        }

        // Phase 2.1.2: bilinear operations in parallel (wall-clock timed).
        auto bilinear_start = std::chrono::steady_clock::now();
#pragma omp parallel for schedule(static)
        for (int sample = 0; sample < NUM_SAMPLES; sample++) {
            SampleArtifacts& sample_data = samples[static_cast<size_t>(0)];
            DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];
            for (int i = 0; i < DIM_M; i++) {
                element_pairing(temp_pairing[sample], sample_data.sk.K2[i], sample_data.ct.C2[i]);
                element_mul(phase_data.D2, phase_data.D2, temp_pairing[sample]);
            }
        }
        auto bilinear_stop = std::chrono::steady_clock::now();
        decrypt_bilinear_parallel_ms = std::chrono::duration<double, std::milli>(bilinear_stop - bilinear_start).count();

        // Phase 2.1.3: bilinear operations teardown
        for (int sample = 0; sample < NUM_SAMPLES; sample++) {
            element_clear(temp_pairing[sample]);
        }
        

        // Phase 2.2: compare D1^expected_output == D2.
        for (int sample = 0; sample < NUM_SAMPLES; sample++) {
            SampleArtifacts& sample_data = samples[static_cast<size_t>(0)];
            DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];

            element_t expected_exp, D1_expected;
            element_init_Zr(expected_exp, pairing);
            element_init_GT(D1_expected, pairing);
            element_set_si(expected_exp, sample_data.expected_output);
            element_pow_zn(D1_expected, phase_data.D1, expected_exp);

            bool eq = (element_cmp(D1_expected, phase_data.D2) == 0);
            element_clear(expected_exp);
            element_clear(D1_expected);

            if (!eq) {
                printf("[ASSERTION FAILED] D1^expected_output != D2 at sample %d\n", sample);
                failed = true;
                failed_sample = sample;
                break;
            }
        }

        // Phase 2.3: LUT lookup in parallel (wall-clock timed).
        if (!failed) {
            std::vector<int> lookup_status(static_cast<size_t>(NUM_SAMPLES), 1);
            auto lookup_start = std::chrono::steady_clock::now();

#pragma omp parallel for schedule(static)
            for (int sample = 0; sample < NUM_SAMPLES; sample++) {
                SampleArtifacts& sample_data = samples[static_cast<size_t>(0)];
                DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];
                if (!MapLTinGTtoG1WithEncryptedLUT(pairing,
                                                   phase_data.D2,
                                                   sample_data.lut,
                                                   phase_data.L_in_G1,
                                                   false)) {
                    lookup_status[static_cast<size_t>(sample)] = 0;
                } else {
                    phase_data.has_L_in_G1 = true;
                }
            }

            auto lookup_stop = std::chrono::steady_clock::now();
            decrypt_lookup_parallel_ms = std::chrono::duration<double, std::milli>(lookup_stop - lookup_start).count();

            for (int sample = 0; sample < NUM_SAMPLES; sample++) {
                if (lookup_status[static_cast<size_t>(sample)] == 0) {
                    printf("[ASSERTION FAILED] Lookup failed at sample %d\n", sample);
                    failed = true;
                    failed_sample = sample;
                    break;
                }
            }
        }

        // Phase 2.4: final G1 comparison.
        if (!failed) {
            for (int sample = 0; sample < NUM_SAMPLES; sample++) {
                SampleArtifacts& sample_data = samples[static_cast<size_t>(0)];
                DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];

                element_t lut_exp, expected_L_in_G1;
                element_init_Zr(lut_exp, pairing);
                element_init_G1(expected_L_in_G1, pairing);
                element_set_si(lut_exp, sample_data.r4 * non_linear_transform((long double)sample_data.output_values) + sample_data.r3);
                element_pow_zn(expected_L_in_G1, sample_data.pk.g1, lut_exp);

                bool eq = (element_cmp(phase_data.L_in_G1, expected_L_in_G1) == 0);
                element_clear(lut_exp);
                element_clear(expected_L_in_G1);

                if (!eq) {
                    printf("[ASSERTION FAILED] L_in_G1 mismatch at sample %d\n", sample);
                    failed = true;
                    failed_sample = sample;
                    break;
                }
            }
        }

        for (int sample = 0; sample < NUM_SAMPLES; sample++) {
            ClearDecryptPhaseArtifacts(&decrypt_artifacts[static_cast<size_t>(sample)]);
        }
    }

    for (int sample = 0; sample < NUM_SAMPLES; sample++) {
        ClearSampleArtifacts(&samples[static_cast<size_t>(sample)]);
    }

    if (failed) {
        printf("Pipeline failed at sample %d\n", failed_sample);
        pairing_clear(pairing);
        return 1;
    }

    printf("\n=== Benchmark Summary (%d samples) ===\n", NUM_SAMPLES);
    printf("KeyGen total: %lld ms, average: %.3f ms\n",
           total_keygen_ms,
           static_cast<double>(total_keygen_ms) / NUM_SAMPLES);
    printf("Encrypt total: %lld ms, average: %.3f ms\n",
           total_encrypt_ms,
           static_cast<double>(total_encrypt_ms) / NUM_SAMPLES);
    printf("Decrypt bilinear parallel loop total: %.3f ms, average: %.3f ms\n",
            decrypt_bilinear_parallel_ms,
            decrypt_bilinear_parallel_ms / NUM_SAMPLES);
    printf("Decrypt lookup parallel loop total: %.3f ms, average: %.3f ms\n",
            decrypt_lookup_parallel_ms,
            decrypt_lookup_parallel_ms / NUM_SAMPLES);
    printf("Setup total: %.3f ms, average: %.3f ms\n",
            total_setup_ms,
            total_setup_ms / NUM_SAMPLES);
    printf("LUT build total: %.3f ms, average: %.3f ms\n",
            total_lut_build_ms,
            total_lut_build_ms / NUM_SAMPLES);
    printf("Cumulative LUT size: %.6Lf GB\n",
            total_lut_size_bytes / (1024.0L * 1024.0L * 1024.0L));

    pairing_clear(pairing);

    return 0;
}