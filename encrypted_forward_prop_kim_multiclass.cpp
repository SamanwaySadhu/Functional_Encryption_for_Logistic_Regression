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

// --- Multiclass (3-way softmax) extension of encrypted_forward_prop_kim.cpp ---
//
// Instead of a single inner product w.x per data point (fed through a sigmoid),
// we now have NUM_CLASSES independent weight vectors w_0, w_1, w_2, so each data
// point produces NUM_CLASSES logits x_c = w_c . x. Each logit is computed by its
// own function-hiding IP-FE instance (independent Setup/KeyGen/Encrypt, so it has
// its own OTP randomness r2[c], r3[c] hiding it as r2[c]*x_c + r3[c]).
//
// Two LUT stages glue the classes together:
//
//   Stage A (per class, per sample -- "truncation LUT"): maps this class's
//   full-precision blinded logit r2[c]*x_c + r3[c] down to a freshly
//   OTP-masked, small-domain TRUNCATED logit rT2[c]*trunc(x_c) + rT3[c],
//   embedded as a single G1 element. This table has O(range) rows -- cheap,
//   linear in the logit range.
//
//   Stage B (once per sample -- "softmax LUT"): keyed jointly on the
//   NUM_CLASSES truncated G1 outputs of Stage A, and returns, for each class
//   c, an OTP-masked softmax value z1[c]*softmax(trunc(x_c); trunc(x_0),
//   trunc(x_1), trunc(x_2)) + z4[c].
//
// Why the split: a single combined LUT keyed directly on the NUM_CLASSES full-
// precision logits costs O(range^NUM_CLASSES) rows -- cubic in the (wide)
// logit range. By first collapsing each logit into a small TRUNC_OUTPUT_BITS-
// wide bucket via three cheap linear-cost LUTs, the only cubic table left
// (Stage B) is cubic in the much smaller truncated range instead, i.e.
// O((1<<TRUNC_OUTPUT_BITS)^NUM_CLASSES) rows. Raising TRUNC_OUTPUT_BITS trades
// softmax resolution for Stage B size; it has no effect on Stage A's cost.
#define NUM_CLASSES 3
#define FEATURE_SIZE 2
#define NUM_SAMPLES 150
#define DIM_M (FEATURE_SIZE + 1)
#define BATCH_SIZE 4
#define QUANTIZATION_BITS 3
#define MIN_X -(1 << (QUANTIZATION_BITS - 1))
#define MAX_X (1 << (QUANTIZATION_BITS - 1)) - 1

// The small domain each class's logit is squeezed into by Stage A before the
// three classes are combined in Stage B. Stage B's cost is
// O((1<<TRUNC_OUTPUT_BITS)^NUM_CLASSES), so this -- not FEATURE_SIZE or
// QUANTIZATION_BITS -- is the knob that controls the size of the expensive
// combined table.
#define TRUNC_OUTPUT_BITS 4
#define TRUNC_MIN (-(1 << (TRUNC_OUTPUT_BITS - 1)))
#define TRUNC_MAX ((1 << (TRUNC_OUTPUT_BITS - 1)) - 1)

long long total_decrypt_ms = 0;
double total_lookup_us = 0.0;

// --- Struct Definitions for Kim et al. Scheme (one instance per (sample, class)) ---
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

struct ClassArtifacts {
    PublicKey pk;
    DecryptionKey sk;
    Ciphertext ct;
    EncryptedLookupTable trunc_lut;  // Stage A: this class's truncation LUT
    long r2 = 0;                     // OTP scale hiding this class's full-precision logit
    long r3 = 0;                     // OTP offset hiding this class's full-precision logit
    long expected_output = 0;        // r2 * output_value + r3
    long output_value = 0;           // true (unblinded) logit w_c . x
    bool has_pk = false;
    bool has_sk = false;
    bool has_ct = false;
};

struct SampleArtifacts {
    ClassArtifacts classes[NUM_CLASSES];
    EncryptedLookupTable lut; // Stage B: jointly keyed softmax LUT for this sample
};

struct DecryptPhaseArtifacts {
    element_t D1[NUM_CLASSES];
    element_t D2[NUM_CLASSES];
    element_t T[NUM_CLASSES]; // Stage A output: per-class truncated, OTP-masked G1 logit
    element_t L_in_G1[NUM_CLASSES][FEATURE_SIZE][BATCH_SIZE + 1];
    bool has_D = false;
    bool has_T = false;
    bool has_L_in_G1 = false;
};

size_t estimate_lut_size_bytes(const EncryptedLookupTable& lut) {
    size_t total = lut.occupied.capacity() * sizeof(unsigned char) / 8;

    for (const auto& row : lut.slots) {
        total += row.ciphertext.capacity() * sizeof(unsigned char);
    }

    return total;
}

size_t estimate_lut_row_size_bytes(const EncryptedLookupRow& row) {
    size_t total = row.ciphertext.capacity() * sizeof(unsigned char);
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

// Numerically-stable softmax probability for class `c` given the NUM_CLASSES logits.
long double softmax_prob(const long double logits[NUM_CLASSES], int c) {
    long double max_logit = logits[0];
    for (int i = 1; i < NUM_CLASSES; i++) {
        if (logits[i] > max_logit) max_logit = logits[i];
    }

    long double sum = 0.0L;
    for (int i = 0; i < NUM_CLASSES; i++) {
        sum += std::exp(logits[i] - max_logit);
    }

    return std::exp(logits[c] - max_logit) / sum;
}

// Computes the quantized softmax output for class c given the ALREADY
// TRUNCATED (small-domain, Stage A output) logits of all classes.
int non_linear_transform_softmax(int c, const int trunc_logits[NUM_CLASSES]) {
    long double logits[NUM_CLASSES];
    for (int i = 0; i < NUM_CLASSES; i++) {
        logits[i] = static_cast<long double>(trunc_logits[i]);
    }
    long double prob = softmax_prob(logits, c);
    return static_cast<int>(prob * (1 << (QUANTIZATION_BITS - 1)));
}

// Linearly rescales x (known to lie in [min_x, max_x]) down onto the small
// [TRUNC_MIN, TRUNC_MAX] domain consumed by the softmax LUT (Stage B).
int truncate_logit(int x, int min_x, int max_x) {
    long double span = static_cast<long double>(max_x - min_x);
    long double normalized = 0.0L;
    if (span > 0.0L) {
        normalized = (static_cast<long double>(x - min_x) / span) *
                     static_cast<long double>(TRUNC_MAX - TRUNC_MIN);
    }
    long t = static_cast<long>(TRUNC_MIN) + std::llround(normalized);
    if (t < TRUNC_MIN) t = TRUNC_MIN;
    if (t > TRUNC_MAX) t = TRUNC_MAX;
    return static_cast<int>(t);
}

// Stage A (per class, per sample): maps this class's raw, full-precision
// blinded logit r2*x+r3 down to a freshly OTP-masked, small-domain truncated
// logit rT2*trunc(x)+rT3, embedded as a single G1 element. The row is keyed
// exactly like a single-class Kim-et-al. LUT (HKDF over the GT pairing value
// that this class's real decryption will reproduce for logit x). Domain size
// is O(max_x - min_x), i.e. linear in the logit range.
EncryptedLookupTable BuildTruncationLUT(
        pairing_t pairing,
        PublicKey* pk,
        int min_x, int max_x,
        long r2, long r3,
        element_t alpha, element_t beta, element_t det_B,
        long rT2, long rT3) {
    EncryptedLookupTable lut;
    lut.min_x = min_x;
    lut.max_x = max_x;
    lut.num_entries = 0;
    lut.table_size = 0;

    std::vector<unsigned char> salt = {'G','T','2','G','1','-','T','R','U','N','C','-','S','A','L','T'};
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
            element_t expt, gt_val;
            element_init_Zr(expt, pairing);
            element_init_GT(gt_val, pairing);

            element_set_si(expt, r2 * x + r3);
            element_mul(expt, expt, alpha);
            element_mul(expt, expt, beta);
            element_mul(expt, expt, det_B);
            element_pow_zn(gt_val, pk->gT_base, expt);
            std::vector<unsigned char> gt_bytes = serialize_element_to_bytes(gt_val);

            int t = truncate_logit(x, min_x, max_x);

            element_t out_exp, out_g1;
            element_init_Zr(out_exp, pairing);
            element_init_G1(out_g1, pairing);
            element_set_si(out_exp, rT2 * t + rT3);
            element_pow_zn(out_g1, pk->g1_base, out_exp);
            std::vector<unsigned char> plaintext = serialize_g1_element_to_compressed_bytes(out_g1);
            element_clear(out_exp);
            element_clear(out_g1);

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
            element_clear(gt_val);
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

// Looks up a class's Stage-A truncation LUT using its real, decrypted GT
// pairing value D2, and writes the recovered truncated G1 logit into `out_g1`
// (which the caller must have already element_init_G1'd).
bool MapGTtoTruncatedG1(pairing_t pairing,
                        element_t D2,
                        const EncryptedLookupTable& lut,
                        element_t out_g1,
                        bool verbose = true) {
    std::vector<unsigned char> salt = {'G','T','2','G','1','-','T','R','U','N','C','-','S','A','L','T'};
    std::vector<unsigned char> info = {'H','K','D','F','-','S','H','A','2','5','6','-','R','O','W'};

    std::vector<unsigned char> d2_bytes = serialize_element_to_bytes(D2);
    std::vector<unsigned char> key;
    if (!hkdf_sha256(d2_bytes, salt, info, HKDF_KEY_LEN, key)) {
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

        element_t g1_probe;
        element_init_G1(g1_probe, pairing);
        int g1_comp_len = element_length_in_bytes_compressed(g1_probe);
        element_clear(g1_probe);

        if (plaintext.size() != static_cast<size_t>(g1_comp_len)) {
            continue;
        }

        element_from_bytes_compressed(out_g1, const_cast<unsigned char*>(plaintext.data()));

        if (verbose) {
            printf("Truncation lookup completed with success\n");
        }
        return true;
    }
    if (verbose) {
        printf("Truncation lookup completed with failure\n");
    }
    return false;
}

// Stage B (combined, once per sample): keyed on the tuple of NUM_CLASSES
// truncated, OTP-masked G1 logits produced by Stage A. Because the domain is
// now [TRUNC_MIN, TRUNC_MAX] instead of the full logit range, this table has
// O((1<<TRUNC_OUTPUT_BITS)^NUM_CLASSES) rows instead of O(width^NUM_CLASSES).
// The row payload is unchanged from before: for every class c, the
// FEATURE_SIZE x (BATCH_SIZE+1) tensor of G1 elements encoding
// z1[c] * softmax_c(trunc_0,trunc_1,trunc_2) + z4[c].
EncryptedLookupTable BuildSoftmaxLUT(
        pairing_t pairing,
        element_t g1_base[NUM_CLASSES],
        long rT2[NUM_CLASSES], long rT3[NUM_CLASSES],
        int z1[NUM_CLASSES], int z4[NUM_CLASSES],
        element_t betad[NUM_CLASSES][FEATURE_SIZE],
        element_t Bstar[NUM_CLASSES][FEATURE_SIZE][BATCH_SIZE + 1][BATCH_SIZE + 1],
        int idx) {
    EncryptedLookupTable lut;
    lut.min_x = TRUNC_MIN;
    lut.max_x = TRUNC_MAX;
    lut.num_entries = 0;
    lut.table_size = 0;

    std::vector<unsigned char> salt = {'G','T','2','G','1','-','L','U','T','-','M','C','-','S','A','L','T'};
    std::vector<unsigned char> info = {'H','K','D','F','-','S','H','A','2','5','6','-','R','O','W'};

    const int width = TRUNC_MAX - TRUNC_MIN + 1;
    const size_t candidate_count = static_cast<size_t>(width) * static_cast<size_t>(width) * static_cast<size_t>(width);
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

        // Parallelize over the outer (class-0) candidate dimension; each thread
        // owns a full (width x width) slab of the (class-1, class-2) sub-grid.
#pragma omp for schedule(static)
        for (int t0 = TRUNC_MIN; t0 <= TRUNC_MAX; t0++) {
            for (int t1 = TRUNC_MIN; t1 <= TRUNC_MAX; t1++) {
                for (int t2 = TRUNC_MIN; t2 <= TRUNC_MAX; t2++) {
                    int ts[NUM_CLASSES] = {t0, t1, t2};

                    element_t row_exp, row_g1, exp1[NUM_CLASSES];
                    element_init_Zr(row_exp, pairing);
                    element_init_G1(row_g1, pairing);
                    for (int c = 0; c < NUM_CLASSES; c++) {
                        element_init_Zr(exp1[c], pairing);
                    }

                    std::vector<unsigned char> row_key_material;
                    for (int c = 0; c < NUM_CLASSES; c++) {
                        element_set_si(row_exp, rT2[c] * ts[c] + rT3[c]);
                        element_pow_zn(row_g1, g1_base[c], row_exp);
                        std::vector<unsigned char> g1_bytes = serialize_g1_element_to_compressed_bytes(row_g1);
                        row_key_material.insert(row_key_material.end(), g1_bytes.begin(), g1_bytes.end());

                        element_set_si(exp1[c], z1[c] * non_linear_transform_softmax(c, ts) + z4[c]);
                    }

                    std::vector<unsigned char> plaintext;
                    element_t base_exp, slot_exp, slot_g1;
                    element_init_Zr(base_exp, pairing);
                    element_init_Zr(slot_exp, pairing);
                    element_init_G1(slot_g1, pairing);

                    for (int c = 0; c < NUM_CLASSES; c++) {
                        for (int feature_idx = 0; feature_idx < FEATURE_SIZE; feature_idx++) {
                            for (int batch_idx = 0; batch_idx < BATCH_SIZE + 1; batch_idx++) {
                                element_mul(base_exp,
                                            betad[c][feature_idx],
                                            Bstar[c][feature_idx][idx][batch_idx]);
                                element_mul(slot_exp, base_exp, exp1[c]);
                                element_pow_zn(slot_g1, g1_base[c], slot_exp);

                                std::vector<unsigned char> slot_bytes =
                                    serialize_g1_element_to_compressed_bytes(slot_g1);
                                plaintext.insert(plaintext.end(), slot_bytes.begin(), slot_bytes.end());
                            }
                        }
                    }

                    element_clear(base_exp);
                    element_clear(slot_exp);
                    element_clear(slot_g1);

                    std::vector<unsigned char> key;
                    if (hkdf_sha256(row_key_material, salt, info, HKDF_KEY_LEN, key)) {
                        EncryptedLookupRow row;
                        row.nonce.assign(GCM_NONCE_LEN, 0);
                        if (RAND_bytes(row.nonce.data(), row.nonce.size()) == 1 &&
                            aes_gcm_encrypt(key, row.nonce, plaintext, row.ciphertext, row.tag)) {
                            local_entries.push_back({std::move(row), std::move(key)});
                        }
                    }

                    element_clear(row_exp);
                    element_clear(row_g1);
                    for (int c = 0; c < NUM_CLASSES; c++) {
                        element_clear(exp1[c]);
                    }
                }
            }
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

// Looks up the row jointly keyed by all NUM_CLASSES Stage-A truncated G1
// outputs T[c], and, on success, splits the decrypted plaintext back into
// NUM_CLASSES separate FEATURE_SIZE x (BATCH_SIZE+1) tensors of G1 elements.
bool MapCombinedTruncatedG1ToG1WithEncryptedLUT(pairing_t pairing,
                                                element_t T[NUM_CLASSES],
                                                const EncryptedLookupTable& lut,
                                                element_t L_in_G1[NUM_CLASSES][FEATURE_SIZE][BATCH_SIZE + 1],
                                                bool verbose = true) {
    std::vector<unsigned char> salt = {'G','T','2','G','1','-','L','U','T','-','M','C','-','S','A','L','T'};
    std::vector<unsigned char> info = {'H','K','D','F','-','S','H','A','2','5','6','-','R','O','W'};

    std::vector<unsigned char> row_key_material;
    for (int c = 0; c < NUM_CLASSES; c++) {
        std::vector<unsigned char> t_bytes = serialize_g1_element_to_compressed_bytes(T[c]);
        row_key_material.insert(row_key_material.end(), t_bytes.begin(), t_bytes.end());
    }

    std::vector<unsigned char> key;
    if (!hkdf_sha256(row_key_material, salt, info, HKDF_KEY_LEN, key)) {
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

        element_t g1_probe;
        element_init_G1(g1_probe, pairing);
        int g1_comp_len = element_length_in_bytes_compressed(g1_probe);
        element_clear(g1_probe);

        size_t expected_len = static_cast<size_t>(NUM_CLASSES) *
                              static_cast<size_t>(FEATURE_SIZE) *
                              static_cast<size_t>(BATCH_SIZE + 1) *
                              static_cast<size_t>(g1_comp_len);
        if (plaintext.size() != expected_len) {
            continue;
        }

        size_t offset = 0;
        for (int c = 0; c < NUM_CLASSES; c++) {
            for (int feature_idx = 0; feature_idx < FEATURE_SIZE; feature_idx++) {
                for (int batch_idx = 0; batch_idx < BATCH_SIZE + 1; batch_idx++) {
                    element_init_G1(L_in_G1[c][feature_idx][batch_idx], pairing);
                    element_from_bytes_compressed(
                        L_in_G1[c][feature_idx][batch_idx],
                        const_cast<unsigned char*>(plaintext.data() + offset));
                    offset += static_cast<size_t>(g1_comp_len);
                }
            }
        }

        if (verbose) {
            printf("Combined softmax lookup completed with success\n");
        }
        return true;
    }
    if (verbose) {
        printf("Combined softmax lookup completed with failure\n");
    }
    return false;
}

// --- Modified Matrix Inversion over Fq using Gaussian Elimination (Simultaneous Inv & Det) ---
int invert_and_det_matrix_Fq(pairing_t pairing, element_t M[DIM_M][DIM_M], element_t inverse[DIM_M][DIM_M], element_t det) {
    element_t aug[DIM_M][2 * DIM_M];
    element_t temp, pivot_inv;

    element_init_Zr(temp, pairing);
    element_init_Zr(pivot_inv, pairing);

    element_set1(det);
    int sign = 1;

#ifdef _OPENMP
#pragma omp parallel for collapse(2) schedule(static)
#endif
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
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
        for (int j = 0; j < 2 * DIM_M; j++) {
            element_mul(aug[i][j], aug[i][j], pivot_inv);
        }

#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
        for (int k = 0; k < DIM_M; k++) {
            if (k != i) {
                element_t factor;
                element_t local_temp;
                element_init_Zr(factor, pairing);
                element_init_Zr(local_temp, pairing);
                element_set(factor, aug[k][i]);
                for (int j = 0; j < 2 * DIM_M; j++) {
                    element_mul(local_temp, factor, aug[i][j]);
                    element_sub(aug[k][j], aug[k][j], local_temp);
                }
                element_clear(factor);
                element_clear(local_temp);
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
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < 2 * DIM_M; j++) {
            element_clear(aug[i][j]);
        }
    }

    return 1;
}

int invert_and_det_matrix_Fq_batch(pairing_t pairing,
                                   element_t M[BATCH_SIZE + 1][BATCH_SIZE + 1],
                                   element_t inverse[BATCH_SIZE + 1][BATCH_SIZE + 1],
                                   element_t det) {
    element_t aug[BATCH_SIZE + 1][2 * (BATCH_SIZE + 1)];
    element_t temp, pivot_inv, factor;

    element_init_Zr(temp, pairing);
    element_init_Zr(pivot_inv, pairing);
    element_init_Zr(factor, pairing);

    element_set1(det);
    int sign = 1;

    for (int i = 0; i < BATCH_SIZE + 1; i++) {
        for (int j = 0; j < BATCH_SIZE + 1; j++) {
            element_init_Zr(aug[i][j], pairing);
            element_set(aug[i][j], M[i][j]);

            element_init_Zr(aug[i][j + (BATCH_SIZE + 1)], pairing);
            if (i == j) {
                element_set1(aug[i][j + (BATCH_SIZE + 1)]);
            } else {
                element_set0(aug[i][j + (BATCH_SIZE + 1)]);
            }
        }
    }

    for (int i = 0; i < BATCH_SIZE + 1; i++) {
        int pivot_row = i;
        for (int k = i + 1; k < BATCH_SIZE + 1; k++) {
            if (!element_is0(aug[k][i])) {
                pivot_row = k;
                break;
            }
        }
        if (element_is0(aug[pivot_row][i])) {
            element_set0(det);
            for (int r = 0; r < BATCH_SIZE + 1; r++) {
                for (int c = 0; c < 2 * (BATCH_SIZE + 1); c++) {
                    element_clear(aug[r][c]);
                }
            }
            element_clear(temp);
            element_clear(pivot_inv);
            element_clear(factor);
            return 0;
        }

        if (pivot_row != i) {
            for (int j = 0; j < 2 * (BATCH_SIZE + 1); j++) {
                element_set(temp, aug[i][j]);
                element_set(aug[i][j], aug[pivot_row][j]);
                element_set(aug[pivot_row][j], temp);
            }
            sign = -sign;
        }

        element_mul(det, det, aug[i][i]);
        element_invert(pivot_inv, aug[i][i]);
        for (int j = 0; j < 2 * (BATCH_SIZE + 1); j++) {
            element_mul(aug[i][j], aug[i][j], pivot_inv);
        }

        for (int k = 0; k < BATCH_SIZE + 1; k++) {
            if (k != i) {
                element_set(factor, aug[k][i]);
                for (int j = 0; j < 2 * (BATCH_SIZE + 1); j++) {
                    element_mul(temp, factor, aug[i][j]);
                    element_sub(aug[k][j], aug[k][j], temp);
                }
            }
        }
    }

    if (sign == -1) {
        element_neg(det, det);
    }

    for (int i = 0; i < BATCH_SIZE + 1; i++) {
        for (int j = 0; j < BATCH_SIZE + 1; j++) {
            element_set(inverse[i][j], aug[i][j + (BATCH_SIZE + 1)]);
        }
    }

    element_clear(temp);
    element_clear(pivot_inv);
    element_clear(factor);
    for (int i = 0; i < BATCH_SIZE + 1; i++) {
        for (int j = 0; j < 2 * (BATCH_SIZE + 1); j++) {
            element_clear(aug[i][j]);
        }
    }

    return 1;
}

// --- 1. Setup Algorithm (Kim et al. Section 3); one independent instance per (sample, class) ---
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
#ifdef _OPENMP
#pragma omp parallel for collapse(2) schedule(static)
#endif
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_init_Zr(msk->B[i][j], pairing);
            element_init_Zr(msk->B_star[i][j], pairing);
            element_init_Zr(B_inv[i][j], pairing);
        }
    }

    int is_invertible = 0;
    while (!is_invertible) {
#ifdef _OPENMP
#pragma omp parallel for collapse(2) schedule(static)
#endif
        for (int i = 0; i < DIM_M; i++) {
            for (int j = 0; j < DIM_M; j++) {
                element_random(msk->B[i][j]);
            }
        }
        is_invertible = invert_and_det_matrix_Fq(pairing, msk->B, B_inv, msk->det_B);
    }

#ifdef _OPENMP
#pragma omp parallel for collapse(2) schedule(static)
#endif
    for (int i = 0; i < DIM_M; i++) {
        for (int j = 0; j < DIM_M; j++) {
            element_t local_temp;
            element_init_Zr(local_temp, pairing);
            element_mul(local_temp, msk->det_B, B_inv[j][i]);
            element_set(msk->B_star[i][j], local_temp);
            element_clear(local_temp);
        }
    }

#ifdef _OPENMP
#pragma omp parallel for collapse(2) schedule(static)
#endif
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
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (int i = 0; i < DIM_M; i++) {
        element_t dot_product, term;
        element_init_Zr(dot_product, pairing);
        element_init_Zr(term, pairing);

        element_set0(dot_product);
        for (int j = 0; j < DIM_M; j++) {
            element_mul(term, x[j], msk->B[j][i]);
            element_add(dot_product, dot_product, term);
        }
        element_mul(dot_product, dot_product, alpha);

        element_init_G1(sk->K2[i], pairing);
        element_pow_zn(sk->K2[i], pk->g1, dot_product);

        element_clear(dot_product);
        element_clear(term);
    }

    element_clear(alpha);
    element_clear(temp_scalar);
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
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (int i = 0; i < DIM_M; i++) {
        element_t dot_product, term;
        element_init_Zr(dot_product, pairing);
        element_init_Zr(term, pairing);

        element_set0(dot_product);
        for (int j = 0; j < DIM_M; j++) {
            element_mul(term, y[j], msk->B_star[j][i]);
            element_add(dot_product, dot_product, term);
        }
        element_mul(dot_product, dot_product, beta);

        element_init_G2(ct->C2[i], pairing);
        element_pow_zn(ct->C2[i], pk->g2, dot_product);

        element_clear(dot_product);
        element_clear(term);
    }

    element_clear(beta);
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

void ClearClassArtifacts(ClassArtifacts* cls) {
    if (cls->has_sk) {
        ClearDecryptionKey(&cls->sk);
        cls->has_sk = false;
    }
    if (cls->has_ct) {
        ClearCiphertexts(&cls->ct);
        cls->has_ct = false;
    }
    if (cls->has_pk) {
        ClearPublicKey(&cls->pk);
        cls->has_pk = false;
    }
    cls->trunc_lut = EncryptedLookupTable();
}

void ClearSampleArtifacts(SampleArtifacts* sample) {
    for (int c = 0; c < NUM_CLASSES; c++) {
        ClearClassArtifacts(&sample->classes[c]);
    }
    sample->lut = EncryptedLookupTable();
}

void ClearDecryptPhaseArtifacts(DecryptPhaseArtifacts* artifacts) {
    if (artifacts->has_L_in_G1) {
        for (int c = 0; c < NUM_CLASSES; c++) {
            for (int feature_idx = 0; feature_idx < FEATURE_SIZE; feature_idx++) {
                for (int batch_idx = 0; batch_idx < BATCH_SIZE + 1; batch_idx++) {
                    element_clear(artifacts->L_in_G1[c][feature_idx][batch_idx]);
                }
            }
        }
        artifacts->has_L_in_G1 = false;
    }
    if (artifacts->has_T) {
        for (int c = 0; c < NUM_CLASSES; c++) {
            element_clear(artifacts->T[c]);
        }
        artifacts->has_T = false;
    }
    if (artifacts->has_D) {
        for (int c = 0; c < NUM_CLASSES; c++) {
            element_clear(artifacts->D1[c]);
            element_clear(artifacts->D2[c]);
        }
        artifacts->has_D = false;
    }
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
    omp_set_num_threads(omp_get_max_threads());
#endif

    pairing_t pairing;
    pbc_param_t pbc_param;
    pbc_param_init_a_gen(pbc_param, 80, 256);
    pairing_init_pbc_param(pairing, pbc_param);
    pbc_param_clear(pbc_param);

    double total_setup_ms = 0.0;
    double total_trunc_lut_build_ms = 0.0;
    double total_softmax_lut_build_ms = 0.0;
    long double total_trunc_lut_size_bytes = 0.0L;
    long double total_softmax_lut_size_bytes = 0.0L;
    long long total_keygen_us = 0;
    long long total_encrypt_us = 0;
    double decrypt_bilinear_parallel_ms = 0.0;
    double decrypt_trunc_lookup_parallel_ms = 0.0;
    double decrypt_softmax_lookup_parallel_ms = 0.0;
    double c2_generation_parallel_ms = 0.0;
    bool failed = false;
    int failed_sample = -1;
    int failed_class = -1;

    std::vector<SampleArtifacts> samples(BATCH_SIZE);

    // MIN_X has strictly larger magnitude than MAX_X (e.g. -4..3), so the
    // largest achievable per-feature product w[i]*x[i] is MIN_X*MIN_X, not
    // MAX_X*MAX_X. This is the full (pre-truncation) domain each class's
    // Stage-A LUT is built over.
    const int min_x = FEATURE_SIZE * MIN_X * MAX_X;
    const int max_x = FEATURE_SIZE * MIN_X * MIN_X;

    // Softmax-output masking randomness, one scale/offset pair per class.
    int z1[NUM_CLASSES];
    int z4[NUM_CLASSES][BATCH_SIZE];
    for (int c = 0; c < NUM_CLASSES; c++) {
        z1[c] = generate_random_int(-(1 << 15), (1 << 15) - 1);
        for (int i = 0; i < BATCH_SIZE; i++) {
            z4[c][i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
        }
    }

    // Per-class batch-combination secret sharing material (mirrors the single-class
    // scheme's betad/Bstar, just replicated once per class).
    element_t betad[NUM_CLASSES][FEATURE_SIZE];
    element_t Bstar[NUM_CLASSES][FEATURE_SIZE][BATCH_SIZE + 1][BATCH_SIZE + 1];
    for (int c = 0; c < NUM_CLASSES; c++) {
        for (int feature_idx = 0; feature_idx < FEATURE_SIZE; feature_idx++) {
            element_init_Zr(betad[c][feature_idx], pairing);
            element_random(betad[c][feature_idx]);

            element_t B[BATCH_SIZE + 1][BATCH_SIZE + 1];
            element_t B_inv[BATCH_SIZE + 1][BATCH_SIZE + 1];
            element_t det_B_feature;
            element_t tmp;
            element_init_Zr(det_B_feature, pairing);
            element_init_Zr(tmp, pairing);

            for (int i = 0; i < BATCH_SIZE + 1; i++) {
                for (int j = 0; j < BATCH_SIZE + 1; j++) {
                    element_init_Zr(B[i][j], pairing);
                    element_init_Zr(B_inv[i][j], pairing);
                    element_init_Zr(Bstar[c][feature_idx][i][j], pairing);
                }
            }

            int is_invertible = 0;
            while (!is_invertible) {
                for (int i = 0; i < BATCH_SIZE + 1; i++) {
                    for (int j = 0; j < BATCH_SIZE + 1; j++) {
                        element_random(B[i][j]);
                    }
                }
                is_invertible = invert_and_det_matrix_Fq_batch(pairing, B, B_inv, det_B_feature);
            }

            for (int i = 0; i < BATCH_SIZE + 1; i++) {
                for (int j = 0; j < BATCH_SIZE + 1; j++) {
                    element_mul(tmp, det_B_feature, B_inv[j][i]);
                    element_set(Bstar[c][feature_idx][i][j], tmp);
                }
            }

            element_clear(tmp);
            element_clear(det_B_feature);
            for (int i = 0; i < BATCH_SIZE + 1; i++) {
                for (int j = 0; j < BATCH_SIZE + 1; j++) {
                    element_clear(B[i][j]);
                    element_clear(B_inv[i][j]);
                }
            }
        }
    }

    // Phase 1: for every sample, run NUM_CLASSES independent Setup/KeyGen/Encrypt
    // instances (one per class weight vector, sharing the same data point x),
    // build each class's Stage-A truncation LUT, and finally build the single
    // Stage-B combined softmax LUT for that sample.
    for (int sample = 0; sample < BATCH_SIZE && !failed; sample++) {
        SampleArtifacts& sample_data = samples[static_cast<size_t>(sample)];
        auto sample_phase1_start = std::chrono::steady_clock::now();

        long x[FEATURE_SIZE];
        for (int i = 0; i < FEATURE_SIZE; i++) {
            x[i] = (i == FEATURE_SIZE - 1) ? MAX_X : generate_random_int(MIN_X, MAX_X);
        }

        element_t g1_base_local[NUM_CLASSES];
        long rT2_local[NUM_CLASSES], rT3_local[NUM_CLASSES];

        for (int c = 0; c < NUM_CLASSES && !failed; c++) {
            ClassArtifacts& cls = sample_data.classes[c];

            MasterSecretKey msk;
            auto start = std::chrono::steady_clock::now();
            Setup(pairing, &cls.pk, &msk);
            cls.has_pk = true;
            auto stop = std::chrono::steady_clock::now();
            total_setup_ms += std::chrono::duration<double, std::milli>(stop - start).count();

            element_t alpha_sample, beta_sample;
            element_init_Zr(alpha_sample, pairing);
            element_init_Zr(beta_sample, pairing);

            element_t x_vec[DIM_M];
            element_t y_vec[DIM_M];

            long w[FEATURE_SIZE];
            long r1[FEATURE_SIZE];
            long x_values[DIM_M];
            long y_values[DIM_M];
            long r3 = generate_random_int(-(1 << 15), (1 << 15) - 1);
            long r2 = generate_random_int(-(1 << 15), (1 << 15) - 1);

            long output_value = 0;
            for (int i = 0; i < FEATURE_SIZE; i++) {
                w[i] = generate_random_int(MIN_X, MAX_X);
                output_value += w[i] * x[i];
            }

            y_values[DIM_M - 1] = r3;
            x_values[DIM_M - 1] = 1;
            for (int i = 0; i < FEATURE_SIZE; i++) {
                r1[i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
                y_values[DIM_M - 1] -= x[i] * r1[i];
            }

            long expected_output = 0;
            for (int i = 0; i < FEATURE_SIZE; i++) {
                x_values[i] = r2 * w[i] + r1[i];
                y_values[i] = x[i];
            }

            for (int j = 0; j < DIM_M; j++) {
                element_init_Zr(x_vec[j], pairing);
                element_init_Zr(y_vec[j], pairing);
                element_set_si(x_vec[j], x_values[j]);
                element_set_si(y_vec[j], y_values[j]);
                expected_output += x_values[j] * y_values[j];
            }

            if (expected_output != (r2 * output_value + r3)) {
                printf("\n[ASSERTION FAILED] expected_output != r2 * output_value + r3 at sample %d, class %d\n", sample, c);
                for (int i = 0; i < DIM_M; i++) {
                    element_clear(x_vec[i]);
                    element_clear(y_vec[i]);
                }
                element_clear(alpha_sample);
                element_clear(beta_sample);
                ClearMasterSecretKey(&msk);
                failed = true;
                failed_sample = sample;
                failed_class = c;
                break;
            }

            start = std::chrono::steady_clock::now();
            KeyGen(pairing, &cls.pk, &msk, y_vec, &cls.sk, alpha_sample);
            cls.has_sk = true;
            stop = std::chrono::steady_clock::now();
            total_keygen_us += std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();

            start = std::chrono::steady_clock::now();
            Encrypt(pairing, &cls.pk, &msk, x_vec, &cls.ct, beta_sample);
            cls.has_ct = true;
            stop = std::chrono::steady_clock::now();
            total_encrypt_us += std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();

            cls.r2 = r2;
            cls.r3 = r3;
            cls.expected_output = expected_output;
            cls.output_value = output_value;

            // Stage A: build this class's truncation LUT right here, while
            // alpha_sample/beta_sample/msk.det_B (this class's IPFE secret
            // scalars) are still in scope.
            long rT2 = generate_random_int(-(1 << 15), (1 << 15) - 1);
            long rT3 = generate_random_int(-(1 << 15), (1 << 15) - 1);

            auto trunc_start = std::chrono::steady_clock::now();
            cls.trunc_lut = BuildTruncationLUT(pairing, &cls.pk, min_x, max_x, r2, r3,
                                               alpha_sample, beta_sample, msk.det_B, rT2, rT3);
            auto trunc_stop = std::chrono::steady_clock::now();
            total_trunc_lut_build_ms += std::chrono::duration<double, std::milli>(trunc_stop - trunc_start).count();
            total_trunc_lut_size_bytes += static_cast<long double>(estimate_lut_size_bytes(cls.trunc_lut));

            rT2_local[c] = rT2;
            rT3_local[c] = rT3;

            // Stash this class's g1_base for the Stage-B softmax LUT build below.
            element_init_G1(g1_base_local[c], pairing);
            element_set(g1_base_local[c], cls.pk.g1_base);

            for (int i = 0; i < DIM_M; i++) {
                element_clear(x_vec[i]);
                element_clear(y_vec[i]);
            }
            element_clear(alpha_sample);
            element_clear(beta_sample);
            ClearMasterSecretKey(&msk);
        }

        if (failed) {
            break;
        }

        if (sample == 0) {
            EncryptedLookupTable& t_lut = sample_data.classes[0].trunc_lut;
            size_t one_row_size_bytes = 0;
            for (size_t idx = 0; idx < t_lut.table_size; idx++) {
                if (idx < t_lut.occupied.size() && t_lut.occupied[idx]) {
                    one_row_size_bytes = estimate_lut_row_size_bytes(t_lut.slots[idx]);
                    break;
                }
            }
            printf("\n=== Truncation LUT Stats (sample 0, class 0) ===\n");
            printf("Total table size: %.6f MB\n", estimate_lut_size_bytes(t_lut) / (1024.0 * 1024.0));
            printf("One row size: %zu bytes\n", one_row_size_bytes);
            printf("Number of rows: %zu\n", t_lut.num_entries);
        }

        int z4_sample[NUM_CLASSES];
        for (int c = 0; c < NUM_CLASSES; c++) {
            z4_sample[c] = z4[c][sample];
        }

        auto softmax_start = std::chrono::steady_clock::now();
        sample_data.lut = BuildSoftmaxLUT(pairing, g1_base_local, rT2_local, rT3_local,
                                          z1, z4_sample, betad, Bstar, sample);
        auto softmax_stop = std::chrono::steady_clock::now();
        total_softmax_lut_build_ms += std::chrono::duration<double, std::milli>(softmax_stop - softmax_start).count();
        total_softmax_lut_size_bytes += static_cast<long double>(estimate_lut_size_bytes(sample_data.lut));

        if (sample == 0) {
            size_t one_row_size_bytes = 0;
            for (size_t idx = 0; idx < sample_data.lut.table_size; idx++) {
                if (idx < sample_data.lut.occupied.size() && sample_data.lut.occupied[idx]) {
                    one_row_size_bytes = estimate_lut_row_size_bytes(sample_data.lut.slots[idx]);
                    break;
                }
            }

            printf("\n=== Softmax LUT Stats (sample 0) ===\n");
            printf("Total table size: %.6f MB\n", estimate_lut_size_bytes(sample_data.lut) / (1024.0 * 1024.0));
            printf("One row size: %zu bytes\n", one_row_size_bytes);
            printf("Number of rows: %zu\n", sample_data.lut.num_entries);
        }

        for (int c = 0; c < NUM_CLASSES; c++) {
            element_clear(g1_base_local[c]);
        }

        auto sample_phase1_stop = std::chrono::steady_clock::now();
        double sample_phase1_ms = std::chrono::duration<double, std::milli>(sample_phase1_stop - sample_phase1_start).count();
        printf("Sample %d precompute time: %.3f s\n", sample, sample_phase1_ms / 1000.0);
    }

    if (!failed) {
        std::vector<DecryptPhaseArtifacts> decrypt_artifacts(static_cast<size_t>(BATCH_SIZE));

        // Phase 2.1: bilinear pairing operations, per sample per class, in parallel.
        // Also pre-initialize the Stage-A output slots T[c] here so they are
        // always safe to element_clear later, regardless of lookup outcome.
        auto bilinear_start = std::chrono::steady_clock::now();
#pragma omp parallel for collapse(2) schedule(static)
        for (int sample = 0; sample < BATCH_SIZE; sample++) {
            for (int c = 0; c < NUM_CLASSES; c++) {
                SampleArtifacts& sample_data = samples[static_cast<size_t>(sample)];
                ClassArtifacts& cls = sample_data.classes[c];
                DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];

                element_init_GT(phase_data.D1[c], pairing);
                element_init_GT(phase_data.D2[c], pairing);
                element_init_G1(phase_data.T[c], pairing);

                element_pairing(phase_data.D1[c], cls.sk.K1, cls.ct.C1);

                element_t temp_pairing;
                element_init_GT(temp_pairing, pairing);
                element_set1(phase_data.D2[c]);
                for (int i = 0; i < DIM_M; i++) {
                    element_pairing(temp_pairing, cls.sk.K2[i], cls.ct.C2[i]);
                    element_mul(phase_data.D2[c], phase_data.D2[c], temp_pairing);
                }
                element_clear(temp_pairing);
            }
        }
        auto bilinear_stop = std::chrono::steady_clock::now();
        decrypt_bilinear_parallel_ms = std::chrono::duration<double, std::milli>(bilinear_stop - bilinear_start).count();

        for (int sample = 0; sample < BATCH_SIZE; sample++) {
            decrypt_artifacts[static_cast<size_t>(sample)].has_D = true;
            decrypt_artifacts[static_cast<size_t>(sample)].has_T = true;
        }

        // Phase 2.2: per-class correctness check D1[c]^expected_output[c] == D2[c].
        for (int sample = 0; sample < BATCH_SIZE && !failed; sample++) {
            SampleArtifacts& sample_data = samples[static_cast<size_t>(sample)];
            DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];

            for (int c = 0; c < NUM_CLASSES; c++) {
                element_t expected_exp, D1_expected;
                element_init_Zr(expected_exp, pairing);
                element_init_GT(D1_expected, pairing);
                element_set_si(expected_exp, sample_data.classes[c].expected_output);
                element_pow_zn(D1_expected, phase_data.D1[c], expected_exp);

                bool eq = (element_cmp(D1_expected, phase_data.D2[c]) == 0);
                element_clear(expected_exp);
                element_clear(D1_expected);

                if (!eq) {
                    printf("[ASSERTION FAILED] D1^expected_output != D2 at sample %d, class %d\n", sample, c);
                    failed = true;
                    failed_sample = sample;
                    failed_class = c;
                    break;
                }
            }
        }

        // Phase 2.3a: Stage-A truncation lookups, per (sample, class), in parallel.
        if (!failed) {
            std::vector<int> trunc_status(static_cast<size_t>(BATCH_SIZE * NUM_CLASSES), 1);
            auto trunc_lookup_start = std::chrono::steady_clock::now();

#pragma omp parallel for collapse(2) schedule(static)
            for (int sample = 0; sample < BATCH_SIZE; sample++) {
                for (int c = 0; c < NUM_CLASSES; c++) {
                    SampleArtifacts& sample_data = samples[static_cast<size_t>(sample)];
                    DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];
                    if (!MapGTtoTruncatedG1(pairing, phase_data.D2[c], sample_data.classes[c].trunc_lut,
                                            phase_data.T[c], false)) {
                        trunc_status[static_cast<size_t>(sample) * NUM_CLASSES + static_cast<size_t>(c)] = 0;
                    }
                }
            }

            auto trunc_lookup_stop = std::chrono::steady_clock::now();
            decrypt_trunc_lookup_parallel_ms = std::chrono::duration<double, std::milli>(trunc_lookup_stop - trunc_lookup_start).count();

            for (int sample = 0; sample < BATCH_SIZE && !failed; sample++) {
                for (int c = 0; c < NUM_CLASSES; c++) {
                    if (trunc_status[static_cast<size_t>(sample) * NUM_CLASSES + static_cast<size_t>(c)] == 0) {
                        printf("[ASSERTION FAILED] Truncation lookup failed at sample %d, class %d\n", sample, c);
                        failed = true;
                        failed_sample = sample;
                        failed_class = c;
                        break;
                    }
                }
            }
        }

        // Phase 2.3b: Stage-B combined softmax lookup, one per sample, in parallel.
        if (!failed) {
            std::vector<int> lookup_status(static_cast<size_t>(BATCH_SIZE), 1);
            auto lookup_start = std::chrono::steady_clock::now();

#pragma omp parallel for schedule(static)
            for (int sample = 0; sample < BATCH_SIZE; sample++) {
                SampleArtifacts& sample_data = samples[static_cast<size_t>(sample)];
                DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];
                if (!MapCombinedTruncatedG1ToG1WithEncryptedLUT(pairing,
                                                                phase_data.T,
                                                                sample_data.lut,
                                                                phase_data.L_in_G1,
                                                                false)) {
                    lookup_status[static_cast<size_t>(sample)] = 0;
                } else {
                    phase_data.has_L_in_G1 = true;
                }
            }

            auto lookup_stop = std::chrono::steady_clock::now();
            decrypt_softmax_lookup_parallel_ms = std::chrono::duration<double, std::milli>(lookup_stop - lookup_start).count();

            for (int sample = 0; sample < BATCH_SIZE; sample++) {
                if (lookup_status[static_cast<size_t>(sample)] == 0) {
                    printf("[ASSERTION FAILED] Combined softmax lookup failed at sample %d\n", sample);
                    failed = true;
                    failed_sample = sample;
                    break;
                }
            }
        }

        // Phase 2.4: per-class final ciphertext accumulation across the batch.
        element_t C2[NUM_CLASSES][FEATURE_SIZE][BATCH_SIZE + 1];
        bool has_C2 = false;
        if (!failed) {
            has_C2 = true;
            auto c2_start = std::chrono::steady_clock::now();

#pragma omp parallel for collapse(3) schedule(static)
            for (int c = 0; c < NUM_CLASSES; c++) {
                for (int feature_idx = 0; feature_idx < FEATURE_SIZE; feature_idx++) {
                    for (int batch_idx = 0; batch_idx < BATCH_SIZE + 1; batch_idx++) {
                        element_init_G1(C2[c][feature_idx][batch_idx], pairing);
                        element_set1(C2[c][feature_idx][batch_idx]);

                        for (int sample = 0; sample < BATCH_SIZE; sample++) {
                            DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];
                            element_mul(C2[c][feature_idx][batch_idx],
                                        C2[c][feature_idx][batch_idx],
                                        phase_data.L_in_G1[c][feature_idx][batch_idx]);
                        }

                        // Tail term uses the final row (index BATCH_SIZE) of each class's
                        // per-feature B* matrix, matching the single-class scheme.
                        element_t tail_exp, tail_term;
                        element_init_Zr(tail_exp, pairing);
                        element_init_G1(tail_term, pairing);
                        element_set(tail_exp, Bstar[c][feature_idx][BATCH_SIZE][batch_idx]);
                        element_pow_zn(tail_term, samples[0].classes[c].pk.g1, tail_exp);
                        element_mul(C2[c][feature_idx][batch_idx],
                                    C2[c][feature_idx][batch_idx],
                                    tail_term);
                        element_clear(tail_exp);
                        element_clear(tail_term);
                    }
                }
            }

            auto c2_stop = std::chrono::steady_clock::now();
            c2_generation_parallel_ms = std::chrono::duration<double, std::milli>(c2_stop - c2_start).count();
            printf("Ciphertext generation parallel loop total: %.3f ms\n", c2_generation_parallel_ms);
        }

        // Phase 2.5: final per-sample, per-class G1 comparison against the expected
        // softmax-derived exponent, computed from the TRUNCATED logits (matching
        // what Stage B actually embedded into the softmax LUT).
        if (!failed) {
            for (int sample = 0; sample < BATCH_SIZE && !failed; sample++) {
                SampleArtifacts& sample_data = samples[static_cast<size_t>(sample)];
                DecryptPhaseArtifacts& phase_data = decrypt_artifacts[static_cast<size_t>(sample)];

                int trunc_logits[NUM_CLASSES];
                for (int c = 0; c < NUM_CLASSES; c++) {
                    trunc_logits[c] = truncate_logit(sample_data.classes[c].output_value, min_x, max_x);
                }

                for (int c = 0; c < NUM_CLASSES && !failed; c++) {
                    element_t lut_exp, expected_slot_exp, expected_L_in_G1;
                    element_init_Zr(lut_exp, pairing);
                    element_init_Zr(expected_slot_exp, pairing);
                    element_init_G1(expected_L_in_G1, pairing);
                    element_set_si(lut_exp, z1[c] * non_linear_transform_softmax(c, trunc_logits) + z4[c][sample]);

                    bool eq = true;
                    for (int feature_idx = 0; feature_idx < FEATURE_SIZE && eq; feature_idx++) {
                        for (int batch_idx = 0; batch_idx < BATCH_SIZE + 1; batch_idx++) {
                            element_mul(expected_slot_exp,
                                        betad[c][feature_idx],
                                        Bstar[c][feature_idx][sample][batch_idx]);
                            element_mul(expected_slot_exp, expected_slot_exp, lut_exp);
                            element_pow_zn(expected_L_in_G1, sample_data.classes[c].pk.g1, expected_slot_exp);

                            if (element_cmp(phase_data.L_in_G1[c][feature_idx][batch_idx], expected_L_in_G1) != 0) {
                                eq = false;
                                break;
                            }
                        }
                    }

                    element_clear(lut_exp);
                    element_clear(expected_slot_exp);
                    element_clear(expected_L_in_G1);

                    if (!eq) {
                        printf("[ASSERTION FAILED] L_in_G1 mismatch at sample %d, class %d\n", sample, c);
                        failed = true;
                        failed_sample = sample;
                        failed_class = c;
                        break;
                    }
                }
            }
        }

        if (has_C2) {
            for (int c = 0; c < NUM_CLASSES; c++) {
                for (int feature_idx = 0; feature_idx < FEATURE_SIZE; feature_idx++) {
                    for (int batch_idx = 0; batch_idx < BATCH_SIZE + 1; batch_idx++) {
                        element_clear(C2[c][feature_idx][batch_idx]);
                    }
                }
            }
        }

        for (int sample = 0; sample < BATCH_SIZE; sample++) {
            ClearDecryptPhaseArtifacts(&decrypt_artifacts[static_cast<size_t>(sample)]);
        }
    }

    for (int sample = 0; sample < BATCH_SIZE; sample++) {
        ClearSampleArtifacts(&samples[static_cast<size_t>(sample)]);
    }

    if (failed) {
        printf("Pipeline failed at sample %d, class %d\n", failed_sample, failed_class);
        pairing_clear(pairing);
        return 1;
    }

    printf("\n=== Benchmark Summary (%d samples x %d classes) ===\n", BATCH_SIZE, NUM_CLASSES);
    printf("KeyGen total: %lld us, average: %.3f us\n",
            total_keygen_us,
            static_cast<double>(total_keygen_us) / (BATCH_SIZE * NUM_CLASSES));
    printf("Encrypt total: %lld us, average: %.3f us\n",
            total_encrypt_us,
            static_cast<double>(total_encrypt_us) / (BATCH_SIZE * NUM_CLASSES));
    printf("Decrypt bilinear parallel loop total: %.3f ms, average: %.3f ms\n",
            decrypt_bilinear_parallel_ms,
            decrypt_bilinear_parallel_ms / (BATCH_SIZE * NUM_CLASSES));
    printf("Truncation lookup parallel loop total: %.3f ms, average: %.3f ms\n",
            decrypt_trunc_lookup_parallel_ms,
            decrypt_trunc_lookup_parallel_ms / (BATCH_SIZE * NUM_CLASSES));
    printf("Softmax lookup parallel loop total: %.3f ms, average: %.3f ms\n",
            decrypt_softmax_lookup_parallel_ms,
            decrypt_softmax_lookup_parallel_ms / BATCH_SIZE);
    printf("Decrypt lookup parallel loop total: %.3f ms, average: %.3f ms\n",
            decrypt_trunc_lookup_parallel_ms + decrypt_softmax_lookup_parallel_ms,
            (decrypt_trunc_lookup_parallel_ms + decrypt_softmax_lookup_parallel_ms) / BATCH_SIZE);
    printf("C2 generation parallel loop total: %.3f ms, average: %.3f ms\n",
            c2_generation_parallel_ms,
            c2_generation_parallel_ms / (BATCH_SIZE * NUM_CLASSES));
    printf("Setup total: %.3f ms, average: %.3f ms\n",
            total_setup_ms,
            total_setup_ms / (BATCH_SIZE * NUM_CLASSES));
    printf("Truncation LUT build total: %.3f ms, average: %.3f ms\n",
            total_trunc_lut_build_ms,
            total_trunc_lut_build_ms / (BATCH_SIZE * NUM_CLASSES));
    printf("Softmax LUT build total: %.3f ms, average: %.3f ms\n",
            total_softmax_lut_build_ms,
            total_softmax_lut_build_ms / BATCH_SIZE);
    printf("LUT build total: %.3f ms, average: %.3f ms\n",
            total_trunc_lut_build_ms + total_softmax_lut_build_ms,
            (total_trunc_lut_build_ms + total_softmax_lut_build_ms) / BATCH_SIZE);
    printf("Truncation LUT cumulative size: %.6Lf MB\n",
            total_trunc_lut_size_bytes / (1024.0L * 1024.0L));
    printf("Softmax LUT cumulative size: %.6Lf MB\n",
            total_softmax_lut_size_bytes / (1024.0L * 1024.0L));
    printf("Cumulative LUT size: %.6Lf MB\n",
            (total_trunc_lut_size_bytes + total_softmax_lut_size_bytes) / (1024.0L * 1024.0L));

    pairing_clear(pairing);

    return 0;
}
