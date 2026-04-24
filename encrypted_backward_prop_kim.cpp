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

#define FEATURE_SIZE 5
#define NUM_SAMPLES 150
#define DIM_M (BATCH_SIZE + 1)
#define LR 0.5L
#define BATCH_SIZE 4
#define QUANTIZATION_BITS 6
#define MIN_X -(1 << (QUANTIZATION_BITS - 1))
#define MAX_X (1 << (QUANTIZATION_BITS - 1)) - 1

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

size_t estimate_lut_size_bytes(const EncryptedLookupTable& lut) {
    size_t total = lut.occupied.capacity() * sizeof(unsigned char) / 8;

    for (const auto& row : lut.slots) {
        total += row.ciphertext.capacity() * sizeof(unsigned char);
    }

    return total;
}

void print_lut_row_stats(const char* table_name, const EncryptedLookupTable& lut) {
    size_t occupied_rows = 0;
    size_t min_row_bytes = std::numeric_limits<size_t>::max();
    size_t max_row_bytes = 0;
    long double sum_row_bytes = 0.0L;

    for (size_t i = 0; i < lut.slots.size() && i < lut.occupied.size(); i++) {
        if (!lut.occupied[i]) {
            continue;
        }

        const EncryptedLookupRow& row = lut.slots[i];
        size_t row_bytes = row.ciphertext.size();
        occupied_rows++;
        sum_row_bytes += static_cast<long double>(row_bytes);
        min_row_bytes = std::min(min_row_bytes, row_bytes);
        max_row_bytes = std::max(max_row_bytes, row_bytes);
    }

    printf("%s rows: %zu\n", table_name, occupied_rows);
    if (occupied_rows == 0) {
        printf("%s row size (bytes): N/A (empty table)\n", table_name);
        return;
    }

    long double avg_row_bytes = sum_row_bytes / static_cast<long double>(occupied_rows);
    if (min_row_bytes == max_row_bytes) {
        printf("%s row size (bytes): %zu\n", table_name, min_row_bytes);
    } else {
        printf("%s row size (bytes): min=%zu, max=%zu, avg=%.2Lf\n",
               table_name,
               min_row_bytes,
               max_row_bytes,
               avg_row_bytes);
    }
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

EncryptedLookupTable BuildEncryptedLookupTable(pairing_t pairing, PublicKey* pk, int min_x, int max_x, int z3mz4, int z1, element_t alpha, element_t beta, element_t det_B) {
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

        element_t expt, exp1, gt_val, gt_mapped_val;
        element_init_Zr(expt, pairing);
        element_init_Zr(exp1, pairing);
        element_init_GT(gt_val, pairing);
        element_init_GT(gt_mapped_val, pairing);

#pragma omp for schedule(static)
        for (int x = min_x; x <= max_x; x++) {
            element_set_si(expt, z1 * x + z3mz4);
            element_mul(expt, expt, alpha);
            element_mul(expt, expt, beta);
            element_mul(expt, expt, det_B);
            element_set_si(exp1, z1 * (x >> (QUANTIZATION_BITS - 1)) + z3mz4);
            element_pow_zn(gt_val, pk->gT_base, expt);
            element_pow_zn(gt_mapped_val, pk->gT_base, exp1);

            std::vector<unsigned char> gt_bytes = serialize_element_to_bytes(gt_val);
            std::vector<unsigned char> mapped_gt_bytes = serialize_element_to_bytes(gt_mapped_val);

            std::vector<unsigned char> plaintext = mapped_gt_bytes;

            std::vector<unsigned char> key;
            if (!hkdf_sha256(gt_bytes, salt, info, HKDF_KEY_LEN, key)) {
                continue;
            }

            EncryptedLookupRow row;
            row.nonce.assign(GCM_NONCE_LEN, 0);
            if (RAND_bytes(row.nonce.data(), row.nonce.size()) != 1) {
                continue;
            }

            if (!aes_gcm_encrypt(key, row.nonce, plaintext, row.ciphertext, row.tag)) {
                continue;
            }

            local_entries.push_back({std::move(row), std::move(key)});
        }

        element_clear(expt);
        element_clear(exp1);
        element_clear(gt_val);
        element_clear(gt_mapped_val);
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

EncryptedLookupTable BuildEncryptedLookupTableGTtoG1(pairing_t pairing, PublicKey* pk, int min_x, int max_x, int z1, int z4, int r2, int r1, int Z1, int Z3, element_t betad[BATCH_SIZE], element_t Bstar[BATCH_SIZE][FEATURE_SIZE + 1][FEATURE_SIZE + 1], int idx) {
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

    size_t g1_comp_len = 0;
    {
        element_t g1_probe;
        element_init_G1(g1_probe, pairing);
        g1_comp_len = static_cast<size_t>(element_length_in_bytes_compressed(g1_probe));
        element_clear(g1_probe);
    }

#pragma omp parallel
    {
        int tid = 0;
#ifdef _OPENMP
        tid = omp_get_thread_num();
#endif
        std::vector<LookupBuildEntry>& local_entries = entries_by_thread[static_cast<size_t>(tid)];
        local_entries.reserve((candidate_count / static_cast<size_t>(thread_count)) + 1);

        element_t expt, gt_val, target_expt, target_gt_val, z_scalar, slot_exp, slot_g1;
        element_init_Zr(expt, pairing);
        element_init_GT(gt_val, pairing);
        element_init_Zr(target_expt, pairing);
        element_init_GT(target_gt_val, pairing);
        element_init_Zr(z_scalar, pairing);
        element_init_Zr(slot_exp, pairing);
        element_init_G1(slot_g1, pairing);

#pragma omp for schedule(static)
        for (int x = min_x; x <= max_x; x++) {
            element_set_si(expt, z1 * x + z4);
            element_set_si(target_expt, Z1 * x + Z3);
            int z = r2 * (int)((long double)x * (long double)LR / (long double)BATCH_SIZE) + r1;
            element_set_si(z_scalar, z);
            element_pow_zn(gt_val, pk->gT_base, expt);
            element_pow_zn(target_gt_val, pk->gT_base, target_expt);

            std::vector<unsigned char> gt_bytes = serialize_element_to_bytes(gt_val);
            std::vector<unsigned char> target_gt_bytes = serialize_element_to_bytes(target_gt_val);

            std::vector<unsigned char> plaintext;
            plaintext.reserve(static_cast<size_t>(BATCH_SIZE) * static_cast<size_t>(FEATURE_SIZE + 1) * g1_comp_len +
                              target_gt_bytes.size());
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
                    element_mul(slot_exp, betad[batch_idx], Bstar[batch_idx][idx][feature_idx]);
                    element_mul(slot_exp, slot_exp, z_scalar);
                    element_pow_zn(slot_g1, pk->g1_base, slot_exp);

                    std::vector<unsigned char> slot_bytes =
                        serialize_g1_element_to_compressed_bytes(slot_g1);
                    plaintext.insert(plaintext.end(), slot_bytes.begin(), slot_bytes.end());
                }
            }
            plaintext.insert(plaintext.end(), target_gt_bytes.begin(), target_gt_bytes.end());

            std::vector<unsigned char> key;
            if (!hkdf_sha256(gt_bytes, salt, info, HKDF_KEY_LEN, key)) {
                continue;
            }

            EncryptedLookupRow row;
            row.nonce.assign(GCM_NONCE_LEN, 0);
            if (RAND_bytes(row.nonce.data(), row.nonce.size()) != 1) {
                continue;
            }

            if (!aes_gcm_encrypt(key, row.nonce, plaintext, row.ciphertext, row.tag)) {
                continue;
            }

            local_entries.push_back({std::move(row), std::move(key)});
        }

        element_clear(expt);
        element_clear(gt_val);
        element_clear(target_expt);
        element_clear(target_gt_val);
        element_clear(z_scalar);
        element_clear(slot_exp);
        element_clear(slot_g1);
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

bool MapLTinGTtoGTWithEncryptedLUT(pairing_t pairing,
                                   element_t L_T,
                                   const EncryptedLookupTable& lut,
                                   element_t L_in_GT,
                                   bool verbose = true) {
    auto start = std::chrono::steady_clock::now();
    auto stop = std::chrono::steady_clock::now();
    auto duration_us = std::chrono::duration<double, std::micro>(stop - start);
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

        element_init_GT(L_in_GT, pairing);
        element_from_bytes(L_in_GT, plaintext.data());
        stop = std::chrono::steady_clock::now();
        duration_us = std::chrono::duration<double, std::micro>(stop - start);
    #ifdef _OPENMP
        #pragma omp atomic update
    #endif
        total_lookup_us += duration_us.count();
        if (verbose) {
            printf("Lookup completed with success in %.3f us\n", duration_us.count());
        }
        return true;
    }
    stop = std::chrono::steady_clock::now();
    duration_us = std::chrono::duration<double, std::micro>(stop - start);
#ifdef _OPENMP
    #pragma omp atomic update
#endif
    total_lookup_us += duration_us.count();
    if (verbose) {
        printf("Lookup completed with failure in %.3f us\n", duration_us.count());
    }
    return false;
}

bool MapLTinGTtoG1WithEncryptedLUT(pairing_t pairing,
                                   element_t L_T,
                                   const EncryptedLookupTable& lut,
                                   element_t L_in_G1[BATCH_SIZE][FEATURE_SIZE + 1],
                                   element_t L_in_GT,
                                   bool verbose = true) {
    auto start = std::chrono::steady_clock::now();
    auto stop = std::chrono::steady_clock::now();
    auto duration_us = std::chrono::duration<double, std::micro>(stop - start);
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

        
        element_t g1_probe, gt_probe;
        element_init_G1(g1_probe, pairing);
        element_init_GT(gt_probe, pairing);
        int g1_comp_len = element_length_in_bytes_compressed(g1_probe);
        int gt_comp_len = element_length_in_bytes(gt_probe);
        element_clear(g1_probe);
        element_clear(gt_probe);

        size_t expected_len = static_cast<size_t>(FEATURE_SIZE + 1) *
                              static_cast<size_t>(BATCH_SIZE) *
                              static_cast<size_t>(g1_comp_len) +
                              static_cast<size_t>(gt_comp_len);
        if (plaintext.size() != expected_len) {
            continue;
        }

        size_t offset = 0;
        for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
            for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
                element_init_G1(L_in_G1[batch_idx][feature_idx], pairing);
                element_from_bytes_compressed(
                    L_in_G1[batch_idx][feature_idx],
                    const_cast<unsigned char*>(plaintext.data() + offset));
                offset += static_cast<size_t>(g1_comp_len);
            }
        }
        element_init_GT(L_in_GT, pairing);
        element_from_bytes(L_in_GT, plaintext.data() + offset);

        stop = std::chrono::steady_clock::now();
        duration_us = std::chrono::duration<double, std::micro>(stop - start);
    #ifdef _OPENMP
        #pragma omp atomic update
    #endif
        total_lookup_us += duration_us.count();
        if (verbose) {
            printf("GT->G1 lookup completed with success in %.3f us\n", duration_us.count());
        }
        return true;
    }

    stop = std::chrono::steady_clock::now();
    duration_us = std::chrono::duration<double, std::micro>(stop - start);
#ifdef _OPENMP
    #pragma omp atomic update
#endif
    total_lookup_us += duration_us.count();
    if (verbose) {
        printf("GT->G1 lookup completed with failure in %.3f us\n", duration_us.count());
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

// --- 4. Decrypt Algorithm (Kim et al. Section 3) ---
bool Decrypt(pairing_t pairing, PublicKey* pk, DecryptionKey* sk, Ciphertext* ct,
             const EncryptedLookupTable& lut,
             const EncryptedLookupTable& lut_gt_to_g1,
             long wd,
             long z1, long z3mz4, long w, long expected_output, long output_value,
             int r2, int r1, int Z1, int Z3, element_t betad[BATCH_SIZE], element_t Bstar[BATCH_SIZE][FEATURE_SIZE + 1][FEATURE_SIZE + 1], int idx,
             bool verbose = true) {
    // Start of phase 1
    element_t D1, D2, temp_pairing;
    element_init_GT(D1, pairing);
    element_init_GT(D2, pairing);
    element_init_GT(temp_pairing, pairing);

    // D1 = e(K1, C1)
    element_pairing(D1, sk->K1, ct->C1);
    // End of phase 1

    // D2 = product e(K2[i], C2[i])
    auto start = std::chrono::steady_clock::now();
    // Start of phase 2
    element_set1(D2);
    for (int i = 0; i < DIM_M; i++) {
        element_pairing(temp_pairing, sk->K2[i], ct->C2[i]);
        element_mul(D2, D2, temp_pairing);
    }
    // End of phase 2

    auto stop = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    total_decrypt_ms += duration.count();

    if (verbose) {
        printf("Decrypt pairings completed in %lld ms\n", duration.count());
    }

    // Start of Phase 3
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
    // End of Phase 3

    // Pass D2 off to the LUT. In a fully symmetric system where D1 changes organically, 
    // LUT structure would hash a pairing derived value or be modified, but we pass D2 
    // seamlessly directly down here.
    // Start of Phase 4
    element_t L_in_GT;
    if (!MapLTinGTtoGTWithEncryptedLUT(pairing, D2, lut, L_in_GT, verbose)) {
        printf("Failed to map D2 from GT to GT using encrypted LUT.\n");
        element_clear(D1);
        element_clear(D2);
        element_clear(temp_pairing);
        return false;
    }
    // End of Phase 4

    // Start of Phase 5
    element_t lut_exp, expected_L_in_GT;
    element_init_Zr(lut_exp, pairing);
    element_init_GT(expected_L_in_GT, pairing);
    element_set_si(lut_exp, z1 * (output_value >> (QUANTIZATION_BITS - 1)) + z3mz4);
    element_pow_zn(expected_L_in_GT, pk->gT_base, lut_exp);
    if (element_cmp(L_in_GT, expected_L_in_GT) != 0) {
        printf("[ASSERTION FAILED] L_in_GT != gT_base^(z1 * (output_value >> (QUANTIZATION_BITS - 1)) + z3mz4)\n");
        element_clear(lut_exp);
        element_clear(expected_L_in_GT);
        element_clear(L_in_GT);
        element_clear(D1);
        element_clear(D2);
        element_clear(temp_pairing);
        return false;
    }
    // End of Phase 5

    auto wd_start = std::chrono::steady_clock::now();
    // Start of Phase 6
    element_t wd_exp, gt_wd, l_in_gt_inv, gt_wd_over_l;
    element_init_Zr(wd_exp, pairing);
    element_init_GT(gt_wd, pairing);
    element_init_GT(l_in_gt_inv, pairing);
    element_init_GT(gt_wd_over_l, pairing);

    element_set_si(wd_exp, wd);
    element_pow_zn(gt_wd, pk->gT_base, wd_exp);
    element_invert(l_in_gt_inv, L_in_GT);
    element_mul(gt_wd_over_l, gt_wd, l_in_gt_inv);
    // End of Phase 6

    element_t gt_wd_over_l_in_g1[BATCH_SIZE][FEATURE_SIZE + 1];
    element_t gt_wd_over_l_in_gt;
    // Start of Phase 7
    if (!MapLTinGTtoG1WithEncryptedLUT(pairing, gt_wd_over_l, lut_gt_to_g1, gt_wd_over_l_in_g1, gt_wd_over_l_in_gt, verbose)) {
        printf("Failed to map gt_wd_over_l from GT to G1 using encrypted LUT.\n");
        element_clear(wd_exp);
        element_clear(gt_wd);
        element_clear(l_in_gt_inv);
        element_clear(gt_wd_over_l);
        element_clear(lut_exp);
        element_clear(expected_L_in_GT);
        element_clear(L_in_GT);
        element_clear(D1);
        element_clear(D2);
        element_clear(temp_pairing);
        return false;
    }
    // End of Phase 7

    // Start of Phase 8
    const bool enable_gt_wd_over_l_in_g1_assert = true;
    if (enable_gt_wd_over_l_in_g1_assert) {
        long expected_g1_exp_si = static_cast<long>(
            r2 * (int)((w - (output_value >> (QUANTIZATION_BITS - 1))) * (long double)LR / (long double)BATCH_SIZE) + r1);

        element_t expected_g1_z, expected_slot_exp, expected_slot_g1;
        element_t expected_gt_exp, expected_gt;
        element_init_Zr(expected_g1_z, pairing);
        element_init_Zr(expected_slot_exp, pairing);
        element_init_G1(expected_slot_g1, pairing);
        element_init_Zr(expected_gt_exp, pairing);
        element_init_GT(expected_gt, pairing);
        element_set_si(expected_g1_z, expected_g1_exp_si);

        bool g1_ok = true;
        for (int batch_idx = 0; batch_idx < BATCH_SIZE && g1_ok; batch_idx++) {
            for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
                element_mul(expected_slot_exp,
                            betad[batch_idx],
                            Bstar[batch_idx][idx][feature_idx]);
                element_mul(expected_slot_exp, expected_slot_exp, expected_g1_z);
                element_pow_zn(expected_slot_g1, pk->g1_base, expected_slot_exp);

                if (element_cmp(gt_wd_over_l_in_g1[batch_idx][feature_idx], expected_slot_g1) != 0) {
                    g1_ok = false;
                    break;
                }
            }
        }

        if (!g1_ok) {
            printf("[ASSERTION FAILED] gt_wd_over_l_in_g1[batch_idx][feature_idx] != g1^(betad[batch_idx] * Bstar[batch_idx][idx][feature_idx] * expected_g1_exp_si)\n");
            element_clear(expected_g1_z);
            element_clear(expected_slot_exp);
            element_clear(expected_slot_g1);
            element_clear(expected_gt_exp);
            element_clear(expected_gt);
            element_clear(wd_exp);
            element_clear(gt_wd);
            element_clear(l_in_gt_inv);
            element_clear(gt_wd_over_l);
            for (int i = 0; i < BATCH_SIZE; i++) {
                for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                    element_clear(gt_wd_over_l_in_g1[i][j]);
                }
            }
            element_clear(gt_wd_over_l_in_gt);
            element_clear(lut_exp);
            element_clear(expected_L_in_GT);
            element_clear(L_in_GT);
            element_clear(D1);
            element_clear(D2);
            element_clear(temp_pairing);
            return false;
        }

        long expected_gt_exp_si =
            static_cast<long>(Z1 * (w - (output_value >> (QUANTIZATION_BITS - 1))) + Z3);
        element_set_si(expected_gt_exp, expected_gt_exp_si);
        element_pow_zn(expected_gt, pk->gT_base, expected_gt_exp);

        if (element_cmp(gt_wd_over_l_in_gt, expected_gt) != 0) {
            printf("[ASSERTION FAILED] gt_wd_over_l_in_gt != gT_base^(Z1 * (w - (output_value >> (QUANTIZATION_BITS - 1))) + Z3)\n");
            element_clear(expected_g1_z);
            element_clear(expected_slot_exp);
            element_clear(expected_slot_g1);
            element_clear(expected_gt_exp);
            element_clear(expected_gt);
            element_clear(wd_exp);
            element_clear(gt_wd);
            element_clear(l_in_gt_inv);
            element_clear(gt_wd_over_l);
            for (int i = 0; i < BATCH_SIZE; i++) {
                for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                    element_clear(gt_wd_over_l_in_g1[i][j]);
                }
            }
            element_clear(gt_wd_over_l_in_gt);
            element_clear(lut_exp);
            element_clear(expected_L_in_GT);
            element_clear(L_in_GT);
            element_clear(D1);
            element_clear(D2);
            element_clear(temp_pairing);
            return false;
        }

        element_clear(expected_g1_z);
        element_clear(expected_slot_exp);
        element_clear(expected_slot_g1);
        element_clear(expected_gt_exp);
        element_clear(expected_gt);
    }
    // End of Phase 8

    auto wd_stop = std::chrono::steady_clock::now();
    auto wd_duration = std::chrono::duration_cast<std::chrono::milliseconds>(wd_stop - wd_start);
    total_decrypt_ms += wd_duration.count();

    if (verbose) {
        printf("Mapped D2 from GT to GT using encrypted LUT.\n");
        printf("Computed gT_base^wd / L_in_GT in %lld ms\n", wd_duration.count());
        printf("Mapped gt_wd_over_l from GT to G1 using encrypted LUT.\n");
    }

    // Start of Phase 9
    element_clear(wd_exp);
    element_clear(gt_wd);
    element_clear(l_in_gt_inv);
    element_clear(gt_wd_over_l);
    for (int i = 0; i < BATCH_SIZE; i++) {
        for (int j = 0; j < FEATURE_SIZE + 1; j++) {
            element_clear(gt_wd_over_l_in_g1[i][j]);
        }
    }
    element_clear(gt_wd_over_l_in_gt);
    element_clear(lut_exp);
    element_clear(expected_L_in_GT);
    element_clear(L_in_GT);

    element_clear(D1);
    element_clear(D2);
    element_clear(temp_pairing);
    return true;
    // End of Phase 9
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

int invert_and_det_matrix_Fq_feature(pairing_t pairing,
                                   element_t M[FEATURE_SIZE + 1][FEATURE_SIZE + 1],
                                   element_t inverse[FEATURE_SIZE + 1][FEATURE_SIZE + 1],
                                   element_t det) {
    element_t aug[FEATURE_SIZE + 1][2 * (FEATURE_SIZE + 1)];
    element_t temp, pivot_inv, factor;

    element_init_Zr(temp, pairing);
    element_init_Zr(pivot_inv, pairing);
    element_init_Zr(factor, pairing);

    element_set1(det);
    int sign = 1;

    for (int i = 0; i < FEATURE_SIZE + 1; i++) {
        for (int j = 0; j < FEATURE_SIZE + 1; j++) {
            element_init_Zr(aug[i][j], pairing);
            element_set(aug[i][j], M[i][j]);

            element_init_Zr(aug[i][j + (FEATURE_SIZE + 1)], pairing);
            if (i == j) {
                element_set1(aug[i][j + (FEATURE_SIZE + 1)]);
            } else {
                element_set0(aug[i][j + (FEATURE_SIZE + 1)]);
            }
        }
    }

    for (int i = 0; i < FEATURE_SIZE + 1; i++) {
        int pivot_row = i;
        for (int k = i + 1; k < FEATURE_SIZE + 1; k++) {
            if (!element_is0(aug[k][i])) {
                pivot_row = k;
                break;
            }
        }
        if (element_is0(aug[pivot_row][i])) {
            element_set0(det);
            for (int r = 0; r < FEATURE_SIZE + 1; r++) {
                for (int c = 0; c < 2 * (FEATURE_SIZE + 1); c++) {
                    element_clear(aug[r][c]);
                }
            }
            element_clear(temp);
            element_clear(pivot_inv);
            element_clear(factor);
            return 0;
        }

        if (pivot_row != i) {
            for (int j = 0; j < 2 * (FEATURE_SIZE + 1); j++) {
                element_set(temp, aug[i][j]);
                element_set(aug[i][j], aug[pivot_row][j]);
                element_set(aug[pivot_row][j], temp);
            }
            sign = -sign;
        }

        element_mul(det, det, aug[i][i]);
        element_invert(pivot_inv, aug[i][i]);
        for (int j = 0; j < 2 * (FEATURE_SIZE + 1); j++) {
            element_mul(aug[i][j], aug[i][j], pivot_inv);
        }

        for (int k = 0; k < FEATURE_SIZE + 1; k++) {
            if (k != i) {
                element_set(factor, aug[k][i]);
                for (int j = 0; j < 2 * (FEATURE_SIZE + 1); j++) {
                    element_mul(temp, factor, aug[i][j]);
                    element_sub(aug[k][j], aug[k][j], temp);
                }
            }
        }
    }

    if (sign == -1) {
        element_neg(det, det);
    }

    for (int i = 0; i < FEATURE_SIZE + 1; i++) {
        for (int j = 0; j < FEATURE_SIZE + 1; j++) {
            element_set(inverse[i][j], aug[i][j + (FEATURE_SIZE + 1)]);
        }
    }

    element_clear(temp);
    element_clear(pivot_inv);
    element_clear(factor);
    for (int i = 0; i < FEATURE_SIZE + 1; i++) {
        for (int j = 0; j < 2 * (FEATURE_SIZE + 1); j++) {
            element_clear(aug[i][j]);
        }
    }

    return 1;
}

struct FeaturePhaseState {
    PublicKey pk;
    MasterSecretKey msk;
    DecryptionKey sk;
    Ciphertext ct;

    EncryptedLookupTable lut;
    EncryptedLookupTable lut_gt_to_g1;

    element_t alpha_sample;
    element_t beta_sample;
    bool alpha_beta_init;

    long wd;
    long z1;
    long z3mz4;
    long w_scaled;
    long expected_output;
    long output_values;

    int feature_idx;
    int r1_feature;
    int Z3_feature;

    element_t D1;
    element_t D2;
    element_t temp_pairing;
    bool phase1_init;

    element_t L_in_GT;
    bool phase4_init;

    element_t wd_exp;
    element_t gt_wd;
    element_t l_in_gt_inv;
    element_t gt_wd_over_l;
    bool phase6_init;

    element_t gt_wd_over_l_in_g1[BATCH_SIZE][FEATURE_SIZE + 1];
    bool gt_wd_over_l_in_g1_init[BATCH_SIZE][FEATURE_SIZE + 1];
    element_t gt_wd_over_l_in_gt;
    bool phase7_gt_init;

    bool setup_complete;
};

int main() {
    srand(time(NULL));

#ifdef _OPENMP
    omp_set_dynamic(0);
    omp_set_num_threads(omp_get_max_threads());
#endif

    pairing_t pairing;
    pbc_param_t pbc_param;
    // pbc_param_init_a_gen(pbc_param, 160, 512);
    pbc_param_init_a_gen(pbc_param, 80, 256);
    pairing_init_pbc_param(pairing, pbc_param);
    pbc_param_clear(pbc_param);

    PublicKey pk;
    MasterSecretKey msk;
    DecryptionKey sk;
    Ciphertext ct;

    double total_setup_ms = 0.0;
    double total_lut_build_ms = 0.0;
    long double total_lut_size_bytes = 0.0L;
    long long total_keygen_ms = 0;
    long long total_encrypt_ms = 0;

    int r2 = generate_random_int(-(1 << 15), (1 << 15) - 1);
    int Z1 = generate_random_int(-(1 << 15), (1 << 15) - 1);
    int r1[FEATURE_SIZE], Z3[FEATURE_SIZE];
    for (int i = 0; i < FEATURE_SIZE; i++) {
        r1[i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
        Z3[i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
    }
    element_t betad[BATCH_SIZE];
    element_t Bstar[BATCH_SIZE][FEATURE_SIZE + 1][FEATURE_SIZE + 1];
    for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
        element_init_Zr(betad[batch_idx], pairing);
        element_random(betad[batch_idx]);

        element_t B[FEATURE_SIZE + 1][FEATURE_SIZE + 1];
        element_t B_inv[FEATURE_SIZE + 1][FEATURE_SIZE + 1];
        element_t det_B_feature;
        element_t tmp;
        element_init_Zr(det_B_feature, pairing);
        element_init_Zr(tmp, pairing);

        for (int i = 0; i < FEATURE_SIZE + 1; i++) {
            for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                element_init_Zr(B[i][j], pairing);
                element_init_Zr(B_inv[i][j], pairing);
                element_init_Zr(Bstar[batch_idx][i][j], pairing);
            }
        }

        int is_invertible = 0;
        while (!is_invertible) {
            for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                    element_random(B[i][j]);
                }
            }
            is_invertible = invert_and_det_matrix_Fq_feature(pairing, B, B_inv, det_B_feature);
        }

        for (int i = 0; i < FEATURE_SIZE + 1; i++) {
            for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                element_mul(tmp, det_B_feature, B_inv[j][i]);
                element_set(Bstar[batch_idx][i][j], tmp);
            }
        }

        element_clear(tmp);
        element_clear(det_B_feature);
        for (int i = 0; i < FEATURE_SIZE + 1; i++) {
            for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                element_clear(B[i][j]);
                element_clear(B_inv[i][j]);
            }
        }
    }

    FeaturePhaseState states[FEATURE_SIZE] = {};
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        states[feature].feature_idx = feature;
        states[feature].r1_feature = r1[feature];
        states[feature].Z3_feature = Z3[feature];
        for (int i = 0; i < BATCH_SIZE; i++) {
            for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                states[feature].gt_wd_over_l_in_g1_init[i][j] = false;
            }
        }
    }

    double phase2_ms = 0.0;
    double phase4_ms = 0.0;
    double phase6_ms = 0.0;
    double phase7_ms = 0.0;
    double phase9_c2_ms = 0.0;

    // Phase 0: setup + keygen + encrypt + LUT builds for all features.
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        auto sample_start = std::chrono::steady_clock::now();
        FeaturePhaseState& s = states[feature];

        auto start = std::chrono::steady_clock::now();
        Setup(pairing, &s.pk, &s.msk);
        auto stop = std::chrono::steady_clock::now();
        total_setup_ms += std::chrono::duration<double, std::milli>(stop - start).count();

        element_init_Zr(s.alpha_sample, pairing);
        element_init_Zr(s.beta_sample, pairing);
        s.alpha_beta_init = true;

        // Single flat vectors of DIM_M dimension.
        element_t x_vec[DIM_M];
        element_t y_vec[DIM_M];

        long w;
        long x[BATCH_SIZE];
        long y[BATCH_SIZE];
        long y_hat[BATCH_SIZE];
        long z1;
        long z3;
        long z4;
        long z2[BATCH_SIZE];
        long x_values[DIM_M];
        long y_values[DIM_M];

        w = generate_random_int(MIN_X, MAX_X);
        z1 = generate_random_int(-(1 << 15), (1 << 15) - 1);
        z3 = generate_random_int(-(1 << 15), (1 << 15) - 1);
        z4 = generate_random_int(-(1 << 15), (1 << 15) - 1);

        long output_values = 0;
        for (int i = 0; i < BATCH_SIZE; i++) {
            y[i] = MAX_X * generate_random_int(0, 1);
            y_hat[i] = generate_random_int(0, MAX_X);
            x[i] = (feature == FEATURE_SIZE - 1)? MAX_X: generate_random_int(MIN_X, MAX_X);
            output_values -= (y[i] - y_hat[i]) * x[i];
        }

        y_values[DIM_M - 1] = z3 - z4;
        for (int i = 0; i < BATCH_SIZE; i++) {
            z2[i] = generate_random_int(-(1 << 15), (1 << 15) - 1);
            y_values[DIM_M - 1] -= x[i] * (z2[i] + z1 * y[i]);
        }

        long expected_output = 0;
        for (int i = 0; i < BATCH_SIZE; i++) {
            x_values[i] = z1 * y_hat[i] + z2[i];
        }
        x_values[DIM_M - 1] = 1;

        for (int i = 0; i < BATCH_SIZE; i++) {
            y_values[i] = x[i];
        }

        for (int j = 0; j < DIM_M; j++) {
            element_init_Zr(x_vec[j], pairing);
            element_init_Zr(y_vec[j], pairing);
            element_set_si(x_vec[j], x_values[j]);
            element_set_si(y_vec[j], y_values[j]);
            expected_output += x_values[j] * y_values[j];
        }

        if (expected_output != (z1 * output_values + z3 - z4)) {
            printf("\n[ASSERTION FAILED] expected_output != z1 * output_values + z3 - z4 at feature %d\n", feature);
            for (int i = 0; i < BATCH_SIZE; i++) {
                printf("index=%d, x=%ld, y=%ld, y_hat=%ld, z2=%ld\n", i, x[i], y[i], y_hat[i], z2[i]);
            }
            printf("z3=%ld, z4=%ld, z1=%ld\n", z3, z4, z1);
            printf("output_value=%ld, expected_output=%ld\n", output_values, expected_output);

            for (int i = 0; i < DIM_M; i++) {
                element_clear(x_vec[i]);
                element_clear(y_vec[i]);
            }
            for (int f = 0; f <= feature; f++) {
                if (states[f].setup_complete) {
                    ClearDecryptionKey(&states[f].sk);
                    ClearCiphertexts(&states[f].ct);
                    ClearPublicKey(&states[f].pk);
                    ClearMasterSecretKey(&states[f].msk);
                }
                if (states[f].alpha_beta_init) {
                    element_clear(states[f].alpha_sample);
                    element_clear(states[f].beta_sample);
                }
            }
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                element_clear(betad[batch_idx]);
                for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        element_clear(Bstar[batch_idx][i][j]);
                    }
                }
            }
            pairing_clear(pairing);
            return 1;
        }

        s.wd = static_cast<long>(z1 * ((long double)BATCH_SIZE / (long double)LR) * w + z3);
        s.z1 = z1;
        s.z3mz4 = z3 - z4;
        s.w_scaled = static_cast<long>(((long double)BATCH_SIZE / (long double)LR) * w);
        s.expected_output = expected_output;
        s.output_values = output_values;

        start = std::chrono::steady_clock::now();
        KeyGen(pairing, &s.pk, &s.msk, y_vec, &s.sk, s.alpha_sample);
        stop = std::chrono::steady_clock::now();
        total_keygen_ms += std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count();

        start = std::chrono::steady_clock::now();
        Encrypt(pairing, &s.pk, &s.msk, x_vec, &s.ct, s.beta_sample);
        stop = std::chrono::steady_clock::now();
        total_encrypt_ms += std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count();

        start = std::chrono::steady_clock::now();
        s.lut = BuildEncryptedLookupTable(pairing, &s.pk, (BATCH_SIZE) * (MIN_X) * (MAX_X), BATCH_SIZE * (MAX_X) * (MAX_X), z3 - z4, z1, s.alpha_sample, s.beta_sample, s.msk.det_B);
        stop = std::chrono::steady_clock::now();
        total_lut_build_ms += std::chrono::duration<double, std::milli>(stop - start).count();
        total_lut_size_bytes += static_cast<long double>(estimate_lut_size_bytes(s.lut));

        start = std::chrono::steady_clock::now();
        s.lut_gt_to_g1 = BuildEncryptedLookupTableGTtoG1(pairing, &s.pk, ((BATCH_SIZE) / (LR) + (BATCH_SIZE)) * (MIN_X), ((BATCH_SIZE) / (LR) + (BATCH_SIZE)) * (MAX_X), z1, z4, r2, s.r1_feature, Z1, s.Z3_feature, betad, Bstar, feature);
        stop = std::chrono::steady_clock::now();
        total_lut_build_ms += std::chrono::duration<double, std::milli>(stop - start).count();
        total_lut_size_bytes += static_cast<long double>(estimate_lut_size_bytes(s.lut_gt_to_g1));

        if (feature == 0) {
            printf("\n=== LUT Row Stats feature 0 ===\n");
            print_lut_row_stats("GT->GT LUT", s.lut);
            print_lut_row_stats("GT->G1 LUT", s.lut_gt_to_g1);
            printf("=========================================\n\n");
        }

        for (int i = 0; i < DIM_M; i++) {
            element_clear(x_vec[i]);
            element_clear(y_vec[i]);
        }

        s.setup_complete = true;
        auto sample_stop = std::chrono::steady_clock::now();
        double sample_total_ms = std::chrono::duration<double, std::milli>(sample_stop - sample_start).count();
        printf("feature %d phase-0 time: %.3f s\n", feature, sample_total_ms / 1000.0);
    }

    // Decrypt phase 1 loop.
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        element_init_GT(s.D1, pairing);
        element_init_GT(s.D2, pairing);
        element_init_GT(s.temp_pairing, pairing);

        element_pairing(s.D1, s.sk.K1, s.ct.C1);
        s.phase1_init = true;
    }

    // Decrypt phase 2 loop (timed).
    auto phase2_start = std::chrono::steady_clock::now();
    #pragma omp parallel for schedule(static)
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        element_set1(s.D2);
        for (int i = 0; i < DIM_M; i++) {
            element_pairing(s.temp_pairing, s.sk.K2[i], s.ct.C2[i]);
            element_mul(s.D2, s.D2, s.temp_pairing);
        }
    }
    auto phase2_stop = std::chrono::steady_clock::now();
    phase2_ms = std::chrono::duration<double, std::milli>(phase2_stop - phase2_start).count();

    // Decrypt phase 3 loop.
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        element_t expected_exp, D1_expected;
        element_init_Zr(expected_exp, pairing);
        element_init_GT(D1_expected, pairing);
        element_set_si(expected_exp, s.expected_output);
        element_pow_zn(D1_expected, s.D1, expected_exp);
        if (element_cmp(D1_expected, s.D2) != 0) {
            printf("[ASSERTION FAILED] D1^expected_output != D2 at feature %d\n", feature);
            element_clear(expected_exp);
            element_clear(D1_expected);
            for (int f = 0; f < FEATURE_SIZE; f++) {
                if (states[f].phase1_init) {
                    element_clear(states[f].D1);
                    element_clear(states[f].D2);
                    element_clear(states[f].temp_pairing);
                    states[f].phase1_init = false;
                }
                if (states[f].phase4_init) {
                    element_clear(states[f].L_in_GT);
                    states[f].phase4_init = false;
                }
                if (states[f].phase6_init) {
                    element_clear(states[f].wd_exp);
                    element_clear(states[f].gt_wd);
                    element_clear(states[f].l_in_gt_inv);
                    element_clear(states[f].gt_wd_over_l);
                    states[f].phase6_init = false;
                }
                if (states[f].phase7_gt_init) {
                    element_clear(states[f].gt_wd_over_l_in_gt);
                    states[f].phase7_gt_init = false;
                }
                for (int i = 0; i < BATCH_SIZE; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        if (states[f].gt_wd_over_l_in_g1_init[i][j]) {
                            element_clear(states[f].gt_wd_over_l_in_g1[i][j]);
                            states[f].gt_wd_over_l_in_g1_init[i][j] = false;
                        }
                    }
                }
                if (states[f].setup_complete) {
                    ClearDecryptionKey(&states[f].sk);
                    ClearCiphertexts(&states[f].ct);
                    ClearPublicKey(&states[f].pk);
                    ClearMasterSecretKey(&states[f].msk);
                    states[f].setup_complete = false;
                }
                if (states[f].alpha_beta_init) {
                    element_clear(states[f].alpha_sample);
                    element_clear(states[f].beta_sample);
                    states[f].alpha_beta_init = false;
                }
            }
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                element_clear(betad[batch_idx]);
                for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        element_clear(Bstar[batch_idx][i][j]);
                    }
                }
            }
            pairing_clear(pairing);
            return 1;
        }
        element_clear(expected_exp);
        element_clear(D1_expected);
    }

    // Decrypt phase 4 loop (timed).
    auto phase4_start = std::chrono::steady_clock::now();
    int phase4_failed = 0;
    int phase4_failed_feature = -1;
    #pragma omp parallel for schedule(static)
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        if (!MapLTinGTtoGTWithEncryptedLUT(pairing, s.D2, s.lut, s.L_in_GT, false)) {
            #pragma omp critical
            {
                if (!phase4_failed) {
                    phase4_failed = 1;
                    phase4_failed_feature = feature;
                }
            }
        } else {
            s.phase4_init = true;
        }
    }
    auto phase4_stop = std::chrono::steady_clock::now();
    phase4_ms = std::chrono::duration<double, std::milli>(phase4_stop - phase4_start).count();
    if (phase4_failed) {
            printf("Failed to map D2 from GT to GT using encrypted LUT at feature %d.\n", phase4_failed_feature);
            for (int f = 0; f < FEATURE_SIZE; f++) {
                if (states[f].phase1_init) {
                    element_clear(states[f].D1);
                    element_clear(states[f].D2);
                    element_clear(states[f].temp_pairing);
                    states[f].phase1_init = false;
                }
                if (states[f].phase4_init) {
                    element_clear(states[f].L_in_GT);
                    states[f].phase4_init = false;
                }
                if (states[f].phase6_init) {
                    element_clear(states[f].wd_exp);
                    element_clear(states[f].gt_wd);
                    element_clear(states[f].l_in_gt_inv);
                    element_clear(states[f].gt_wd_over_l);
                    states[f].phase6_init = false;
                }
                if (states[f].phase7_gt_init) {
                    element_clear(states[f].gt_wd_over_l_in_gt);
                    states[f].phase7_gt_init = false;
                }
                for (int i = 0; i < BATCH_SIZE; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        if (states[f].gt_wd_over_l_in_g1_init[i][j]) {
                            element_clear(states[f].gt_wd_over_l_in_g1[i][j]);
                            states[f].gt_wd_over_l_in_g1_init[i][j] = false;
                        }
                    }
                }
                if (states[f].setup_complete) {
                    ClearDecryptionKey(&states[f].sk);
                    ClearCiphertexts(&states[f].ct);
                    ClearPublicKey(&states[f].pk);
                    ClearMasterSecretKey(&states[f].msk);
                    states[f].setup_complete = false;
                }
                if (states[f].alpha_beta_init) {
                    element_clear(states[f].alpha_sample);
                    element_clear(states[f].beta_sample);
                    states[f].alpha_beta_init = false;
                }
            }
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                element_clear(betad[batch_idx]);
                for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        element_clear(Bstar[batch_idx][i][j]);
                    }
                }
            }
            pairing_clear(pairing);
            return 1;
    }

    // Decrypt phase 5 loop.
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        element_t lut_exp, expected_L_in_GT;
        element_init_Zr(lut_exp, pairing);
        element_init_GT(expected_L_in_GT, pairing);
        element_set_si(lut_exp, s.z1 * (s.output_values >> (QUANTIZATION_BITS - 1)) + s.z3mz4);
        element_pow_zn(expected_L_in_GT, s.pk.gT_base, lut_exp);
        if (element_cmp(s.L_in_GT, expected_L_in_GT) != 0) {
            printf("[ASSERTION FAILED] L_in_GT mismatch at feature %d\n", feature);
            element_clear(lut_exp);
            element_clear(expected_L_in_GT);
            for (int f = 0; f < FEATURE_SIZE; f++) {
                if (states[f].phase1_init) {
                    element_clear(states[f].D1);
                    element_clear(states[f].D2);
                    element_clear(states[f].temp_pairing);
                    states[f].phase1_init = false;
                }
                if (states[f].phase4_init) {
                    element_clear(states[f].L_in_GT);
                    states[f].phase4_init = false;
                }
                if (states[f].phase6_init) {
                    element_clear(states[f].wd_exp);
                    element_clear(states[f].gt_wd);
                    element_clear(states[f].l_in_gt_inv);
                    element_clear(states[f].gt_wd_over_l);
                    states[f].phase6_init = false;
                }
                if (states[f].phase7_gt_init) {
                    element_clear(states[f].gt_wd_over_l_in_gt);
                    states[f].phase7_gt_init = false;
                }
                for (int i = 0; i < BATCH_SIZE; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        if (states[f].gt_wd_over_l_in_g1_init[i][j]) {
                            element_clear(states[f].gt_wd_over_l_in_g1[i][j]);
                            states[f].gt_wd_over_l_in_g1_init[i][j] = false;
                        }
                    }
                }
                if (states[f].setup_complete) {
                    ClearDecryptionKey(&states[f].sk);
                    ClearCiphertexts(&states[f].ct);
                    ClearPublicKey(&states[f].pk);
                    ClearMasterSecretKey(&states[f].msk);
                    states[f].setup_complete = false;
                }
                if (states[f].alpha_beta_init) {
                    element_clear(states[f].alpha_sample);
                    element_clear(states[f].beta_sample);
                    states[f].alpha_beta_init = false;
                }
            }
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                element_clear(betad[batch_idx]);
                for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        element_clear(Bstar[batch_idx][i][j]);
                    }
                }
            }
            pairing_clear(pairing);
            return 1;
        }
        element_clear(lut_exp);
        element_clear(expected_L_in_GT);
    }

    // Decrypt phase 6 loop (timed).
    auto phase6_start = std::chrono::steady_clock::now();
    #pragma omp parallel for schedule(static)
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        element_init_Zr(s.wd_exp, pairing);
        element_init_GT(s.gt_wd, pairing);
        element_init_GT(s.l_in_gt_inv, pairing);
        element_init_GT(s.gt_wd_over_l, pairing);

        element_set_si(s.wd_exp, s.wd);
        element_pow_zn(s.gt_wd, s.pk.gT_base, s.wd_exp);
        element_invert(s.l_in_gt_inv, s.L_in_GT);
        element_mul(s.gt_wd_over_l, s.gt_wd, s.l_in_gt_inv);
        s.phase6_init = true;
    }
    auto phase6_stop = std::chrono::steady_clock::now();
    phase6_ms = std::chrono::duration<double, std::milli>(phase6_stop - phase6_start).count();

    // Decrypt phase 7 loop (timed).
    auto phase7_start = std::chrono::steady_clock::now();
    int phase7_failed = 0;
    int phase7_failed_feature = -1;
    #pragma omp parallel for schedule(static)
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        if (!MapLTinGTtoG1WithEncryptedLUT(pairing, s.gt_wd_over_l, s.lut_gt_to_g1,
                                           s.gt_wd_over_l_in_g1, s.gt_wd_over_l_in_gt, false)) {
            #pragma omp critical
            {
                if (!phase7_failed) {
                    phase7_failed = 1;
                    phase7_failed_feature = feature;
                }
            }
        } else {
            s.phase7_gt_init = true;
        }
    }
    auto phase7_stop = std::chrono::steady_clock::now();
    phase7_ms = std::chrono::duration<double, std::milli>(phase7_stop - phase7_start).count();
    if (phase7_failed) {
            printf("Failed to map gt_wd_over_l from GT to G1 using encrypted LUT at feature %d.\n", phase7_failed_feature);
            for (int f = 0; f < FEATURE_SIZE; f++) {
                if (states[f].phase1_init) {
                    element_clear(states[f].D1);
                    element_clear(states[f].D2);
                    element_clear(states[f].temp_pairing);
                    states[f].phase1_init = false;
                }
                if (states[f].phase4_init) {
                    element_clear(states[f].L_in_GT);
                    states[f].phase4_init = false;
                }
                if (states[f].phase6_init) {
                    element_clear(states[f].wd_exp);
                    element_clear(states[f].gt_wd);
                    element_clear(states[f].l_in_gt_inv);
                    element_clear(states[f].gt_wd_over_l);
                    states[f].phase6_init = false;
                }
                if (states[f].phase7_gt_init) {
                    element_clear(states[f].gt_wd_over_l_in_gt);
                    states[f].phase7_gt_init = false;
                }
                for (int i = 0; i < BATCH_SIZE; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        if (states[f].gt_wd_over_l_in_g1_init[i][j]) {
                            element_clear(states[f].gt_wd_over_l_in_g1[i][j]);
                            states[f].gt_wd_over_l_in_g1_init[i][j] = false;
                        }
                    }
                }
                if (states[f].setup_complete) {
                    ClearDecryptionKey(&states[f].sk);
                    ClearCiphertexts(&states[f].ct);
                    ClearPublicKey(&states[f].pk);
                    ClearMasterSecretKey(&states[f].msk);
                    states[f].setup_complete = false;
                }
                if (states[f].alpha_beta_init) {
                    element_clear(states[f].alpha_sample);
                    element_clear(states[f].beta_sample);
                    states[f].alpha_beta_init = false;
                }
            }
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                element_clear(betad[batch_idx]);
                for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        element_clear(Bstar[batch_idx][i][j]);
                    }
                }
            }
            pairing_clear(pairing);
            return 1;
    }

    // Mark phase-7 G1 outputs as initialized outside timed phase measurement.
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        for (int i = 0; i < BATCH_SIZE; i++) {
            for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                s.gt_wd_over_l_in_g1_init[i][j] = true;
            }
        }
    }

    // Decrypt phase 8 loop.
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        long expected_g1_exp_si = static_cast<long>(
            r2 * (int)((s.w_scaled - (s.output_values >> (QUANTIZATION_BITS - 1))) * (long double)LR / (long double)BATCH_SIZE) + s.r1_feature);

        element_t expected_g1_z, expected_slot_exp, expected_slot_g1;
        element_t expected_gt_exp, expected_gt;
        element_init_Zr(expected_g1_z, pairing);
        element_init_Zr(expected_slot_exp, pairing);
        element_init_G1(expected_slot_g1, pairing);
        element_init_Zr(expected_gt_exp, pairing);
        element_init_GT(expected_gt, pairing);
        element_set_si(expected_g1_z, expected_g1_exp_si);

        bool g1_ok = true;
        for (int batch_idx = 0; batch_idx < BATCH_SIZE && g1_ok; batch_idx++) {
            for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
                element_mul(expected_slot_exp,
                            betad[batch_idx],
                            Bstar[batch_idx][feature][feature_idx]);
                element_mul(expected_slot_exp, expected_slot_exp, expected_g1_z);
                element_pow_zn(expected_slot_g1, s.pk.g1_base, expected_slot_exp);

                if (element_cmp(s.gt_wd_over_l_in_g1[batch_idx][feature_idx], expected_slot_g1) != 0) {
                    g1_ok = false;
                    break;
                }
            }
        }

        if (!g1_ok) {
            printf("[ASSERTION FAILED] gt_wd_over_l_in_g1 mismatch at feature %d\n", feature);
            element_clear(expected_g1_z);
            element_clear(expected_slot_exp);
            element_clear(expected_slot_g1);
            element_clear(expected_gt_exp);
            element_clear(expected_gt);
            for (int f = 0; f < FEATURE_SIZE; f++) {
                if (states[f].phase1_init) {
                    element_clear(states[f].D1);
                    element_clear(states[f].D2);
                    element_clear(states[f].temp_pairing);
                    states[f].phase1_init = false;
                }
                if (states[f].phase4_init) {
                    element_clear(states[f].L_in_GT);
                    states[f].phase4_init = false;
                }
                if (states[f].phase6_init) {
                    element_clear(states[f].wd_exp);
                    element_clear(states[f].gt_wd);
                    element_clear(states[f].l_in_gt_inv);
                    element_clear(states[f].gt_wd_over_l);
                    states[f].phase6_init = false;
                }
                if (states[f].phase7_gt_init) {
                    element_clear(states[f].gt_wd_over_l_in_gt);
                    states[f].phase7_gt_init = false;
                }
                for (int i = 0; i < BATCH_SIZE; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        if (states[f].gt_wd_over_l_in_g1_init[i][j]) {
                            element_clear(states[f].gt_wd_over_l_in_g1[i][j]);
                            states[f].gt_wd_over_l_in_g1_init[i][j] = false;
                        }
                    }
                }
                if (states[f].setup_complete) {
                    ClearDecryptionKey(&states[f].sk);
                    ClearCiphertexts(&states[f].ct);
                    ClearPublicKey(&states[f].pk);
                    ClearMasterSecretKey(&states[f].msk);
                    states[f].setup_complete = false;
                }
                if (states[f].alpha_beta_init) {
                    element_clear(states[f].alpha_sample);
                    element_clear(states[f].beta_sample);
                    states[f].alpha_beta_init = false;
                }
            }
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                element_clear(betad[batch_idx]);
                for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        element_clear(Bstar[batch_idx][i][j]);
                    }
                }
            }
            pairing_clear(pairing);
            return 1;
        }

        long expected_gt_exp_si =
            static_cast<long>(Z1 * (s.w_scaled - (s.output_values >> (QUANTIZATION_BITS - 1))) + s.Z3_feature);
        element_set_si(expected_gt_exp, expected_gt_exp_si);
        element_pow_zn(expected_gt, s.pk.gT_base, expected_gt_exp);

        if (element_cmp(s.gt_wd_over_l_in_gt, expected_gt) != 0) {
            printf("[ASSERTION FAILED] gt_wd_over_l_in_gt mismatch at feature %d\n", feature);
            element_clear(expected_g1_z);
            element_clear(expected_slot_exp);
            element_clear(expected_slot_g1);
            element_clear(expected_gt_exp);
            element_clear(expected_gt);
            for (int f = 0; f < FEATURE_SIZE; f++) {
                if (states[f].phase1_init) {
                    element_clear(states[f].D1);
                    element_clear(states[f].D2);
                    element_clear(states[f].temp_pairing);
                    states[f].phase1_init = false;
                }
                if (states[f].phase4_init) {
                    element_clear(states[f].L_in_GT);
                    states[f].phase4_init = false;
                }
                if (states[f].phase6_init) {
                    element_clear(states[f].wd_exp);
                    element_clear(states[f].gt_wd);
                    element_clear(states[f].l_in_gt_inv);
                    element_clear(states[f].gt_wd_over_l);
                    states[f].phase6_init = false;
                }
                if (states[f].phase7_gt_init) {
                    element_clear(states[f].gt_wd_over_l_in_gt);
                    states[f].phase7_gt_init = false;
                }
                for (int i = 0; i < BATCH_SIZE; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        if (states[f].gt_wd_over_l_in_g1_init[i][j]) {
                            element_clear(states[f].gt_wd_over_l_in_g1[i][j]);
                            states[f].gt_wd_over_l_in_g1_init[i][j] = false;
                        }
                    }
                }
                if (states[f].setup_complete) {
                    ClearDecryptionKey(&states[f].sk);
                    ClearCiphertexts(&states[f].ct);
                    ClearPublicKey(&states[f].pk);
                    ClearMasterSecretKey(&states[f].msk);
                    states[f].setup_complete = false;
                }
                if (states[f].alpha_beta_init) {
                    element_clear(states[f].alpha_sample);
                    element_clear(states[f].beta_sample);
                    states[f].alpha_beta_init = false;
                }
            }
            for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
                element_clear(betad[batch_idx]);
                for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                    for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                        element_clear(Bstar[batch_idx][i][j]);
                    }
                }
            }
            pairing_clear(pairing);
            return 1;
        }

        element_clear(expected_g1_z);
        element_clear(expected_slot_exp);
        element_clear(expected_slot_g1);
        element_clear(expected_gt_exp);
        element_clear(expected_gt);
    }

    // Decrypt phase 9 loop (timed): aggregate C2 across all samples/features.
    element_t C2[BATCH_SIZE][FEATURE_SIZE + 1];
    auto phase9_c2_start = std::chrono::steady_clock::now();
    #pragma omp parallel for collapse(2) schedule(static)
    for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
        for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
            element_init_G1(C2[batch_idx][feature_idx], pairing);
            element_set1(C2[batch_idx][feature_idx]);

            for (int sample = 0; sample < FEATURE_SIZE; sample++) {
                element_mul(C2[batch_idx][feature_idx],
                            C2[batch_idx][feature_idx],
                            states[sample].gt_wd_over_l_in_g1[batch_idx][feature_idx]);
            }

            element_t tail_exp, tail_term;
            element_init_Zr(tail_exp, pairing);
            element_init_G1(tail_term, pairing);
            element_set(tail_exp, Bstar[batch_idx][FEATURE_SIZE][feature_idx]);
            element_pow_zn(tail_term, states[0].pk.g1, tail_exp);
            element_mul(C2[batch_idx][feature_idx],
                        C2[batch_idx][feature_idx],
                        tail_term);
            element_clear(tail_exp);
            element_clear(tail_term);
        }
    }
    auto phase9_c2_stop = std::chrono::steady_clock::now();
    phase9_c2_ms =
        std::chrono::duration<double, std::milli>(phase9_c2_stop - phase9_c2_start).count();

    for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
        for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
            element_clear(C2[batch_idx][feature_idx]);
        }
    }

    // Decrypt phase 10 loop (cleanup per feature).
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        if (s.phase6_init) {
            element_clear(s.wd_exp);
            element_clear(s.gt_wd);
            element_clear(s.l_in_gt_inv);
            element_clear(s.gt_wd_over_l);
            s.phase6_init = false;
        }
        if (s.phase7_gt_init) {
            element_clear(s.gt_wd_over_l_in_gt);
            s.phase7_gt_init = false;
        }
        for (int i = 0; i < BATCH_SIZE; i++) {
            for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                if (s.gt_wd_over_l_in_g1_init[i][j]) {
                    element_clear(s.gt_wd_over_l_in_g1[i][j]);
                    s.gt_wd_over_l_in_g1_init[i][j] = false;
                }
            }
        }
        if (s.phase4_init) {
            element_clear(s.L_in_GT);
            s.phase4_init = false;
        }
        if (s.phase1_init) {
            element_clear(s.D1);
            element_clear(s.D2);
            element_clear(s.temp_pairing);
            s.phase1_init = false;
        }

        if (s.setup_complete) {
            ClearDecryptionKey(&s.sk);
            ClearCiphertexts(&s.ct);
            ClearPublicKey(&s.pk);
            ClearMasterSecretKey(&s.msk);
            s.setup_complete = false;
        }
        if (s.alpha_beta_init) {
            element_clear(s.alpha_sample);
            element_clear(s.beta_sample);
            s.alpha_beta_init = false;
        }
    }

    total_decrypt_ms =
        static_cast<long long>(phase2_ms + phase4_ms + phase6_ms + phase7_ms + phase9_c2_ms);

    double bilinear_total_ms = phase2_ms + phase6_ms;
    double lookup_total_ms = phase4_ms + phase7_ms;

    printf("\n=== Benchmark Summary ===\n");
    printf("KeyGen total: %lld ms\n",
           total_keygen_ms);
    printf("Encrypt total: %lld ms\n",
           total_encrypt_ms);
    printf("Setup total: %.3f ms\n",
            total_setup_ms);
    printf("LUT build total: %.3f ms\n",
            total_lut_build_ms);
    printf("Total bilinear operations time (phase 2 + phase 6): %.3f ms\n", bilinear_total_ms);
    printf("Total lookup time (phase 4 + phase 7): %.3f ms\n", lookup_total_ms);
    printf("Ciphertext generation time (phase 9): %.3f ms\n", phase9_c2_ms);
    printf("Cumulative LUT size: %.6Lf MB\n",
            total_lut_size_bytes / (1024.0L * 1024.0L));

        for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
            element_clear(betad[batch_idx]);
            for (int i = 0; i < FEATURE_SIZE + 1; i++) {
                for (int j = 0; j < FEATURE_SIZE + 1; j++) {
                    element_clear(Bstar[batch_idx][i][j]);
                }
            }
        }

    pairing_clear(pairing);

    return 0;
}