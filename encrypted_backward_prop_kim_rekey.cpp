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
#include <gmp.h>
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

// --- Two-level LUT (garbled-circuit style rekeying) ---
// Many rows of a LUT carry the same payload, so each LUT is split in two:
//  * Value table: one row per distinct payload, one-time-padded under a fresh
//    random key K_v. Rows are stored in a random (permuted) order and the low
//    pointer_bits of K_v give the row's position (point-and-permute), so a
//    lookup decrypts exactly one value-table row. A wrong key must be rejected,
//    since a one-time pad decrypts to something under any key. If the payload is
//    G1 points, each point's sign byte must be 0 or 1, which a wrong key violates
//    with probability 1 - 2^-7 per point, so no extra bytes are stored. Otherwise
//    (GT payload) each row starts with a zero check block.
//  * Key table: a cuckoo table over every x of the LUT's domain, whose row holds
//    K_v for x's payload, plus any part of the row that is specific to x and so
//    cannot be shared. It is one-time-padded under masks derived from the GT
//    value that identifies x.
// Both tables carry only ciphertext: no nonces and no authentication tags.
struct EncryptedLookupRow {
    std::vector<unsigned char> ciphertext;
};

struct EncryptedLookupTable {
    int min_x;
    int max_x;
    int table_id = 0; // domain-separates the OTP KDFs of different LUTs
    // True: value rows start with a CHECK_LEN-byte zero check block. False: value
    // rows are all G1 points, checked by their sign bytes.
    bool value_zero_check = true;
    // Key table, cuckoo hashed by the GT value of x.
    size_t num_entries;
    size_t table_size;
    std::vector<EncryptedLookupRow> slots;
    std::vector<unsigned char> occupied;
    // Value table, indexed by the pointer bits of K_v.
    std::vector<EncryptedLookupRow> value_rows;
    int pointer_bits = 0;
};

// Wall-clock time of each table's build, including its KDF calls.
struct LutBuildTimings {
    double value_table_ms = 0.0;
    double key_table_ms = 0.0;
};

// Time spent in each stage of one lookup. The KDF calls are included in the
// stage they derive masks for; decode_us is the deserialization of the result.
struct LutLookupTimings {
    double key_table_us = 0.0;
    double value_table_us = 0.0;
    double decode_us = 0.0;
};

// Sizes count the stored ciphertext of every row plus the key table's cuckoo
// occupancy bitmap (one bit per slot).
size_t estimate_key_table_size_bytes(const EncryptedLookupTable& lut) {
    size_t total = lut.occupied.capacity() * sizeof(unsigned char) / 8;

    for (const auto& row : lut.slots) {
        total += row.ciphertext.capacity() * sizeof(unsigned char);
    }

    return total;
}

size_t estimate_value_table_size_bytes(const EncryptedLookupTable& lut) {
    size_t total = 0;

    for (const auto& row : lut.value_rows) {
        total += row.ciphertext.capacity() * sizeof(unsigned char);
    }

    return total;
}

size_t estimate_lut_size_bytes(const EncryptedLookupTable& lut) {
    return estimate_key_table_size_bytes(lut) + estimate_value_table_size_bytes(lut);
}

void print_lut_stats(const char* table_name, const EncryptedLookupTable& lut) {
    size_t key_row_bytes = 0;
    for (size_t i = 0; i < lut.slots.size() && i < lut.occupied.size(); i++) {
        if (lut.occupied[i]) {
            key_row_bytes = lut.slots[i].ciphertext.size();
            break;
        }
    }
    size_t value_row_bytes = lut.value_rows.empty() ? 0 : lut.value_rows[0].ciphertext.size();

    printf("%s key table: %zu rows x %zu bytes (%zu cuckoo slots), size %.6f MB\n",
           table_name, lut.num_entries, key_row_bytes, lut.table_size,
           estimate_key_table_size_bytes(lut) / (1024.0 * 1024.0));
    printf("%s value table: %zu rows x %zu bytes (%d pointer bits), size %.6f MB\n",
           table_name, lut.value_rows.size(), value_row_bytes, lut.pointer_bits,
           estimate_value_table_size_bytes(lut) / (1024.0 * 1024.0));
    printf("%s total size: %.6f MB\n", table_name, estimate_lut_size_bytes(lut) / (1024.0 * 1024.0));
}

static const int HKDF_KEY_LEN = 32;
// Length of the per-payload key K_v stored in each key-table row (128 bits).
static const int ROW_KEY_LEN = 16;
// Length of the zero check block that starts each value-table row of a LUT whose
// payload has no redundancy of its own (the GT->GT LUT). A value row decrypted under
// the wrong key passes the check with probability 2^(-8 * CHECK_LEN).
static const int CHECK_LEN = 16;
static const int OTP_PRIME_REPS = 50;
static const int OTP_MAX_RESAMPLES = 64;
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

// --- One-time pad for both tables ---
// A row is a sequence of blocks, each one a serialized group element or key.
// Every block, read as a big-endian integer M < P, is masked as
//     C = a * M + b mod P,   a in [1, P), b in [0, P),
// where P is a prime with the block's bit length (so C fits in the block's own
// size) and (a, b) is a multiplicative/additive mask pair of that same length,
// derived by HKDF from the row's secret with info || block index. No mask pair
// is ever reused. There are three block types:
//  * OTP_G1:  compressed G1 element, x-coordinate (< q) then a sign byte, so
//             M <= 256 * (q - 1) + 1.
//  * OTP_GT:  GT element, two fixed-width Fq coordinates, so
//             M <= (q - 1) * (256^w + 1) for coordinate width w.
//  * OTP_KEY: ROW_KEY_LEN-byte key, M < P.
//  * OTP_CHECK: CHECK_LEN-byte zero check block, M = 0.
enum OtpModulus { OTP_G1 = 0, OTP_GT = 1, OTP_KEY = 2, OTP_CHECK = 3 };
static const int OTP_MODULUS_COUNT = 4;
typedef std::vector<OtpModulus> OtpLayout;

// Public OTP parameters, fixed by the pairing parameters (not per row or LUT).
struct OtpParams {
    size_t len[OTP_MODULUS_COUNT];
    mpz_t P[OTP_MODULUS_COUNT];

    OtpParams() {
        for (int i = 0; i < OTP_MODULUS_COUNT; i++) {
            len[i] = 0;
            mpz_init(P[i]);
        }
    }
    ~OtpParams() {
        for (int i = 0; i < OTP_MODULUS_COUNT; i++) {
            mpz_clear(P[i]);
        }
    }
    OtpParams(const OtpParams&) = delete;
    OtpParams& operator=(const OtpParams&) = delete;
};

static OtpParams g_otp;

size_t otp_layout_bytes(const OtpLayout& layout) {
    size_t total = 0;
    for (OtpModulus m : layout) {
        total += g_otp.len[m];
    }
    return total;
}

// Writes value as a big-endian, zero-padded len-byte string; value must fit.
void mpz_to_fixed_bytes(const mpz_t value, unsigned char* out, size_t len) {
    std::memset(out, 0, len);
    if (mpz_sgn(value) == 0) {
        return;
    }
    size_t value_len = (mpz_sizeinbase(value, 2) + 7) / 8;
    mpz_export(out + (len - value_len), NULL, 1, 1, 1, 0, value);
}

// Sets P for len-byte blocks whose plaintexts are at most max_plaintext: the
// largest prime that fits in len bytes (so masks sampled as len-byte strings
// are almost never resampled), or the smallest prime above max_plaintext if
// that prime is too small.
bool choose_otp_modulus(size_t len, const mpz_t max_plaintext, mpz_t P) {
    mpz_set_ui(P, 0);
    mpz_setbit(P, 8 * len);
    mpz_sub_ui(P, P, 1);
    while (mpz_cmp(P, max_plaintext) > 0 && !mpz_probab_prime_p(P, OTP_PRIME_REPS)) {
        mpz_sub_ui(P, P, 2);
    }
    if (mpz_cmp(P, max_plaintext) <= 0) {
        mpz_nextprime(P, max_plaintext);
    }
    return mpz_sizeinbase(P, 2) <= 8 * len && mpz_probab_prime_p(P, OTP_PRIME_REPS) > 0;
}

bool init_otp_params(pairing_t pairing) {
    element_t g1, gt;
    element_init_G1(g1, pairing);
    element_init_GT(gt, pairing);
    g_otp.len[OTP_G1] = static_cast<size_t>(element_length_in_bytes_compressed(g1));
    g_otp.len[OTP_GT] = static_cast<size_t>(element_length_in_bytes(gt));
    g_otp.len[OTP_KEY] = static_cast<size_t>(ROW_KEY_LEN);
    g_otp.len[OTP_CHECK] = static_cast<size_t>(CHECK_LEN);

    mpz_t q_minus_1, max_plaintext;
    mpz_init(q_minus_1);
    mpz_init(max_plaintext);
    mpz_sub_ui(q_minus_1, element_x(g1)->field->order, 1);

    // GT coordinates are Fq elements, the same width as a G1 x-coordinate.
    const size_t coord_len = g_otp.len[OTP_G1] - 1;
    bool ok = (g_otp.len[OTP_GT] == 2 * coord_len);

    mpz_mul_ui(max_plaintext, q_minus_1, 256);
    mpz_add_ui(max_plaintext, max_plaintext, 1);
    ok = ok && choose_otp_modulus(g_otp.len[OTP_G1], max_plaintext, g_otp.P[OTP_G1]);

    mpz_set_ui(max_plaintext, 0);
    mpz_setbit(max_plaintext, 8 * coord_len);
    mpz_add_ui(max_plaintext, max_plaintext, 1);
    mpz_mul(max_plaintext, max_plaintext, q_minus_1);
    ok = ok && choose_otp_modulus(g_otp.len[OTP_GT], max_plaintext, g_otp.P[OTP_GT]);

    mpz_set_ui(max_plaintext, 0);
    ok = ok && choose_otp_modulus(g_otp.len[OTP_KEY], max_plaintext, g_otp.P[OTP_KEY]);
    ok = ok && choose_otp_modulus(g_otp.len[OTP_CHECK], max_plaintext, g_otp.P[OTP_CHECK]);

    mpz_clear(q_minus_1);
    mpz_clear(max_plaintext);
    element_clear(g1);
    element_clear(gt);
    return ok;
}

// KDF: derives block `block`'s mask pair, each a len-byte string. Candidates
// outside [1, P) for a or [0, P) for b are resampled from a further HKDF output
// (info || block || kind || attempt), keeping every mask uniform.
bool derive_otp_block_masks(const std::vector<unsigned char>& ikm,
                            const std::vector<unsigned char>& salt,
                            const std::vector<unsigned char>& info,
                            const mpz_t P,
                            size_t len,
                            size_t block,
                            mpz_t mult_mask,
                            mpz_t add_mask) {
    std::vector<unsigned char> block_info = info;
    append_u32_be(block_info, static_cast<uint32_t>(block));

    std::vector<unsigned char> pair;
    if (!hkdf_sha256(ikm, salt, block_info, 2 * len, pair)) {
        return false;
    }

    for (int kind = 0; kind < 2; kind++) {
        mpz_ptr mask = (kind == 0) ? mult_mask : add_mask;
        unsigned long min_value = (kind == 0) ? 1 : 0;
        mpz_import(mask, len, 1, 1, 1, 0, pair.data() + kind * len);

        for (int attempt = 0; mpz_cmp_ui(mask, min_value) < 0 || mpz_cmp(mask, P) >= 0; attempt++) {
            if (attempt == OTP_MAX_RESAMPLES) {
                return false;
            }
            std::vector<unsigned char> resample_info = block_info;
            resample_info.push_back(static_cast<unsigned char>(kind));
            append_u32_be(resample_info, static_cast<uint32_t>(attempt));

            std::vector<unsigned char> candidate;
            if (!hkdf_sha256(ikm, salt, resample_info, len, candidate)) {
                return false;
            }
            mpz_import(mask, len, 1, 1, 1, 0, candidate.data());
        }
    }

    return true;
}

// Mask pairs for every block of a row, with the multiplicative part inverted
// for decryption. Used when the same masks are tried against several rows.
struct OtpMasks {
    std::vector<__mpz_struct> mult_inv;
    std::vector<__mpz_struct> add;

    explicit OtpMasks(size_t blocks) : mult_inv(blocks), add(blocks) {
        for (size_t i = 0; i < blocks; i++) {
            mpz_init(&mult_inv[i]);
            mpz_init(&add[i]);
        }
    }
    ~OtpMasks() {
        for (size_t i = 0; i < mult_inv.size(); i++) {
            mpz_clear(&mult_inv[i]);
            mpz_clear(&add[i]);
        }
    }
    OtpMasks(const OtpMasks&) = delete;
    OtpMasks& operator=(const OtpMasks&) = delete;
};

bool derive_otp_masks(const std::vector<unsigned char>& ikm,
                      const std::vector<unsigned char>& salt,
                      const std::vector<unsigned char>& info,
                      const OtpLayout& layout,
                      OtpMasks& masks) {
    for (size_t block = 0; block < layout.size(); block++) {
        OtpModulus m = layout[block];
        if (!derive_otp_block_masks(ikm, salt, info, g_otp.P[m], g_otp.len[m], block,
                                    &masks.mult_inv[block], &masks.add[block]) ||
            mpz_invert(&masks.mult_inv[block], &masks.mult_inv[block], g_otp.P[m]) == 0) {
            return false;
        }
    }
    return true;
}

bool otp_encrypt_layout(const std::vector<unsigned char>& ikm,
                        const std::vector<unsigned char>& salt,
                        const std::vector<unsigned char>& info,
                        const OtpLayout& layout,
                        const std::vector<unsigned char>& plaintext,
                        std::vector<unsigned char>& ciphertext) {
    if (layout.empty() || plaintext.size() != otp_layout_bytes(layout)) {
        return false;
    }

    ciphertext.assign(plaintext.size(), 0);
    bool ok = true;
    mpz_t a, b, value;
    mpz_init(a);
    mpz_init(b);
    mpz_init(value);
    size_t offset = 0;
    for (size_t block = 0; block < layout.size(); block++) {
        OtpModulus m = layout[block];
        size_t len = g_otp.len[m];
        if (!derive_otp_block_masks(ikm, salt, info, g_otp.P[m], len, block, a, b)) {
            ok = false;
            break;
        }
        mpz_import(value, len, 1, 1, 1, 0, plaintext.data() + offset);
        if (mpz_cmp(value, g_otp.P[m]) >= 0) {
            ok = false;
            break;
        }
        mpz_mul(value, value, a);
        mpz_add(value, value, b);
        mpz_mod(value, value, g_otp.P[m]);
        mpz_to_fixed_bytes(value, ciphertext.data() + offset, len);
        offset += len;
    }
    mpz_clear(a);
    mpz_clear(b);
    mpz_clear(value);

    if (!ok) {
        ciphertext.clear();
    }
    return ok;
}

// Decrypts with masks derived up front (see derive_otp_masks).
bool otp_decrypt_with_masks(const OtpMasks& masks,
                            const OtpLayout& layout,
                            const std::vector<unsigned char>& ciphertext,
                            std::vector<unsigned char>& plaintext) {
    if (layout.empty() || ciphertext.size() != otp_layout_bytes(layout)) {
        return false;
    }

    plaintext.assign(ciphertext.size(), 0);
    bool ok = true;
    mpz_t value;
    mpz_init(value);
    size_t offset = 0;
    for (size_t block = 0; block < layout.size(); block++) {
        OtpModulus m = layout[block];
        size_t len = g_otp.len[m];
        mpz_import(value, len, 1, 1, 1, 0, ciphertext.data() + offset);
        if (mpz_cmp(value, g_otp.P[m]) >= 0) {
            ok = false;
            break;
        }
        mpz_sub(value, value, &masks.add[block]);
        mpz_mul(value, value, &masks.mult_inv[block]);
        mpz_mod(value, value, g_otp.P[m]);
        mpz_to_fixed_bytes(value, plaintext.data() + offset, len);
        offset += len;
    }
    mpz_clear(value);

    if (!ok) {
        plaintext.clear();
    }
    return ok;
}

// Decrypts a value-table row and rejects it if it was not encrypted under this
// key. Masks are derived block by block, so a wrong key is rejected after its
// first block (about one block's work) in both modes:
//  * zero_check: the first block is a zero check block (false accept
//    2^(-8 * CHECK_LEN)); it is dropped from the returned payload.
//  * otherwise every block is a compressed G1 element, whose last (sign) byte is
//    0 or 1 (false accept 2^-7 per point, 2^-168 for a 24-point row).
bool otp_decrypt_checked(const std::vector<unsigned char>& ikm,
                         const std::vector<unsigned char>& salt,
                         const std::vector<unsigned char>& info,
                         const OtpLayout& layout,
                         bool zero_check,
                         const std::vector<unsigned char>& ciphertext,
                         std::vector<unsigned char>& payload) {
    if (layout.size() < (zero_check ? 2u : 1u) || ciphertext.size() != otp_layout_bytes(layout)) {
        return false;
    }

    payload.clear();
    payload.reserve(ciphertext.size() - (zero_check ? g_otp.len[layout[0]] : 0));
    bool ok = true;
    mpz_t a, b, value;
    mpz_init(a);
    mpz_init(b);
    mpz_init(value);
    std::vector<unsigned char> block_bytes;
    size_t offset = 0;
    for (size_t block = 0; block < layout.size(); block++) {
        OtpModulus m = layout[block];
        size_t len = g_otp.len[m];
        mpz_import(value, len, 1, 1, 1, 0, ciphertext.data() + offset);
        if (mpz_cmp(value, g_otp.P[m]) >= 0 ||
            !derive_otp_block_masks(ikm, salt, info, g_otp.P[m], len, block, a, b) ||
            mpz_invert(a, a, g_otp.P[m]) == 0) {
            ok = false;
            break;
        }
        mpz_sub(value, value, b);
        mpz_mul(value, value, a);
        mpz_mod(value, value, g_otp.P[m]);
        if (zero_check && block == 0) {
            if (mpz_sgn(value) != 0) {
                ok = false;
                break;
            }
        } else {
            block_bytes.assign(len, 0);
            mpz_to_fixed_bytes(value, block_bytes.data(), len);
            if (!zero_check && block_bytes[len - 1] > 1) {
                ok = false;
                break;
            }
            payload.insert(payload.end(), block_bytes.begin(), block_bytes.end());
        }
        offset += len;
    }
    mpz_clear(a);
    mpz_clear(b);
    mpz_clear(value);

    if (!ok) {
        payload.clear();
    }
    return ok;
}

// Uniform integer in [0, n) from the OpenSSL CSPRNG.
bool random_below(uint32_t n, uint32_t& out) {
    if (n == 0) {
        return false;
    }
    const uint32_t limit = UINT32_MAX - (UINT32_MAX % n);
    for (;;) {
        unsigned char bytes[4];
        if (RAND_bytes(bytes, sizeof(bytes)) != 1) {
            return false;
        }
        uint32_t r = (static_cast<uint32_t>(bytes[0]) << 24) |
                     (static_cast<uint32_t>(bytes[1]) << 16) |
                     (static_cast<uint32_t>(bytes[2]) << 8) |
                     static_cast<uint32_t>(bytes[3]);
        if (r < limit) {
            out = r % n;
            return true;
        }
    }
}

// Samples K_v uniformly from the keys below P whose low pointer_bits equal
// pointer, so the key itself points at its value-table row.
bool sample_row_key(const mpz_t P, size_t key_len, int pointer_bits, uint32_t pointer,
                    std::vector<unsigned char>& key) {
    std::vector<unsigned char> bytes(key_len);
    mpz_t k;
    mpz_init(k);
    bool ok = false;
    for (int attempt = 0; attempt < OTP_MAX_RESAMPLES && !ok; attempt++) {
        if (RAND_bytes(bytes.data(), static_cast<int>(bytes.size())) != 1) {
            break;
        }
        mpz_import(k, key_len, 1, 1, 1, 0, bytes.data());
        mpz_fdiv_q_2exp(k, k, static_cast<mp_bitcnt_t>(pointer_bits));
        mpz_mul_2exp(k, k, static_cast<mp_bitcnt_t>(pointer_bits));
        mpz_add_ui(k, k, pointer);
        if (mpz_cmp(k, P) < 0) {
            key.assign(key_len, 0);
            mpz_to_fixed_bytes(k, key.data(), key_len);
            ok = true;
        }
    }
    mpz_clear(k);
    return ok;
}

// Reads the value-table pointer from the low pointer_bits of a key.
uint32_t row_key_pointer(const std::vector<unsigned char>& key, int pointer_bits) {
    uint32_t pointer = 0;
    for (int bit = 0; bit < pointer_bits; bit++) {
        size_t byte_idx = key.size() - 1 - static_cast<size_t>(bit / 8);
        pointer |= static_cast<uint32_t>((key[byte_idx] >> (bit % 8)) & 1) << bit;
    }
    return pointer;
}

static const std::vector<unsigned char> LUT_SALT = {'G','T','2','G','1','-','L','U','T','-','S','A','L','T'};
// Cuckoo index key, derived from the GT value of x.
static const std::vector<unsigned char> LUT_INDEX_INFO = {'H','K','D','F','-','S','H','A','2','5','6','-','R','O','W'};

// KDF info label for one table of one LUT, e.g. "HKDF-SHA256-KEY" || table_id.
std::vector<unsigned char> lut_otp_info(const char* label, int table_id) {
    std::vector<unsigned char> info(label, label + std::strlen(label));
    info.push_back(static_cast<unsigned char>(table_id));
    return info;
}

OtpLayout lut_key_row_layout(const OtpLayout& key_extra_layout) {
    OtpLayout layout(1, OTP_KEY);
    layout.insert(layout.end(), key_extra_layout.begin(), key_extra_layout.end());
    return layout;
}

// With zero_check, value rows start with a zero check block (see
// otp_decrypt_checked); otherwise a row is just its payload.
OtpLayout lut_value_row_layout(const OtpLayout& payload_layout, bool zero_check) {
    OtpLayout layout;
    if (zero_check) {
        layout.push_back(OTP_CHECK);
    }
    layout.insert(layout.end(), payload_layout.begin(), payload_layout.end());
    return layout;
}

// Builds a two-level LUT over [min_x, max_x].
//  class_of_x[x - min_x]: which of the class_count distinct payloads x maps to.
//  payload_fn(class, payload): the payload (laid out as payload_layout) of a class.
//  key_row_fn(x, gt_bytes, extra): the GT value identifying x, and the part of
//    x's row that is specific to x (laid out as key_extra_layout).
//  value_zero_check: store a zero check block in each value row. When false the
//    payload must be all OTP_G1 blocks, which are checked by their sign bytes.
template <typename PayloadFn, typename KeyRowFn>
EncryptedLookupTable build_two_level_lut(int table_id, int min_x, int max_x,
                                         const std::vector<size_t>& class_of_x, size_t class_count,
                                         const OtpLayout& payload_layout,
                                         const OtpLayout& key_extra_layout,
                                         bool value_zero_check,
                                         PayloadFn payload_fn, KeyRowFn key_row_fn,
                                         LutBuildTimings* timings) {
    EncryptedLookupTable lut;
    lut.min_x = min_x;
    lut.max_x = max_x;
    lut.table_id = table_id;
    lut.value_zero_check = value_zero_check;
    lut.num_entries = 0;
    lut.table_size = 0;

    if (!value_zero_check &&
        (payload_layout.empty() ||
         std::any_of(payload_layout.begin(), payload_layout.end(),
                     [](OtpModulus m) { return m != OTP_G1; }))) {
        printf("A value table without a zero check needs an all-G1 payload.\n");
        return lut;
    }

    const OtpLayout value_layout = lut_value_row_layout(payload_layout, value_zero_check);
    const OtpLayout key_layout = lut_key_row_layout(key_extra_layout);
    const std::vector<unsigned char> value_info = lut_otp_info("HKDF-SHA256-VAL", table_id);
    const std::vector<unsigned char> key_info = lut_otp_info("HKDF-SHA256-KEY", table_id);
    const size_t key_len = g_otp.len[OTP_KEY];

    // ---- Value table: one permuted row per distinct payload ----
    auto value_start = std::chrono::steady_clock::now();

    lut.pointer_bits = 0;
    while ((static_cast<size_t>(1) << lut.pointer_bits) < class_count) {
        lut.pointer_bits++;
    }

    // Random permutation of the value rows; class i is stored at row perm[i].
    std::vector<uint32_t> perm(class_count);
    for (size_t i = 0; i < class_count; i++) {
        perm[i] = static_cast<uint32_t>(i);
    }
    bool value_ok = true;
    for (size_t i = class_count; i > 1 && value_ok; i--) {
        uint32_t j = 0;
        value_ok = random_below(static_cast<uint32_t>(i), j);
        std::swap(perm[i - 1], perm[j]);
    }

    // Fresh key per class; its low pointer_bits point at the class's row.
    std::vector<std::vector<unsigned char>> value_keys(class_count);
    for (size_t i = 0; i < class_count && value_ok; i++) {
        value_ok = sample_row_key(g_otp.P[OTP_KEY], key_len, lut.pointer_bits, perm[i], value_keys[i]);
    }

    lut.value_rows.assign(class_count, EncryptedLookupRow());
    if (value_ok) {
        int value_failures = 0;
#pragma omp parallel for schedule(dynamic) reduction(+:value_failures)
        for (int i = 0; i < static_cast<int>(class_count); i++) {
            std::vector<unsigned char> plaintext(value_zero_check ? g_otp.len[OTP_CHECK] : 0, 0); // zero check block
            std::vector<unsigned char> payload;
            if (!payload_fn(static_cast<size_t>(i), payload) ||
                payload.size() != otp_layout_bytes(payload_layout)) {
                value_failures++;
                continue;
            }
            plaintext.insert(plaintext.end(), payload.begin(), payload.end());
            if (!otp_encrypt_layout(value_keys[static_cast<size_t>(i)], LUT_SALT, value_info, value_layout,
                                    plaintext, lut.value_rows[perm[static_cast<size_t>(i)]].ciphertext)) {
                value_failures++;
            }
        }
        value_ok = (value_failures == 0);
    }

    auto value_stop = std::chrono::steady_clock::now();
    if (timings) {
        timings->value_table_ms = std::chrono::duration<double, std::milli>(value_stop - value_start).count();
    }

    if (!value_ok) {
        printf("Failed to build the value table.\n");
        lut.value_rows.clear();
        return lut;
    }

    // ---- Key table: K_v (plus x's own data) for every x, cuckoo hashed ----
    auto key_start = std::chrono::steady_clock::now();

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
            std::vector<unsigned char> gt_bytes;
            std::vector<unsigned char> extra;
            if (!key_row_fn(x, gt_bytes, extra) ||
                extra.size() != otp_layout_bytes(key_extra_layout)) {
                continue;
            }

            std::vector<unsigned char> plaintext = value_keys[class_of_x[static_cast<size_t>(x - min_x)]];
            plaintext.insert(plaintext.end(), extra.begin(), extra.end());

            std::vector<unsigned char> key;
            if (hkdf_sha256(gt_bytes, LUT_SALT, LUT_INDEX_INFO, HKDF_KEY_LEN, key)) {
                EncryptedLookupRow row;
                if (otp_encrypt_layout(gt_bytes, LUT_SALT, key_info, key_layout, plaintext, row.ciphertext)) {
                    local_entries.push_back({std::move(row), std::move(key)});
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

    bool built = false;
    if (entries.size() == candidate_count) {
        size_t table_size = next_power_of_two(entries.size() * 2);
        for (int rebuild = 0; rebuild < LUT_MAX_REBUILDS; rebuild++) {
            if (build_point_permute_cuckoo(entries, lut, table_size)) {
                built = true;
                break;
            }
            table_size <<= 1;
        }
    }

    if (!built) {
        printf("Failed to build the key table.\n");
        lut.num_entries = 0;
        lut.table_size = 0;
        lut.slots.clear();
        lut.occupied.clear();
    }

    auto key_stop = std::chrono::steady_clock::now();
    if (timings) {
        timings->key_table_ms = std::chrono::duration<double, std::milli>(key_stop - key_start).count();
    }

    return lut;
}

// Looks up the row for the GT value lt_bytes. Tries both cuckoo candidates; a
// candidate is accepted only if the key it yields decrypts its value-table row
// to a valid row (see otp_decrypt_checked). Returns the key row's x-specific part in key_extra
// and the value row's payload in payload.
bool lookup_two_level(const EncryptedLookupTable& lut,
                      const std::vector<unsigned char>& lt_bytes,
                      const OtpLayout& key_extra_layout,
                      const OtpLayout& payload_layout,
                      std::vector<unsigned char>& key_extra,
                      std::vector<unsigned char>& payload,
                      LutLookupTimings* timings) {
    auto key_start = std::chrono::steady_clock::now();

    if (lut.table_size == 0 || lut.slots.empty() || lut.occupied.empty() || lut.value_rows.empty()) {
        return false;
    }

    std::vector<unsigned char> index_key;
    if (!hkdf_sha256(lt_bytes, LUT_SALT, LUT_INDEX_INFO, HKDF_KEY_LEN, index_key)) {
        return false;
    }

    size_t idx1 = lut_hash_idx1(index_key, lut.table_size);
    size_t idx2 = lut_hash_idx2(index_key, lut.table_size);
    unsigned char permute = lut_permute_bit(index_key);
    size_t candidates[2] = {
        permute ? idx2 : idx1,
        permute ? idx1 : idx2
    };

    const OtpLayout value_layout = lut_value_row_layout(payload_layout, lut.value_zero_check);
    const OtpLayout key_layout = lut_key_row_layout(key_extra_layout);
    const std::vector<unsigned char> value_info = lut_otp_info("HKDF-SHA256-VAL", lut.table_id);
    const std::vector<unsigned char> key_info = lut_otp_info("HKDF-SHA256-KEY", lut.table_id);
    const size_t key_len = g_otp.len[OTP_KEY];

    // Both candidate slots are tried with the same key-table masks, so derive
    // them once.
    OtpMasks key_masks(key_layout.size());
    if (!derive_otp_masks(lt_bytes, LUT_SALT, key_info, key_layout, key_masks)) {
        return false;
    }

    double key_table_us =
        std::chrono::duration<double, std::micro>(std::chrono::steady_clock::now() - key_start).count();
    double value_table_us = 0.0;
    bool found = false;

    for (size_t slot_idx : candidates) {
        if (slot_idx >= lut.occupied.size() || !lut.occupied[slot_idx]) {
            continue;
        }

        // Key table: recover the candidate K_v, its row pointer and x's own data.
        auto slot_key_start = std::chrono::steady_clock::now();
        std::vector<unsigned char> key_plain;
        bool key_ok = otp_decrypt_with_masks(key_masks, key_layout, lut.slots[slot_idx].ciphertext, key_plain);
        std::vector<unsigned char> row_key;
        uint32_t pointer = 0;
        if (key_ok) {
            row_key.assign(key_plain.begin(), key_plain.begin() + key_len);
            pointer = row_key_pointer(row_key, lut.pointer_bits);
        }
        key_table_us += std::chrono::duration<double, std::micro>(
            std::chrono::steady_clock::now() - slot_key_start).count();
        if (!key_ok || pointer >= lut.value_rows.size()) {
            continue;
        }

        // Value table: decrypt the row K_v points at.
        auto value_start = std::chrono::steady_clock::now();
        std::vector<unsigned char> candidate_payload;
        bool value_ok = otp_decrypt_checked(row_key, LUT_SALT, value_info, value_layout, lut.value_zero_check,
                                            lut.value_rows[pointer].ciphertext, candidate_payload) &&
                        candidate_payload.size() == otp_layout_bytes(payload_layout);
        value_table_us += std::chrono::duration<double, std::micro>(
            std::chrono::steady_clock::now() - value_start).count();

        if (value_ok) {
            payload = std::move(candidate_payload);
            key_extra.assign(key_plain.begin() + key_len, key_plain.end());
            found = true;
            break;
        }
    }

    if (timings) {
        timings->key_table_us = key_table_us;
        timings->value_table_us = value_table_us;
    }
    return found;
}

// Sorted distinct values of v, and each element's index into them.
void classify_values(const std::vector<int>& values, std::vector<int>& classes,
                     std::vector<size_t>& class_of) {
    classes = values;
    std::sort(classes.begin(), classes.end());
    classes.erase(std::unique(classes.begin(), classes.end()), classes.end());
    class_of.resize(values.size());
    for (size_t i = 0; i < values.size(); i++) {
        class_of[i] = static_cast<size_t>(std::lower_bound(classes.begin(), classes.end(), values[i]) - classes.begin());
    }
}

// GT->GT LUT. The row for x holds g_T^(z1 * (x >> (QUANTIZATION_BITS-1)) + z3mz4),
// which depends only on x >> (QUANTIZATION_BITS-1), so the value table has one row
// per distinct shifted value and the key table holds only K_v.
EncryptedLookupTable BuildEncryptedLookupTable(pairing_t pairing, PublicKey* pk, int min_x, int max_x, int z3mz4, int z1, element_t alpha, element_t beta, element_t det_B, LutBuildTimings* timings = nullptr) {
    std::vector<int> payload_exp_of_x;
    payload_exp_of_x.reserve(static_cast<size_t>(max_x - min_x + 1));
    for (int x = min_x; x <= max_x; x++) {
        payload_exp_of_x.push_back(z1 * (x >> (QUANTIZATION_BITS - 1)) + z3mz4);
    }
    std::vector<int> classes;
    std::vector<size_t> class_of_x;
    classify_values(payload_exp_of_x, classes, class_of_x);

    auto payload_fn = [&](size_t cls, std::vector<unsigned char>& payload) {
        element_t exp1, gt_mapped_val;
        element_init_Zr(exp1, pairing);
        element_init_GT(gt_mapped_val, pairing);
        element_set_si(exp1, classes[cls]);
        element_pow_zn(gt_mapped_val, pk->gT_base, exp1);
        payload = serialize_element_to_bytes(gt_mapped_val);
        element_clear(exp1);
        element_clear(gt_mapped_val);
        return true;
    };

    auto key_row_fn = [&](int x, std::vector<unsigned char>& gt_bytes, std::vector<unsigned char>& extra) {
        element_t expt, gt_val;
        element_init_Zr(expt, pairing);
        element_init_GT(gt_val, pairing);
        element_set_si(expt, z1 * x + z3mz4);
        element_mul(expt, expt, alpha);
        element_mul(expt, expt, beta);
        element_mul(expt, expt, det_B);
        element_pow_zn(gt_val, pk->gT_base, expt);
        gt_bytes = serialize_element_to_bytes(gt_val);
        extra.clear();
        element_clear(expt);
        element_clear(gt_val);
        return true;
    };

    return build_two_level_lut(0, min_x, max_x, class_of_x, classes.size(),
                               OtpLayout(1, OTP_GT), OtpLayout(),
                               /*value_zero_check=*/true,
                               payload_fn, key_row_fn, timings);
}

// GT->G1 LUT. The row for x holds BATCH_SIZE * (FEATURE_SIZE + 1) G1 points that
// depend only on z = r2 * trunc(x * LR / BATCH_SIZE) + r1, and g_T^(Z1 * x + Z3),
// which is different for every x. The G1 points go in the value table, one row per
// distinct z; the key table row holds K_v and the per-x GT element.
EncryptedLookupTable BuildEncryptedLookupTableGTtoG1(pairing_t pairing, PublicKey* pk, int min_x, int max_x, int z1, int z4, int r2, int r1, int Z1, int Z3, element_t betad[BATCH_SIZE], element_t Bstar[BATCH_SIZE][FEATURE_SIZE + 1][FEATURE_SIZE + 1], int idx, LutBuildTimings* timings = nullptr) {
    std::vector<int> z_of_x;
    z_of_x.reserve(static_cast<size_t>(max_x - min_x + 1));
    for (int x = min_x; x <= max_x; x++) {
        z_of_x.push_back(r2 * (int)((long double)x * (long double)LR / (long double)BATCH_SIZE) + r1);
    }
    std::vector<int> classes;
    std::vector<size_t> class_of_x;
    classify_values(z_of_x, classes, class_of_x);

    auto payload_fn = [&](size_t cls, std::vector<unsigned char>& payload) {
        element_t z_scalar, slot_exp, slot_g1;
        element_init_Zr(z_scalar, pairing);
        element_init_Zr(slot_exp, pairing);
        element_init_G1(slot_g1, pairing);
        element_set_si(z_scalar, classes[cls]);

        payload.clear();
        for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
            for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
                element_mul(slot_exp, betad[batch_idx], Bstar[batch_idx][idx][feature_idx]);
                element_mul(slot_exp, slot_exp, z_scalar);
                element_pow_zn(slot_g1, pk->g1_base, slot_exp);

                std::vector<unsigned char> slot_bytes = serialize_g1_element_to_compressed_bytes(slot_g1);
                payload.insert(payload.end(), slot_bytes.begin(), slot_bytes.end());
            }
        }

        element_clear(z_scalar);
        element_clear(slot_exp);
        element_clear(slot_g1);
        return true;
    };

    auto key_row_fn = [&](int x, std::vector<unsigned char>& gt_bytes, std::vector<unsigned char>& extra) {
        element_t expt, gt_val, target_expt, target_gt_val;
        element_init_Zr(expt, pairing);
        element_init_GT(gt_val, pairing);
        element_init_Zr(target_expt, pairing);
        element_init_GT(target_gt_val, pairing);
        element_set_si(expt, z1 * x + z4);
        element_set_si(target_expt, Z1 * x + Z3);
        element_pow_zn(gt_val, pk->gT_base, expt);
        element_pow_zn(target_gt_val, pk->gT_base, target_expt);
        gt_bytes = serialize_element_to_bytes(gt_val);
        extra = serialize_element_to_bytes(target_gt_val);
        element_clear(expt);
        element_clear(gt_val);
        element_clear(target_expt);
        element_clear(target_gt_val);
        return true;
    };

    return build_two_level_lut(1, min_x, max_x, class_of_x, classes.size(),
                               OtpLayout(static_cast<size_t>(BATCH_SIZE) * (FEATURE_SIZE + 1), OTP_G1),
                               OtpLayout(1, OTP_GT),
                               /*value_zero_check=*/false,
                               payload_fn, key_row_fn, timings);
}

bool MapLTinGTtoGTWithEncryptedLUT(pairing_t pairing,
                                   element_t L_T,
                                   const EncryptedLookupTable& lut,
                                   element_t L_in_GT,
                                   bool verbose = true,
                                   LutLookupTimings* timings = nullptr) {
    auto start = std::chrono::steady_clock::now();
    static const OtpLayout no_extra;
    static const OtpLayout payload_layout(1, OTP_GT);

    std::vector<unsigned char> lt_bytes = serialize_element_to_bytes(L_T);
    std::vector<unsigned char> key_extra, payload;
    LutLookupTimings local;
    bool found = lookup_two_level(lut, lt_bytes, no_extra, payload_layout, key_extra, payload, &local);
    if (found) {
        auto decode_start = std::chrono::steady_clock::now();
        element_init_GT(L_in_GT, pairing);
        element_from_bytes(L_in_GT, payload.data());
        local.decode_us = std::chrono::duration<double, std::micro>(
            std::chrono::steady_clock::now() - decode_start).count();
    }
    if (timings) {
        *timings = local;
    }

    auto stop = std::chrono::steady_clock::now();
    auto duration_us = std::chrono::duration<double, std::micro>(stop - start);
#ifdef _OPENMP
    #pragma omp atomic update
#endif
    total_lookup_us += duration_us.count();
    if (verbose) {
        printf("Lookup completed with %s in %.3f us\n", found ? "success" : "failure", duration_us.count());
    }
    return found;
}

bool MapLTinGTtoG1WithEncryptedLUT(pairing_t pairing,
                                   element_t L_T,
                                   const EncryptedLookupTable& lut,
                                   element_t L_in_G1[BATCH_SIZE][FEATURE_SIZE + 1],
                                   element_t L_in_GT,
                                   bool verbose = true,
                                   LutLookupTimings* timings = nullptr) {
    auto start = std::chrono::steady_clock::now();
    static const OtpLayout key_extra_layout(1, OTP_GT);
    static const OtpLayout payload_layout(static_cast<size_t>(BATCH_SIZE) * (FEATURE_SIZE + 1), OTP_G1);

    std::vector<unsigned char> lt_bytes = serialize_element_to_bytes(L_T);
    std::vector<unsigned char> key_extra, payload;
    LutLookupTimings local;
    bool found = lookup_two_level(lut, lt_bytes, key_extra_layout, payload_layout, key_extra, payload, &local);
    if (found) {
        auto decode_start = std::chrono::steady_clock::now();
        const size_t g1_len = g_otp.len[OTP_G1];
        size_t offset = 0;
        for (int batch_idx = 0; batch_idx < BATCH_SIZE; batch_idx++) {
            for (int feature_idx = 0; feature_idx < FEATURE_SIZE + 1; feature_idx++) {
                element_init_G1(L_in_G1[batch_idx][feature_idx], pairing);
                element_from_bytes_compressed(
                    L_in_G1[batch_idx][feature_idx],
                    const_cast<unsigned char*>(payload.data() + offset));
                offset += g1_len;
            }
        }
        element_init_GT(L_in_GT, pairing);
        element_from_bytes(L_in_GT, key_extra.data());
        local.decode_us = std::chrono::duration<double, std::micro>(
            std::chrono::steady_clock::now() - decode_start).count();
    }
    if (timings) {
        *timings = local;
    }

    auto stop = std::chrono::steady_clock::now();
    auto duration_us = std::chrono::duration<double, std::micro>(stop - start);
#ifdef _OPENMP
    #pragma omp atomic update
#endif
    total_lookup_us += duration_us.count();
    if (verbose) {
        printf("GT->G1 lookup completed with %s in %.3f us\n", found ? "success" : "failure", duration_us.count());
    }
    return found;
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

    // Public OTP moduli, fixed by the pairing parameters (timed separately: not
    // part of any one LUT's build).
    auto otp_setup_start = std::chrono::steady_clock::now();
    if (!init_otp_params(pairing)) {
        printf("Failed to choose the OTP moduli.\n");
        pairing_clear(pairing);
        return 1;
    }
    double otp_param_setup_ms =
        std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - otp_setup_start).count();

    PublicKey pk;
    MasterSecretKey msk;
    DecryptionKey sk;
    Ciphertext ct;

    double total_setup_ms = 0.0;
    double total_lut_build_ms = 0.0;
    // Per-LUT, per-table build time (index 0: GT->GT LUT, 1: GT->G1 LUT).
    double total_value_table_build_ms[2] = {0.0, 0.0};
    double total_key_table_build_ms[2] = {0.0, 0.0};
    long double total_lut_size_bytes = 0.0L;
    long double total_key_table_size_bytes[2] = {0.0L, 0.0L};
    long double total_value_table_size_bytes[2] = {0.0L, 0.0L};
    long long total_keygen_us = 0;
    long long total_encrypt_us = 0;

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
        total_keygen_us += std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();

        start = std::chrono::steady_clock::now();
        Encrypt(pairing, &s.pk, &s.msk, x_vec, &s.ct, s.beta_sample);
        stop = std::chrono::steady_clock::now();
        total_encrypt_us += std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();

        start = std::chrono::steady_clock::now();
        // Each build covers both tables of the LUT (value table and key table)
        // with all of their KDF calls.
        LutBuildTimings gt_to_gt_timings;
        s.lut = BuildEncryptedLookupTable(pairing, &s.pk, (BATCH_SIZE) * (MIN_X) * (MAX_X), BATCH_SIZE * (MIN_X) * (MIN_X), z3 - z4, z1, s.alpha_sample, s.beta_sample, s.msk.det_B, &gt_to_gt_timings);
        stop = std::chrono::steady_clock::now();
        total_lut_build_ms += std::chrono::duration<double, std::milli>(stop - start).count();
        total_value_table_build_ms[0] += gt_to_gt_timings.value_table_ms;
        total_key_table_build_ms[0] += gt_to_gt_timings.key_table_ms;
        total_key_table_size_bytes[0] += static_cast<long double>(estimate_key_table_size_bytes(s.lut));
        total_value_table_size_bytes[0] += static_cast<long double>(estimate_value_table_size_bytes(s.lut));
        total_lut_size_bytes += static_cast<long double>(estimate_lut_size_bytes(s.lut));

        start = std::chrono::steady_clock::now();
        LutBuildTimings gt_to_g1_timings;
        s.lut_gt_to_g1 = BuildEncryptedLookupTableGTtoG1(pairing, &s.pk, ((BATCH_SIZE) / (LR) + (BATCH_SIZE)) * (MIN_X), ((BATCH_SIZE) / (LR) + (BATCH_SIZE)) * (MAX_X), z1, z4, r2, s.r1_feature, Z1, s.Z3_feature, betad, Bstar, feature, &gt_to_g1_timings);
        stop = std::chrono::steady_clock::now();
        total_lut_build_ms += std::chrono::duration<double, std::milli>(stop - start).count();
        total_value_table_build_ms[1] += gt_to_g1_timings.value_table_ms;
        total_key_table_build_ms[1] += gt_to_g1_timings.key_table_ms;
        total_key_table_size_bytes[1] += static_cast<long double>(estimate_key_table_size_bytes(s.lut_gt_to_g1));
        total_value_table_size_bytes[1] += static_cast<long double>(estimate_value_table_size_bytes(s.lut_gt_to_g1));
        total_lut_size_bytes += static_cast<long double>(estimate_lut_size_bytes(s.lut_gt_to_g1));

        if (feature == 0) {
            printf("\n=== LUT Stats feature 0 ===\n");
            print_lut_stats("GT->GT LUT", s.lut);
            printf("GT->GT LUT build time: value table %.3f ms, key table %.3f ms\n",
                   gt_to_gt_timings.value_table_ms, gt_to_gt_timings.key_table_ms);
            print_lut_stats("GT->G1 LUT", s.lut_gt_to_g1);
            printf("GT->G1 LUT build time: value table %.3f ms, key table %.3f ms\n",
                   gt_to_g1_timings.value_table_ms, gt_to_g1_timings.key_table_ms);
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
    std::vector<LutLookupTimings> phase4_timings(static_cast<size_t>(FEATURE_SIZE));
    #pragma omp parallel for schedule(static)
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        if (!MapLTinGTtoGTWithEncryptedLUT(pairing, s.D2, s.lut, s.L_in_GT, false,
                                           &phase4_timings[static_cast<size_t>(feature)])) {
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
    std::vector<LutLookupTimings> phase7_timings(static_cast<size_t>(FEATURE_SIZE));
    #pragma omp parallel for schedule(static)
    for (int feature = 0; feature < FEATURE_SIZE; feature++) {
        FeaturePhaseState& s = states[feature];
        if (!MapLTinGTtoG1WithEncryptedLUT(pairing, s.gt_wd_over_l, s.lut_gt_to_g1,
                                           s.gt_wd_over_l_in_g1, s.gt_wd_over_l_in_gt, false,
                                           &phase7_timings[static_cast<size_t>(feature)])) {
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
        printf("KeyGen total: %lld us, average: %.3f us\n",
            total_keygen_us,
            static_cast<double>(total_keygen_us) / FEATURE_SIZE);
        printf("Encrypt total: %lld us, average: %.3f us\n",
            total_encrypt_us,
            static_cast<double>(total_encrypt_us) / FEATURE_SIZE);
    printf("Setup total: %.3f ms\n",
            total_setup_ms);
    printf("OTP parameter setup: %.3f ms\n", otp_param_setup_ms);
    printf("LUT build total: %.3f ms\n",
            total_lut_build_ms);
    const char* lut_names[2] = {"GT->GT", "GT->G1"};
    for (int t = 0; t < 2; t++) {
        printf("%s LUT build total: value table %.3f ms, key table %.3f ms\n",
                lut_names[t], total_value_table_build_ms[t], total_key_table_build_ms[t]);
    }
    printf("Total bilinear operations time (phase 2 + phase 6): %.3f ms\n", bilinear_total_ms);
    printf("Total lookup time (phase 4 + phase 7): %.3f ms\n", lookup_total_ms);
    // Per-stage lookup time, summed over features (the loops run features in
    // parallel, so these sums can exceed the wall-clock phase times above).
    const std::vector<LutLookupTimings>* lookup_phase_timings[2] = {&phase4_timings, &phase7_timings};
    for (int t = 0; t < 2; t++) {
        double key_us = 0.0, value_us = 0.0, decode_us = 0.0;
        for (const auto& lt : *lookup_phase_timings[t]) {
            key_us += lt.key_table_us;
            value_us += lt.value_table_us;
            decode_us += lt.decode_us;
        }
        printf("%s lookup stages (summed over features): key table %.3f us, value table %.3f us, decode %.3f us\n",
                lut_names[t], key_us, value_us, decode_us);
    }
    printf("Ciphertext generation time (phase 9): %.3f ms\n", phase9_c2_ms);
    for (int t = 0; t < 2; t++) {
        printf("%s LUT cumulative size: key table %.6Lf MB, value table %.6Lf MB\n",
                lut_names[t],
                total_key_table_size_bytes[t] / (1024.0L * 1024.0L),
                total_value_table_size_bytes[t] / (1024.0L * 1024.0L));
    }
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