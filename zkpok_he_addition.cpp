// ZKPoK + Homomorphic Encryption benchmark pipeline.
//
// Part 1: Pedersen-committed vector addition a + r, proved correct under a
//         batched Schnorr-style ZKPoK (elliptic curve P-256, via OpenSSL).
// Part 2: Paillier-encrypt b, then homomorphically evaluate <ct_b, -r> + R
//         (r reused from Part 1), with a ZKPoK that the same r is opened
//         from its Pedersen commitment and that R is correctly opened both
//         as a Pedersen commitment and as the Paillier ciphertext used in
//         the evaluation.
// Part 3: d independent Paillier instances each homomorphically evaluating
//         x[i]*c[i] + y[i], with no ZKPoK (not requested for this part).
//
// Design note on the Part 2 ZKPoK: the proof is a Fiat-Shamir AND-composition
// of (a) a batched Okamoto opening proof in the EC group for r and R, and
// (b) a Paillier-side proof of knowledge of the opening of ct_R. Both share
// one Fiat-Shamir transcript, so the whole thing is a single non-interactive
// proof object. It does NOT cryptographically bind that the very exponent
// used inside ct_b[i]^(-r_i) equals the EC-committed r_i -- a full
// cross-group equality proof (Damgard-Fujisaki style, over integer
// commitments) would be needed for that, and is out of scope here.
//
// Libraries: OpenSSL (EC_POINT/BIGNUM for Pedersen commitments and Fiat-Shamir
// hashing, already a project dependency) and GMP (arbitrary-precision
// arithmetic for a hand-rolled, CRT-optimized Paillier cryptosystem, also
// already a project dependency). OpenMP parallelizes every per-index loop
// (commitment generation, weighted-sum proof verification, HE encryption/
// evaluation, and the d independent Part 3 pipelines).

#include <gmp.h>
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/obj_mac.h>
#include <openssl/rand.h>
#include <openssl/sha.h>

#ifdef _OPENMP
#include <omp.h>
#endif

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <random>
#include <string>
#include <vector>

#define DEFAULT_DIM 8
#define VALUE_BITS 6
#define R_BITS 20
#define PAILLIER_MODULUS_BITS 2048
#define ZK_STAT_SEC_BITS 128

using Clock = std::chrono::steady_clock;

static double ms(Clock::time_point a, Clock::time_point b) {
    return std::chrono::duration<double, std::milli>(b - a).count();
}

// ============================ RAII wrappers ============================

struct BNDeleter {
    void operator()(BIGNUM* p) const { BN_free(p); }
};
using BNPtr = std::unique_ptr<BIGNUM, BNDeleter>;

struct ECPointDeleter {
    void operator()(EC_POINT* p) const { EC_POINT_free(p); }
};
using ECPointPtr = std::unique_ptr<EC_POINT, ECPointDeleter>;

class BigInt {
public:
    mpz_t v;
    BigInt() { mpz_init(v); }
    ~BigInt() { mpz_clear(v); }
    BigInt(const BigInt&) = delete;
    BigInt& operator=(const BigInt&) = delete;
    BigInt(BigInt&& o) noexcept {
        mpz_init(v);
        mpz_swap(v, o.v);
    }
    BigInt& operator=(BigInt&& o) noexcept {
        mpz_swap(v, o.v);
        return *this;
    }
};

// ============================ Thread-local BN_CTX pool ============================

static std::vector<BN_CTX*> g_bn_ctx_pool;

static int CurrentThreadId() {
#ifdef _OPENMP
    return omp_get_thread_num();
#else
    return 0;
#endif
}

static int MaxThreads() {
#ifdef _OPENMP
    return omp_get_max_threads();
#else
    return 1;
#endif
}

// ============================ Byte-buffer helpers ============================

static void append_u32_be(std::vector<unsigned char>& buf, uint32_t value) {
    buf.push_back((value >> 24) & 0xFF);
    buf.push_back((value >> 16) & 0xFF);
    buf.push_back((value >> 8) & 0xFF);
    buf.push_back(value & 0xFF);
}

static void append_u64_be(std::vector<unsigned char>& buf, uint64_t value) {
    for (int i = 7; i >= 0; i--) {
        buf.push_back(static_cast<unsigned char>((value >> (i * 8)) & 0xFF));
    }
}

static void append_i64_be(std::vector<unsigned char>& buf, long value) {
    append_u64_be(buf, static_cast<uint64_t>(value));
}

static void AppendMpz(std::vector<unsigned char>& buf, const mpz_t v) {
    mpz_t abs_v;
    mpz_init(abs_v);
    mpz_abs(abs_v, v);
    size_t bytes = (mpz_sizeinbase(abs_v, 2) + 7) / 8;
    std::vector<unsigned char> out(bytes);
    size_t written = 0;
    mpz_export(out.data(), &written, 1, 1, 1, 0, abs_v);
    mpz_clear(abs_v);
    buf.push_back(mpz_sgn(v) < 0 ? 1 : 0);
    append_u32_be(buf, static_cast<uint32_t>(written));
    buf.insert(buf.end(), out.begin(), out.begin() + written);
}

// ============================ Random dummy-value sampling ============================

static long RandomSigned(int bits) {
    thread_local std::mt19937_64 gen(std::random_device{}());
    long half = 1L << (bits - 1);
    std::uniform_int_distribution<long> dist(-half, half - 1);
    return dist(gen);
}

static long RandomUnsigned(int bits) {
    thread_local std::mt19937_64 gen(std::random_device{}());
    std::uniform_int_distribution<long> dist(0, (1L << bits) - 1);
    return dist(gen);
}

// ============================ EC / Pedersen commitment layer ============================

struct ECParams {
    EC_GROUP* group;
    ECPointPtr H;
    BNPtr order;
    size_t point_bytes;
    size_t scalar_bytes;
};

static BIGNUM* LongToBN(long v) {
    char buf[32];
    snprintf(buf, sizeof(buf), "%ld", v);
    BIGNUM* bn = nullptr;
    BN_dec2bn(&bn, buf);
    return bn;
}

static void AppendPoint(const ECParams& ec, std::vector<unsigned char>& buf, const EC_POINT* p, BN_CTX* ctx) {
    std::vector<unsigned char> enc(ec.point_bytes);
    size_t written = EC_POINT_point2oct(ec.group, p, POINT_CONVERSION_COMPRESSED, enc.data(), enc.size(), ctx);
    buf.insert(buf.end(), enc.begin(), enc.begin() + written);
}

// Nothing-up-my-sleeve second generator H, derived by hashing a domain tag
// with an incrementing counter and treating the digest as a compressed
// point's x-coordinate (try-and-increment hash-to-curve).
static ECPointPtr DeriveGeneratorH(const EC_GROUP* group, BN_CTX* ctx) {
    ECPointPtr H(EC_POINT_new(group));
    const char* seed = "ZKPoK-HE-PEDERSEN-H-GENERATOR";
    uint32_t counter = 0;
    while (true) {
        std::vector<unsigned char> input(seed, seed + strlen(seed));
        append_u32_be(input, counter);
        unsigned char digest[SHA256_DIGEST_LENGTH];
        SHA256(input.data(), input.size(), digest);

        std::vector<unsigned char> candidate;
        candidate.push_back(0x02);
        candidate.insert(candidate.end(), digest, digest + SHA256_DIGEST_LENGTH);
        if (EC_POINT_oct2point(group, H.get(), candidate.data(), candidate.size(), ctx) == 1) {
            break;
        }
        counter++;
    }
    return H;
}

static ECParams SetupECParams() {
    ECParams ec;
    ec.group = EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1);
    ec.order.reset(BN_new());
    EC_GROUP_get_order(ec.group, ec.order.get(), g_bn_ctx_pool[0]);
    ec.H = DeriveGeneratorH(ec.group, g_bn_ctx_pool[0]);
    ec.point_bytes = EC_POINT_point2oct(ec.group, EC_GROUP_get0_generator(ec.group),
                                         POINT_CONVERSION_COMPRESSED, nullptr, 0, g_bn_ctx_pool[0]);
    ec.scalar_bytes = static_cast<size_t>((BN_num_bits(ec.order.get()) + 7) / 8);
    return ec;
}

static BNPtr RandomScalar(const ECParams& ec) {
    BNPtr r(BN_new());
    BN_rand_range(r.get(), ec.order.get());
    return r;
}

// C = value*G + rho*H
static ECPointPtr PedersenCommit(const ECParams& ec, BN_CTX* ctx, long value, const BIGNUM* rho) {
    ECPointPtr C(EC_POINT_new(ec.group));
    BNPtr value_bn(LongToBN(value));
    EC_POINT_mul(ec.group, C.get(), value_bn.get(), ec.H.get(), rho, ctx);
    return C;
}

// ============================ Fiat-Shamir helpers ============================

static BNPtr HashToScalarMod(const ECParams& ec, const std::vector<unsigned char>& transcript, const char* domain) {
    std::vector<unsigned char> input(transcript);
    input.insert(input.end(), domain, domain + strlen(domain));
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256(input.data(), input.size(), digest);
    BNPtr h(BN_new());
    BN_bin2bn(digest, SHA256_DIGEST_LENGTH, h.get());
    BNPtr result(BN_new());
    BN_mod(result.get(), h.get(), ec.order.get(), g_bn_ctx_pool[CurrentThreadId()]);
    return result;
}

// Public, per-index batching weight used to fold d Sigma-protocol instances
// into one (soundness holds since the verifier derives the same weights from
// public data only, after the commitments are already fixed).
static BNPtr DeriveGamma(const ECParams& ec, const std::vector<unsigned char>& seed, size_t index) {
    std::vector<unsigned char> input(seed);
    append_u64_be(input, static_cast<uint64_t>(index));
    return HashToScalarMod(ec, input, "GAMMA");
}

static BigInt DeriveChallengeSEC(const std::vector<unsigned char>& input, int sec_bits) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256(input.data(), input.size(), digest);
    BigInt e;
    size_t bytes_needed = static_cast<size_t>((sec_bits + 7) / 8);
    mpz_import(e.v, bytes_needed, 1, 1, 1, 0, digest);
    return e;
}

// Parallel weighted sum: P = sum_i gamma_i(transcript, i) * points[i].
static ECPointPtr WeightedSum(const ECParams& ec, const std::vector<unsigned char>& transcript,
                               const std::vector<const EC_POINT*>& points) {
    size_t n = points.size();
    int nthreads = MaxThreads();
    std::vector<ECPointPtr> partials;
    for (int t = 0; t < nthreads; t++) {
        partials.emplace_back(EC_POINT_new(ec.group));
        EC_POINT_set_to_infinity(ec.group, partials.back().get());
    }

#pragma omp parallel
    {
        int tid = CurrentThreadId();
        BN_CTX* lctx = g_bn_ctx_pool[tid];
        EC_POINT* local_partial = partials[tid].get();
        ECPointPtr scaled(EC_POINT_new(ec.group));

#pragma omp for schedule(static)
        for (long i = 0; i < static_cast<long>(n); i++) {
            BNPtr gamma = DeriveGamma(ec, transcript, static_cast<size_t>(i));
            EC_POINT_mul(ec.group, scaled.get(), nullptr, points[static_cast<size_t>(i)], gamma.get(), lctx);
            EC_POINT_add(ec.group, local_partial, local_partial, scaled.get(), lctx);
        }
    }

    ECPointPtr total(EC_POINT_new(ec.group));
    EC_POINT_set_to_infinity(ec.group, total.get());
    for (int t = 0; t < nthreads; t++) {
        EC_POINT_add(ec.group, total.get(), total.get(), partials[t].get(), g_bn_ctx_pool[0]);
    }
    return total;
}

// D_i = C_a[i] + C_r[i] - s[i]*G, built in parallel.
static std::vector<ECPointPtr> BuildDVector(const ECParams& ec, const std::vector<ECPointPtr>& Ca,
                                             const std::vector<ECPointPtr>& Cr, const std::vector<long>& s) {
    size_t d = Ca.size();
    std::vector<ECPointPtr> D(d);
    for (auto& dp : D) dp.reset(EC_POINT_new(ec.group));

#pragma omp parallel for schedule(static)
    for (long i = 0; i < static_cast<long>(d); i++) {
        BN_CTX* lctx = g_bn_ctx_pool[CurrentThreadId()];
        BNPtr neg_s(LongToBN(-s[static_cast<size_t>(i)]));
        ECPointPtr sG(EC_POINT_new(ec.group));
        EC_POINT_mul(ec.group, sG.get(), neg_s.get(), nullptr, nullptr, lctx);
        EC_POINT_add(ec.group, D[static_cast<size_t>(i)].get(), Ca[static_cast<size_t>(i)].get(),
                     Cr[static_cast<size_t>(i)].get(), lctx);
        EC_POINT_add(ec.group, D[static_cast<size_t>(i)].get(), D[static_cast<size_t>(i)].get(), sG.get(), lctx);
    }
    return D;
}

static std::vector<const EC_POINT*> RawPoints(const std::vector<ECPointPtr>& v) {
    std::vector<const EC_POINT*> out;
    out.reserve(v.size());
    for (auto& p : v) out.push_back(p.get());
    return out;
}

// ============================ Part 1: batched Schnorr proof that a+r=s ============================

struct SchnorrProof {
    ECPointPtr T;
    BNPtr z;
};

static std::vector<unsigned char> BuildTranscriptSum(const ECParams& ec, BN_CTX* ctx,
                                                       const std::vector<ECPointPtr>& Ca,
                                                       const std::vector<ECPointPtr>& Cr,
                                                       const std::vector<long>& s) {
    std::vector<unsigned char> t = {'S', 'U', 'M'};
    for (size_t i = 0; i < Ca.size(); i++) {
        AppendPoint(ec, t, Ca[i].get(), ctx);
        AppendPoint(ec, t, Cr[i].get(), ctx);
        append_i64_be(t, s[i]);
    }
    return t;
}

// Proves knowledge of {a_i, rho_a_i, r_i, rho_r_i} such that C_a[i], C_r[i]
// open to a_i, r_i respectively and a_i + r_i = s[i] for every i, without
// revealing a_i or r_i. Batched into one Schnorr proof over the base H via
// a Fiat-Shamir random linear combination across the d instances.
static SchnorrProof ProveVectorSum(const ECParams& ec, BN_CTX* ctx, const std::vector<long>& s,
                                    const std::vector<BNPtr>& rhoA, const std::vector<BNPtr>& rhoR,
                                    const std::vector<unsigned char>& transcript) {
    size_t d = s.size();
    int nthreads = MaxThreads();
    std::vector<BNPtr> partials;
    for (int t = 0; t < nthreads; t++) {
        partials.emplace_back(BN_new());
        BN_zero(partials.back().get());
    }

#pragma omp parallel for schedule(static)
    for (long i = 0; i < static_cast<long>(d); i++) {
        int tid = CurrentThreadId();
        BN_CTX* lctx = g_bn_ctx_pool[tid];
        BNPtr gamma = DeriveGamma(ec, transcript, static_cast<size_t>(i));
        BNPtr sum_rho(BN_new());
        BN_mod_add(sum_rho.get(), rhoA[static_cast<size_t>(i)].get(), rhoR[static_cast<size_t>(i)].get(),
                   ec.order.get(), lctx);
        BNPtr weighted(BN_new());
        BN_mod_mul(weighted.get(), gamma.get(), sum_rho.get(), ec.order.get(), lctx);
        BN_mod_add(partials[tid].get(), partials[tid].get(), weighted.get(), ec.order.get(), lctx);
    }

    BNPtr rho_total(BN_new());
    BN_zero(rho_total.get());
    for (int t = 0; t < nthreads; t++) {
        BN_mod_add(rho_total.get(), rho_total.get(), partials[t].get(), ec.order.get(), ctx);
    }

    BNPtr k = RandomScalar(ec);
    ECPointPtr T(EC_POINT_new(ec.group));
    EC_POINT_mul(ec.group, T.get(), nullptr, ec.H.get(), k.get(), ctx);

    std::vector<unsigned char> challenge_input = transcript;
    AppendPoint(ec, challenge_input, T.get(), ctx);
    BNPtr e = HashToScalarMod(ec, challenge_input, "CHALLENGE-SUM");

    BNPtr z(BN_new());
    BN_mod_mul(z.get(), e.get(), rho_total.get(), ec.order.get(), ctx);
    BN_mod_add(z.get(), z.get(), k.get(), ec.order.get(), ctx);

    return SchnorrProof{std::move(T), std::move(z)};
}

static bool VerifyVectorSum(const ECParams& ec, BN_CTX* ctx, const std::vector<ECPointPtr>& Ca,
                             const std::vector<ECPointPtr>& Cr, const std::vector<long>& s,
                             const std::vector<unsigned char>& transcript, const SchnorrProof& proof) {
    std::vector<ECPointPtr> D = BuildDVector(ec, Ca, Cr, s);
    ECPointPtr P = WeightedSum(ec, transcript, RawPoints(D));

    std::vector<unsigned char> challenge_input = transcript;
    AppendPoint(ec, challenge_input, proof.T.get(), ctx);
    BNPtr e = HashToScalarMod(ec, challenge_input, "CHALLENGE-SUM");

    ECPointPtr lhs(EC_POINT_new(ec.group));
    EC_POINT_mul(ec.group, lhs.get(), nullptr, ec.H.get(), proof.z.get(), ctx);

    ECPointPtr eP(EC_POINT_new(ec.group));
    EC_POINT_mul(ec.group, eP.get(), nullptr, P.get(), e.get(), ctx);
    ECPointPtr rhs(EC_POINT_new(ec.group));
    EC_POINT_add(ec.group, rhs.get(), proof.T.get(), eP.get(), ctx);

    return EC_POINT_cmp(ec.group, lhs.get(), rhs.get(), ctx) == 0;
}

// ============================ Batched Okamoto opening proof (Part 2) ============================

struct OkamotoProof {
    ECPointPtr T;
    BNPtr z1;
    BNPtr z2;
};

static std::vector<unsigned char> BuildTranscriptOpen(const ECParams& ec, BN_CTX* ctx,
                                                        const std::vector<const EC_POINT*>& C) {
    std::vector<unsigned char> t = {'O', 'P', 'E', 'N'};
    for (auto* p : C) AppendPoint(ec, t, p, ctx);
    return t;
}

// Proves knowledge of {(v_i, rho_i)} opening each C[i] = v_i*G + rho_i*H,
// batched into one proof via a Fiat-Shamir random linear combination.
static OkamotoProof ProveBatchOpening(const ECParams& ec, BN_CTX* ctx, const std::vector<long>& v,
                                       const std::vector<const BIGNUM*>& rho,
                                       const std::vector<unsigned char>& transcript) {
    size_t n = v.size();
    int nthreads = MaxThreads();
    std::vector<BNPtr> v_partials, rho_partials;
    for (int t = 0; t < nthreads; t++) {
        v_partials.emplace_back(BN_new());
        BN_zero(v_partials.back().get());
        rho_partials.emplace_back(BN_new());
        BN_zero(rho_partials.back().get());
    }

#pragma omp parallel for schedule(static)
    for (long i = 0; i < static_cast<long>(n); i++) {
        int tid = CurrentThreadId();
        BN_CTX* lctx = g_bn_ctx_pool[tid];
        BNPtr gamma = DeriveGamma(ec, transcript, static_cast<size_t>(i));

        BNPtr v_bn(LongToBN(v[static_cast<size_t>(i)]));
        BNPtr term1(BN_new());
        BN_mod_mul(term1.get(), gamma.get(), v_bn.get(), ec.order.get(), lctx);
        BN_mod_add(v_partials[tid].get(), v_partials[tid].get(), term1.get(), ec.order.get(), lctx);

        BNPtr term2(BN_new());
        BN_mod_mul(term2.get(), gamma.get(), rho[static_cast<size_t>(i)], ec.order.get(), lctx);
        BN_mod_add(rho_partials[tid].get(), rho_partials[tid].get(), term2.get(), ec.order.get(), lctx);
    }

    BNPtr v_agg(BN_new());
    BN_zero(v_agg.get());
    BNPtr rho_agg(BN_new());
    BN_zero(rho_agg.get());
    for (int t = 0; t < nthreads; t++) {
        BN_mod_add(v_agg.get(), v_agg.get(), v_partials[t].get(), ec.order.get(), ctx);
        BN_mod_add(rho_agg.get(), rho_agg.get(), rho_partials[t].get(), ec.order.get(), ctx);
    }

    BNPtr k1 = RandomScalar(ec);
    BNPtr k2 = RandomScalar(ec);
    ECPointPtr T(EC_POINT_new(ec.group));
    EC_POINT_mul(ec.group, T.get(), k1.get(), ec.H.get(), k2.get(), ctx);

    std::vector<unsigned char> challenge_input = transcript;
    AppendPoint(ec, challenge_input, T.get(), ctx);
    BNPtr e = HashToScalarMod(ec, challenge_input, "CHALLENGE-OPEN");

    BNPtr z1(BN_new());
    BN_mod_mul(z1.get(), e.get(), v_agg.get(), ec.order.get(), ctx);
    BN_mod_add(z1.get(), z1.get(), k1.get(), ec.order.get(), ctx);

    BNPtr z2(BN_new());
    BN_mod_mul(z2.get(), e.get(), rho_agg.get(), ec.order.get(), ctx);
    BN_mod_add(z2.get(), z2.get(), k2.get(), ec.order.get(), ctx);

    return OkamotoProof{std::move(T), std::move(z1), std::move(z2)};
}

static bool VerifyBatchOpening(const ECParams& ec, BN_CTX* ctx, const std::vector<const EC_POINT*>& C,
                                const std::vector<unsigned char>& transcript, const OkamotoProof& proof) {
    ECPointPtr P = WeightedSum(ec, transcript, C);

    std::vector<unsigned char> challenge_input = transcript;
    AppendPoint(ec, challenge_input, proof.T.get(), ctx);
    BNPtr e = HashToScalarMod(ec, challenge_input, "CHALLENGE-OPEN");

    ECPointPtr lhs(EC_POINT_new(ec.group));
    EC_POINT_mul(ec.group, lhs.get(), proof.z1.get(), ec.H.get(), proof.z2.get(), ctx);

    ECPointPtr eP(EC_POINT_new(ec.group));
    EC_POINT_mul(ec.group, eP.get(), nullptr, P.get(), e.get(), ctx);
    ECPointPtr rhs(EC_POINT_new(ec.group));
    EC_POINT_add(ec.group, rhs.get(), proof.T.get(), eP.get(), ctx);

    return EC_POINT_cmp(ec.group, lhs.get(), rhs.get(), ctx) == 0;
}

// ============================ Paillier cryptosystem (GMP, CRT-optimized) ============================

struct PaillierPublicKey {
    BigInt n;
    BigInt n2;
    int bits = 0;
};

struct PaillierSecretKey {
    BigInt p, q;
    BigInt hp, hq;  // CRT decryption precomputation
};

static void SeedRandState(gmp_randstate_t state) {
    gmp_randinit_default(state);
    unsigned char seed_bytes[32];
    RAND_bytes(seed_bytes, sizeof(seed_bytes));
    mpz_t seed;
    mpz_init(seed);
    mpz_import(seed, sizeof(seed_bytes), 1, 1, 1, 0, seed_bytes);
    gmp_randseed(state, seed);
    mpz_clear(seed);
}

static void GenRandomPrime(mpz_t out, int bits, gmp_randstate_t state) {
    mpz_t candidate;
    mpz_init(candidate);
    mpz_urandomb(candidate, state, static_cast<unsigned long>(bits));
    mpz_setbit(candidate, bits - 1);
    mpz_setbit(candidate, 0);
    mpz_nextprime(out, candidate);
    mpz_clear(candidate);
}

static void PaillierKeyGen(PaillierPublicKey& pk, PaillierSecretKey& sk, int bits) {
    int prime_bits = bits / 2;
    gmp_randstate_t state;
    SeedRandState(state);

    BigInt p, q;
    do {
        GenRandomPrime(p.v, prime_bits, state);
        GenRandomPrime(q.v, prime_bits, state);
    } while (mpz_cmp(p.v, q.v) == 0);

    mpz_mul(pk.n.v, p.v, q.v);
    mpz_mul(pk.n2.v, pk.n.v, pk.n.v);
    pk.bits = bits;

    BigInt g;
    mpz_add_ui(g.v, pk.n.v, 1);

    BigInt p2, pm1, u, L;
    mpz_mul(p2.v, p.v, p.v);
    mpz_sub_ui(pm1.v, p.v, 1);
    mpz_powm(u.v, g.v, pm1.v, p2.v);
    mpz_sub_ui(u.v, u.v, 1);
    mpz_tdiv_q(L.v, u.v, p.v);
    mpz_invert(sk.hp.v, L.v, p.v);

    BigInt q2, qm1;
    mpz_mul(q2.v, q.v, q.v);
    mpz_sub_ui(qm1.v, q.v, 1);
    mpz_powm(u.v, g.v, qm1.v, q2.v);
    mpz_sub_ui(u.v, u.v, 1);
    mpz_tdiv_q(L.v, u.v, q.v);
    mpz_invert(sk.hq.v, L.v, q.v);

    sk.p = std::move(p);
    sk.q = std::move(q);

    gmp_randclear(state);
}

static void PaillierEncrypt(const PaillierPublicKey& pk, mpz_t ct_out, long m, mpz_t rho_out) {
    gmp_randstate_t state;
    SeedRandState(state);

    BigInt rho, gcd_check;
    do {
        mpz_urandomm(rho.v, state, pk.n.v);
        mpz_gcd(gcd_check.v, rho.v, pk.n.v);
    } while (mpz_cmp_ui(rho.v, 0) == 0 || mpz_cmp_ui(gcd_check.v, 1) != 0);

    BigInt g;
    mpz_add_ui(g.v, pk.n.v, 1);
    BigInt m_bn;
    mpz_set_si(m_bn.v, m);
    BigInt m_mod;
    mpz_mod(m_mod.v, m_bn.v, pk.n.v);

    BigInt gm, rn;
    mpz_powm(gm.v, g.v, m_mod.v, pk.n2.v);
    mpz_powm(rn.v, rho.v, pk.n.v, pk.n2.v);

    mpz_mul(ct_out, gm.v, rn.v);
    mpz_mod(ct_out, ct_out, pk.n2.v);
    mpz_set(rho_out, rho.v);

    gmp_randclear(state);
}

static long PaillierDecryptCRT(const PaillierPublicKey& pk, const PaillierSecretKey& sk, const mpz_t ct) {
    BigInt p2, q2, pm1, qm1;
    mpz_mul(p2.v, sk.p.v, sk.p.v);
    mpz_mul(q2.v, sk.q.v, sk.q.v);
    mpz_sub_ui(pm1.v, sk.p.v, 1);
    mpz_sub_ui(qm1.v, sk.q.v, 1);

    BigInt up, Lp, mp;
    mpz_powm(up.v, ct, pm1.v, p2.v);
    mpz_sub_ui(up.v, up.v, 1);
    mpz_tdiv_q(Lp.v, up.v, sk.p.v);
    mpz_mul(mp.v, Lp.v, sk.hp.v);
    mpz_mod(mp.v, mp.v, sk.p.v);

    BigInt uq, Lq, mq;
    mpz_powm(uq.v, ct, qm1.v, q2.v);
    mpz_sub_ui(uq.v, uq.v, 1);
    mpz_tdiv_q(Lq.v, uq.v, sk.q.v);
    mpz_mul(mq.v, Lq.v, sk.hq.v);
    mpz_mod(mq.v, mq.v, sk.q.v);

    BigInt p_inv_q, diff, m, n, half_n;
    mpz_invert(p_inv_q.v, sk.p.v, sk.q.v);
    mpz_sub(diff.v, mq.v, mp.v);
    mpz_mod(diff.v, diff.v, sk.q.v);
    mpz_mul(diff.v, diff.v, p_inv_q.v);
    mpz_mod(diff.v, diff.v, sk.q.v);
    mpz_mul(m.v, sk.p.v, diff.v);
    mpz_add(m.v, m.v, mp.v);

    mpz_mul(n.v, sk.p.v, sk.q.v);
    mpz_tdiv_q_ui(half_n.v, n.v, 2);
    if (mpz_cmp(m.v, half_n.v) > 0) {
        mpz_sub(m.v, m.v, n.v);
    }
    return mpz_get_si(m.v);
}

static void PaillierAdd(const PaillierPublicKey& pk, mpz_t out, const mpz_t c1, const mpz_t c2) {
    mpz_mul(out, c1, c2);
    mpz_mod(out, out, pk.n2.v);
}

// Handles a negative scalar via modular inversion of the ciphertext, so this
// covers both HE.Eval(x[i]*c[i] + ...) and the <ct_b, -r> inner product.
static void PaillierScalarMulSigned(const PaillierPublicKey& pk, mpz_t out, const mpz_t ct, long scalar) {
    BigInt base;
    if (scalar >= 0) {
        mpz_set(base.v, ct);
    } else {
        mpz_invert(base.v, ct, pk.n2.v);
    }
    BigInt exp;
    mpz_set_si(exp.v, scalar >= 0 ? scalar : -scalar);
    mpz_powm(out, base.v, exp.v, pk.n2.v);
}

// ============================ Paillier proof of knowledge of ciphertext opening ============================

struct PaillierOpeningProof {
    BigInt A;
    BigInt z;
    BigInt w;
};

// Proves knowledge of (m, rho) with |m| < 2^R_BITS such that
// ct = (1+n)^m * rho^n mod n^2, using a Girault-style Sigma protocol with a
// statistical-hiding slack of ZK_STAT_SEC_BITS extra bits on the response.
static PaillierOpeningProof ProvePaillierOpening(const PaillierPublicKey& pk, const mpz_t ct, long m,
                                                  const mpz_t rho, const std::vector<unsigned char>& transcript) {
    gmp_randstate_t state;
    SeedRandState(state);

    int slack_bits = R_BITS + ZK_STAT_SEC_BITS;
    BigInt u, bound, m_prime;
    mpz_urandomb(u.v, state, static_cast<unsigned long>(slack_bits + 1));
    mpz_ui_pow_ui(bound.v, 2, static_cast<unsigned long>(slack_bits));
    mpz_sub(m_prime.v, u.v, bound.v);  // symmetric range [-2^slack_bits, 2^slack_bits)

    BigInt rho_prime, gcd_check;
    do {
        mpz_urandomm(rho_prime.v, state, pk.n.v);
        mpz_gcd(gcd_check.v, rho_prime.v, pk.n.v);
    } while (mpz_cmp_ui(rho_prime.v, 0) == 0 || mpz_cmp_ui(gcd_check.v, 1) != 0);

    BigInt g;
    mpz_add_ui(g.v, pk.n.v, 1);
    BigInt m_prime_mod;
    mpz_mod(m_prime_mod.v, m_prime.v, pk.n.v);
    BigInt gm, rn;
    mpz_powm(gm.v, g.v, m_prime_mod.v, pk.n2.v);
    mpz_powm(rn.v, rho_prime.v, pk.n.v, pk.n2.v);

    PaillierOpeningProof proof;
    mpz_mul(proof.A.v, gm.v, rn.v);
    mpz_mod(proof.A.v, proof.A.v, pk.n2.v);

    std::vector<unsigned char> input = transcript;
    AppendMpz(input, ct);
    AppendMpz(input, proof.A.v);
    BigInt e = DeriveChallengeSEC(input, ZK_STAT_SEC_BITS);

    BigInt em;
    mpz_mul_si(em.v, e.v, m);
    mpz_add(proof.z.v, m_prime.v, em.v);

    BigInt rho_e;
    mpz_powm(rho_e.v, rho, e.v, pk.n.v);
    mpz_mul(proof.w.v, rho_prime.v, rho_e.v);
    mpz_mod(proof.w.v, proof.w.v, pk.n.v);

    gmp_randclear(state);
    return proof;
}

static bool VerifyPaillierOpening(const PaillierPublicKey& pk, const mpz_t ct, const PaillierOpeningProof& proof,
                                   const std::vector<unsigned char>& transcript) {
    std::vector<unsigned char> input = transcript;
    AppendMpz(input, ct);
    AppendMpz(input, proof.A.v);
    BigInt e = DeriveChallengeSEC(input, ZK_STAT_SEC_BITS);

    BigInt bound, abs_z;
    mpz_ui_pow_ui(bound.v, 2, static_cast<unsigned long>(R_BITS + ZK_STAT_SEC_BITS + 1));
    mpz_abs(abs_z.v, proof.z.v);
    if (mpz_cmp(abs_z.v, bound.v) > 0) return false;

    BigInt g, z_mod, gz, wn, lhs;
    mpz_add_ui(g.v, pk.n.v, 1);
    mpz_mod(z_mod.v, proof.z.v, pk.n.v);
    mpz_powm(gz.v, g.v, z_mod.v, pk.n2.v);
    mpz_powm(wn.v, proof.w.v, pk.n.v, pk.n2.v);
    mpz_mul(lhs.v, gz.v, wn.v);
    mpz_mod(lhs.v, lhs.v, pk.n2.v);

    BigInt ct_e, rhs;
    mpz_powm(ct_e.v, ct, e.v, pk.n2.v);
    mpz_mul(rhs.v, proof.A.v, ct_e.v);
    mpz_mod(rhs.v, rhs.v, pk.n2.v);

    return mpz_cmp(lhs.v, rhs.v) == 0;
}

// ============================ Reporting helpers ============================

static void PrintTime(const char* label, double total_ms, int count) {
    printf("%-52s total: %10.3f ms, average: %10.3f ms\n", label, total_ms, total_ms / count);
}

static void PrintSize(const char* label, size_t bytes) {
    printf("%-52s %10zu bytes (%.3f KB)\n", label, bytes, bytes / 1024.0);
}

// ============================ main ============================

int main(int argc, char** argv) {
    int d = DEFAULT_DIM;
    if (argc > 1) {
        int parsed = std::atoi(argv[1]);
        if (parsed > 0) d = parsed;
    }

#ifdef _OPENMP
    omp_set_dynamic(0);
    omp_set_num_threads(omp_get_max_threads());
#endif
    int nthreads = MaxThreads();

    g_bn_ctx_pool.resize(static_cast<size_t>(nthreads));
    for (auto& c : g_bn_ctx_pool) c = BN_CTX_new();

    ECParams ec = SetupECParams();
    BN_CTX* ctx = g_bn_ctx_pool[0];

    printf("=== ZKPoK + HE Benchmark (dimension d=%d, threads=%d, Paillier modulus=%d bits) ===\n\n", d, nthreads,
           PAILLIER_MODULUS_BITS);

    // ============================ Part 1 ============================
    printf("--- Part 1: Pedersen-committed vector addition a + r under ZKPoK ---\n");

    std::vector<long> a(static_cast<size_t>(d)), r(static_cast<size_t>(d)), s(static_cast<size_t>(d));
    for (int i = 0; i < d; i++) a[static_cast<size_t>(i)] = RandomSigned(VALUE_BITS);  // dummy input vector a
    for (int i = 0; i < d; i++) r[static_cast<size_t>(i)] = RandomSigned(VALUE_BITS);  // randomly sampled r

    std::vector<BNPtr> rhoA(static_cast<size_t>(d)), rhoR(static_cast<size_t>(d));
    std::vector<ECPointPtr> Ca(static_cast<size_t>(d)), Cr(static_cast<size_t>(d));

    auto t0 = Clock::now();
#pragma omp parallel for schedule(static)
    for (long i = 0; i < d; i++) {
        BN_CTX* lctx = g_bn_ctx_pool[CurrentThreadId()];
        rhoA[static_cast<size_t>(i)] = RandomScalar(ec);
        Ca[static_cast<size_t>(i)] = PedersenCommit(ec, lctx, a[static_cast<size_t>(i)], rhoA[static_cast<size_t>(i)].get());
    }
    auto t1 = Clock::now();
    double commitA_ms = ms(t0, t1);

    t0 = Clock::now();
#pragma omp parallel for schedule(static)
    for (long i = 0; i < d; i++) {
        BN_CTX* lctx = g_bn_ctx_pool[CurrentThreadId()];
        rhoR[static_cast<size_t>(i)] = RandomScalar(ec);
        Cr[static_cast<size_t>(i)] = PedersenCommit(ec, lctx, r[static_cast<size_t>(i)], rhoR[static_cast<size_t>(i)].get());
    }
    t1 = Clock::now();
    double commitR_ms = ms(t0, t1);

    t0 = Clock::now();
    for (int i = 0; i < d; i++) s[static_cast<size_t>(i)] = a[static_cast<size_t>(i)] + r[static_cast<size_t>(i)];
    t1 = Clock::now();
    double compute_ms = ms(t0, t1);

    std::vector<unsigned char> transcriptSum = BuildTranscriptSum(ec, ctx, Ca, Cr, s);

    t0 = Clock::now();
    SchnorrProof sumProof = ProveVectorSum(ec, ctx, s, rhoA, rhoR, transcriptSum);
    t1 = Clock::now();
    double proveSum_ms = ms(t0, t1);

    t0 = Clock::now();
    bool sumValid = VerifyVectorSum(ec, ctx, Ca, Cr, s, transcriptSum, sumProof);
    t1 = Clock::now();
    double verifySum_ms = ms(t0, t1);

    size_t commitA_bytes = static_cast<size_t>(d) * ec.point_bytes;
    size_t commitR_bytes = static_cast<size_t>(d) * ec.point_bytes;
    size_t sumProof_bytes = ec.point_bytes + ec.scalar_bytes;
    size_t result_bytes = static_cast<size_t>(d) * sizeof(long);

    PrintTime("Commitment generation for a (parallel loop)", commitA_ms, d);
    PrintTime("Commitment generation for r (parallel loop)", commitR_ms, d);
    PrintTime("Plaintext computation of a+r", compute_ms, d);
    PrintTime("ZKPoK proof generation (a+r=s, batched)", proveSum_ms, d);
    PrintTime("ZKPoK verification (commitments + proof)", verifySum_ms, d);
    PrintSize("Commitments for a, total size", commitA_bytes);
    PrintSize("Commitments for r, total size", commitR_bytes);
    PrintSize("ZKPoK proof size (O(1), independent of d)", sumProof_bytes);
    PrintSize("Result a+r size", result_bytes);
    printf("Verification result: %s\n", sumValid ? "PASS" : "FAIL");

    // ============================ Part 2 ============================
    printf("\n--- Part 2: HE.Eval(<ct_b, -r> + R) with ZKPoK over committed r, R ---\n");

    std::vector<long> b(static_cast<size_t>(d));
    for (int i = 0; i < d; i++) b[static_cast<size_t>(i)] = RandomSigned(VALUE_BITS);  // dummy input vector b
    long R = RandomUnsigned(R_BITS);                                                  // randomly sampled scalar R

    PaillierPublicKey pk;
    PaillierSecretKey sk;
    t0 = Clock::now();
    PaillierKeyGen(pk, sk, PAILLIER_MODULUS_BITS);
    t1 = Clock::now();
    double heSetup_ms = ms(t0, t1);
    size_t pubkey_bytes = static_cast<size_t>(PAILLIER_MODULUS_BITS) / 8;
    size_t ct_bytes_each = 2 * (static_cast<size_t>(PAILLIER_MODULUS_BITS) / 8);

    std::vector<BigInt> ctB(static_cast<size_t>(d));
    std::vector<BigInt> rhoB(static_cast<size_t>(d));
    t0 = Clock::now();
#pragma omp parallel for schedule(static)
    for (long i = 0; i < d; i++) {
        PaillierEncrypt(pk, ctB[static_cast<size_t>(i)].v, b[static_cast<size_t>(i)], rhoB[static_cast<size_t>(i)].v);
    }
    t1 = Clock::now();
    double encryptB_ms = ms(t0, t1);
    size_t ctB_total_bytes = static_cast<size_t>(d) * ct_bytes_each;

    // Commitment for R (new); commitments for r are reused verbatim from Part 1.
    t0 = Clock::now();
    BNPtr rhoRscalar = RandomScalar(ec);
    ECPointPtr CR = PedersenCommit(ec, ctx, R, rhoRscalar.get());
    t1 = Clock::now();
    double commitR_new_ms = ms(t0, t1);

    BigInt ctR, rhoR_pai;
    t0 = Clock::now();
    PaillierEncrypt(pk, ctR.v, R, rhoR_pai.v);
    t1 = Clock::now();
    double encryptR_ms = ms(t0, t1);

    // HE.Eval(<ct_b, -r> + R) = ( prod_i ct_b[i]^(-r_i) ) * ct_R  mod n^2
    t0 = Clock::now();
    BigInt evalResult;
    mpz_set_ui(evalResult.v, 1);
    {
        int nthreads_local = MaxThreads();
        std::vector<BigInt> partials(static_cast<size_t>(nthreads_local));
        for (auto& p : partials) mpz_set_ui(p.v, 1);

#pragma omp parallel
        {
            int tid = CurrentThreadId();
#pragma omp for schedule(static)
            for (long i = 0; i < d; i++) {
                BigInt term;
                PaillierScalarMulSigned(pk, term.v, ctB[static_cast<size_t>(i)].v, -r[static_cast<size_t>(i)]);
                mpz_mul(partials[static_cast<size_t>(tid)].v, partials[static_cast<size_t>(tid)].v, term.v);
                mpz_mod(partials[static_cast<size_t>(tid)].v, partials[static_cast<size_t>(tid)].v, pk.n2.v);
            }
        }

        for (auto& p : partials) {
            mpz_mul(evalResult.v, evalResult.v, p.v);
            mpz_mod(evalResult.v, evalResult.v, pk.n2.v);
        }
        mpz_mul(evalResult.v, evalResult.v, ctR.v);
        mpz_mod(evalResult.v, evalResult.v, pk.n2.v);
    }
    t1 = Clock::now();
    double heEval_ms = ms(t0, t1);
    size_t evalResult_bytes = ct_bytes_each;

    // Combined batched Okamoto opening proof over (C_r[0..d-1], C_R).
    std::vector<const EC_POINT*> openCommits = RawPoints(Cr);
    openCommits.push_back(CR.get());
    std::vector<long> openValues = r;
    openValues.push_back(R);
    std::vector<const BIGNUM*> openRho;
    for (auto& rp : rhoR) openRho.push_back(rp.get());
    openRho.push_back(rhoRscalar.get());

    std::vector<unsigned char> transcriptOpen = BuildTranscriptOpen(ec, ctx, openCommits);

    t0 = Clock::now();
    OkamotoProof openProof = ProveBatchOpening(ec, ctx, openValues, openRho, transcriptOpen);
    t1 = Clock::now();
    double proveOpen_ms = ms(t0, t1);

    // Shared master transcript binding the EC proof's first message to the
    // Paillier proof, so both sub-proofs are Fiat-Shamir'd as one AND-composition.
    std::vector<unsigned char> masterTranscript = transcriptOpen;
    AppendPoint(ec, masterTranscript, openProof.T.get(), ctx);

    t0 = Clock::now();
    PaillierOpeningProof paiProof = ProvePaillierOpening(pk, ctR.v, R, rhoR_pai.v, masterTranscript);
    t1 = Clock::now();
    double provePai_ms = ms(t0, t1);

    size_t okamotoProof_bytes = ec.point_bytes + 2 * ec.scalar_bytes;
    size_t paiProof_bytes = 2 * ct_bytes_each / 2 /*A is one n2 element*/ + pubkey_bytes /*w is one n element*/ +
                             static_cast<size_t>((R_BITS + ZK_STAT_SEC_BITS + 2 + 7) / 8) /*z*/;

    t0 = Clock::now();
    bool openValid = VerifyBatchOpening(ec, ctx, openCommits, transcriptOpen, openProof);
    bool paiValid = VerifyPaillierOpening(pk, ctR.v, paiProof, masterTranscript);
    t1 = Clock::now();
    double verifyPart2_ms = ms(t0, t1);

    t0 = Clock::now();
    long decryptedEval = PaillierDecryptCRT(pk, sk, evalResult.v);
    t1 = Clock::now();
    double decrypt_ms = ms(t0, t1);

    long expectedEval = R;
    for (int i = 0; i < d; i++) expectedEval += (-r[static_cast<size_t>(i)]) * b[static_cast<size_t>(i)];

    PrintTime("HE Setup (Paillier KeyGen)", heSetup_ms, 1);
    PrintSize("HE public key size", pubkey_bytes);
    PrintTime("Encryption of b (parallel loop)", encryptB_ms, d);
    PrintSize("Encryption of b, total size", ctB_total_bytes);
    PrintTime("New commitment generation for R", commitR_new_ms, 1);
    PrintTime("HE.Encrypt(R) (needed for HE.Eval and its ZKPoK)", encryptR_ms, 1);
    PrintTime("HE Computation (HE.Eval(<ct_b,-r>+R), parallel loop)", heEval_ms, d);
    PrintSize("HE.Eval(<ct_b,-r>+R) result size", evalResult_bytes);
    PrintTime("ZKPoK proof generation: EC opening proof (r, R)", proveOpen_ms, d + 1);
    PrintTime("ZKPoK proof generation: Paillier opening proof (R)", provePai_ms, 1);
    PrintSize("Additional commitment for R, size", ec.point_bytes);
    printf("Commitments for r: reused from Part 1 (0 additional bytes/time)\n");
    PrintSize("EC opening proof size (O(1), independent of d)", okamotoProof_bytes);
    PrintSize("Paillier opening proof size", paiProof_bytes);
    PrintTime("Verification of proofs and commitments (Part 2)", verifyPart2_ms, 1);
    PrintTime("HE.Decrypt", decrypt_ms, 1);
    printf("EC opening proof valid: %s\n", openValid ? "PASS" : "FAIL");
    printf("Paillier opening proof valid: %s\n", paiValid ? "PASS" : "FAIL");
    printf("Decrypted eval result: %ld (expected %ld) -> %s\n", decryptedEval, expectedEval,
           decryptedEval == expectedEval ? "PASS" : "FAIL");

    // ============================ Part 3 ============================
    printf("\n--- Part 3: %d independent HE.Eval(x[i]*c[i]+y[i]) pipelines ---\n", d);

    std::vector<long> c(static_cast<size_t>(d)), x(static_cast<size_t>(d)), y(static_cast<size_t>(d));
    for (int i = 0; i < d; i++) {
        c[static_cast<size_t>(i)] = RandomSigned(VALUE_BITS);
        x[static_cast<size_t>(i)] = RandomSigned(VALUE_BITS);
        y[static_cast<size_t>(i)] = RandomSigned(VALUE_BITS);
    }

    std::vector<PaillierPublicKey> pk3(static_cast<size_t>(d));
    std::vector<PaillierSecretKey> sk3(static_cast<size_t>(d));
    std::vector<BigInt> ctC(static_cast<size_t>(d)), rhoC(static_cast<size_t>(d));
    std::vector<BigInt> ctEval(static_cast<size_t>(d));
    std::vector<long> decrypted3(static_cast<size_t>(d));

    t0 = Clock::now();
#pragma omp parallel for schedule(dynamic)
    for (long i = 0; i < d; i++) {
        PaillierKeyGen(pk3[static_cast<size_t>(i)], sk3[static_cast<size_t>(i)], PAILLIER_MODULUS_BITS);
    }
    t1 = Clock::now();
    double keygen3_ms = ms(t0, t1);

    t0 = Clock::now();
#pragma omp parallel for schedule(dynamic)
    for (long i = 0; i < d; i++) {
        PaillierEncrypt(pk3[static_cast<size_t>(i)], ctC[static_cast<size_t>(i)].v, c[static_cast<size_t>(i)],
                         rhoC[static_cast<size_t>(i)].v);
    }
    t1 = Clock::now();
    double encrypt3_ms = ms(t0, t1);

    t0 = Clock::now();
#pragma omp parallel for schedule(dynamic)
    for (long i = 0; i < d; i++) {
        BigInt scaled, ctY, rhoY;
        PaillierScalarMulSigned(pk3[static_cast<size_t>(i)], scaled.v, ctC[static_cast<size_t>(i)].v, x[static_cast<size_t>(i)]);
        PaillierEncrypt(pk3[static_cast<size_t>(i)], ctY.v, y[static_cast<size_t>(i)], rhoY.v);
        PaillierAdd(pk3[static_cast<size_t>(i)], ctEval[static_cast<size_t>(i)].v, scaled.v, ctY.v);
    }
    t1 = Clock::now();
    double eval3_ms = ms(t0, t1);

    t0 = Clock::now();
#pragma omp parallel for schedule(dynamic)
    for (long i = 0; i < d; i++) {
        decrypted3[static_cast<size_t>(i)] =
            PaillierDecryptCRT(pk3[static_cast<size_t>(i)], sk3[static_cast<size_t>(i)], ctEval[static_cast<size_t>(i)].v);
    }
    t1 = Clock::now();
    double decrypt3_ms = ms(t0, t1);

    size_t pubkey3_total_bytes = static_cast<size_t>(d) * pubkey_bytes;
    size_t ctC_total_bytes = static_cast<size_t>(d) * ct_bytes_each;
    size_t ctEval3_total_bytes = static_cast<size_t>(d) * ct_bytes_each;

    int correct3 = 0;
    for (int i = 0; i < d; i++) {
        long expected = x[static_cast<size_t>(i)] * c[static_cast<size_t>(i)] + y[static_cast<size_t>(i)];
        if (decrypted3[static_cast<size_t>(i)] == expected) correct3++;
    }

    PrintTime("Total HE KeyGen for all d instances (parallel)", keygen3_ms, d);
    PrintSize("Total public key size (all d instances)", pubkey3_total_bytes);
    PrintTime("Total encryption of c[1..d] (parallel)", encrypt3_ms, d);
    PrintSize("Total size of encryptions of c[1..d]", ctC_total_bytes);
    PrintTime("Total HE.Eval(x[i]*c[i]+y[i]) (parallel)", eval3_ms, d);
    PrintSize("Total size of all HE.Eval(x[i]*c[i]+y[i]) ciphertexts", ctEval3_total_bytes);
    PrintTime("Total HE.Decrypt for all d instances (parallel)", decrypt3_ms, d);
    printf("Decryption correctness: %d / %d PASS\n", correct3, d);

    for (auto* c : g_bn_ctx_pool) BN_CTX_free(c);
    EC_GROUP_free(ec.group);

    return 0;
}
