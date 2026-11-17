// cks26.cpp -- UNTRUSTED evaluation driver (harness/eval/cks26).
//
// Reproduces, on OpenFHE v1.6.1 with the fhe_check tracer, the EVALUATION CIRCUITS of attacks 2
// and 3 of Choe, Kang, Stehle, "New IND-CPA-D Attacks on BFV and BGV" (ACM CCS 2026, ePrint
// 2026/2546), at the parameters their public code uses (github.com/hmchoe0528/NEW_INDCPAD_HE,
// commit 8d057909e0fe2d57e74c7facd0d99fd934f7d3ab; cited as [repo] below). Written from the paper
// and from a reading of that code; no code of [repo] is copied. It does NOT implement the key
// recovery, the distinguisher or the brute-force search over fresh encryptions: only the circuit
// the adversary asks the library to evaluate, the parameters, and a measurement of the real noise
// with the secret key.
//
//   cks26 ptct DIR --logn L --t T [--depth D] [--K k] [--c C] [--idx k] [--enc coef|packed]
//                  [--sec notset|128] [--time R]
//     Attack 2 (Section 4, Algorithm 1 for one index k): ct_0 = Enc(0); ct_d = EvalMult(ct_{d-1}, mu')
//     for d = 1..K, mu' the non-negative plaintext of Appendix B scaled by C:
//     mu'_j = C if cos(pi (2k-1)(2j+1) / 2N) >= 0, else 0   ([repo] BFV-pt-ct/bfv_ptct.hpp:430-456).
//     Context as [repo] BFV-pt-ct/bfv_ptct_sk_general.cpp:287-292: SetRingDim(2^L),
//     SetPlaintextModulus(T), SetMultiplicativeDepth(D = 4), HPSPOVERQLEVELED, HEStd_NotSet;
//     everything else OpenFHE's default (BV key switching, STANDARD encryption, 60-bit primes).
//     Defaults for K and C: the formulas of [repo] (:413-431): K = the "theoretical estimated
//     depth" floor((log2 Q - 1 - log2 t - log2 Vnorm) / (log2 t - 1 + log2 delta_N)), delta_N =
//     2 sqrt(N), Vnorm = Berr (1 + 8 sqrt(N)); C = min(floor(2^cf), t >> 1), cf = (log2 Q - 1.5 - E1
//     + (K-1)(log2 pi - log2 N)) / K with their profiled E1(log N). --idx: k (default 7, the index
//     of the paper's Figures 3 and 9).
//     --sec 128: HEStd_128_classic and NO SetRingDim (OpenFHE chooses N); for the cost table.
//     --enc coef: MakeCoefPackedPlaintext, as [repo]. --enc packed: the SAME polynomials made with
//     MakePackedPlaintext (possible iff t = 1 mod 2N is prime; the driver checks that the encoded
//     elements are identical limb by limb).
//
//   cks26 ctct DIR --t T --depth D [--K k] [--pool m] [--lincomb M --rho R] [--mu zero|H]
//                  [--enc coef|packed] [--mult HPS|BEHZ|HPSPOVERQ|HPSPOVERQLEVELED] [--time R]
//                  [--scal B] [--dnum n]
//     Attack 3 (Section 5). Context as [repo] BFV-ct-ct/indcpad_ctct.cpp:58-67: plaintext modulus
//     T, HPS, SetMultiplicativeDepth(D), HYBRID, SetScalingModSize(52), SetNumLargeDigits(5),
//     HEStd_128_classic (OpenFHE chooses N).
//     Phase 1 circuit (default): ct = Enc(0); K times: ct = EvalMult(r, r), r = ct + (m fresh
//     encryptions of 0), m = --pool (default 1). The adversary of the paper picks the added
//     encryption(s) of 0 among many so that the a-part is skewed; here they are simply fresh.
//     Phase 2/3 circuit (--lincomb M --rho R): ct = sum_i c_i Enc(mu), i < M, integer c_i summing
//     to C = R*t (c_i = floor(C/M) or that plus one, as [repo] bfv_ctct.hpp:697-702), computed
//     with ciphertext additions only (sum, then double-and-add), then the same K-fold loop.
//     --mu H: the plaintext of Eq. (10) for the index --idx (default 1); zero otherwise.
//
// Files written to DIR: params.json (fhecheck::paramsJson), trace.jsonl (the fhe_check tracer,
// from KeyGen to the last evaluation), measure.json: for the fresh ciphertext and after every
// step the exact BFV noise ||[c0 + c1 s]_Q||_inf (the tracked plaintext is 0 in every circuit
// here), |e(omega_k)| in double precision, the number of coefficients the LIBRARY's decryption
// (PKEBFVRNS::Decrypt) returns nonzero, and the number exact rounding would. With --time R: the
// same evaluation re-run R times untraced (OpenFHE's NullTracer), wall time per run.
//
// Run single-threaded (OMP_NUM_THREADS=1), as the tracer requires.

#include "openfhe.h"
#include "utils/fhecheck-tracer.h"

#include <chrono>
#include <cmath>
#include <complex>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

using namespace lbcrypto;
typedef Ciphertext<DCRTPoly> CT;

static const double PI = 3.141592653589793238462643383279502884;

struct Meas {
    std::string noise;   // decimal, exact
    double log2w;        // log2 |e(omega_k)|
    size_t libNonzero;   // coefficients the library's Decrypt returns != 0 mod t
    size_t exactNonzero; // coefficients with 2 t |e_i| >= Q (exact rounding would not return 0)
};

// Tracked plaintext 0: the BFV noise is the centred phase [c0 + c1 s]_Q.
static Meas measure(const CryptoContext<DCRTPoly>& cc, const CT& c, const PrivateKey<DCRTPoly>& sk, uint64_t t,
                    size_t k) {
    std::vector<DCRTPoly> cv = c->GetElements();
    DCRTPoly s               = sk->GetPrivateElement();
    size_t sizeQl            = cv[0].GetNumOfElements();
    if (s.GetNumOfElements() > sizeQl) s.DropLastElements(s.GetNumOfElements() - sizeQl);
    for (auto& x : cv) x.SetFormat(Format::EVALUATION);
    DCRTPoly phase = cv[0], sp = s;
    for (size_t i = 1; i < cv.size(); i++) {
        phase += cv[i] * sp;
        sp *= s;
    }
    phase.SetFormat(Format::COEFFICIENT);
    Poly big     = phase.CRTInterpolate();
    BigInteger Q = big.GetModulus(), half = Q >> 1, worst(0), T(t);
    size_t N     = big.GetLength();
    Meas m;
    m.exactNonzero = 0;
    for (size_t i = 0; i < N; i++) {
        BigInteger d = big[i] > half ? Q - big[i] : big[i];
        if (d > worst) worst = d;
        if (((d * T) << 1) >= Q) m.exactNonzero++;
    }
    m.noise = worst.ToString();
    // e(omega_k) in floating point; the coefficients are shifted so that the largest has at most
    // 900 bits (a double holds 2^1023), and the shift is added back to the logarithm
    uint32_t msb = worst.GetMSB(), shift = msb > 900 ? msb - 900 : 0;
    double theta = (2.0 * k - 1.0) * PI / static_cast<double>(N);
    std::complex<long double> w(std::cos((long double)theta), std::sin((long double)theta)), acc(0, 0);
    for (size_t jj = N; jj-- > 0;) {
        bool neg      = big[jj] > half;
        BigInteger d  = neg ? Q - big[jj] : big[jj];
        long double x = static_cast<long double>((d >> shift).ConvertToDouble());
        acc           = acc * w + (neg ? -x : x);
    }
    m.log2w = static_cast<double>(std::log2(std::abs(acc))) + shift;
    NativePoly raw;
    cc->GetScheme()->Decrypt(c, sk, &raw);
    m.libNonzero = 0;
    for (size_t i = 0; i < raw.GetLength(); i++)
        if (raw[i].ConvertToInt() % t != 0) m.libNonzero++;
    return m;
}

static void writeMeas(std::ostream& o, uint32_t d, const Meas& m) {
    o << "{\"d\": " << d << ", \"noise\": \"" << m.noise << "\", \"log2AtOmega\": " << m.log2w
      << ", \"libNonzero\": " << m.libNonzero << ", \"exactNonzero\": " << m.exactNonzero << "}";
}

// Every stored coefficient of the plaintext is the same integer in [0, t) in every limb: what
// the frontend's declarations (bound t - 1, encoding deviation of ceil(Q m / t)) need.
static std::vector<uint64_t> liftCheck(const Plaintext& p, uint64_t t) {
    DCRTPoly e = p->GetElement<DCRTPoly>();
    e.SetFormat(Format::COEFFICIENT);
    const NativePoly& z = e.GetElementAtIndex(0);
    std::vector<uint64_t> r(z.GetLength());
    for (size_t i = 0; i < r.size(); i++) {
        r[i] = z[i].ConvertToInt();
        if (r[i] >= t) throw std::runtime_error("encoded coefficient not in [0, t)");
        for (size_t j = 1; j < e.GetNumOfElements(); j++)
            if (e.GetElementAtIndex(j)[i].ConvertToInt() != r[i])
                throw std::runtime_error("encoded coefficient differs between limbs");
    }
    return r;
}

// The plaintext with coefficient vector `coeffs` (values in (-t/2, t/2]), CoefPacked or, for
// packed, the packed plaintext whose encoded polynomial is the same (checked).
static Plaintext makePt(const CryptoContext<DCRTPoly>& cc, const std::vector<int64_t>& coeffs, bool packed,
                        uint64_t t) {
    Plaintext coef = cc->MakeCoefPackedPlaintext(coeffs);
    if (!packed) {
        liftCheck(coef, t);
        return coef;
    }
    std::vector<uint64_t> want = liftCheck(coef, t);
    // slots = Decode of the polynomial (the inverse of PackedEncoding::Encode)
    auto ep       = cc->GetCryptoParameters()->GetElementParams();
    Plaintext dec = CryptoContextImpl<DCRTPoly>::GetPlaintextForDecrypt(PACKED_ENCODING, ep,
                                                                        cc->GetCryptoParameters()->GetEncodingParams());
    NativePoly np(ep->GetParams()[0], Format::COEFFICIENT, true);
    for (size_t i = 0; i < want.size(); i++) np[i] = NativeInteger(want[i]);
    dec->GetElement<NativePoly>() = np;
    dec->Decode();
    Plaintext pk = cc->MakePackedPlaintext(dec->GetPackedValue());
    if (liftCheck(pk, t) != want) throw std::runtime_error("packed plaintext does not encode the same polynomial");
    return pk;
}

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "usage: cks26 ptct|ctct DIR [options] (see the header of cks26.cpp)\n";
        return 2;
    }
    std::string mode = argv[1], out = argv[2];
    uint32_t logn = 12, depth = 0, K = 0, idx = 0, pool = 1, M = 0, timeReps = 0, scal = 52, dnum = 5;
    uint64_t t = 786433, rho = 0;
    int64_t cconst = 0;
    std::string enc = "coef", sec = "", mult = "HPS", mu = "zero";
    for (int i = 3; i + 1 < argc; i += 2) {
        std::string k = argv[i], v = argv[i + 1];
        if (k == "--logn") logn = std::stoul(v);
        else if (k == "--t") t = std::stoull(v);
        else if (k == "--depth") depth = std::stoul(v);
        else if (k == "--K") K = std::stoul(v);
        else if (k == "--c") cconst = std::stoll(v);
        else if (k == "--idx") idx = std::stoul(v);
        else if (k == "--enc") enc = v;
        else if (k == "--sec") sec = v;
        else if (k == "--time") timeReps = std::stoul(v);
        else if (k == "--pool") pool = std::stoul(v);
        else if (k == "--lincomb") M = std::stoul(v);
        else if (k == "--rho") rho = std::stoull(v);
        else if (k == "--mu") mu = v;
        else if (k == "--mult") mult = v;
        else if (k == "--scal") scal = std::stoul(v);
        else if (k == "--dnum") dnum = std::stoul(v);
        else { std::cerr << "unknown option " << k << "\n"; return 2; }
    }
    bool ptct = mode == "ptct";
    if (!ptct && mode != "ctct") { std::cerr << "unknown mode\n"; return 2; }
    if (enc != "coef" && enc != "packed") { std::cerr << "unknown --enc\n"; return 2; }
    bool packed = enc == "packed";

    CCParams<CryptoContextBFVRNS> params;
    params.SetPlaintextModulus(t);
    if (ptct) {
        if (!depth) depth = 4;
        if (!idx) idx = 7;
        if (sec.empty()) sec = "notset";
        params.SetMultiplicativeDepth(depth);
        params.SetMultiplicationTechnique(HPSPOVERQLEVELED);
        if (sec == "notset") {
            params.SetRingDim(1u << logn);
            params.SetSecurityLevel(HEStd_NotSet);
        } else if (sec == "128") {
            params.SetSecurityLevel(HEStd_128_classic);
        } else { std::cerr << "unknown --sec\n"; return 2; }
    } else {
        if (!depth) { std::cerr << "ctct needs --depth\n"; return 2; }
        if (!idx) idx = 1;
        if (mult == "HPS") params.SetMultiplicationTechnique(HPS);
        else if (mult == "BEHZ") params.SetMultiplicationTechnique(BEHZ);
        else if (mult == "HPSPOVERQ") params.SetMultiplicationTechnique(HPSPOVERQ);
        else if (mult == "HPSPOVERQLEVELED") params.SetMultiplicationTechnique(HPSPOVERQLEVELED);
        else { std::cerr << "unknown --mult\n"; return 2; }
        params.SetMultiplicativeDepth(depth);
        params.SetKeySwitchTechnique(HYBRID);
        params.SetScalingModSize(scal);
        params.SetNumLargeDigits(dnum);
        params.SetSecurityLevel(HEStd_128_classic);
    }
    CryptoContext<DCRTPoly> cc = GenCryptoContext(params);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    auto cp = std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc->GetCryptoParameters());
    { std::ofstream f(out + "/params.json"); f << fhecheck::paramsJson(*cc); }

    const uint32_t N = cc->GetRingDimension();
    double logQ      = 0;
    size_t sizeQ     = cp->GetElementParams()->GetParams().size();
    for (auto& p : cp->GetElementParams()->GetParams()) logQ += std::log2(p->GetModulus().ConvertToDouble());

    // [repo]'s formulas for the pt-ct attack (bfv_ptct_sk_general.cpp:180-220,413-431).
    double sigma = cp->GetDistributionParameter(), alpha = cp->GetAssuranceMeasure();
    double berr  = sigma * std::sqrt(alpha);
    double vnormRepo = berr * (1. + 2. * (4. * std::sqrt((double)N)));  // their GetVnorm (STANDARD, ternary)
    double deltaN    = 2.0 * std::sqrt((double)N);
    uint32_t Kest    = 0;
    double cf        = 0;
    bool capped      = false;
    if (ptct) {
        Kest = static_cast<uint32_t>(
            std::floor((logQ - 1.0 - std::log2((double)t) - std::log2(vnormRepo)) / (std::log2((double)t) - 1.0 + std::log2(deltaN))));
        if (!K) K = Kest;
        if (!cconst) {
            static const double E1[] = {16.1807, 17.3890, 18.1876, 19.2704, 20.2343};  // their profile, log N = 12..16
            uint32_t ln = 0;
            while ((1u << ln) < N) ln++;
            if (ln < 12 || ln > 16 || Kest == 0) { std::cerr << "no default constant for this N: pass --c\n"; return 2; }
            cf     = (logQ - 1.5 - E1[ln - 12] + ((double)Kest - 1.0) * (std::log2(PI) - std::log2((double)N))) / (double)Kest;
            cconst = static_cast<int64_t>(std::pow(2.0, cf));
            if ((double)cconst > (double)t / 2.0) {
                cconst = std::min(cconst, static_cast<int64_t>(t) >> 1);
                capped = true;
            }
        }
    } else if (!K) {
        K = depth;
    }

    auto tracer = std::make_shared<fhecheck::JsonTracer>(std::make_shared<std::ofstream>(out + "/trace.jsonl"));
    IF_TRACE(cc->setTracer(tracer));
    auto kp = cc->KeyGen();
    if (!ptct) cc->EvalMultKeyGen(kp.secretKey);

    // plaintexts
    std::vector<int64_t> zeros(N, 0), coeffs(N, 0);
    Plaintext ptZero = makePt(cc, zeros, packed, t), ptMu;
    double log2MuAtOmega = 0;
    if (ptct) {
        for (uint32_t j = 0; j < N; j++) {
            double angle = ((2.0 * idx - 1.0) * PI * ((double)j + 0.5)) / (double)N;
            coeffs[j]    = (std::cos(angle) >= 0.0) ? cconst : 0;
        }
        ptMu = makePt(cc, coeffs, packed, t);
        double theta = (2.0 * idx - 1.0) * PI / (double)N;
        std::complex<long double> w(std::cos((long double)theta), std::sin((long double)theta)), acc(0, 0);
        for (size_t jj = N; jj-- > 0;) acc = acc * w + (long double)coeffs[jj];
        log2MuAtOmega = static_cast<double>(std::log2(std::abs(acc)));
    } else if (mu == "H") {
        // Eq. (10): H_j = sign(cos(pi (2k-1)(2j+1) / 2N)) * m*, m* = argmax_{0 < m <= t/2} [Q m]_t
        BigInteger Q = cp->GetElementParams()->GetModulus();
        uint64_t r   = (Q.Mod(BigInteger(t))).ConvertToInt();
        uint64_t best = 0, mstar = 1;
        for (uint64_t m = 1; m <= t / 2; m++) {
            uint64_t v = static_cast<uint64_t>((static_cast<unsigned __int128>(r) * m) % t);
            if (v > best) { best = v; mstar = m; }
        }
        for (uint32_t j = 0; j < N; j++) {
            double angle = ((2.0 * idx - 1.0) * PI * ((double)j + 0.5)) / (double)N;
            coeffs[j]    = (std::cos(angle) >= 0.0) ? (int64_t)mstar : -(int64_t)mstar;
        }
        ptMu = makePt(cc, coeffs, packed, t);
    } else {
        ptMu = ptZero;
    }

    // The traced evaluation. `rec` (measurement) is null in the timed re-runs.
    std::vector<Meas> meas;
    uint32_t nEnc = 0;
    auto measureHere = [&](const CT& c) {
        // the measurement calls PKEBFVRNS::Decrypt through the scheme object: keep it out of the trace
        IF_TRACE(cc->setTracer(std::make_shared<NullTracer<DCRTPoly>>()));
        meas.push_back(measure(cc, c, kp.secretKey, t, idx));
        IF_TRACE(cc->setTracer(tracer));
    };
    std::vector<CT> freshPool;  // the fresh encryptions, kept so that the timed re-runs reuse them
    size_t poolPos = 0;
    auto fresh = [&](const Plaintext& p, bool rerun) -> CT {
        if (rerun) return freshPool[poolPos++];
        CT c = cc->Encrypt(kp.publicKey, p);
        nEnc++;
        if (timeReps) freshPool.push_back(c);
        return c;
    };
    auto eval = [&](bool rerun) -> CT {
        poolPos = 0;
        CT ct;
        if (ptct) {
            ct = fresh(ptZero, rerun);
            if (!rerun) measureHere(ct);
            for (uint32_t d = 1; d <= K; d++) {
                ct = cc->EvalMult(ct, ptMu);
                if (!rerun) measureHere(ct);
            }
            return ct;
        }
        if (M) {
            // sum_i c_i Enc(mu), c_i = q + [i < r], C = q M + r: q * (sum of all) + (sum of the first r)
            unsigned __int128 C = static_cast<unsigned __int128>(rho) * t;
            uint64_t q = static_cast<uint64_t>(C / M), r = static_cast<uint64_t>(C % M);
            CT all, pre;
            for (uint32_t i = 0; i < M; i++) {
                CT ci = fresh(ptMu, rerun);
                all   = all ? cc->EvalAdd(all, ci) : ci;
                if (i + 1 == r) pre = all;
            }
            // q * all by double-and-add, most significant bit first
            CT acc;
            for (int b = 63; b >= 0; b--) {
                if (acc) acc = cc->EvalAdd(acc, acc);
                if ((q >> b) & 1) acc = acc ? cc->EvalAdd(acc, all) : all;
            }
            ct = pre ? (acc ? cc->EvalAdd(acc, pre) : pre) : acc;
        } else {
            ct = fresh(ptZero, rerun);
        }
        if (!rerun) measureHere(ct);
        for (uint32_t d = 1; d <= K; d++) {
            CT r = ct;
            for (uint32_t j = 0; j < pool; j++) r = cc->EvalAdd(r, fresh(ptZero, rerun));
            ct = cc->EvalMult(r, r);
            if (!rerun) measureHere(ct);
        }
        return ct;
    };
    auto t0 = std::chrono::steady_clock::now();
    CT res  = eval(false);
    double tracedMs = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
    IF_TRACE(cc->setTracer(std::make_shared<NullTracer<DCRTPoly>>()));

    std::vector<double> times;
    for (uint32_t r = 0; r < timeReps; r++) {
        auto a = std::chrono::steady_clock::now();
        CT x   = eval(true);
        times.push_back(std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - a).count());
        if (x->GetElements()[0] != res->GetElements()[0]) { std::cerr << "timed re-run differs\n"; return 1; }
    }
    std::sort(times.begin(), times.end());

    std::ofstream f(out + "/measure.json");
    f.precision(10);
    f << "{\"mode\": \"" << mode << "\", \"N\": " << N << ", \"t\": " << t << ", \"sizeQ\": " << sizeQ << ", \"log2Q\": " << logQ
      << ", \"depthSet\": " << depth << ", \"K\": " << K << ", \"idx\": " << idx << ", \"enc\": \"" << enc << "\", \"encryptions\": "
      << nEnc << ",\n \"sigma\": " << sigma << ", \"alpha\": " << alpha << ", \"tracedEvalMs\": " << tracedMs;
    if (ptct)
        f << ",\n \"repoFormulas\": {\"Kest\": " << Kest << ", \"log2Vnorm\": " << std::log2(vnormRepo) << ", \"log2Factor\": "
          << (std::log2((double)t) - 1.0 + std::log2(deltaN)) << ", \"constantLog2\": " << cf << ", \"cappedAtHalfT\": "
          << (capped ? "true" : "false") << "},\n \"c\": " << cconst << ", \"log2MuAtOmega\": " << log2MuAtOmega;
    else
        f << ",\n \"pool\": " << pool << ", \"lincombM\": " << M << ", \"rho\": " << rho << ", \"mu\": \"" << mu << "\", \"mult\": \""
          << mult << "\"";
    if (timeReps)
        f << ",\n \"timing\": {\"reps\": " << timeReps << ", \"minMs\": " << times.front() << ", \"medianMs\": "
          << times[times.size() / 2] << "}";
    f << ",\n \"steps\": [";
    for (size_t i = 0; i < meas.size(); i++) {
        f << (i ? ",\n  " : "\n  ");
        writeMeas(f, static_cast<uint32_t>(i), meas[i]);
    }
    f << "]}\n";
    std::cout << "wrote " << out << ": N=" << N << " log2Q=" << logQ << " sizeQ=" << sizeQ << " K=" << K;
    if (ptct) std::cout << " c=" << cconst;
    std::cout << "\n";
    return 0;
}
