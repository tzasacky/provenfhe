// bfv_demo.cpp -- UNTRUSTED helper for the fhe_check OpenFHE frontend (BFV).
//
// Two modes:
//   bfv_demo run <outdir> [--mult HPS|HPSPOVERQ|HPSPOVERQLEVELED|BEHZ|default]
//                         [--ks HYBRID|BV|default] [--enc STANDARD|EXTENDED|default]
//                         [--depth D] [--t T] [--n N] [--qbits B] [--dnum K] [--digitsize W]
//                         [--batch S] [--prog P] [--progdepth K]
//       "default" never calls the corresponding setter: OpenFHE v1.6.1's BFVRNS defaults are
//       HPSPOVERQLEVELED, BV (digit size 0), STANDARD, 60-bit primes
//       (gen-cryptocontext-params-defaults.h:92-126: :111, :99, :95, :110, :105).
//       --n sets the ring dimension AND HEStd_NotSet (NOT secure; fixtures only).
//       --qbits is SetScalingModSize (the size of the primes of Q; default 60).
//       --depth is SetMultiplicativeDepth; the program's own depth is --progdepth (default: the
//       same), so "--depth D+1 --progdepth D" runs a depth-D program on parameters sized for D+1.
//       P: chain | dot | rot | plain | rotsum | norelin | neg | compress
//          | coefpk   (CoefPacked plaintexts: encrypted, and as operands of EvalMult/EvalAdd/EvalSub,
//            with negative coefficients and the extreme values +-t/2)
//          | innerprod | symenc | threepart | nocheck | mixadd   (refused by extract_bfv.py; kept
//            for the refusal fixtures tests/refused-bfv/: EvalInnerProduct = EvalMult + EvalSum,
//            which OpenFHE >= 1.6 fuses; Encrypt with the private key;
//            EvalMult with a key on a 3-part operand; EvalMultNoRelinNoCheck, which is the BGV
//            tensor product without the BFV scaling by t/Q)
//       Creates a BFVrns CryptoContext with OpenFHE's own parameter generation, writes
//         <outdir>/cc.json       the context, serialized by OpenFHE (cereal JSON)
//         <outdir>/params.json   the fields fhe_check needs, read through OpenFHE's API
//                                (fhecheck::paramsJson in fhecheck-tracer.h): N, t, the primes of
//                                Q, the special primes P (HYBRID), the auxiliary basis of the
//                                multiplication (HPS family: R; BEHZ: B, m_sk, gamma), the extra
//                                prime of EXTENDED encryption, the library's own FindLevelsToDrop
//                                (bfvrns-leveledshe.cpp:98) evaluated on this context for every
//                                noiseScaleDeg up to 64, and the build options
//         <outdir>/trace.jsonl   JSON-lines trace (fhecheck-tracer.h) of the program, from KeyGen
//                                (the extractor checks where every key comes from) to the last
//                                evaluation (Decrypt is not traced)
//         <outdir>/values.json   for value_check_bfv.py: the coefficients mod t of every traced
//                                plaintext, and per output the raw decrypted polynomial mod t
//                                (PKEBFVRNS::Decrypt, before Decode), the decoded slots, and the
//                                OBSERVED BFV noise ||[c0 + c1 s (+ c2 s^2) - floor(Q/t) m]_Q||_inf
//                                of every fresh ciphertext and of the output (exact big-integer
//                                arithmetic; m = the encoded plaintext resp. the raw decryption)
//         <outdir>/check.txt     decoded slots vs. the same function computed in the clear
//   bfv_demo dump <cc.json>
//       Deserializes a context a user saved with Serial::SerializeToFile(..., SerType::JSON)
//       and prints params.json for it to stdout.
//
// Nothing here is trusted: the Lean checker re-checks primality, coprimality, and recomputes
// every bound from these numbers.

#include "openfhe.h"
#include "cryptocontext-ser.h"
#include "scheme/bfvrns/bfvrns-ser.h"
#include "utils/fhecheck-tracer.h"  // harness/frontend/openfhe/fhecheck-tracer.h, installed by build_openfhe.sh

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

using namespace lbcrypto;

static std::string paramsJson(const CryptoContext<DCRTPoly>& cc) {
    return fhecheck::paramsJson(*cc);  // fhecheck-tracer.h: the same fields the tracer writes (FHECHECK_TRACE_DIR)
}

static int dump(const std::string& path) {
    CryptoContext<DCRTPoly> cc;
    if (!Serial::DeserializeFromFile(path, cc, SerType::JSON)) {
        std::cerr << "cannot deserialize " << path << "\n";
        return 1;
    }
    std::cout << paramsJson(cc);
    return 0;
}

// Coefficients of a plaintext's encoded polynomial: tower 0 in coefficient form. Packed encoding
// lifts to [0, t) and copies the same value into every tower (packedencoding.cpp:68-119).
static std::vector<uint64_t> ptVec(const Plaintext& p, uint64_t t) {
    DCRTPoly e = p->GetElement<DCRTPoly>();
    e.SetFormat(Format::COEFFICIENT);
    const NativePoly& z = e.GetElementAtIndex(0);
    std::vector<uint64_t> r(z.GetLength());
    for (size_t i = 0; i < r.size(); i++) {
        r[i] = z[i].ConvertToInt();
        if (r[i] >= t) throw std::runtime_error("encoded coefficient not in [0, t)");
        for (size_t j = 1; j < e.GetNumOfElements(); j++)
            if (e.GetElementAtIndex(j)[i].ConvertToInt() != r[i])
                throw std::runtime_error("encoded coefficient differs between towers");
    }
    return r;
}

static std::string vecJson(const std::vector<uint64_t>& v) {
    std::ostringstream o;
    o << "[";
    for (size_t i = 0; i < v.size(); i++) o << (i ? "," : "") << v[i];
    o << "]";
    return o.str();
}

// || [ c0 + c1 s (+ c2 s^2 ...) - floor(Q_l/t) m ]_{Q_l} ||_inf, exactly. m has coefficients in [0, t).
static std::string observedNoise(const Ciphertext<DCRTPoly>& c, const PrivateKey<DCRTPoly>& sk,
                                 const std::vector<uint64_t>& m, uint64_t t) {
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
    BigInteger Q = big.GetModulus();
    BigInteger delta = Q / BigInteger(t), half = Q >> 1, worst(0);
    for (size_t i = 0; i < big.GetLength(); i++) {
        BigInteger d = big[i].ModSub(delta * BigInteger(m[i]), Q);
        if (d > half) d = Q - d;
        if (d > worst) worst = d;
    }
    return worst.ToString();
}

int main(int argc, char** argv) {
    if (argc >= 3 && std::string(argv[1]) == "dump") return dump(argv[2]);
    if (argc < 3 || (std::string(argv[1]) != "run" && std::string(argv[1]) != "params")) {
        std::cerr << "usage: frontier_bfv run|params <outdir> [opts] | frontier_bfv dump <cc.json>\n";
        return 2;
    }
    const bool paramsOnly = std::string(argv[1]) == "params";
    std::string out = argv[2];
    uint32_t depth = 2, dnum = 0, n = 0, qbits = 0, batch = 0, digitsize = 0, pd = 0, ringdim = 0;
    uint64_t t = 65537;
    std::string mult = "default", ks = "default", enc = "default", prog = "chain";
    for (int i = 3; i + 1 < argc; i += 2) {
        std::string k = argv[i], v = argv[i + 1];
        if (k == "--depth") depth = std::stoul(v);
        else if (k == "--t") t = std::stoull(v);
        else if (k == "--mult") mult = v;
        else if (k == "--ks") ks = v;
        else if (k == "--enc") enc = v;
        else if (k == "--dnum") dnum = std::stoul(v);
        else if (k == "--digitsize") digitsize = std::stoul(v);
        else if (k == "--prog") prog = v;
        else if (k == "--n") n = std::stoul(v);
        else if (k == "--qbits") qbits = std::stoul(v);
        else if (k == "--batch") batch = std::stoul(v);
        else if (k == "--progdepth") pd = std::stoul(v);
        else if (k == "--ringdim") ringdim = std::stoul(v);
        else { std::cerr << "unknown option " << k << "\n"; return 2; }
    }
    if (prog == "innerprod" && !batch) batch = 8;
    if (!pd) pd = depth;  // the program's multiplicative depth (default: the context's)

    CCParams<CryptoContextBFVRNS> params;
    params.SetMultiplicativeDepth(depth);
    params.SetPlaintextModulus(t);
    if (dnum) params.SetNumLargeDigits(dnum);
    if (digitsize) params.SetDigitSize(digitsize);
    if (qbits) params.SetScalingModSize(qbits);
    if (n) { params.SetRingDim(n); params.SetSecurityLevel(HEStd_NotSet); }
    if (ringdim) params.SetRingDim(ringdim);  // keeps the security level: OpenFHE throws if N is too small (bfvrns-parametergeneration.cpp:314)
    if (batch) params.SetBatchSize(batch);
    if (prog == "norelin") params.SetMaxRelinSkDeg(2);
    if (mult == "HPS") params.SetMultiplicationTechnique(HPS);
    else if (mult == "HPSPOVERQ") params.SetMultiplicationTechnique(HPSPOVERQ);
    else if (mult == "HPSPOVERQLEVELED") params.SetMultiplicationTechnique(HPSPOVERQLEVELED);
    else if (mult == "BEHZ") params.SetMultiplicationTechnique(BEHZ);
    else if (mult != "default") { std::cerr << "unknown multiplication technique " << mult << "\n"; return 2; }
    if (ks == "HYBRID") params.SetKeySwitchTechnique(HYBRID);
    else if (ks == "BV") params.SetKeySwitchTechnique(BV);
    else if (ks != "default") { std::cerr << "unknown key-switching technique " << ks << "\n"; return 2; }
    if (enc == "STANDARD") params.SetEncryptionTechnique(STANDARD);
    else if (enc == "EXTENDED") params.SetEncryptionTechnique(EXTENDED);
    else if (enc != "default") { std::cerr << "unknown encryption technique " << enc << "\n"; return 2; }
    CryptoContext<DCRTPoly> cc = GenCryptoContext(params);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    cc->Enable(ADVANCEDSHE);
    auto cp = std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc->GetCryptoParameters());

    { std::ofstream f(out + "/params.json"); f << paramsJson(cc); }
    if (paramsOnly) return 0;  // "params": the context OpenFHE generates, nothing else

    // Trace everything from key generation to the last evaluation: the extractor takes ciphertext
    // inputs only from traced CryptoContext::Encrypt outputs, and keys only from traced KeyGen /
    // EvalMultKeyGen / EvalRotateKeyGen calls (key provenance).
    auto tracer = std::make_shared<fhecheck::JsonTracer>(std::make_shared<std::ofstream>(out + "/trace.jsonl"));
    tracer->watch(cc);  // refuse the trace if a parameter setter changes the context after params.json
    IF_TRACE(cc->setTracer(tracer));
    auto kp = cc->KeyGen();
    cc->EvalMultKeyGen(kp.secretKey);
    cc->EvalRotateKeyGen(kp.secretKey, {1, 2, 4, -1});
    if (prog == "innerprod") cc->EvalSumKeyGen(kp.secretKey);

    std::vector<int64_t> va = {1, 2, 3, 4, 5, 6, 7, 8}, vb = {5, 6, 7, 8, -1, -2, -3, -4},
                         vc = {2, 2, 2, 2, 2, 2, 2, 2}, v1 = {3, 1, 4, 1, 5, 9, 2, 6},
                         v2 = {10, 20, 30, 40, 50, 60, 70, 80}, v3 = {-7, 7, -7, 7, -7, 7, -7, 7};

    std::vector<Plaintext> pts;  // every plaintext made under the trace (for values.json)
    std::vector<std::pair<Ciphertext<DCRTPoly>, Plaintext>> fresh;
    auto mk = [&](const std::vector<int64_t>& v) {
        auto p = cc->MakePackedPlaintext(v);
        pts.push_back(p);
        return p;
    };
    auto encr = [&](const std::vector<int64_t>& v) {
        auto p = mk(v);
        auto c = prog == "symenc" && &v == &vc ? cc->Encrypt(kp.secretKey, p) : cc->Encrypt(kp.publicKey, p);
        fresh.emplace_back(c, p);
        return c;
    };
    auto ca  = encr(va);
    auto cb  = encr(vb);
    auto cc3 = encr(vc);

    // Cleartext model of the program, slot-wise mod t (sanity check only).
    auto mod = [&](int64_t x) { int64_t r = x % (int64_t)t; return r < 0 ? r + (int64_t)t : r; };
    size_t S = va.size();
    std::vector<int64_t> want(S);
    auto zip = [&](const std::vector<int64_t>& x, const std::vector<int64_t>& y, int op) {
        std::vector<int64_t> r(S);
        for (size_t i = 0; i < S; i++) r[i] = mod(op == 0 ? x[i] + y[i] : op == 1 ? x[i] - y[i] : x[i] * y[i]);
        return r;
    };
    size_t checkLen = S, lo = 0;

    Ciphertext<DCRTPoly> res;
    if (prog == "chain") {
        // y = (a*b)^(2^(pd-1)): pd multiplications, each relinearized
        res  = cc->EvalMult(ca, cb);
        want = zip(va, vb, 2);
        for (uint32_t d = 1; d < pd; d++) {
            res  = cc->EvalSquare(res);
            want = zip(want, want, 2);
        }
    } else if (prog == "tree") {
        // balanced product tree of 2^pd leaves (leaves cycle over a, b, c), each product relinearized
        std::vector<Ciphertext<DCRTPoly>> lv;
        std::vector<std::vector<int64_t>> wv;
        const Ciphertext<DCRTPoly>* L3[3] = {&ca, &cb, &cc3};
        const std::vector<int64_t>* W3[3] = {&va, &vb, &vc};
        for (uint32_t i = 0; i < (1u << pd); i++) { lv.push_back(*L3[i % 3]); wv.push_back(*W3[i % 3]); }
        while (lv.size() > 1) {
            std::vector<Ciphertext<DCRTPoly>> nx;
            std::vector<std::vector<int64_t>> nw;
            for (size_t i = 0; i + 1 < lv.size(); i += 2) {
                nx.push_back(cc->EvalMult(lv[i], lv[i + 1]));
                nw.push_back(zip(wv[i], wv[i + 1], 2));
            }
            lv = nx;
            wv = nw;
        }
        res  = lv[0];
        want = wv[0];
    } else if (prog == "poly") {
        // frontier_bgv.cpp's poly without ModReduce/LevelReduce: u = a * b; u += rot(u,1);
        // u += rot(u,2); u += rot(u,4); y = u + c_{D-1}; for j = D-2..0: y = y*u + c_j.
        // Exactly D ciphertext x ciphertext multiplications on the critical path (depth D).
        const size_t R = cc->GetRingDimension() / 2;
        auto rowv = [&](const std::vector<int64_t>& v) { std::vector<int64_t> r(R, 0); for (size_t i = 0; i < v.size(); i++) r[i] = mod(v[i]); return r; };
        auto rot = [&](const std::vector<int64_t>& v, size_t k) { std::vector<int64_t> r(R); for (size_t i = 0; i < R; i++) r[i] = v[(i + k) % R]; return r; };
        auto zipR = [&](const std::vector<int64_t>& x, const std::vector<int64_t>& y, int op) {
            std::vector<int64_t> r(R);
            for (size_t i = 0; i < R; i++) r[i] = mod(op == 0 ? x[i] + y[i] : x[i] * y[i]);
            return r;
        };
        auto u = cc->EvalMult(ca, cb);
        auto wu = zipR(rowv(va), rowv(vb), 2);
        for (size_t k : {1, 2, 4}) {
            u  = cc->EvalAdd(u, cc->EvalRotate(u, (int32_t)k));
            wu = zipR(wu, rot(wu, k), 0);
        }
        auto coef = [&](uint32_t j) { std::vector<int64_t> c(S); for (size_t i = 0; i < S; i++) c[i] = (int64_t)((3 * j + 5 * i + 1) % 17) - 8; return c; };
        { Plaintext pc = mk(coef(pd - 1)); res = cc->EvalAdd(u, pc); }
        auto wy = zipR(wu, rowv(coef(pd - 1)), 0);
        for (int32_t j = (int32_t)pd - 2; j >= 0; j--) {
            res = cc->EvalMult(res, u);
            { Plaintext pc = mk(coef(j)); res = cc->EvalAdd(res, pc); }
            wy = zipR(zipR(wy, wu, 2), rowv(coef(j)), 0);
        }
        for (size_t i = 0; i < S; i++) want[i] = wy[i];
    } else if (prog == "mixed") {
        // the same op sequence as bgv_u's mixed: x = a*b; then alternately (even k) x = x*p_k;
        // x += rot(x,1); x += rot(x,2); x += q_k  and (odd k) x = x*x; finally y = x + c
        res  = cc->EvalMult(ca, cb);
        want = zip(va, vb, 2);
        bool rotated = false;
        for (uint32_t k = 2; k <= pd; k++) {
            if (k % 2 == 0) {
                { Plaintext pp1 = mk(v1); res = cc->EvalMult(res, pp1); }
                res = cc->EvalAdd(res, cc->EvalRotate(res, 1));
                res = cc->EvalAdd(res, cc->EvalRotate(res, 2));
                { Plaintext pp2 = mk(v2); res = cc->EvalAdd(res, pp2); }
                rotated = true;
            } else {
                res  = cc->EvalSquare(res);
                want = zip(want, want, 2);
            }
        }
        res  = cc->EvalAdd(res, cc3);
        want = zip(want, vc, 0);
        if (rotated) checkLen = 0;
    } else if (prog == "advchain") {
        // tightness probe: CoefPacked messages with every coefficient at +-(t/2) (largest centred
        // magnitude); (x*y) then squarings; observed noise of fresh inputs and output in values.json
        int64_t h = static_cast<int64_t>(t >> 1);
        size_t Nn = cc->GetRingDimension();
        std::vector<int64_t> vx(Nn), vy(Nn);
        for (size_t i = 0; i < Nn; i++) { vx[i] = (h > 0) ? -1 : -1; vy[i] = -1; }  // -1 is stored as t-1 (BFVRNS CoefPacked)
        auto mkc = [&](const std::vector<int64_t>& v) { auto p = cc->MakeCoefPackedPlaintext(v); pts.push_back(p); return p; };
        Plaintext px = mkc(vx), py = mkc(vy);
        auto xa = cc->Encrypt(kp.publicKey, px), xb = cc->Encrypt(kp.publicKey, py);
        fresh.emplace_back(xa, px);
        fresh.emplace_back(xb, py);
        res = cc->EvalMult(xa, xb);
        for (uint32_t d = 1; d < pd; d++) res = cc->EvalSquare(res);
        checkLen = 0;
    } else if (prog == "dot") {
        // y = a*b + rot(a*b, 1) + c
        auto p = cc->EvalMult(ca, cb);
        auto r = cc->EvalRotate(p, 1);
        res    = cc->EvalAdd(p, r);
        res    = cc->EvalAdd(res, cc3);
        auto ab = zip(va, vb, 2);
        for (size_t i = 0; i + 1 < S; i++) want[i] = mod(ab[i] + ab[i + 1] + vc[i]);
        checkLen = S - 1;
    } else if (prog == "rot") {
        res = cc->EvalRotate(ca, 1);
        res = cc->EvalAdd(res, cb);
        for (size_t i = 0; i + 1 < S; i++) want[i] = mod(va[i + 1] + vb[i]);
        checkLen = S - 1;
    } else if (prog == "plain") {
        // y = ((a*b) * p1 + p2) - p3
        res  = cc->EvalMult(ca, cb);
        Plaintext p1 = mk(v1), p2 = mk(v2), p3 = mk(v3);
        res  = cc->EvalMult(res, p1);
        res  = cc->EvalAdd(res, p2);
        res  = cc->EvalSub(res, p3);
        want = zip(zip(zip(zip(va, vb, 2), v1, 2), v2, 0), v3, 1);
    } else if (prog == "rotsum") {
        // s = a*b; s = s + rot(s,1); s = s + rot(s,2); y = s - rot(a,-1)
        auto s = cc->EvalMult(ca, cb);
        s      = cc->EvalAdd(s, cc->EvalAtIndex(s, 1));
        s      = cc->EvalAdd(s, cc->EvalRotate(s, 2));
        res    = cc->EvalSub(s, cc->EvalAtIndex(ca, -1));
        auto ab = zip(va, vb, 2);
        for (size_t i = 1; i + 3 < S; i++) want[i] = mod(ab[i] + ab[i + 1] + ab[i + 2] + ab[i + 3] - va[i - 1]);
        lo = 1;
        checkLen = S - 3;
    } else if (prog == "innerprod") {
        res       = cc->EvalInnerProduct(ca, cb, batch);
        int64_t s = 0;
        for (size_t i = 0; i < S; i++) s += va[i] * vb[i];
        for (size_t i = 0; i < S; i++) want[i] = mod(s);
        checkLen = 1;
    } else if (prog == "norelin") {
        // y = Relinearize(a*b + a*c) (3-part sum), then squared with relinearization
        auto p = cc->EvalMultNoRelin(ca, cb);
        auto q = cc->EvalMultNoRelin(ca, cc3);
        res    = cc->EvalAdd(p, q);
        res    = cc->Relinearize(res);
        want   = zip(zip(va, vb, 2), zip(va, vc, 2), 0);
        if (pd >= 2) {
            res  = cc->EvalSquare(res);
            want = zip(want, want, 2);
        }
    } else if (prog == "neg") {
        // y = -(a*b) + (-c)
        res  = cc->EvalNegate(cc->EvalMult(ca, cb));
        res  = cc->EvalAdd(res, cc->EvalNegate(cc3));
        want = zip(zip(vc, vc, 1), zip(zip(va, vb, 2), vc, 0), 1);
    } else if (prog == "compress") {
        // y = Compress(a*b, k) * Compress(c, k) with k = max(1, L-1) towers left: a modulus switch of
        // both, then a multiplication below the top level. BFV Compress exists for the
        // HPSPOVERQ* techniques with STANDARD encryption only (bfvrns-leveledshe.cpp:906-914).
        size_t L = cp->GetElementParams()->GetParams().size();
        size_t k = L > 2 ? L - 1 : 1;
        auto p   = cc->Compress(cc->EvalMult(ca, cb), k);
        auto c2  = cc->Compress(cc3, k);
        res      = pd >= 2 && k >= 2 ? cc->EvalMult(p, c2) : cc->EvalAdd(p, c2);
        want     = pd >= 2 && k >= 2 ? zip(zip(va, vb, 2), vc, 2) : zip(zip(va, vb, 2), vc, 0);
    } else if (prog == "symenc") {
        // y = a*b + c, c encrypted with the PRIVATE key (refused: only public-key encryption is mapped)
        res  = cc->EvalAdd(cc->EvalMult(ca, cb), cc3);
        want = zip(zip(va, vb, 2), vc, 0);
    } else if (prog == "coefpk") {
        // y = ((Enc(a) + Enc(x)) * Enc(b)) * x + p2 - b with every plaintext made by
        // MakeCoefPackedPlaintext. Negative coefficients are stored as t - |v| for BFVRNS
        // (coefpackedencoding.cpp:58-61), i.e. >= t/2: vb and v3 have some, and x holds the extreme
        // values the encoding accepts, t/2 (stored as is) and -(t/2) (stored as t - t/2 > t/2).
        // ptVec (values.json) throws unless every stored coefficient is in [0, t) and equal in all limbs.
        int64_t h = static_cast<int64_t>(t >> 1);
        std::vector<int64_t> vx = {h, -h, 1, -1, 0, h - 1, -(h - 1), 2};
        auto mkc = [&](const std::vector<int64_t>& v) {
            auto p = cc->MakeCoefPackedPlaintext(v);
            pts.push_back(p);
            return p;
        };
        Plaintext pa = mkc(va), pb = mkc(vb), px = mkc(vx), pp = mkc(v2);
        auto xa = cc->Encrypt(kp.publicKey, pa), xb = cc->Encrypt(kp.publicKey, pb), xx = cc->Encrypt(kp.publicKey, px);
        fresh.emplace_back(xa, pa);
        fresh.emplace_back(xb, pb);
        fresh.emplace_back(xx, px);
        res      = cc->EvalMult(cc->EvalAdd(xa, xx), xb);
        res      = cc->EvalMult(res, px);
        res      = cc->EvalAdd(res, pp);
        res      = cc->EvalSub(res, pb);
        checkLen = 0;  // no slot-wise model: value_check_bfv.py checks every coefficient of the raw decryption
    } else if (prog == "threepart") {
        // y = EvalMult(EvalMultNoRelin(a, b), c): the relinearization of the 4-part product
        // key-switches only cv[2] and drops cv[3] (refused)
        res      = cc->EvalMult(cc->EvalMultNoRelin(ca, cb), cc3);
        checkLen = 0;
    } else if (prog == "mixadd") {
        // y = EvalAdd(EvalMultNoRelin(a, b), c): an unrelinearised product combined with an ordinary
        // ciphertext (refused by extract_bfv.py: only sums/differences of such products, negation and
        // relinearization are mapped)
        res      = cc->EvalAdd(cc->EvalMultNoRelin(ca, cb), cc3);
        checkLen = 0;
    } else if (prog == "nocheck") {
        // y = Relinearize(EvalMultNoRelinNoCheck(a, b)): CryptoContext's componentwise tensor product,
        // which for BFV lacks the scaling by t/Q (refused)
        res      = cc->Relinearize(cc->EvalMultNoRelinNoCheck(ca, cb));
        checkLen = 0;
    } else {
        std::cerr << "unknown prog\n";
        return 2;
    }
    IF_TRACE(cc->setTracer(std::make_shared<fhecheck::JsonTracer>(std::make_shared<std::ofstream>("/dev/null"))));
    if (prog == "threepart" || prog == "nocheck" || prog == "mixadd") {  // refusal fixtures: trace only
        std::cout << "wrote " << out << " (" << prog << ": trace only)\n";
        return 0;
    }

    // values.json: plaintext coefficients, the raw decryption of the output, observed noises.
    std::ofstream vf(out + "/values.json");
    vf << "{\"t\": " << t << ",\n \"plaintexts\": {";
    for (size_t i = 0; i < pts.size(); i++)
        vf << (i ? ",\n  " : "\n  ") << "\"" << tracer->idOf(pts[i], "pt") << "\": " << vecJson(ptVec(pts[i], t));
    vf << "},\n \"fresh\": {";
    for (size_t i = 0; i < fresh.size(); i++)
        vf << (i ? ",\n  " : "\n  ") << "\"" << tracer->idOf(fresh[i].first, "ct") << "\": {\"towers\": "
           << fresh[i].first->GetElements()[0].GetNumOfElements() << ", \"noise\": \""
           << observedNoise(fresh[i].first, kp.secretKey, ptVec(fresh[i].second, t), t) << "\"}";
    vf << "},\n \"outputs\": {";
    NativePoly raw;
    cc->GetScheme()->Decrypt(res, kp.secretKey, &raw);
    std::vector<uint64_t> rawv(raw.GetLength());
    for (size_t i = 0; i < rawv.size(); i++) rawv[i] = raw[i].ConvertToInt() % t;
    vf << "\n  \"" << tracer->idOf(res, "ct") << "\": {\"towers\": " << res->GetElements()[0].GetNumOfElements()
       << ", \"parts\": " << res->NumberCiphertextElements() << ", \"nsd\": " << res->GetNoiseScaleDeg()
       << ", \"noise\": \"" << observedNoise(res, kp.secretKey, rawv, t) << "\", \"raw\": " << vecJson(rawv);
    Plaintext pt;
    cc->Decrypt(kp.secretKey, res, &pt);
    pt->SetLength(S);
    vf << ", \"slots\": [";
    // a CoefPacked result decodes to coefficients, not slots (coefpk has no slot-wise check: checkLen = 0)
    auto got = (prog == "coefpk" || prog == "advchain") ? pt->GetCoefPackedValue() : pt->GetPackedValue();
    for (size_t i = 0; i < S; i++) vf << (i ? "," : "") << mod(got[i]);
    bool ok = true;
    for (size_t i = lo; i < checkLen; i++) ok = ok && mod(got[i]) == want[i];
    vf << "], \"cleartextCheck\": " << (ok ? "true" : "false") << "}}}\n";

    std::ofstream f(out + "/check.txt");
    f << "decrypted: " << pt << "\nexpected (slots " << lo << ".." << checkLen << " mod t):";
    for (size_t i = lo; i < checkLen; i++) f << " " << want[i];
    f << "\ncleartext check: " << (ok ? "OK" : "MISMATCH") << "\ntowers: "
      << res->GetElements()[0].GetNumOfElements() << " parts: " << res->NumberCiphertextElements()
      << " nsd: " << res->GetNoiseScaleDeg() << "\n";
    std::cout << "wrote " << out << (ok ? "" : " (CLEARTEXT MISMATCH)") << "\n";
    return ok ? 0 : 3;
}
