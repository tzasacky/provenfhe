// bgv_demo.cpp -- UNTRUSTED helper for the fhe_check OpenFHE frontend.
//
// Two modes:
//   bgv_demo run  <outdir> [--depth D] [--t T] [--scal TECH] [--dnum K] [--prog P] [--n N]
//                          [--qbits B] [--firstbits B] [--batch S] [--evaladd A] [--kscount K]
//       TECH: FIXEDMANUAL | FIXEDAUTO | FLEXIBLEAUTO | FLEXIBLEAUTOEXT | default
//             ("default" never calls SetScalingTechnique: OpenFHE's BGVRNS default, which is
//             FLEXIBLEAUTOEXT, gen-cryptocontext-params-defaults.h:135)
//       P:    chain | dot | rot | plain | plainlvl | lr | rotsum | innerprod | negate | symenc | nocheck | subpt | coefpk | threepart
//             (coefpk: a CoefPacked plaintext; threepart: EvalMult with a key on a 3-part operand;
//             both are refused by the extractor, kept for the refusal fixtures)
//             (innerprod uses EvalInnerProduct = EvalMult + EvalSum, which the extractor REFUSES on
//             OpenFHE >= 1.6: kept to produce the refusal fixtures)
//       Creates a BGVrns CryptoContext with OpenFHE's own parameter generation, writes
//         <outdir>/cc.json       the context, serialized by OpenFHE (cereal JSON)
//         <outdir>/params.json   the fields fhe_check needs, read through OpenFHE's API
//         <outdir>/trace.jsonl   JSON-lines trace (fhecheck-tracer.h) of the program, from KeyGen
//                                (the extractor checks where every key comes from) to the last
//                                evaluation (Decrypt is not traced)
//         <outdir>/values.json   for the plaintext-value cross-check (harness/frontend/openfhe/
//                                value_check.py): the coefficients mod t of every traced
//                                plaintext (tower 0, coefficient form), and, per output, the
//                                raw decrypted polynomial mod t (PKEBGVRNS::Decrypt, before
//                                Decode), OpenFHE's scalingFactorInt and the decoded slots
//         <outdir>/check.txt     decoded slots vs. the same function computed in the clear
//       --ringdim N sets SetRingDim(N) and KEEPS the security level (OpenFHE then checks N against
//       its table and throws if it is too small; --n N instead also sets HEStd_NotSet).
//       --time R re-runs the program evaluation R more times with the tracer replaced by OpenFHE's
//       NullTracer (no keygen, no encryption, no decryption in the timed region) and writes
//       <outdir>/timing.json (per-run milliseconds, median, OpenMP threads).
//       --qbits sets SetScalingModSize, --firstbits SetFirstModSize (0 = OpenFHE's choice; OpenFHE
//       allows both for FIXEDMANUAL only, gen-cryptocontext-params-validation.cpp:124-133);
//       --evaladd / --kscount set SetEvalAddCount / SetKeySwitchCount (defaults 5 / 3), which the
//       automatic modes use to size their primes (bgvrns-parametergeneration.cpp:101-260).
//   bgv_demo dump <cc.json>
//       Deserializes a context a user saved with Serial::SerializeToFile(..., SerType::JSON)
//       and prints params.json for it to stdout. Special primes P are not stored in the
//       serialization; OpenFHE recomputes them on load, and we read them back from the API.
//
// Nothing here is trusted: the Lean checker re-checks primality, roots, coprimality,
// and recomputes every bound from these numbers.

#include "openfhe.h"
#include "cryptocontext-ser.h"
#include "scheme/bgvrns/bgvrns-ser.h"
#include "utils/fhecheck-tracer.h"  // harness/frontend/openfhe/fhecheck-tracer.h, installed by build_openfhe.sh

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <algorithm>
#include <chrono>
#include <vector>

using namespace lbcrypto;

static std::string paramsJson(const CryptoContext<DCRTPoly>& cc) {
    return fhecheck::paramsJson(*cc);  // fhecheck-tracer.h (the same fields the tracer writes)
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

// Coefficients mod t of a plaintext's encoded polynomial: tower 0 in coefficient form. Packed
// encoding lifts to [0, t) before SetModulus (packedencoding.cpp:70-112), so tower 0 holds them.
static std::string ptCoeffs(const Plaintext& p, uint64_t t) {
    DCRTPoly e = p->GetElement<DCRTPoly>();
    e.SetFormat(Format::COEFFICIENT);
    const NativePoly& z = e.GetElementAtIndex(0);
    std::ostringstream o;
    o << "[";
    for (size_t i = 0; i < z.GetLength(); i++) {
        uint64_t v = z[i].ConvertToInt();
        if (v >= t) throw std::runtime_error("encoded coefficient not in [0, t)");
        o << (i ? "," : "") << v;
    }
    o << "]";
    return o.str();
}

// || [c0 + c1 s (+ c2 s^2)]_{Q_l} ||_inf (centred), exactly: the BGV phase m + t*e the checker bounds.
static std::string phaseNorm(const Ciphertext<DCRTPoly>& c, const PrivateKey<DCRTPoly>& sk) {
    std::vector<DCRTPoly> cv = c->GetElements();
    DCRTPoly s = sk->GetPrivateElement();
    size_t sizeQl = cv[0].GetNumOfElements();
    if (s.GetNumOfElements() > sizeQl) s.DropLastElements(s.GetNumOfElements() - sizeQl);
    for (auto& x : cv) x.SetFormat(Format::EVALUATION);
    s.SetFormat(Format::EVALUATION);
    DCRTPoly phase = cv[0], sp = s;
    for (size_t i = 1; i < cv.size(); i++) { phase += cv[i] * sp; sp *= s; }
    phase.SetFormat(Format::COEFFICIENT);
    Poly big = phase.CRTInterpolate();
    BigInteger Q = big.GetModulus(), half = Q >> 1, worst(0);
    for (size_t i = 0; i < big.GetLength(); i++) {
        BigInteger d = big[i];
        if (d > half) d = Q - d;
        if (d > worst) worst = d;
    }
    return worst.ToString();
}

int main(int argc, char** argv) {
    if (argc >= 3 && std::string(argv[1]) == "dump") return dump(argv[2]);
    if (argc < 3 || (std::string(argv[1]) != "run" && std::string(argv[1]) != "params")) {
        std::cerr << "usage: frontier_bgv run|params <outdir> [opts] | frontier_bgv dump <cc.json>\n";
        return 2;
    }
    const bool paramsOnly = std::string(argv[1]) == "params";
    std::string out = argv[2];
    uint32_t depth = 2, dnum = 0, n = 0, qbits = 0, firstbits = 0, batch = 0, evaladd = 0, kscount = 0,
             ringdim = 0, pd = 0;
    uint64_t t = 65537;
    std::string scal = "FIXEDMANUAL", prog = "chain";
    for (int i = 3; i + 1 < argc; i += 2) {
        std::string k = argv[i], v = argv[i + 1];
        if (k == "--depth") depth = std::stoul(v);
        else if (k == "--t") t = std::stoull(v);
        else if (k == "--scal") scal = v;
        else if (k == "--dnum") dnum = std::stoul(v);
        else if (k == "--prog") prog = v;
        else if (k == "--n") n = std::stoul(v);
        else if (k == "--qbits") qbits = std::stoul(v);
        else if (k == "--firstbits") firstbits = std::stoul(v);
        else if (k == "--batch") batch = std::stoul(v);
        else if (k == "--evaladd") evaladd = std::stoul(v);
        else if (k == "--kscount") kscount = std::stoul(v);
        else if (k == "--ringdim") ringdim = std::stoul(v);
        else if (k == "--progdepth") pd = std::stoul(v);
        else { std::cerr << "unknown option " << k << "\n"; return 2; }
    }
    if (prog == "innerprod" && !batch) batch = 8;
    const uint32_t ctxDepth = depth;
    if (pd) depth = pd;  // the program's depth (default: the context's): --depth sets the context only

    CCParams<CryptoContextBGVRNS> params;
    params.SetMultiplicativeDepth(ctxDepth);
    params.SetPlaintextModulus(t);
    if (dnum) params.SetNumLargeDigits(dnum);
    if (qbits) params.SetScalingModSize(qbits);
    if (firstbits) params.SetFirstModSize(firstbits);
    if (n) { params.SetRingDim(n); params.SetSecurityLevel(HEStd_NotSet); }
    if (ringdim) params.SetRingDim(ringdim);
    if (batch) params.SetBatchSize(batch);
    if (evaladd) params.SetEvalAddCount(evaladd);
    if (kscount) params.SetKeySwitchCount(kscount);
    if (scal == "FIXEDMANUAL") params.SetScalingTechnique(FIXEDMANUAL);
    else if (scal == "FIXEDAUTO") params.SetScalingTechnique(FIXEDAUTO);
    else if (scal == "FLEXIBLEAUTO") params.SetScalingTechnique(FLEXIBLEAUTO);
    else if (scal == "FLEXIBLEAUTOEXT") params.SetScalingTechnique(FLEXIBLEAUTOEXT);
    else if (scal != "default") { std::cerr << "unknown scaling technique " << scal << "\n"; return 2; }
    CryptoContext<DCRTPoly> cc = GenCryptoContext(params);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    cc->Enable(ADVANCEDSHE);
    auto cp = std::dynamic_pointer_cast<CryptoParametersBGVRNS>(cc->GetCryptoParameters());
    bool manual = cp->GetScalingTechnique() == FIXEDMANUAL;

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
    auto mk = [&](const std::vector<int64_t>& v) {
        auto p = cc->MakePackedPlaintext(v);
        pts.push_back(p);
        return p;
    };
    auto mkAt = [&](const std::vector<int64_t>& v, const Ciphertext<DCRTPoly>& like) {
        auto p = cc->MakePackedPlaintext(v, like->GetNoiseScaleDeg(), like->GetLevel());
        pts.push_back(p);
        return p;
    };
    auto ca = cc->Encrypt(kp.publicKey, mk(va));
    auto cb = cc->Encrypt(kp.publicKey, mk(vb));
    // symenc: the third input is encrypted with the PRIVATE key (symmetric encryption)
    auto cc3 = prog == "symenc" ? cc->Encrypt(kp.secretKey, mk(vc)) : cc->Encrypt(kp.publicKey, mk(vc));

    // Cleartext model of the program, slot-wise mod t (sanity check only).
    auto mod = [&](int64_t x) { int64_t r = x % (int64_t)t; return r < 0 ? r + (int64_t)t : r; };
    size_t S = va.size();
    std::vector<int64_t> want(S);
    auto zip = [&](const std::vector<int64_t>& x, const std::vector<int64_t>& y, int op) {
        std::vector<int64_t> r(S);
        for (size_t i = 0; i < S; i++) r[i] = mod(op == 0 ? x[i] + y[i] : op == 1 ? x[i] - y[i] : x[i] * y[i]);
        return r;
    };
    // Rotation by k on the first S slots is only checked where it does not wrap.
    size_t checkLen = S;

    // The program, as a function, so that --time can re-run it untraced.
    bool unknownProg = false;
    auto program = [&]() -> Ciphertext<DCRTPoly> {
    Ciphertext<DCRTPoly> res;
    if (prog == "chain") {
        // y = (a*b)^(2^(depth-1)): depth multiplications, ModReduce after each under FIXEDMANUAL
        res = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(res);
        want = zip(va, vb, 2);
        for (uint32_t d = 1; d < depth; d++) {
            res = cc->EvalSquare(res);
            if (manual) cc->ModReduceInPlace(res);
            want = zip(want, want, 2);
        }
    } else if (prog == "mulonly") {
        // tightness probe: one relinearized product, no ModReduce (FIXEDMANUAL)
        res = cc->EvalMult(ca, cb);
        want = zip(va, vb, 2);
    } else if (prog == "msonly") {
        // tightness probe: ModReduce of a fresh ciphertext (FIXEDMANUAL)
        res = cc->ModReduce(ca);
        want = va;
    } else if (prog == "tree") {
        // balanced product tree of 2^depth leaves (leaves cycle over a, b, c): depth levels,
        // 2^depth - 1 products, ModReduce after each under FIXEDMANUAL
        std::vector<Ciphertext<DCRTPoly>> lv;
        std::vector<std::vector<int64_t>> wv;
        const Ciphertext<DCRTPoly>* L3[3] = {&ca, &cb, &cc3};
        const std::vector<int64_t>* W3[3] = {&va, &vb, &vc};
        for (uint32_t i = 0; i < (1u << depth); i++) { lv.push_back(*L3[i % 3]); wv.push_back(*W3[i % 3]); }
        while (lv.size() > 1) {
            std::vector<Ciphertext<DCRTPoly>> nx;
            std::vector<std::vector<int64_t>> nw;
            for (size_t i = 0; i + 1 < lv.size(); i += 2) {
                auto p = cc->EvalMult(lv[i], lv[i + 1]);
                if (manual) cc->ModReduceInPlace(p);
                nx.push_back(p);
                nw.push_back(zip(wv[i], wv[i + 1], 2));
            }
            lv = nx;
            wv = nw;
        }
        res  = lv[0];
        want = wv[0];
    } else if (prog == "poly") {
        // Inner product, then a monic degree-`depth` polynomial by Horner's rule:
        //   u = a * b [MR];  u += rot(u,1); u += rot(u,2); u += rot(u,4)   (slot i: sum_{j<8} (a b)[i+j])
        //   y = u + c_{D-1};  for j = D-2..0: y = y * u [MR]; y += c_j    (u level-reduced to y's level)
        // = p(<a, b>) with p(x) = x^D + c_{D-1} x^{D-1} + ... + c_0: exactly D ciphertext x ciphertext
        // multiplications, all on the critical path (depth D), 3 rotations and D plaintext additions.
        const size_t R = cc->GetRingDimension() / 2;  // slots per row: EvalRotate rotates within a row
        auto rowv = [&](const std::vector<int64_t>& v) { std::vector<int64_t> r(R, 0); for (size_t i = 0; i < v.size(); i++) r[i] = mod(v[i]); return r; };
        auto rot = [&](const std::vector<int64_t>& v, size_t k) { std::vector<int64_t> r(R); for (size_t i = 0; i < R; i++) r[i] = v[(i + k) % R]; return r; };
        auto zipR = [&](const std::vector<int64_t>& x, const std::vector<int64_t>& y, int op) {
            std::vector<int64_t> r(R);
            for (size_t i = 0; i < R; i++) r[i] = mod(op == 0 ? x[i] + y[i] : x[i] * y[i]);
            return r;
        };
        auto u = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(u);
        auto wu = zipR(rowv(va), rowv(vb), 2);
        for (size_t k : {1, 2, 4}) {
            u  = cc->EvalAdd(u, cc->EvalRotate(u, (int32_t)k));
            wu = zipR(wu, rot(wu, k), 0);
        }
        auto coef = [&](uint32_t j) { std::vector<int64_t> c(S); for (size_t i = 0; i < S; i++) c[i] = (int64_t)((3 * j + 5 * i + 1) % 17) - 8; return c; };
        { Plaintext pc = mk(coef(depth - 1)); res = cc->EvalAdd(u, pc); }
        auto wy = zipR(wu, rowv(coef(depth - 1)), 0);
        for (int32_t j = (int32_t)depth - 2; j >= 0; j--) {
            auto uj = u;
            if (manual && res->GetLevel() > u->GetLevel()) uj = cc->LevelReduce(u, nullptr, res->GetLevel() - u->GetLevel());
            res = cc->EvalMult(res, uj);
            if (manual) cc->ModReduceInPlace(res);
            { Plaintext pc = mk(coef(j)); res = cc->EvalAdd(res, pc); }
            wy = zipR(zipR(wy, wu, 2), rowv(coef(j)), 0);
        }
        for (size_t i = 0; i < S; i++) want[i] = wy[i];
    } else if (prog == "mixed") {
        // depth levels: x = a*b; then alternately (even k) x = x*p_k [ModReduce]; x += rot(x,1);
        // x += rot(x,2); x += q_k   and (odd k) x = x*x [ModReduce]; finally y = x + c.
        res  = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(res);
        want = zip(va, vb, 2);
        bool rotated = false;
        for (uint32_t k = 2; k <= depth; k++) {
            if (k % 2 == 0) {
                { Plaintext pp1 = mk(v1); res = cc->EvalMult(res, pp1); }
                if (manual) cc->ModReduceInPlace(res);
                res = cc->EvalAdd(res, cc->EvalRotate(res, 1));
                res = cc->EvalAdd(res, cc->EvalRotate(res, 2));
                { Plaintext pp2 = mk(v2); res = cc->EvalAdd(res, pp2); }
                rotated = true;
            } else {
                res = cc->EvalSquare(res);
                if (manual) cc->ModReduceInPlace(res);
                want = zip(want, want, 2);
            }
        }
        res = cc->EvalAdd(res, cc3);
        want = zip(want, vc, 0);
        if (rotated) checkLen = 0;
    } else if (prog == "dot") {
        // y = a*b + rot(a*b, 1) + c
        auto p = cc->EvalMult(ca, cb);
        auto r = cc->EvalRotate(p, 1);
        res = cc->EvalAdd(p, r);
        if (manual) cc->ModReduceInPlace(res);
        res = cc->EvalAdd(res, cc3);
        auto ab = zip(va, vb, 2);
        for (size_t i = 0; i + 1 < S; i++) want[i] = mod(ab[i] + ab[i + 1] + vc[i]);
        checkLen = S - 1;
    } else if (prog == "rot") {
        res = cc->EvalRotate(ca, 1);
        res = cc->EvalAdd(res, cb);
        for (size_t i = 0; i + 1 < S; i++) want[i] = mod(va[i + 1] + vb[i]);
        checkLen = S - 1;
    } else if (prog == "plain" || prog == "plainlvl") {
        // y = ((a*b) * p1 + p2) - p3. "plain": plaintexts made with MakePackedPlaintext(v)
        // (level 0, the usual call); "plainlvl": made at the ciphertext's level and depth.
        bool lvl = prog == "plainlvl";
        res = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(res);
        Plaintext p1 = lvl ? mkAt(v1, res) : mk(v1);
        res = cc->EvalMult(res, p1);
        if (manual) cc->ModReduceInPlace(res);
        Plaintext p2 = lvl ? mkAt(v2, res) : mk(v2);
        res = cc->EvalAdd(res, p2);
        Plaintext p3 = lvl ? mkAt(v3, res) : mk(v3);
        res = cc->EvalSub(res, p3);
        want = zip(zip(zip(zip(va, vb, 2), v1, 2), v2, 0), v3, 1);
    } else if (prog == "lr") {
        // y = ModReduce(a*b) + LevelReduce(c, 1). LevelReduce/ModReduce act only under
        // FIXEDMANUAL (rns-leveledshe.cpp:441,478); the auto modes align levels themselves.
        res = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(res);
        auto c2 = cc->LevelReduce(cc3, nullptr, 1);
        res = cc->EvalAdd(res, c2);
        want = zip(zip(va, vb, 2), vc, 0);
    } else if (prog == "rotsum") {
        // y = rot(a,1) + rot(a,-1)... on a*b: s = a*b; s = s + rot(s,1); s = s + rot(s,2) (EvalAtIndex)
        auto s = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(s);
        s = cc->EvalAdd(s, cc->EvalAtIndex(s, 1));
        s = cc->EvalAdd(s, cc->EvalRotate(s, 2));
        res = cc->EvalSub(s, cc->EvalAtIndex(ca, -1));
        auto ab = zip(va, vb, 2);
        for (size_t i = 1; i + 3 < S; i++)
            want[i] = mod(ab[i] + ab[i + 1] + ab[i + 2] + ab[i + 3] - va[i - 1]);
        // checked on slots 1..S-4 only (wrap-around and the -1 rotation)
        checkLen = S - 3;
    } else if (prog == "innerprod") {
        // y = EvalInnerProduct(a, b, batch): EvalMult + EvalSum (log2(batch) rotations + adds)
        res = cc->EvalInnerProduct(ca, cb, batch);
        int64_t s = 0;
        for (size_t i = 0; i < S; i++) s += va[i] * vb[i];
        for (size_t i = 0; i < S; i++) want[i] = mod(s);
        checkLen = 1;
    } else if (prog == "negate") {
        // y = -(a*b) + c (EvalNegate)
        res = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(res);
        res = cc->EvalNegate(res);
        res = cc->EvalAdd(res, cc3);
        auto ab = zip(va, vb, 2);
        for (size_t i = 0; i < S; i++) want[i] = mod(-ab[i] + vc[i]);
    } else if (prog == "subpt") {
        // y = p1 - (a*b): EvalSub(plaintext, ciphertext) = EvalAdd(EvalNegate(ct), pt)
        res = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(res);
        Plaintext p1 = mk(v1);
        res = cc->EvalSub(p1, res);
        auto ab = zip(va, vb, 2);
        for (size_t i = 0; i < S; i++) want[i] = mod(v1[i] - ab[i]);
    } else if (prog == "coefpk") {
        // y = Encrypt(MakeCoefPackedPlaintext(a)) + Encrypt(MakeCoefPackedPlaintext(b))
        auto pa = cc->MakeCoefPackedPlaintext(va), pb = cc->MakeCoefPackedPlaintext(vb);
        // (not added to `pts`: values.json lists [0, t) coefficients, and these are centred)
        res = cc->EvalAdd(cc->Encrypt(kp.publicKey, pa), cc->Encrypt(kp.publicKey, pb));
        checkLen = 0;
    } else if (prog == "threepart") {
        // y = EvalMult(EvalMultNoRelin(a, b), c): OpenFHE relinearizes only cv[2] of the 4-part product
        res = cc->EvalMult(cc->EvalMultNoRelin(ca, cb), cc3);
        checkLen = 0;
    } else if (prog == "symenc") {
        // y = a*b + c, c encrypted with the private key
        res = cc->EvalMult(ca, cb);
        if (manual) cc->ModReduceInPlace(res);
        res = cc->EvalAdd(res, cc3);
        want = zip(zip(va, vb, 2), vc, 0);
    } else if (prog == "nocheck") {
        // y = Relinearize(EvalMultNoRelinNoCheck(a, b)) (+ ModReduce under FIXEDMANUAL)
        res = cc->Relinearize(cc->EvalMultNoRelinNoCheck(ca, cb));
        if (manual) cc->ModReduceInPlace(res);
        want = zip(va, vb, 2);
    } else {
        unknownProg = true;
    }
    return res;
    };
    Ciphertext<DCRTPoly> res = program();
    if (unknownProg) {
        std::cerr << "unknown prog\n";
        return 2;
    }
    IF_TRACE(cc->setTracer(std::make_shared<fhecheck::JsonTracer>(std::make_shared<std::ofstream>("/dev/null"))));
    if (prog == "coefpk") {  // refusal fixture only: no packed decoding, no values.json
        std::cout << "wrote " << out << " (coefpk: trace only)\n";
        return 0;
    }

    // values.json: plaintext coefficients and the raw decryption of the output.
    std::ofstream vf(out + "/values.json");
    vf << "{\"t\": " << t << ",\n \"plaintexts\": {";
    for (size_t i = 0; i < pts.size(); i++)
        vf << (i ? ",\n  " : "\n  ") << "\"" << tracer->idOf(pts[i], "pt") << "\": " << ptCoeffs(pts[i], t);
    vf << "},\n \"outputs\": {";
    NativePoly raw;
    auto dr = cc->GetScheme()->Decrypt(res, kp.secretKey, &raw);
    vf << "\n  \"" << tracer->idOf(res, "ct") << "\": {\"towers\": " << res->GetElements()[0].GetNumOfElements()
       << ", \"sf\": " << res->GetScalingFactorInt() << ", \"decryptSf\": " << dr.scalingFactorInt
       << ", \"raw\": [";
    for (size_t i = 0; i < raw.GetLength(); i++) vf << (i ? "," : "") << raw[i].ConvertToInt() % t;
    { std::ofstream nf(out + "/noise.json");
      nf << "{\"outPhaseNorm\": \"" << phaseNorm(res, kp.secretKey) << "\", \"inPhaseNorm\": [\""
         << phaseNorm(ca, kp.secretKey) << "\", \"" << phaseNorm(cb, kp.secretKey) << "\"], \"towers\": "
         << res->GetElements()[0].GetNumOfElements() << "}\n"; }
    Plaintext pt;
    cc->Decrypt(kp.secretKey, res, &pt);
    pt->SetLength(S);
    vf << "], \"slots\": [";
    auto got = pt->GetPackedValue();
    for (size_t i = 0; i < S; i++) vf << (i ? "," : "") << mod(got[i]);
    vf << "]}}}\n";

    bool ok = true;
    size_t lo = prog == "rotsum" ? 1 : 0;
    for (size_t i = lo; i < checkLen; i++) ok = ok && mod(got[i]) == want[i];
    std::ofstream f(out + "/check.txt");
    f << "decrypted: " << pt << "\nexpected (first " << checkLen << " slots mod t):";
    for (size_t i = lo; i < checkLen; i++) f << " " << want[i];
    f << "\ncleartext check: " << (ok ? "OK" : "MISMATCH") << "\nlevel: " << res->GetLevel()
      << " towers: " << res->GetElements()[0].GetNumOfElements() << " parts: " << res->NumberCiphertextElements()
      << " nsd: " << res->GetNoiseScaleDeg() << " sf: " << res->GetScalingFactorInt() << "\n";
    std::cout << "wrote " << out << (ok ? "" : " (CLEARTEXT MISMATCH)") << "\n";
    return ok ? 0 : 3;
}
