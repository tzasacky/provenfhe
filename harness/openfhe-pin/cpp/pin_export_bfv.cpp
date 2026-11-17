// pin_export_bfv.cpp -- UNTRUSTED. Runs one OpenFHE BFV program (CryptoContextBFVRNS) under the
// deterministic pin_prng engine and writes one BFV case directory of the openfhe-pin harness
// (harness/openfhe-pin/FORMAT.md, "BFV cases"): params.json, trace.jsonl, pin.json, polys.txt.
//
//   pin_export_bfv <outdir> --seed S [--n N] [--depth D] [--progdepth K] [--t T]
//        [--mult HPS|HPSPOVERQ|HPSPOVERQLEVELED|BEHZ|default] [--ks HYBRID|BV|default]
//        [--enc STANDARD|EXTENDED|default] [--qbits B] [--dnum K] [--digitsize W] [--batch S]
//        [--evaladd A] [--kscount K] [--skdist UNIFORM_TERNARY|GAUSSIAN|SPARSE_TERNARY]
//        [--prog NAME] [--msg random|small|max|zero] [--len K] [--menu core|all] [--towers K]
//        [--prng /abs/libpin_prng.so] [--floatfacts FILE]
//
//   "default" never calls the setter (OpenFHE v1.6.1 BFVRNS defaults: HPSPOVERQLEVELED, BV with
//   digit size 0, STANDARD, 60-bit primes; gen-cryptocontext-params-defaults.h:92-126).
//   --n given  => SetRingDim(n) + HEStd_NotSet; absent => OpenFHE picks the secure ring dimension
//                 (HEStd_128_classic) and nothing but depth and t (and what else is given) is set.
//   --depth    SetMultiplicativeDepth; --progdepth: the program's own depth (default: --depth).
//   --prog     chain       a*b, then EvalMult(x, x) progdepth-1 times
//              square      EvalSquare(a), progdepth times in total
//              dot         a*b + rot(a*b, 1) + c
//              rot         rot(a, 1) + b
//              rotsum      s = a*b; s += rot(s,1); s += rot(s,2); s - rot(a,-1)
//              plain       ((a*b)*p1 + p2) - p3
//              addsub      add, sub, negate, EvalAdd/EvalSub with a plaintext in both orders, in-place forms
//              mixadd      Relinearize(EvalMultNoRelin(a,b) + c) and c - EvalMultNoRelin(a,b): an
//                          unrelinearised product combined with a 2-part ciphertext (refused by the extractor)
//              norelin     Relinearize(EvalMultNoRelin(a,b) + EvalMultNoRelin(a,c)), then EvalSquare
//              norelin2    Relinearize(-(ab - ac) + bc) with unrelinearised products ab, ac, bc, then EvalSquare
//              compress    Compress(a*b, k), Compress(c, k), a product / sum, a plaintext operand and a
//                          fresh encryption at the lower level, a rotation there (k: --towers, default L-1)
//              levels      a chain of progdepth products with a rotation after each: under HPSPOVERQLEVELED
//                          the products (from noiseScaleDeg 3 on) and the rotation key switches (from
//                          noiseScaleDeg 4..6 on) drop limbs internally (the traced levelsDropped)
//              ops         every mapped operation once
//              random      --len seeded random operations (--menu core: operations extract_bfv.py maps;
//                          all: also EvalSub(pt, ct), products with a 3-part operand, Compress at will)
//              coefpacked  MakeCoefPackedPlaintext inputs and plaintext operands (refused by the extractor)
//              innerprod symenc threepart nocheck coefpk      the refusal programs of bfv_demo
//              advplain:<v>  advmul:<v>                       adversarial inputs (see pin_adv_bfv.h)
//   --msg      random  packed, N uniform slots          small  packed, 8 slots in [-8, 8]
//              max     packed, the slots whose encoded polynomial has EVERY coefficient t-1
//              zero    packed, all slots 0
//   An OpenFHE exception inside a program step is caught and recorded in pin.json "notes"
//   ("EXC <step>: <message>"); the run continues and the case is still dumped.
//   Exit status: 0 = dumped; 2 = usage; 1 = the exporter itself failed (no valid dump; e.g.
//   GenCryptoContext threw: the message is printed).
#include "pin_dump_bfv.h"

#include <libgen.h>
#include <unistd.h>

#include <cstring>
#include <cstdlib>
#include <functional>
#include <iostream>

using namespace lbcrypto;
using Ct = Ciphertext<DCRTPoly>;

struct Rng {  // the program generator's own stream (independent of OpenFHE's PRNG)
    uint64_t s;
    uint64_t next() {
        uint64_t z = (s += 0x9E3779B97F4A7C15ULL);
        z          = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z          = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        return z ^ (z >> 31);
    }
    uint64_t below(uint64_t n) { return next() % n; }
};

static std::string cleanMsg(std::string m) {
    // drop absolute source paths from OpenFHE exception texts ("/abs/.../src/pke/lib/x.cpp:l:f(): msg")
    size_t i = 0;
    std::string r;
    while (i < m.size()) {
        if (m[i] == '/' && (i == 0 || m[i - 1] == ' ' || m[i - 1] == '(' || m[i - 1] == '\n')) {
            size_t e = i;
            while (e < m.size() && m[e] != ' ' && m[e] != ':' && m[e] != ')' && m[e] != '\n') e++;
            std::string tok = m.substr(i, e - i);
            size_t k = tok.rfind("/src/");
            if (k == std::string::npos) k = tok.rfind("/include/");
            r += k == std::string::npos ? tok.substr(tok.rfind('/') + 1) : tok.substr(k + 1);
            i = e;
        }
        else
            r += m[i++];
    }
    return r;
}

struct Run {
    CryptoContext<DCRTPoly> cc;
    std::shared_ptr<CryptoParametersBFVRNS> cp;
    pin::CaseBfv* c;
    std::shared_ptr<pin::Tracer> tr;
    uint64_t t;
    uint32_t N, L, depth;  // depth: the program's
    std::string msg;
    bool menuAll;
    Rng rng;
    Ct last;

    bool poverq() const {
        auto m = cp->GetMultiplicationTechnique();
        return m == HPSPOVERQ || m == HPSPOVERQLEVELED;
    }
    bool canCompress() const { return poverq() && cp->GetEncryptionTechnique() == STANDARD; }

    // ---- plaintexts -------------------------------------------------------------------------
    // The packed plaintext whose STORED polynomial is exactly `coeffs` (values in [0, t)): the
    // slots are found by decoding that polynomial with OpenFHE's PackedEncoding::Decode, and the
    // encoded result is asserted. Needs t = 1 mod 2N (else MakePackedPlaintext itself throws).
    Plaintext packedOfPoly(const std::vector<uint64_t>& coeffs, uint32_t level = 0) {
        pin::detach(cc);
        Plaintext p0 = cc->MakePackedPlaintext(std::vector<int64_t>{0}, 1, level);
        DCRTPoly d(p0->GetElement<DCRTPoly>().GetParams(), Format::COEFFICIENT, true);
        for (size_t l = 0; l < d.GetNumOfElements(); l++) {
            NativePoly z = d.GetElementAtIndex(l);
            for (size_t i = 0; i < N; i++) z[i] = coeffs[i];
            d.SetElementAtIndex(l, std::move(z));
        }
        p0->GetElement<DCRTPoly>() = d;
        p0->Decode();
        std::vector<int64_t> slots = p0->GetPackedValue();
        pin::attach(cc, tr);
        Plaintext p = cc->MakePackedPlaintext(slots, 1, level);
        DCRTPoly e  = p->GetElement<DCRTPoly>();
        e.SetFormat(Format::COEFFICIENT);
        for (size_t l = 0; l < e.GetNumOfElements(); l++)
            for (size_t i = 0; i < N; i++)
                if (e.GetElementAtIndex(l)[i].ConvertToInt() != coeffs[i])
                    throw std::runtime_error("packedOfPoly: encoded polynomial differs from the requested one");
        return p;
    }
    Plaintext mkKind(const std::string& kind, uint32_t level = 0) {
        int64_t h = (int64_t)(t / 2);
        if (kind == "random") {
            std::vector<int64_t> v(N);
            for (auto& x : v) {
                uint64_t r = rng.below(t);
                x          = r > t / 2 ? (int64_t)r - (int64_t)t : (int64_t)r;
            }
            return cc->MakePackedPlaintext(v, 1, level);
        }
        if (kind == "small") {
            std::vector<int64_t> v(std::min<uint32_t>(8, N));
            for (auto& x : v) x = (int64_t)rng.below(17) - 8;
            return cc->MakePackedPlaintext(v, 1, level);
        }
        if (kind == "zero") return cc->MakePackedPlaintext(std::vector<int64_t>{0}, 1, level);
        if (kind == "max") return packedOfPoly(std::vector<uint64_t>(N, t - 1), level);
        if (kind == "coefrandom") {
            std::vector<int64_t> v(N);
            for (auto& x : v) x = (int64_t)rng.below(2 * h + 1) - h;
            return cc->MakeCoefPackedPlaintext(v, 1, level);
        }
        throw std::runtime_error("unknown --msg " + kind);
    }
    Plaintext mk(uint32_t level = 0) { return mkKind(msg, level); }
    Ct enc(Plaintext p) { return last = c->encrypt(tr, p); }
    Ct fresh() { return enc(mk()); }

    // ---- guarded steps ----------------------------------------------------------------------
    Ct T(const std::string& step, std::initializer_list<Ct> operands, const std::function<Ct()>& f) {
        for (auto& o : operands)
            if (!o) {
                c->note("SKIP " + step + ": an operand is missing (an earlier step threw)");
                return nullptr;
            }
        try {
            Ct r = f();
            if (r) last = r;
            return r;
        }
        catch (const std::exception& e) {
            c->note("EXC " + step + ": " + cleanMsg(e.what()));
            return nullptr;
        }
    }
    Plaintext P(const std::string& step, const std::function<Plaintext()>& f) {
        try {
            return f();
        }
        catch (const std::exception& e) {
            c->note("EXC " + step + ": " + cleanMsg(e.what()));
            return nullptr;
        }
    }
    Ct mul(Ct a, Ct b) { return T("EvalMult(ct,ct)", {a, b}, [&] { return cc->EvalMult(a, b); }); }
    Ct sq(Ct a) { return T("EvalSquare", {a}, [&] { return cc->EvalSquare(a); }); }
    Ct mulNR(Ct a, Ct b) { return T("EvalMultNoRelin", {a, b}, [&] { return cc->EvalMultNoRelin(a, b); }); }
    Ct relin(Ct a) { return T("Relinearize", {a}, [&] { return cc->Relinearize(a); }); }
    Ct add(Ct a, Ct b) { return T("EvalAdd(ct,ct)", {a, b}, [&] { return cc->EvalAdd(a, b); }); }
    Ct sub(Ct a, Ct b) { return T("EvalSub(ct,ct)", {a, b}, [&] { return cc->EvalSub(a, b); }); }
    Ct neg(Ct a) { return T("EvalNegate", {a}, [&] { return cc->EvalNegate(a); }); }
    Ct rot(Ct a, int k) { return T("EvalRotate " + std::to_string(k), {a}, [&] { return cc->EvalRotate(a, k); }); }
    Ct atIndex(Ct a, int k) { return T("EvalAtIndex " + std::to_string(k), {a}, [&] { return cc->EvalAtIndex(a, k); }); }
    Ct addp(Ct a, Plaintext p) { return !p ? nullptr : T("EvalAdd(ct,pt)", {a}, [&] { return cc->EvalAdd(a, p); }); }
    Ct subp(Ct a, Plaintext p) { return !p ? nullptr : T("EvalSub(ct,pt)", {a}, [&] { return cc->EvalSub(a, p); }); }
    Ct mulp(Ct a, Plaintext p) { return !p ? nullptr : T("EvalMult(ct,pt)", {a}, [&] { return cc->EvalMult(a, p); }); }
    Ct compress(Ct a, size_t k) {
        return T("Compress to " + std::to_string(k), {a}, [&] { return cc->Compress(a, k); });
    }
    static size_t towers(const Ct& x) { return x->GetElements()[0].GetNumOfElements(); }
    static size_t parts(const Ct& x) { return x->NumberCiphertextElements(); }
};

static std::string exeDir(const char* argv0) {
    char buf[4096];
    ssize_t n = readlink("/proc/self/exe", buf, sizeof buf - 1);
    std::string exe = n > 0 ? std::string(buf, n) : std::string(argv0);
    std::vector<char> tmp(exe.begin(), exe.end());
    tmp.push_back(0);
    return std::string(dirname(tmp.data()));
}

// ---------------------------------------------------------------------------------------------
// programs
// ---------------------------------------------------------------------------------------------
static std::vector<Ct> progBasic(Run& R, const std::string& prog, uint32_t batch, uint32_t towersOpt) {
    auto& cc = R.cc;
    const auto& kp = R.c->keys();
    if (prog == "coefpk") {
        // y = Encrypt(MakeCoefPackedPlaintext(a)) + Encrypt(MakeCoefPackedPlaintext(b)) (refused)
        Ct a = R.enc(R.mkKind("coefrandom")), b = R.enc(R.mkKind("coefrandom"));
        return {R.add(a, b)};
    }
    Ct ca = R.fresh(), cb = R.fresh();
    Ct cc3;
    if (prog == "symenc") cc3 = R.last = R.c->encryptSecret(R.tr, R.mk());
    else cc3 = R.fresh();
    Ct res;
    if (prog == "chain") {
        res = R.mul(ca, cb);
        for (uint32_t d = 1; d < R.depth; d++) res = R.mul(res, res);
    }
    else if (prog == "square") {
        res = R.sq(ca);
        for (uint32_t d = 1; d < R.depth; d++) res = R.sq(res);
        res = R.add(res, cb);
    }
    else if (prog == "dot") {
        auto p = R.mul(ca, cb);
        auto r = R.rot(p, 1);
        res    = R.add(p, r);
        res    = R.add(res, cc3);
    }
    else if (prog == "rot") {
        res = R.rot(ca, 1);
        res = R.add(res, cb);
    }
    else if (prog == "rotsum") {
        auto s = R.mul(ca, cb);
        s      = R.add(s, R.atIndex(s, 1));
        s      = R.add(s, R.rot(s, 2));
        res    = R.sub(s, R.atIndex(ca, -1));
    }
    else if (prog == "plain") {
        res = R.mul(ca, cb);
        Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
        res = R.mulp(res, p1);
        res = R.addp(res, p2);
        res = R.subp(res, p3);
    }
    else if (prog == "addsub") {
        Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
        Ct x1 = R.add(ca, cb);
        Ct x2 = R.sub(x1, cc3);
        Ct x3 = R.neg(x2);
        Ct x4 = R.addp(x3, p1);
        Ct x5 = R.T("EvalAdd(pt,ct)", {x4}, [&] { return cc->EvalAdd(p2, x4); });
        Ct x6 = R.subp(x5, p3);
        Ct x7 = R.T("EvalSub(pt,ct)", {x6}, [&] { return cc->EvalSub(p1, x6); });
        Ct x8 = x7 ? x7->Clone() : nullptr;
        R.T("EvalAddInPlace(ct,ct)", {x8}, [&] { cc->EvalAddInPlace(x8, ca); return x8; });
        R.T("EvalSubInPlace(ct,ct)", {x8}, [&] { cc->EvalSubInPlace(x8, cb); return x8; });
        R.T("EvalAddInPlace(ct,pt)", {x8}, [&] { cc->EvalAddInPlace(x8, p2); return x8; });
        R.T("EvalSubInPlace(ct,pt)", {x8}, [&] { cc->EvalSubInPlace(x8, p3); return x8; });
        R.T("EvalNegateInPlace", {x8}, [&] { cc->EvalNegateInPlace(x8); return x8; });
        res = R.add(x8, x1);
    }
    else if (prog == "norelin") {
        auto p = R.mulNR(ca, cb);
        auto q = R.mulNR(ca, cc3);
        res    = R.add(p, q);
        res    = R.relin(res);
        if (R.depth >= 2) res = R.sq(res);
    }
    else if (prog == "norelin2") {
        // operations on unrelinearised products that extract_bfv.py maps (PRODUCT_RULE): sum,
        // difference and negation of such products, then relinearization
        auto p = R.mulNR(ca, cb);
        auto q = R.mulNR(ca, cc3);
        auto r = R.mulNR(cb, cc3);
        res    = R.relin(R.add(R.neg(R.sub(p, q)), r));
        if (R.depth >= 2) res = R.sq(res);
    }
    else if (prog == "mixadd") {
        // EvalAdd / EvalSub of an unrelinearised 3-part product with a 2-part ciphertext (a combination
        // extract_bfv.py refuses: the refusal is tested on these cases)
        auto n = R.mulNR(ca, cb);
        auto x = R.add(n, cc3);
        auto y = R.sub(cc3, n);
        res    = R.relin(x);
        // optional (PIN_CLEARTEXT_NOTES=1, never for the committed fixtures): compare OpenFHE's own
        // decryption with the cleartext computation and record the counts in pin.json notes
        const char* ctn = std::getenv("PIN_CLEARTEXT_NOTES");
        if (ctn && std::string(ctn) == "1") {
        pin::detach(cc);
        auto slotsOf = [&](const Ct& z) {
            Plaintext p;
            cc->Decrypt(R.c->keys().secretKey, z, &p);
            return p->GetPackedValue();
        };
        auto mod = [&](int64_t v) { int64_t r = v % (int64_t)R.t; return r < 0 ? r + (int64_t)R.t : r; };
        std::vector<int64_t> va = slotsOf(ca), vb = slotsOf(cb), vc = slotsOf(cc3);
        auto check = [&](const std::string& what, const Ct& z, int sgn) {
            if (!z) return;
            std::vector<int64_t> got = slotsOf(z);
            size_t bad = 0;
            for (size_t i = 0; i < got.size() && i < va.size(); i++) {
                __int128 ab = (__int128)mod(va[i]) * mod(vb[i]) % R.t;
                int64_t want = mod(sgn > 0 ? (int64_t)ab + vc[i] : sgn < 0 ? vc[i] - (int64_t)ab : (int64_t)ab);
                bad += mod(got[i]) != want;
            }
            R.c->note("mixadd: cleartext check of cc->Decrypt(" + what + "): " + std::to_string(bad) + " of " +
                      std::to_string(got.size()) + " slots differ from " + (sgn > 0 ? "a*b + c" : sgn < 0 ? "c - a*b" : "a*b") +
                      " mod t (slots of a, b, c from cc->Decrypt of the fresh inputs)");
        };
        check("EvalAdd(EvalMultNoRelin(a,b), c)", x, 1);
        check("EvalSub(c, EvalMultNoRelin(a,b))", y, -1);
        check("Relinearize(EvalAdd(EvalMultNoRelin(a,b), c))", res, 1);
        check("EvalMultNoRelin(a,b) (control, no addition)", n, 0);
        pin::attach(cc, R.tr);
        }
    }
    else if (prog == "neg") {
        res = R.neg(R.mul(ca, cb));
        res = R.add(res, R.neg(cc3));
    }
    else if (prog == "compress") {
        // BFV Compress exists for the HPSPOVERQ* techniques with STANDARD encryption only
        // (bfvrns-leveledshe.cpp:956-966); elsewhere the exception is recorded.
        size_t L = R.L;
        size_t k = towersOpt ? towersOpt : (L > 2 ? L - 1 : 1);
        auto x   = R.mul(ca, cb);
        auto p   = R.compress(x, k);
        auto c2  = R.compress(cc3, k);
        res      = R.depth >= 2 && k >= 2 ? R.mul(p, c2) : R.add(p, c2);
        if (res && k < L) {
            // operands made at the lower level: a plaintext with k limbs, and a fresh encryption of one
            Plaintext pl = R.P("MakePackedPlaintext at level " + std::to_string(L - k), [&] { return R.mk(L - k); });
            Plaintext pe = R.P("MakePackedPlaintext at level " + std::to_string(L - k), [&] { return R.mk(L - k); });
            Ct y = R.addp(res, pl);
            if (y) res = y;
            if (pe) {
                Ct f = R.T("Encrypt(pt at lower level)", {}, [&] { return R.enc(pe); });
                Ct z = R.add(res, f);
                if (z) res = z;
            }
            Ct r = R.rot(res, 1);
            Ct w = R.sub(res, r);
            if (w) res = w;
            if (R.depth >= 3 && pl) {
                Ct m = R.mulp(res, pl);
                if (m) res = m;
            }
        }
        if (!res) res = p ? p : x;
    }
    else if (prog == "levels") {
        // FindLevelsToDrop grows with the noiseScaleDeg of the operand (levels = nsd - 1): products
        // drop limbs from nsd 3 on, rotation key switches from nsd 4..6 on, depending on the context
        Ct r0 = R.rot(ca, 1);              // key switch of a fresh ciphertext (nsd 1)
        Ct y  = R.mul(ca, cb);             // nsd 2
        for (uint32_t d = 1; d < R.depth; d++) {
            Ct rr = R.rot(y, d % 2 ? 1 : -1);  // key switch at nsd d + 1
            Ct z  = R.add(y, rr);
            if (z) y = z;
            y = d % 2 ? R.mul(y, y) : R.sq(y);
        }
        Ct rl2 = R.atIndex(y, 2);          // key switch at the last nsd
        y      = R.add(y, rl2);
        y      = R.add(y, r0);
        Ct n  = R.mulNR(cb, cc3);          // Relinearize called by the user: no internal drop
        Ct rl = R.relin(n);
        res   = R.add(y, rl);
    }
    else if (prog == "innerprod") {
        res = R.T("EvalInnerProduct", {ca, cb}, [&] { return cc->EvalInnerProduct(ca, cb, batch); });
    }
    else if (prog == "symenc") {
        res = R.add(R.mul(ca, cb), cc3);
    }
    else if (prog == "threepart") {
        // EvalMult(EvalMultNoRelin(a, b), c): the relinearization of the 4-part product key-switches
        // only cv[2] and drops cv[3] (refused)
        Ct n = R.mulNR(ca, cb);
        res  = R.T("EvalMult(3-part,2-part)", {n, cc3}, [&] { return cc->EvalMult(n, cc3); });
    }
    else if (prog == "nocheck") {
        Ct n = R.T("EvalMultNoRelinNoCheck", {ca, cb}, [&] { return cc->EvalMultNoRelinNoCheck(ca, cb); });
        res  = R.relin(n);
    }
    else if (prog == "coefpacked") {
        throw std::runtime_error("internal: coefpacked is handled by progCoef");
    }
    else
        throw std::runtime_error("unknown prog " + prog);
    (void)kp;
    return {res ? res : R.last};
}

static std::vector<Ct> progCoef(Run& R) {
    std::string saved = R.msg;
    R.msg = "coefrandom";
    Ct a = R.fresh(), b = R.fresh();
    Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
    Ct x = R.mul(a, b);
    Ct y = R.addp(x, p1);
    Ct res = y;
    if (R.depth >= 2) {
        Ct z = R.mulp(y, p2);
        res  = R.subp(z, p3);
    }
    R.msg = saved;
    return {res ? res : R.last};
}

// Every mapped operation once.
static std::vector<Ct> progOps(Run& R) {
    auto& cc = R.cc;
    Ct a = R.fresh(), b = R.fresh(), c = R.fresh();
    Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
    Ct x1 = R.add(a, b);
    Ct x2 = R.sub(x1, c);
    Ct x3 = R.neg(x2);
    Ct x4 = R.addp(x3, p1);
    Ct x5 = R.subp(x4, p2);
    Ct x6 = R.mulp(x5, p3);
    Ct n1 = R.mulNR(a, b);
    Ct n2 = R.mulNR(b, c);
    Ct n3 = R.add(n1, n2);                 // 3 parts + 3 parts
    Ct n4 = R.sub(n3, a);                  // 3 parts - 2 parts
    Ct r  = R.relin(n4);
    Ct n5 = n1 ? n1->Clone() : nullptr;
    R.T("RelinearizeInPlace", {n5}, [&] { cc->RelinearizeInPlace(n5); return n5; });
    r = R.add(r, n5);
    Ct r1 = R.rot(r, 1);
    Ct r2 = R.atIndex(r, -1);
    Ct r3 = R.rot(r, 2);
    Ct r4;
    try {
        auto& am     = CryptoContextImpl<DCRTPoly>::GetEvalAutomorphismKeyMap(R.c->keys().secretKey->GetKeyTag());
        uint32_t idx = am.rbegin()->first;
        r4 = R.T("EvalAutomorphism " + std::to_string(idx), {r}, [&] { return cc->EvalAutomorphism(r, idx, am); });
    }
    catch (const std::exception& e) {
        R.c->note(std::string("EXC GetEvalAutomorphismKeyMap: ") + cleanMsg(e.what()));
    }
    Ct y = R.add(r1, r2);
    y    = R.sub(y, r3);
    y    = R.add(y, r4);
    Ct res;
    if (R.depth >= 2) {
        Ct m  = R.mul(y, c);
        Ct s2 = R.sq(a);
        res   = R.add(m, s2);
    }
    else
        res = R.add(y, c);
    res = R.add(res, x6);
    if (R.canCompress() && R.L >= 2) {
        Ct z  = R.compress(res, R.L - 1);
        Ct c2 = R.compress(c, R.L - 1);
        Ct w  = R.add(z, c2);
        if (w) res = w;
    }
    return {res ? res : R.last};
}

// A seeded random straight-line program.
static std::vector<Ct> progRandom(Run& R, uint32_t len) {
    auto& cc = R.cc;
    struct V { Ct ct; uint32_t d; };  // d: multiplicative depth consumed (a plaintext product counts as one)
    std::vector<V> pool;
    std::vector<Plaintext> pts;
    uint32_t nIn = 2 + R.rng.below(3);
    for (uint32_t i = 0; i < nIn; i++) pool.push_back({R.fresh(), 0});
    for (uint32_t i = 0; i < 2; i++) pts.push_back(R.mk());
    Ct fin = pool.back().ct;
    auto& am = CryptoContextImpl<DCRTPoly>::GetEvalAutomorphismKeyMap(R.c->keys().secretKey->GetKeyTag());
    static const int rots[] = {1, 2, -1, -2};
    auto pick = [&]() -> V& { return pool[R.rng.below(pool.size())]; };
    auto pickP = [&](V*& out, size_t np, size_t tw) {  // a value with np parts (and tw towers, 0 = any)
        for (int k = 0; k < 24; k++) {
            V& v = pick();
            if (Run::parts(v.ct) == np && (!tw || Run::towers(v.ct) == tw)) { out = &v; return true; }
        }
        return false;
    };
    auto canMul = [&](const V& v) { return v.d + 1 <= R.depth; };
    for (uint32_t i = 0; i < len; i++) {
        uint32_t op = R.rng.below(32);
        std::string step = "random#" + std::to_string(i);
        Ct out;
        uint32_t d = 0;
        try {
            V* pa = nullptr; V* pb = nullptr;
            if (op < 6) {  // add / sub of ciphertexts with the same number of limbs (any number of parts)
                V va = pick();
                bool ok = false;
                V vb;
                for (int k = 0; k < 24 && !ok; k++) { vb = pick(); ok = Run::towers(vb.ct) == Run::towers(va.ct); }
                if (!ok) continue;
                step += op < 3 ? " EvalAdd" : " EvalSub";
                out = op < 3 ? cc->EvalAdd(va.ct, vb.ct) : cc->EvalSub(va.ct, vb.ct);
                d   = std::max(va.d, vb.d);
            }
            else if (op < 7) {
                V va = pick();
                step += " EvalNegate";
                out = cc->EvalNegate(va.ct);
                d   = va.d;
            }
            else if (op < 10) {  // plaintext add / sub (plaintext made at the ciphertext's number of limbs)
                V va = pick();
                size_t tw = Run::towers(va.ct);
                Plaintext p = tw == R.L ? (R.rng.below(3) ? pts[R.rng.below(pts.size())] : R.mk()) : R.mk(R.L - tw);
                if (op == 7) { step += " EvalAdd(ct,pt)"; out = cc->EvalAdd(va.ct, p); }
                else if (op == 8) { step += " EvalSub(ct,pt)"; out = cc->EvalSub(va.ct, p); }
                else if (!R.menuAll) { step += " EvalAdd(pt,ct)"; out = cc->EvalAdd(p, va.ct); }
                else { step += " EvalSub(pt,ct)"; out = cc->EvalSub(p, va.ct); }
                d = va.d;
            }
            else if (op < 12) {  // plaintext product
                if (!pickP(pa, 2, 0) || !canMul(*pa)) continue;
                V va = *pa;
                size_t tw = Run::towers(va.ct);
                Plaintext p = tw == R.L ? (R.rng.below(2) ? pts[R.rng.below(pts.size())] : R.mk()) : R.mk(R.L - tw);
                step += " EvalMult(ct,pt)";
                out = cc->EvalMult(va.ct, p);
                d   = va.d + 1;
            }
            else if (op < 16) {  // product with relinearization
                if (!pickP(pa, 2, 0) || !pickP(pb, 2, Run::towers(pa->ct)) || !canMul(*pa) || !canMul(*pb)) continue;
                V va = *pa, vb = *pb;
                step += " EvalMult";
                out = cc->EvalMult(va.ct, vb.ct);
                d   = std::max(va.d, vb.d) + 1;
            }
            else if (op < 18) {
                if (!pickP(pa, 2, 0) || !canMul(*pa)) continue;
                V va = *pa;
                step += " EvalSquare";
                out = cc->EvalSquare(va.ct);
                d   = va.d + 1;
            }
            else if (op < 20) {  // product without relinearization
                if (!pickP(pa, 2, 0) || !pickP(pb, 2, Run::towers(pa->ct)) || !canMul(*pa) || !canMul(*pb)) continue;
                V va = *pa, vb = *pb;
                step += " EvalMultNoRelin";
                out = cc->EvalMultNoRelin(va.ct, vb.ct);
                d   = std::max(va.d, vb.d) + 1;
            }
            else if (op < 22) {  // relinearize a 3-part value
                V* p3 = nullptr;
                for (auto& v : pool) if (Run::parts(v.ct) == 3) p3 = &v;
                if (!p3) continue;
                V va = *p3;
                step += " Relinearize";
                out = cc->Relinearize(va.ct);
                d   = va.d;
            }
            else if (op < 27) {  // rotations
                if (!pickP(pa, 2, 0)) continue;
                V va = *pa;
                int k = rots[R.rng.below(4)];
                uint32_t w = R.rng.below(3);
                if (w == 0) { step += " EvalRotate " + std::to_string(k); out = cc->EvalRotate(va.ct, k); }
                else if (w == 1) { step += " EvalAtIndex " + std::to_string(k); out = cc->EvalAtIndex(va.ct, k); }
                else {
                    auto it = am.begin();
                    std::advance(it, R.rng.below(am.size()));
                    step += " EvalAutomorphism " + std::to_string(it->first);
                    out = cc->EvalAutomorphism(va.ct, it->first, am);
                }
                d = va.d;
            }
            else if (op < 29) {  // in-place variants
                V va = pick();
                bool ok = false;
                V vb;
                for (int k = 0; k < 24 && !ok; k++) { vb = pick(); ok = Run::towers(vb.ct) == Run::towers(va.ct); }
                if (!ok) continue;
                Ct x = va.ct->Clone();
                uint32_t w = R.rng.below(3);
                if (w == 0) { step += " EvalAddInPlace"; cc->EvalAddInPlace(x, vb.ct); }
                else if (w == 1) { step += " EvalSubInPlace"; cc->EvalSubInPlace(x, vb.ct); }
                else { step += " EvalNegateInPlace"; cc->EvalNegateInPlace(x); }
                out = x;
                d   = std::max(va.d, vb.d);
            }
            else if (op < 31) {  // Compress (P-over-Q techniques with STANDARD encryption; menu all: anywhere)
                if (!R.menuAll && !R.canCompress()) continue;
                if (!pickP(pa, 2, 0)) continue;
                V va = *pa;
                size_t tw = Run::towers(va.ct);
                if (tw < 2) continue;
                step += " Compress to " + std::to_string(tw - 1);
                out = cc->Compress(va.ct, tw - 1);
                d   = va.d;
            }
            else {  // EvalMult on a 3-part operand (refused by the extractor)
                V* p3 = nullptr;
                for (auto& v : pool) if (Run::parts(v.ct) == 3) p3 = &v;
                if (!R.menuAll || !p3 || !pickP(pb, 2, Run::towers(p3->ct)) || !canMul(*p3) || !canMul(*pb)) continue;
                V va = *p3, vb = *pb;
                step += " EvalMultNoRelin(3-part,2-part)";
                out = cc->EvalMultNoRelin(va.ct, vb.ct);
                d   = std::max(va.d, vb.d) + 1;
            }
        }
        catch (const std::exception& e) {
            R.c->note("EXC " + step + ": " + cleanMsg(e.what()));
            continue;
        }
        if (!out) continue;
        pool.push_back({out, d});
        fin = out;
        if (pool.size() > 10) pool.erase(pool.begin() + R.rng.below(pool.size() - 1));
    }
    return {fin};
}

#include "pin_adv_bfv.h"

// ---------------------------------------------------------------------------------------------
int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "usage: pin_export_bfv <outdir> --seed S [opts]  (see the header of pin_export_bfv.cpp)\n";
        return 2;
    }
    std::string out = argv[1];
    uint32_t depth = 2, dnum = 0, n = 0, qbits = 0, batch = 0, digitsize = 0, pd = 0, len = 12, evaladd = 0,
             kscount = 0, towersOpt = 0;
    uint64_t t = 65537, seed = 1;
    bool haveSeed = false;
    std::string mult = "default", ks = "default", enc = "default", prog = "chain", msg = "small", menu = "core",
                skdist, so = exeDir(argv[0]) + "/libpin_prng.so", ff = exeDir(argv[0]) + "/float_facts.json";
    std::string cmdline;
    for (int i = 2; i + 1 < argc; i += 2) {
        std::string k = argv[i], v = argv[i + 1];
        if (k != "--prng" && k != "--floatfacts") cmdline += std::string(cmdline.empty() ? "" : " ") + k + " " + v;
        if (k == "--depth") depth = std::stoul(v);
        else if (k == "--progdepth") pd = std::stoul(v);
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
        else if (k == "--evaladd") evaladd = std::stoul(v);
        else if (k == "--kscount") kscount = std::stoul(v);
        else if (k == "--towers") towersOpt = std::stoul(v);
        else if (k == "--seed") { seed = std::stoull(v); haveSeed = true; }
        else if (k == "--msg") msg = v;
        else if (k == "--len") len = std::stoul(v);
        else if (k == "--menu") menu = v;
        else if (k == "--skdist") skdist = v;
        else if (k == "--prng") so = v;
        else if (k == "--floatfacts") ff = v;
        else { std::cerr << "unknown option " << k << "\n"; return 2; }
    }
    if ((argc - 2) % 2) { std::cerr << "options come in pairs\n"; return 2; }
    if (!haveSeed) { std::cerr << "--seed is required\n"; return 2; }
    if (prog == "innerprod" && !batch) batch = 8;
    if (!pd) pd = depth;

    try {
        pin::Prng::init(so);
        pin::Prng::seed(seed);

        CCParams<CryptoContextBFVRNS> params;
        params.SetMultiplicativeDepth(depth);
        params.SetPlaintextModulus(t);
        if (dnum) params.SetNumLargeDigits(dnum);
        if (digitsize) params.SetDigitSize(digitsize);
        if (qbits) params.SetScalingModSize(qbits);
        if (n) { params.SetRingDim(n); params.SetSecurityLevel(HEStd_NotSet); }
        if (batch) params.SetBatchSize(batch);
        if (evaladd) params.SetEvalAddCount(evaladd);
        if (kscount) params.SetKeySwitchCount(kscount);
        pin::BfvDefaults dflt;
        if (mult == "HPS") params.SetMultiplicationTechnique(HPS);
        else if (mult == "HPSPOVERQ") params.SetMultiplicationTechnique(HPSPOVERQ);
        else if (mult == "HPSPOVERQLEVELED") params.SetMultiplicationTechnique(HPSPOVERQLEVELED);
        else if (mult == "BEHZ") params.SetMultiplicationTechnique(BEHZ);
        else if (mult != "default") { std::cerr << "unknown multiplication technique " << mult << "\n"; return 2; }
        dflt.mult = mult == "default";
        if (ks == "HYBRID") params.SetKeySwitchTechnique(HYBRID);
        else if (ks == "BV") params.SetKeySwitchTechnique(BV);
        else if (ks != "default") { std::cerr << "unknown key-switching technique " << ks << "\n"; return 2; }
        dflt.ks = ks == "default";
        if (enc == "STANDARD") params.SetEncryptionTechnique(STANDARD);
        else if (enc == "EXTENDED") params.SetEncryptionTechnique(EXTENDED);
        else if (enc != "default") { std::cerr << "unknown encryption technique " << enc << "\n"; return 2; }
        dflt.enc = enc == "default";
        if (skdist == "GAUSSIAN") params.SetSecretKeyDist(GAUSSIAN);
        else if (skdist == "SPARSE_TERNARY") params.SetSecretKeyDist(SPARSE_TERNARY);
        else if (skdist == "UNIFORM_TERNARY") params.SetSecretKeyDist(UNIFORM_TERNARY);
        else if (!skdist.empty()) { std::cerr << "unknown --skdist " << skdist << "\n"; return 2; }
        CryptoContext<DCRTPoly> cc = GenCryptoContext(params);
        cc->Enable(PKE);
        cc->Enable(KEYSWITCH);
        cc->Enable(LEVELEDSHE);
        cc->Enable(ADVANCEDSHE);
        auto cp = std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc->GetCryptoParameters());

        { std::ofstream f(out + "/params.json"); f << pin::paramsJson(cc); }

        std::string name = out;
        while (name.size() > 1 && name.back() == '/') name.pop_back();
        name = name.substr(name.find_last_of('/') + 1);
        pin::CaseBfv c(out, name, seed, "pin_export_bfv " + cmdline, cc, dflt);
        c.setFloatFacts(pin::readFile(ff));
        std::string fam = prog.substr(0, prog.find(':'));
        std::string var = prog.find(':') == std::string::npos ? "" : prog.substr(prog.find(':') + 1);
        // the tracer is attached BEFORE KeyGen (key provenance)
        auto tr = std::make_shared<pin::Tracer>(out + "/trace.jsonl");
        pin::attach(cc, tr);
        KeyPair<DCRTPoly> kp = (prog.rfind("advmul:scriptedkey", 0) == 0 || prog == "advmul:handbuiltkey") ? advKeyGen(c, cc, seed) : c.keyGen();
        cc->EvalMultKeyGen(kp.secretKey);
        bool needRot = prog == "dot" || prog == "rot" || prog == "rotsum" || prog == "ops" || prog == "random" ||
                       prog == "compress" || prog == "levels";
        if (needRot) cc->EvalRotateKeyGen(kp.secretKey, {1, 2, -1, -2});
        if (prog == "innerprod") cc->EvalSumKeyGen(kp.secretKey);
        Run R{cc, cp, &c, tr, t, (uint32_t)cc->GetRingDimension(),
              (uint32_t)cp->GetElementParams()->GetParams().size(), pd, msg, menu == "all",
              Rng{seed * 0x2545F4914F6CDD1DULL + 0x1234567}, nullptr};
        std::vector<Ct> fin;
        if (prog == "ops") fin = progOps(R);
        else if (prog == "random") fin = progRandom(R, len);
        else if (prog == "coefpacked") fin = progCoef(R);
        else if (fam == "advplain") fin = advPlain(R, var);
        else if (fam == "advmul") fin = advMul(R, var);
        else fin = progBasic(R, prog, batch, towersOpt);
        pin::detach(cc);
        std::vector<Ct> f2;
        for (auto& x : fin) if (x) f2.push_back(x);
        c.setFinal(f2);
        if (msg == "max")
            c.note("--msg max: packed plaintexts whose encoded polynomial has every coefficient equal to t-1 "
                   "(slots obtained with PackedEncoding::Decode of that polynomial; the encoded result is asserted)");
        // plaintext polynomials as stored: non-packed ones and any with a residue >= t are described
        for (const auto& o : tr->objects()) {
            if (o.isCt) continue;
            std::vector<int64_t> sv;
            DCRTPoly e(o.ptElem);
            e.SetFormat(Format::COEFFICIENT);
            uint64_t mx0 = 0;
            for (size_t i = 0; i < e.GetRingDimension(); i++)
                mx0 = std::max<uint64_t>(mx0, e.GetElementAtIndex(0)[i].ConvertToInt());
            bool small = pin::centredSmall(o.ptElem, sv);
            int64_t mc = 0;
            for (auto x : sv) mc = std::max<int64_t>(mc, std::llabs(x));
            if (o.encoding != "packed" || mx0 >= t)
                c.note("plaintext " + o.id + " (" + o.encoding + "): stored polynomial, limb 0, max canonical residue " +
                       std::to_string(mx0) + (mx0 < t ? " (< t)" : " (>= t)") + "; all limbs one centred integer vector: " +
                       (small ? "yes, max |coefficient| " + std::to_string(mc) : std::string("NO")));
        }
        c.write(tr);
        std::cout << "wrote " << out << "\n";
        return 0;
    }
    catch (const std::exception& e) {
        std::cerr << "pin_export_bfv FAILED: " << cleanMsg(e.what()) << "\n";
        return 1;
    }
}
