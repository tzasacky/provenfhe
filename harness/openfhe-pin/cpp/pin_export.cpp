// pin_export.cpp -- UNTRUSTED. Runs one OpenFHE BGV program under the deterministic pin_prng engine
// and writes one case directory of the openfhe-pin differential-test harness
// (harness/openfhe-pin/FORMAT.md): params.json, trace.jsonl, pin.json, polys.txt.
//
//   pin_export <outdir> --seed S [--n N] [--depth D] [--scal FIXEDMANUAL|FIXEDAUTO|FLEXIBLEAUTO|
//              FLEXIBLEAUTOEXT|default] [--t T] [--dnum K] [--qbits B] [--firstbits B] [--prog NAME]
//              [--msg random|max|alt|witness|small] [--len K] [--batch S] [--evaladd A] [--kscount K]
//              [--skdist UNIFORM_TERNARY|GAUSSIAN|SPARSE_TERNARY] [--prng /abs/libpin_prng.so]
//              [--menu core|all] [--relindeg K]
//   --menu     for --prog random: "core" draws only operations the extractor documents as mapped;
//              "all" (default) adds EvalNegate, EvalSub(pt, ct), EvalFastRotation, the *Mutable
//              variants, EvalNegateInPlace and products with a 3-part operand.
//   --relindeg SetMaxRelinSkDeg(K) and EvalMultKeysGen (keys for s^2..s^K), default OpenFHE's 2.
//
//   --n given  => SetRingDim(n) + HEStd_NotSet; absent => OpenFHE's default (secure) ring dimension.
//   --prog     chain dot rot plain plainlvl lr rotsum innerprod      (the eight of bgv_demo)
//              ops                                                   (every operation once)
//              opsnn                                                 (ops without EvalNegate)
//              random                                                (--len seeded random operations)
//              threepart:{modreduce,mul3x2,mul3x3,square,add3x2,rot,mulplain,autoreduce}
//              paths:{fastrot,multmany,compress,relinearize,mutable,negate,coefpacked,string,evalsum,
//                     ptfirst,multrelin,automorphism,scalar}
//              mixed:{a,b,c,d}                                       (operands at different levels/degrees)
//   --msg      contents of the encrypted inputs and plaintext operands:
//              random   packed encoding, N uniform slots
//              small    packed encoding, 8 slots in [-8, 8]
//              max      packed encoding of the slots whose encoded polynomial has EVERY coefficient
//                       equal to t-1 (the slots are found by decoding that polynomial with OpenFHE's
//                       PackedEncoding::Decode; the result is asserted)
//              alt      coefficient-packed (MakeCoefPackedPlaintext), coefficients +h, -h, +h, ...
//              witness  coefficient-packed, first N/2 coefficients +h, last N/2 -h
//                       (h = floor(t/2), the largest value CoefPackedEncoding accepts)
//   An OpenFHE exception inside a program step is caught and recorded in pin.json "notes"
//   ("EXC <step>: <message>"); the run continues and the case is still dumped.
//   Exit status: 0 = dumped; 2 = usage; 1 = the exporter itself failed (no valid dump).
#include "pin_dump.h"

#include <libgen.h>
#include <unistd.h>

#include <cstring>
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
    // drop absolute source paths from OpenFHE exception texts
    const std::string key = "openfhe-development/";
    for (size_t p = m.find(key); p != std::string::npos; p = m.find(key, p + 1)) {
        size_t b = m.rfind('/', p);
        size_t s = p;
        while (s > 0 && m[s - 1] != ' ' && m[s - 1] != ':' && m[s - 1] != '(' && m[s - 1] != '\n') s--;
        (void)b;
        m.erase(s, p + key.size() - s);
        p = s;
    }
    return m;
}

struct Run {
    CryptoContext<DCRTPoly> cc;
    std::shared_ptr<CryptoParametersBGVRNS> cp;
    pin::Case* c;
    std::shared_ptr<pin::Tracer> tr;
    bool manual;
    uint64_t t;
    uint32_t N, depth;
    std::string msg;
    bool menuAll;
    Rng rng;
    Ct last;  // last successfully produced ciphertext

    // ---- plaintexts -------------------------------------------------------------------------
    Plaintext packedOfPoly(const std::vector<uint64_t>& coeffs, size_t nsd, uint32_t level) {
        pin::detach(cc);
        Plaintext p0 = cc->MakePackedPlaintext(std::vector<int64_t>{0}, nsd, level);
        DCRTPoly d(p0->GetElement<DCRTPoly>().GetParams(), Format::COEFFICIENT, true);
        for (size_t l = 0; l < d.GetNumOfElements(); l++) {
            NativePoly z = d.GetElementAtIndex(l);
            for (size_t i = 0; i < N; i++) z[i] = coeffs[i];
            d.SetElementAtIndex(l, std::move(z));
        }
        p0->GetElement<DCRTPoly>() = d;
        // Decode with factor 1 and divide by the scaling factor modulo t here. (OpenFHE v1.3.1's
        // PackedEncoding::Decode took the inverse of the factor modulo q0, which is only right when
        // q0 > t^2; v1.6.1 takes it modulo t, packedencoding.cpp:199-211. Either way the encoded
        // polynomial of the result is asserted below.)
        uint64_t sf = p0->GetScalingFactorInt().ConvertToInt();
        p0->SetScalingFactorInt(1);
        p0->Decode();
        std::vector<int64_t> slots = p0->GetPackedValue();
        uint64_t sfInv = NativeInteger(sf).ModInverse(NativeInteger(t)).ConvertToInt();
        for (auto& x : slots) {
            uint64_t v = (uint64_t)(x < 0 ? x + (int64_t)t : x);
            v          = (uint64_t)((unsigned __int128)v * sfInv % t);
            x          = v > t / 2 ? (int64_t)v - (int64_t)t : (int64_t)v;
        }
        pin::attach(cc, tr);
        Plaintext p = cc->MakePackedPlaintext(slots, nsd, level);
        DCRTPoly e  = p->GetElement<DCRTPoly>();
        e.SetFormat(Format::COEFFICIENT);
        for (size_t i = 0; i < N; i++)
            if (e.GetElementAtIndex(0)[i].ConvertToInt() != coeffs[i])
                throw std::runtime_error("packedOfPoly: encoded polynomial differs from the requested one");
        return p;
    }
    Plaintext mkKind(const std::string& kind, size_t nsd, uint32_t level) {
        int64_t h = (int64_t)(t / 2);
        if (kind == "random") {
            std::vector<int64_t> v(N);
            for (auto& x : v) {
                uint64_t r = rng.below(t);
                x          = r > t / 2 ? (int64_t)r - (int64_t)t : (int64_t)r;
            }
            return cc->MakePackedPlaintext(v, nsd, level);
        }
        if (kind == "small") {
            std::vector<int64_t> v(8);
            for (auto& x : v) x = (int64_t)rng.below(17) - 8;
            return cc->MakePackedPlaintext(v, nsd, level);
        }
        if (kind == "max") return packedOfPoly(std::vector<uint64_t>(N, t - 1), nsd, level);
        if (kind == "alt" || kind == "witness") {
            std::vector<int64_t> v(N);
            for (size_t i = 0; i < N; i++) v[i] = (kind == "alt" ? (i % 2 == 0) : (i < N / 2)) ? h : -h;
            return cc->MakeCoefPackedPlaintext(v, nsd, level);
        }
        if (kind == "coefrandom") {
            std::vector<int64_t> v(N);
            for (auto& x : v) x = (int64_t)rng.below(2 * h + 1) - h;
            return cc->MakeCoefPackedPlaintext(v, nsd, level);
        }
        throw std::runtime_error("unknown --msg " + kind);
    }
    Plaintext mk() { return mkKind(msg, 1, 0); }
    Plaintext mkAt(const Ct& like) { return mkKind(msg, like->GetNoiseScaleDeg(), like->GetLevel()); }
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
    void MR(Ct& x) {  // ModReduce after a product, FIXEDMANUAL only (as bgv_demo does)
        if (manual && x) {
            try {
                cc->ModReduceInPlace(x);
            }
            catch (const std::exception& e) {
                c->note(std::string("EXC ModReduceInPlace: ") + cleanMsg(e.what()));
            }
        }
    }
    static size_t towers(const Ct& x) { return x->GetElements()[0].GetNumOfElements(); }
    static size_t parts(const Ct& x) { return x->NumberCiphertextElements(); }
};

static std::string soDefault(const char* argv0) {
    char buf[4096];
    ssize_t n = readlink("/proc/self/exe", buf, sizeof buf - 1);
    std::string exe = n > 0 ? std::string(buf, n) : std::string(argv0);
    std::vector<char> tmp(exe.begin(), exe.end());
    tmp.push_back(0);
    return std::string(dirname(tmp.data())) + "/libpin_prng.so";
}

// ---------------------------------------------------------------------------------------------
// programs
// ---------------------------------------------------------------------------------------------
static std::vector<Ct> progBasic(Run& R, const std::string& prog, uint32_t batch) {
    auto& cc = R.cc;
    Ct ca = R.fresh(), cb = R.fresh(), cc3 = R.fresh();
    Ct res;
    if (prog == "chain") {
        res = cc->EvalMult(ca, cb);
        R.MR(res);
        for (uint32_t d = 1; d < R.depth; d++) {
            res = cc->EvalSquare(res);
            R.MR(res);
        }
    }
    else if (prog == "dot") {
        auto p = cc->EvalMult(ca, cb);
        auto r = cc->EvalRotate(p, 1);
        res    = cc->EvalAdd(p, r);
        R.MR(res);
        if (R.manual) {
            // bgv_demo adds the fresh c after the ModReduce, which OpenFHE refuses under FIXEDMANUAL
            // unless the towers agree: bring c down first
            cc3 = cc->LevelReduce(cc3, nullptr, 1);
        }
        res = cc->EvalAdd(res, cc3);
    }
    else if (prog == "rot") {
        res = cc->EvalRotate(ca, 1);
        res = cc->EvalAdd(res, cb);
    }
    else if (prog == "plain" || prog == "plainlvl") {
        bool lvl = prog == "plainlvl";
        res      = cc->EvalMult(ca, cb);
        R.MR(res);
        Plaintext p1 = lvl ? R.mkAt(res) : R.mk();
        res          = cc->EvalMult(res, p1);
        R.MR(res);
        Plaintext p2 = lvl ? R.mkAt(res) : R.mk();
        res          = cc->EvalAdd(res, p2);
        Plaintext p3 = lvl ? R.mkAt(res) : R.mk();
        res          = cc->EvalSub(res, p3);
    }
    else if (prog == "lr") {
        res = cc->EvalMult(ca, cb);
        R.MR(res);
        auto c2 = cc->LevelReduce(cc3, nullptr, 1);
        res     = cc->EvalAdd(res, c2);
    }
    else if (prog == "rotsum") {
        auto s = cc->EvalMult(ca, cb);
        R.MR(s);
        s = cc->EvalAdd(s, cc->EvalAtIndex(s, 1));
        s = cc->EvalAdd(s, cc->EvalRotate(s, 2));
        Ct a1 = cc->EvalAtIndex(ca, -1);
        if (R.manual) a1 = cc->LevelReduce(a1, nullptr, 1);
        res = cc->EvalSub(s, a1);
    }
    else if (prog == "innerprod") {
        res = cc->EvalInnerProduct(ca, cb, batch);
    }
    else
        throw std::runtime_error("unknown prog " + prog);
    return {res};
}

// One program touching every operation of the Lean source language that OpenFHE performs.
static std::vector<Ct> progOps(Run& R, bool negate) {
    auto& cc = R.cc;
    Ct a = R.fresh(), b = R.fresh(), c = R.fresh();
    Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
    Ct x1 = cc->EvalAdd(a, b);
    Ct x2 = cc->EvalSub(x1, c);
    Ct x3 = negate ? cc->EvalNegate(x2) : cc->EvalAdd(x2, a);
    Ct x4 = cc->EvalAdd(x3, p1);
    Ct x5 = cc->EvalSub(x4, p2);
    Ct x6 = cc->EvalMult(x5, p3);
    R.MR(x6);
    // products without relinearization, an addition of two 3-part values, then Relinearize
    Ct n1 = cc->EvalMultNoRelin(a, b);
    Ct n2 = cc->EvalMultNoRelin(b, c);
    Ct n3 = cc->EvalAdd(n1, n2);
    Ct r  = cc->Relinearize(n3);
    R.MR(r);
    // rotations: EvalRotate, EvalAtIndex (negative), and EvalAutomorphism called directly
    Ct r1 = cc->EvalRotate(r, 1);
    Ct r2 = cc->EvalAtIndex(r, -1);
    Ct r3 = cc->EvalRotate(r, 2);
    auto& am     = CryptoContextImpl<DCRTPoly>::GetEvalAutomorphismKeyMap(R.c->keys().secretKey->GetKeyTag());
    uint32_t idx = am.rbegin()->first;
    Ct r4        = cc->EvalAutomorphism(r, idx, am);
    Ct y         = cc->EvalAdd(r1, r2);
    y            = cc->EvalSub(y, r3);
    y            = cc->EvalAdd(y, r4);
    Ct cL        = cc->LevelReduce(c, nullptr, 1);  // acts under FIXEDMANUAL only
    Ct res;
    if (R.depth >= 2) {
        Ct m = cc->EvalMult(y, x6);
        R.MR(m);
        Ct sq = cc->EvalSquare(cL);
        R.MR(sq);
        res = cc->EvalAdd(m, sq);
    }
    else {
        res = cc->EvalAdd(y, x6);
        res = cc->EvalAdd(res, cL);
    }
    // n3 (3 parts) is decrypted by the dump like every other traced ciphertext
    return {res};
}

static std::vector<Ct> progThreepart(Run& R, const std::string& var) {
    auto& cc = R.cc;
    Ct a = R.fresh(), b = R.fresh(), c = R.fresh();
    Ct n = R.T("EvalMultNoRelin(a,b)", {a, b}, [&] { return cc->EvalMultNoRelin(a, b); });
    Ct fin = n;
    auto keep = [&](const Ct& x) { if (x) fin = x; return x; };
    if (var == "modreduce") {
        Ct m = keep(R.T("ModReduce(3-part)", {n}, [&] { return cc->ModReduce(n); }));
        Ct l = R.T("LevelReduce(3-part,1)", {n}, [&] { return cc->LevelReduce(n, nullptr, 1); });
        keep(R.T("Relinearize(ModReduce(3-part))", {m}, [&] { return cc->Relinearize(m); }));
        (void)l;
    }
    else if (var == "mul3x2") {
        Ct x = R.T("EvalMultNoRelin(3-part,2-part)", {n, c}, [&] { return cc->EvalMultNoRelin(n, c); });
        Ct y = R.T("EvalMult(3-part,2-part)", {n, c}, [&] { return cc->EvalMult(n, c); });
        Ct z = R.T("Relinearize(EvalMultNoRelin(3-part,2-part))", {x}, [&] { return cc->Relinearize(x); });
        keep(x); keep(y); keep(z);
    }
    else if (var == "mul3x3") {
        Ct x = R.T("EvalMultNoRelin(3-part,3-part)", {n}, [&] { return cc->EvalMultNoRelin(n, n); });
        Ct y = R.T("EvalMult(3-part,3-part)", {n}, [&] { return cc->EvalMult(n, n); });
        keep(x); keep(y);
    }
    else if (var == "square") {
        keep(R.T("EvalSquare(3-part)", {n}, [&] { return cc->EvalSquare(n); }));
    }
    else if (var == "add3x2") {
        Ct x = R.T("EvalAdd(3-part,2-part)", {n, c}, [&] { return cc->EvalAdd(n, c); });
        Ct y = R.T("EvalAdd(2-part,3-part)", {n, c}, [&] { return cc->EvalAdd(c, n); });
        Ct z = R.T("EvalSub(3-part,2-part)", {n, c}, [&] { return cc->EvalSub(n, c); });
        Ct w = R.T("EvalSub(2-part,3-part)", {n, c}, [&] { return cc->EvalSub(c, n); });
        keep(y); keep(z); keep(w);
        keep(R.T("Relinearize(EvalAdd(3-part,2-part))", {x}, [&] { return cc->Relinearize(x); }));
    }
    else if (var == "rot") {
        keep(R.T("EvalRotate(3-part,1)", {n}, [&] { return cc->EvalRotate(n, 1); }));
        keep(R.T("EvalAtIndex(3-part,-1)", {n}, [&] { return cc->EvalAtIndex(n, -1); }));
    }
    else if (var == "mulplain") {
        Plaintext p = R.mk();
        Ct x = R.T("EvalMult(3-part,plaintext)", {n}, [&] { return cc->EvalMult(n, p); });
        Ct y = R.T("EvalAdd(3-part,plaintext)", {n}, [&] { return cc->EvalAdd(n, p); });
        keep(y);
        keep(R.T("Relinearize(EvalMult(3-part,plaintext))", {x}, [&] { return cc->Relinearize(x); }));
    }
    else if (var == "autoreduce") {
        // a 3-part value added to a deeper 2-part one: the automatic modes must bring the 3-part
        // value down themselves (AdjustLevelsAndDepthInPlace); under FIXEDMANUAL we ModReduce it.
        Ct x = R.T("EvalMult(a,c)", {a, c}, [&] { return cc->EvalMult(a, c); });
        R.MR(x);
        Ct bb = b;
        if (R.manual) bb = R.T("LevelReduce(b,1)", {b}, [&] { return cc->LevelReduce(b, nullptr, 1); });
        Ct y = R.T("EvalMult(x,b)", {x, bb}, [&] { return cc->EvalMult(x, bb); });
        Ct nn = n;
        if (R.manual) nn = R.T("ModReduce(3-part)", {n}, [&] { return cc->ModReduce(n); });
        Ct s = R.T("EvalAdd(3-part, deeper 2-part)", {nn, y}, [&] { return cc->EvalAdd(nn, y); });
        keep(s);
        keep(R.T("Relinearize(sum)", {s}, [&] { return cc->Relinearize(s); }));
    }
    else
        throw std::runtime_error("unknown threepart variant " + var);
    return {fin};
}

static std::vector<Ct> progPaths(Run& R, const std::string& var) {
    auto& cc = R.cc;
    std::string saved = R.msg;
    if (var == "coefpacked") R.msg = "coefrandom";
    Ct a, b, c;
    Ct fin;
    auto keep = [&](const Ct& x) { if (x) fin = x; return x; };
    if (var == "string") {
        try {
            Plaintext sa = cc->MakeStringPlaintext("pin: A!");
            Plaintext sb = cc->MakeStringPlaintext("B string");
            a = R.T("Encrypt(string)", {}, [&] { return R.enc(sa); });
            b = R.T("Encrypt(string)", {}, [&] { return R.enc(sb); });
            Ct x = keep(R.T("EvalAdd(a,b)", {a, b}, [&] { return cc->EvalAdd(a, b); }));
            Plaintext sp = cc->MakeStringPlaintext("operand");
            keep(R.T("EvalAdd(x,stringPlaintext)", {x}, [&] { return cc->EvalAdd(x, sp); }));
            Ct m = R.T("EvalMult(a,b)", {a, b}, [&] { return cc->EvalMult(a, b); });
            R.MR(m);
            keep(m);
        }
        catch (const std::exception& e) {
            R.c->note(std::string("EXC MakeStringPlaintext: ") + cleanMsg(e.what()));
        }
        if (!fin && !a) return {};
        return {fin ? fin : a};
    }
    a = R.fresh(); b = R.fresh(); c = R.fresh();
    fin = a;
    if (var == "fastrot") {
        uint32_t M = 2 * R.N;
        std::shared_ptr<std::vector<DCRTPoly>> pre;
        try {
            pre = cc->EvalFastRotationPrecompute(a);
        }
        catch (const std::exception& e) {
            R.c->note(std::string("EXC EvalFastRotationPrecompute: ") + cleanMsg(e.what()));
        }
        Ct r1 = R.T("EvalFastRotation(a,1)", {a}, [&] { return cc->EvalFastRotation(a, 1, M, pre); });
        Ct r2 = R.T("EvalFastRotation(a,2)", {a}, [&] { return cc->EvalFastRotation(a, 2, M, pre); });
        Ct s  = keep(R.T("EvalAdd(r1,r2)", {r1, r2}, [&] { return cc->EvalAdd(r1, r2); }));
        keep(R.T("EvalAdd(s,b)", {s, b}, [&] { return cc->EvalAdd(s, b); }));
    }
    else if (var == "multmany") {
        std::vector<Ct> v = {a, b, c};
        if (R.depth >= 2) v.push_back(a);
        keep(R.T("EvalMultMany", {a, b, c}, [&] { return cc->EvalMultMany(v); }));
    }
    else if (var == "compress") {
        Ct x = R.T("EvalMult(a,b)", {a, b}, [&] { return cc->EvalMult(a, b); });
        R.MR(x);
        keep(x);
        keep(R.T("Compress(x,1)", {x}, [&] { return cc->Compress(x, 1); }));
        Ct z = R.T("Compress(c,2)", {c}, [&] { return cc->Compress(c, 2); });
        (void)z;
        // leave the compressed product as the result
        if (fin != x && fin) return {fin};
    }
    else if (var == "relinearize") {
        Ct n1 = R.T("EvalMultNoRelin(a,b)", {a, b}, [&] { return cc->EvalMultNoRelin(a, b); });
        Ct r1 = R.T("Relinearize(n1)", {n1}, [&] { return cc->Relinearize(n1); });
        Ct n2 = R.T("EvalMultNoRelin(b,c)", {b, c}, [&] { return cc->EvalMultNoRelin(b, c); });
        R.T("RelinearizeInPlace(n2)", {n2}, [&] { cc->RelinearizeInPlace(n2); return n2; });
        Ct s = R.T("EvalAdd(r1,n2)", {r1, n2}, [&] { return cc->EvalAdd(r1, n2); });
        R.MR(s);
        keep(s);
    }
    else if (var == "mutable") {
        Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
        Ct x = R.T("EvalAddMutable(a,b)", {a, b}, [&] { return cc->EvalAddMutable(a, b); });
        Ct y = R.T("EvalSubMutable(x,c)", {x, c}, [&] { return cc->EvalSubMutable(x, c); });
        Ct z = R.T("EvalMultMutable(y,a)", {y, a}, [&] { return cc->EvalMultMutable(y, a); });
        R.MR(z);
        Ct w = R.T("EvalAddMutable(z,pt)", {z}, [&] { return cc->EvalAddMutable(z, p1); });
        Ct u = R.T("EvalSubMutable(w,pt)", {w}, [&] { return cc->EvalSubMutable(w, p2); });
        keep(u);
        if (R.depth >= 2) {
            Ct k = R.T("EvalMultMutable(u,pt)", {u}, [&] { return cc->EvalMultMutable(u, p3); });
            R.MR(k);
            keep(k);
        }
        Ct k = fin;
        Ct k2 = R.T("EvalAdd(k,k)", {k}, [&] { return cc->EvalAdd(k, k); });
        R.T("EvalAddInPlace(k2,k)", {k2, k}, [&] { cc->EvalAddInPlace(k2, k); return k2; });
        R.T("EvalSubInPlace(k2,k)", {k2, k}, [&] { cc->EvalSubInPlace(k2, k); return k2; });
        R.T("EvalAddMutableInPlace(k2,k)", {k2, k}, [&] { cc->EvalAddMutableInPlace(k2, k); return k2; });
        R.T("EvalSubMutableInPlace(k2,k)", {k2, k}, [&] { cc->EvalSubMutableInPlace(k2, k); return k2; });
        R.T("EvalNegateInPlace(k2)", {k2}, [&] { cc->EvalNegateInPlace(k2); return k2; });
        R.T("EvalAddInPlace(k2,pt)", {k2}, [&] { cc->EvalAddInPlace(k2, p1); return k2; });
        keep(k2);
        if (R.depth >= 3) {
            Ct q = R.T("EvalMultMutableInPlace(k2,k)", {k2, k}, [&] { cc->EvalMultMutableInPlace(k2, k); return k2; });
            R.MR(k2);
            keep(q ? k2 : nullptr);
        }
    }
    else if (var == "negate") {
        Ct x = R.T("EvalNegate(a)", {a}, [&] { return cc->EvalNegate(a); });
        Ct y = R.T("EvalAdd(x,b)", {x, b}, [&] { return cc->EvalAdd(x, b); });
        Ct m = R.T("EvalMult(y,c)", {y, c}, [&] { return cc->EvalMult(y, c); });
        R.MR(m);
        keep(y);
        keep(R.T("EvalNegate(m)", {m}, [&] { return cc->EvalNegate(m); }));
    }
    else if (var == "coefpacked") {
        Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
        Ct x = R.T("EvalMult(a,b)", {a, b}, [&] { return cc->EvalMult(a, b); });
        R.MR(x);
        Ct y = keep(R.T("EvalAdd(x,coefPt)", {x}, [&] { return cc->EvalAdd(x, p1); }));
        if (R.depth >= 2) {
            Ct z = R.T("EvalMult(y,coefPt)", {y}, [&] { return cc->EvalMult(y, p2); });
            R.MR(z);
            keep(z);
            keep(R.T("EvalSub(z,coefPt)", {z}, [&] { return cc->EvalSub(z, p3); }));
        }
    }
    else if (var == "evalsum") {
        try {
            cc->EvalSumKeyGen(R.c->keys().secretKey);
        }
        catch (const std::exception& e) {
            R.c->note(std::string("EXC EvalSumKeyGen: ") + cleanMsg(e.what()));
        }
        keep(R.T("EvalSum(a,8)", {a}, [&] { return cc->EvalSum(a, 8); }));
        Ct m = R.T("EvalMult(a,b)", {a, b}, [&] { return cc->EvalMult(a, b); });
        R.MR(m);
        keep(R.T("EvalSum(a*b,4)", {m}, [&] { return cc->EvalSum(m, 4); }));
    }
    else if (var == "ptfirst") {
        Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
        Ct x = keep(R.T("EvalAdd(pt,a)", {a}, [&] { return cc->EvalAdd(p1, a); }));
        Ct y = keep(R.T("EvalSub(pt,x)", {x}, [&] { return cc->EvalSub(p2, x); }));
        Ct z = R.T("EvalMult(pt,y)", {y}, [&] { return cc->EvalMult(p3, y); });
        R.MR(z);
        keep(z);
        Ct bb = b;
        if (R.manual && z && Run::towers(z) < Run::towers(b))
            bb = R.T("LevelReduce(b)", {b}, [&] { return cc->LevelReduce(b, nullptr, Run::towers(b) - Run::towers(z)); });
        keep(R.T("EvalSub(z,b)", {z, bb}, [&] { return cc->EvalSub(z, bb); }));
    }
    else if (var == "multrelin") {
        Ct x = R.T("EvalMultAndRelinearize(a,b)", {a, b}, [&] { return cc->EvalMultAndRelinearize(a, b); });
        R.MR(x);
        keep(x);
        Ct cc2 = c;
        if (R.manual && x) cc2 = R.T("LevelReduce(c,1)", {c}, [&] { return cc->LevelReduce(c, nullptr, 1); });
        keep(R.T("EvalAdd(x,c)", {x, cc2}, [&] { return cc->EvalAdd(x, cc2); }));
    }
    else if (var == "automorphism") {
        auto& am = CryptoContextImpl<DCRTPoly>::GetEvalAutomorphismKeyMap(R.c->keys().secretKey->GetKeyTag());
        Ct x = a;
        for (auto& kv : am) {
            uint32_t idx = kv.first;
            x = keep(R.T("EvalAutomorphism(x," + std::to_string(idx) + ")", {x},
                         [&] { return cc->EvalAutomorphism(x, idx, am); }));
        }
        keep(R.T("EvalAdd(x,b)", {x, b}, [&] { return cc->EvalAdd(x, b); }));
    }
    else if (var == "scalar") {
        // BGV has no integer-constant API: the scalar overloads take a double (CKKS)
        keep(R.T("EvalMult(a, double 3.0)", {a}, [&] { return cc->EvalMult(a, 3.0); }));
        keep(R.T("EvalAdd(a, double 2.0)", {a}, [&] { return cc->EvalAdd(a, 2.0); }));
        keep(R.T("EvalSub(a, double 2.0)", {a}, [&] { return cc->EvalSub(a, 2.0); }));
        keep(R.T("EvalAdd(a,b)", {a, b}, [&] { return cc->EvalAdd(a, b); }));
    }
    else
        throw std::runtime_error("unknown paths variant " + var);
    R.msg = saved;
    return {fin};
}

// Operands at different levels and noise-scale degrees (meant for the automatic modes; under
// FIXEDMANUAL OpenFHE refuses mismatched towers and the exceptions are recorded).
static std::vector<Ct> progMixed(Run& R, const std::string& var) {
    auto& cc = R.cc;
    Ct a = R.fresh(), b = R.fresh(), c = R.fresh();
    Ct fin = a;
    auto keep = [&](const Ct& x) { if (x) fin = x; return x; };
    auto mul = [&](const std::string& s, Ct x, Ct y) {
        Ct r = R.T("EvalMult " + s, {x, y}, [&] { return cc->EvalMult(x, y); });
        R.MR(r);
        return keep(r);
    };
    auto add = [&](const std::string& s, Ct x, Ct y) {
        return keep(R.T("EvalAdd " + s, {x, y}, [&] { return cc->EvalAdd(x, y); }));
    };
    auto sub = [&](const std::string& s, Ct x, Ct y) {
        return keep(R.T("EvalSub " + s, {x, y}, [&] { return cc->EvalSub(x, y); }));
    };
    if (var == "a") {
        Ct x = mul("x=a*b", a, b);
        Ct y = mul("y=x*x", x, x);
        Ct z = add("z=y+a", y, a);
        Ct w = R.depth >= 3 ? mul("w=y*c", y, c) : add("w=y+c", y, c);
        Ct v = sub("v=w-x", w, x);
        add("res=v+z", v, z);
    }
    else if (var == "b") {
        Ct x = mul("x=a*b", a, b);
        Ct y = keep(R.T("y=EvalSquare(x)", {x}, [&] { return cc->EvalSquare(x); }));
        R.MR(y);
        Ct r  = add("r=y+c (fresh + depth 2)", y, c);
        Ct r2 = sub("r2=c-y", c, y);
        Plaintext p0 = R.mk();
        Ct r3 = keep(R.T("r3=EvalAdd(r,pt@level0)", {r}, [&] { return cc->EvalAdd(r, p0); }));
        Ct r4;
        if (x && R.depth >= 3) {
            Plaintext pl = R.mkAt(x);
            r4 = R.T("r4=EvalMult(y,pt@level(x))", {y}, [&] { return cc->EvalMult(y, pl); });
            R.MR(r4);
            keep(r4);
        }
        else
            r4 = y;
        Ct r5 = keep(R.T("r5=EvalSub(r4,pt@level0)", {r4}, [&] { return cc->EvalSub(r4, p0); }));
        Ct s  = add("s=r5+r2", r5, r2);
        add("res=s+r3", s, r3);
    }
    else if (var == "c") {
        Ct x = mul("x=a*b", a, b);
        Ct y = mul("y=x*x", x, x);
        Ct u = R.depth >= 3 ? mul("u=y*a", y, a) : add("u=y+a", y, a);
        Ct s = add("s=u+x", u, x);
        if (R.depth >= 4) {
            Ct q = keep(R.T("q=EvalSquare(s)", {s}, [&] { return cc->EvalSquare(s); }));
            R.MR(q);
            add("res=q+b", q, b);
        }
        else
            sub("res=s-b", s, b);
    }
    else if (var == "d") {
        Plaintext p1 = R.mk(), p2 = R.mk(), p3 = R.mk();
        Ct x = R.T("x=EvalMult(a,pt)", {a}, [&] { return cc->EvalMult(a, p1); });
        R.MR(x);
        keep(x);
        Ct y = R.T("y=EvalMult(x,pt)", {x}, [&] { return cc->EvalMult(x, p2); });
        R.MR(y);
        keep(y);
        Ct z = add("z=y+a", y, a);
        Ct w = R.depth >= 3 ? mul("w=z*b", z, b) : add("w=z+b", z, b);
        Ct v = sub("v=w-x", w, x);
        Ct u = v;
        if (R.depth >= 4) {
            u = R.T("u=EvalMult(v,pt)", {v}, [&] { return cc->EvalMult(v, p3); });
            R.MR(u);
            keep(u);
        }
        add("res=u+c", u, c);
    }
    else
        throw std::runtime_error("unknown mixed variant " + var);
    return {fin};
}

// A seeded random straight-line program.
static std::vector<Ct> progRandom(Run& R, uint32_t len) {
    auto& cc = R.cc;
    struct V { Ct ct; uint32_t d; };  // d: multiplicative depth consumed (automatic modes)
    std::vector<V> pool;
    std::vector<Plaintext> pts;
    uint32_t nIn = 2 + R.rng.below(3);
    for (uint32_t i = 0; i < nIn; i++) pool.push_back({R.fresh(), 0});
    for (uint32_t i = 0; i < 2; i++) pts.push_back(R.mk());
    Ct fin = pool.back().ct;
    auto& am = CryptoContextImpl<DCRTPoly>::GetEvalAutomorphismKeyMap(R.c->keys().secretKey->GetKeyTag());
    static const int rots[] = {1, 2, -1, -2};
    auto pick = [&]() -> V& { return pool[R.rng.below(pool.size())]; };
    auto pick2 = [&](V*& out) {  // a 2-part value, if any
        for (int k = 0; k < 16; k++) {
            V& v = pick();
            if (Run::parts(v.ct) == 2) { out = &v; return true; }
        }
        return false;
    };
    // can this value still be multiplied (and, under FIXEDMANUAL, ModReduced afterwards)?
    auto canMul = [&](const V& v) { return R.manual ? Run::towers(v.ct) >= 2 : v.d + 1 <= R.depth; };
    // FIXEDMANUAL: bring two operands to the same number of towers (LevelReduce or ModReduce)
    auto align = [&](Ct& x, Ct& y, const std::string& step) {
        if (!R.manual) return;
        Ct& hi = Run::towers(x) > Run::towers(y) ? x : y;
        size_t k = Run::towers(hi) - std::min(Run::towers(x), Run::towers(y));
        if (!k) return;
        if (R.rng.below(2)) hi = cc->LevelReduce(hi, nullptr, k);
        else
            for (size_t i = 0; i < k; i++) hi = cc->ModReduce(hi);
        (void)step;
    };
    for (uint32_t i = 0; i < len; i++) {
        uint32_t op = R.rng.below(32);
        std::string step = "random#" + std::to_string(i);
        Ct out;
        uint32_t d = 0;
        try {
            V* pa = nullptr; V* pb = nullptr;
            if (op < 5) {  // add / sub of ciphertexts (any number of parts)
                V va = pick(), vb = pick();
                Ct x = va.ct, y = vb.ct;
                align(x, y, step);
                step += op < 3 ? " EvalAdd" : " EvalSub";
                out = op < 3 ? cc->EvalAdd(x, y) : cc->EvalSub(x, y);
                d   = std::max(va.d, vb.d);
            }
            else if (op < 6) {
                if (!R.menuAll) continue;
                V va = pick();
                step += " EvalNegate";
                out = cc->EvalNegate(va.ct);
                d   = va.d;
            }
            else if (op < 9) {  // plaintext add / sub
                V va = pick();
                Plaintext p = R.rng.below(3) ? pts[R.rng.below(pts.size())] : R.mk();
                if (op == 6) { step += " EvalAdd(ct,pt)"; out = cc->EvalAdd(va.ct, p); }
                else if (op == 7) { step += " EvalSub(ct,pt)"; out = cc->EvalSub(va.ct, p); }
                else if (!R.menuAll) continue;
                else { step += " EvalSub(pt,ct)"; out = cc->EvalSub(p, va.ct); }
                d = va.d;
            }
            else if (op < 11) {  // plaintext product
                if (!pick2(pa) || !canMul(*pa)) continue;
                V va = *pa;
                Plaintext p = R.rng.below(2) ? pts[R.rng.below(pts.size())] : R.mk();
                step += " EvalMult(ct,pt)";
                out = cc->EvalMult(va.ct, p);
                R.MR(out);
                d = va.d + 1;
            }
            else if (op < 15) {  // product with relinearization
                if (!pick2(pa) || !pick2(pb) || !canMul(*pa) || !canMul(*pb)) continue;
                V va = *pa, vb = *pb;
                Ct x = va.ct, y = vb.ct;
                align(x, y, step);
                step += " EvalMult";
                out = cc->EvalMult(x, y);
                R.MR(out);
                d = std::max(va.d, vb.d) + 1;
            }
            else if (op < 17) {
                if (!pick2(pa) || !canMul(*pa)) continue;
                V va = *pa;
                step += " EvalSquare";
                out = cc->EvalSquare(va.ct);
                R.MR(out);
                d = va.d + 1;
            }
            else if (op < 19) {  // product without relinearization (a 3-part value enters the pool)
                if (!pick2(pa) || !pick2(pb) || !canMul(*pa) || !canMul(*pb)) continue;
                V va = *pa, vb = *pb;
                Ct x = va.ct, y = vb.ct;
                align(x, y, step);
                step += " EvalMultNoRelin";
                out = cc->EvalMultNoRelin(x, y);
                d   = std::max(va.d, vb.d) + 1;
            }
            else if (op < 21) {  // relinearize a 3-part value (then ModReduce under FIXEDMANUAL)
                V* p3 = nullptr;
                for (auto& v : pool) if (Run::parts(v.ct) == 3) p3 = &v;
                if (!p3) continue;
                V va = *p3;
                step += " Relinearize";
                out = cc->Relinearize(va.ct);
                if (Run::towers(out) >= 2) R.MR(out);  // at one tower the product stays unreduced
                d = va.d;
            }
            else if (op < 25) {  // rotations
                if (!pick2(pa)) continue;
                V va = *pa;
                int k = rots[R.rng.below(4)];
                uint32_t w = R.rng.below(R.menuAll ? 4 : 3);
                if (w == 0) { step += " EvalRotate " + std::to_string(k); out = cc->EvalRotate(va.ct, k); }
                else if (w == 1) { step += " EvalAtIndex " + std::to_string(k); out = cc->EvalAtIndex(va.ct, k); }
                else if (w == 2) {
                    auto it = am.begin();
                    std::advance(it, R.rng.below(am.size()));
                    step += " EvalAutomorphism " + std::to_string(it->first);
                    out = cc->EvalAutomorphism(va.ct, it->first, am);
                }
                else {
                    step += " EvalFastRotation " + std::to_string(k);
                    auto pre = cc->EvalFastRotationPrecompute(va.ct);
                    out      = cc->EvalFastRotation(va.ct, k, 2 * R.N, pre);
                }
                d = va.d;
            }
            else if (op < 27) {  // ModReduce / LevelReduce called by the user
                V va = pick();
                if (R.manual && Run::towers(va.ct) < 2) continue;
                if (op == 25) { step += " ModReduce"; out = cc->ModReduce(va.ct); }
                else { step += " LevelReduce"; out = cc->LevelReduce(va.ct, nullptr, 1); }
                d = va.d;
            }
            else if (op < 29) {  // mutable variants (they may rewrite their operands in place)
                if (!R.menuAll) continue;
                V va = pick(), vb = pick();
                Ct x = va.ct->Clone(), y = vb.ct->Clone();
                align(x, y, step);
                if (op == 27) { step += " EvalAddMutable"; out = cc->EvalAddMutable(x, y); }
                else { step += " EvalSubMutable"; out = cc->EvalSubMutable(x, y); }
                d = std::max(va.d, vb.d);
            }
            else if (op < 30) {  // in-place variants
                V va = pick(), vb = pick();
                Ct x = va.ct->Clone(), y = vb.ct;
                align(x, y, step);
                uint32_t w = R.rng.below(R.menuAll ? 3 : 2);
                if (w == 0) { step += " EvalAddInPlace"; cc->EvalAddInPlace(x, y); }
                else if (w == 1) { step += " EvalSubInPlace"; cc->EvalSubInPlace(x, y); }
                else { step += " EvalNegateInPlace"; cc->EvalNegateInPlace(x); }
                out = x;
                d   = std::max(va.d, vb.d);
            }
            else if (op < 31) {  // a plaintext made at the ciphertext's level and degree
                V va = pick();
                Plaintext p = R.mkAt(va.ct);
                step += " EvalAdd(ct,pt@level)";
                out = cc->EvalAdd(va.ct, p);
                d   = va.d;
            }
            else {  // EvalMult on a 3-part operand (what does OpenFHE do?)
                V* p3 = nullptr;
                for (auto& v : pool) if (Run::parts(v.ct) == 3) p3 = &v;
                if (!R.menuAll || !p3 || !pick2(pb) || !canMul(*p3) || !canMul(*pb)) continue;
                V va = *p3, vb = *pb;
                Ct x = va.ct, y = vb.ct;
                align(x, y, step);
                step += " EvalMultNoRelin(3-part,2-part)";
                out = cc->EvalMultNoRelin(x, y);
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

// ---------------------------------------------------------------------------------------------
int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "usage: pin_export <outdir> --seed S [opts]  (see the header of pin_export.cpp)\n";
        return 2;
    }
    std::string out = argv[1];
    uint32_t depth = 2, dnum = 0, n = 0, qbits = 0, firstbits = 0, batch = 0, evaladd = 0, kscount = 0, len = 12;
    uint64_t t = 65537, seed = 1;
    bool haveSeed = false;
    uint32_t relindeg = 0;
    std::string menu = "all";
    std::string scal = "FIXEDMANUAL", prog = "chain", msg = "small", skdist, so = soDefault(argv[0]);
    std::string cmdline;
    for (int i = 2; i < argc; i++) cmdline += std::string(i > 2 ? " " : "") + argv[i];
    for (int i = 2; i + 1 < argc; i += 2) {
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
        else if (k == "--seed") { seed = std::stoull(v); haveSeed = true; }
        else if (k == "--msg") msg = v;
        else if (k == "--len") len = std::stoul(v);
        else if (k == "--skdist") skdist = v;
        else if (k == "--menu") menu = v;
        else if (k == "--relindeg") relindeg = std::stoul(v);
        else if (k == "--prng") so = v;
        else { std::cerr << "unknown option " << k << "\n"; return 2; }
    }
    if (!haveSeed) { std::cerr << "--seed is required\n"; return 2; }
    if (prog == "innerprod" && !batch) batch = 8;

    try {
        pin::Prng::init(so);
        pin::Prng::seed(seed);

        CCParams<CryptoContextBGVRNS> params;
        params.SetMultiplicativeDepth(depth);
        params.SetPlaintextModulus(t);
        if (dnum) params.SetNumLargeDigits(dnum);
        if (qbits) params.SetScalingModSize(qbits);
        if (firstbits) params.SetFirstModSize(firstbits);
        if (n) { params.SetRingDim(n); params.SetSecurityLevel(HEStd_NotSet); }
        if (batch) params.SetBatchSize(batch);
        if (evaladd) params.SetEvalAddCount(evaladd);
        if (kscount) params.SetKeySwitchCount(kscount);
        if (relindeg) params.SetMaxRelinSkDeg(relindeg);
        if (scal == "FIXEDMANUAL") params.SetScalingTechnique(FIXEDMANUAL);
        else if (scal == "FIXEDAUTO") params.SetScalingTechnique(FIXEDAUTO);
        else if (scal == "FLEXIBLEAUTO") params.SetScalingTechnique(FLEXIBLEAUTO);
        else if (scal == "FLEXIBLEAUTOEXT") params.SetScalingTechnique(FLEXIBLEAUTOEXT);
        else if (scal != "default") { std::cerr << "unknown scaling technique " << scal << "\n"; return 2; }
        if (skdist == "GAUSSIAN") params.SetSecretKeyDist(GAUSSIAN);
        else if (skdist == "SPARSE_TERNARY") params.SetSecretKeyDist(SPARSE_TERNARY);
        else if (skdist == "UNIFORM_TERNARY") params.SetSecretKeyDist(UNIFORM_TERNARY);
        else if (!skdist.empty()) { std::cerr << "unknown --skdist " << skdist << "\n"; return 2; }
        CryptoContext<DCRTPoly> cc = GenCryptoContext(params);
        cc->Enable(PKE);
        cc->Enable(KEYSWITCH);
        cc->Enable(LEVELEDSHE);
        cc->Enable(ADVANCEDSHE);
        auto cp = std::dynamic_pointer_cast<CryptoParametersBGVRNS>(cc->GetCryptoParameters());

        { std::ofstream f(out + "/params.json"); f << pin::paramsJson(cc); }

        std::string name = out;
        while (name.size() > 1 && name.back() == '/') name.pop_back();
        name = name.substr(name.find_last_of('/') + 1);
        pin::Case c(out, name, seed, "pin_export " + cmdline, cc);
        // the tracer is attached BEFORE KeyGen: the extractor establishes where every key the
        // program uses came from (key provenance) from the traced key generation
        auto tr = std::make_shared<pin::Tracer>(out + "/trace.jsonl");
        pin::attach(cc, tr);
        auto kp = c.keyGen();
        if (relindeg > 2) {
            // keys for s^2 .. s^relindeg (EvalMultKeysGen only generates when the tag has no key yet,
            // cryptocontext.cpp:115-124, so it replaces EvalMultKeyGen here)
            cc->EvalMultKeysGen(kp.secretKey);
        }
        else
            cc->EvalMultKeyGen(kp.secretKey);
        std::string fam = prog.substr(0, prog.find(':'));
        std::string var = prog.find(':') == std::string::npos ? "" : prog.substr(prog.find(':') + 1);
        bool needRot = prog == "dot" || prog == "rot" || prog == "rotsum" || prog == "ops" || prog == "opsnn" || prog == "random" ||
                       prog == "threepart:rot" || prog == "paths:fastrot" || prog == "paths:automorphism";
        if (needRot) cc->EvalRotateKeyGen(kp.secretKey, {1, 2, -1, -2});
        if (prog == "innerprod") cc->EvalSumKeyGen(kp.secretKey);
        Run R{cc, cp, &c, tr, cp->GetScalingTechnique() == FIXEDMANUAL, t, (uint32_t)cc->GetRingDimension(), depth,
              msg, menu == "all", Rng{seed * 0x2545F4914F6CDD1DULL + 0x1234567}, nullptr};
        pin::attach(cc, tr);
        std::vector<Ct> fin;
        if (prog == "ops") fin = progOps(R, true);
        else if (prog == "opsnn") fin = progOps(R, false);
        else if (prog == "random") fin = progRandom(R, len);
        else if (fam == "threepart") fin = progThreepart(R, var);
        else if (fam == "paths") fin = progPaths(R, var);
        else if (fam == "mixed") fin = progMixed(R, var);
        else fin = progBasic(R, prog, batch);
        pin::detach(cc);
        std::vector<Ct> f2;
        for (auto& x : fin) if (x) f2.push_back(x);
        c.setFinal(f2);
        if (msg == "max")
            c.note("--msg max: packed plaintexts whose encoded polynomial has every coefficient equal to t-1 "
                   "(slots obtained with PackedEncoding::Decode of that polynomial; the encoded result is asserted)");
        if (msg == "alt" || msg == "witness" || prog == "paths:coefpacked")
            c.note("--msg " + msg + ": MakeCoefPackedPlaintext; CoefPackedEncoding stores centred values in "
                   "(-t/2, t/2] (negative v as q - |v|, coefpackedencoding.cpp:56-65) and then multiplies the "
                   "polynomial by scalingFactorInt mod q (:77-91), so the stored integer polynomial is NOT bounded "
                   "by t-1 when the scaling factor is not 1 (FLEXIBLEAUTO*)");
        // plaintext polynomials as stored: largest coefficient (for the t-1 bound a frontend declares)
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
            if (o.encoding != "PACKED_ENCODING" || mx0 >= t)
                c.note("plaintext " + o.id + " (" + o.encoding + ", sf " + o.sf + "): stored polynomial, limb 0, max " +
                       "canonical residue " + std::to_string(mx0) + (mx0 < t ? " (< t)" : " (>= t)") +
                       "; all limbs one centred integer vector: " +
                       (small ? "yes, max |coefficient| " + std::to_string(mc) : std::string("NO")));
        }
        c.write(tr);
        std::cout << "wrote " << out << "\n";
        return 0;
    }
    catch (const std::exception& e) {
        std::cerr << "pin_export FAILED: " << cleanMsg(e.what()) << "\n";
        return 1;
    }
}
