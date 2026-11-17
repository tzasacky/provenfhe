// pin_dump.h -- UNTRUSTED. Exporter side of the openfhe-pin differential-test harness
// (format: harness/openfhe-pin/FORMAT.md, "openfhe-pin/v1"). Header-only; include it from any
// main() built against upstream OpenFHE v1.6.1 with the frontend's observation-only tracer
// (harness/frontend/openfhe/build_openfhe.sh: ENABLE_TRACER hooks + fhecheck-tracer.h), see
// export/build_cpp.sh.
//
// API (namespace pin)
// -------------------
//   pin::Prng::init(soPath)            dlopen()s libpin_prng.so, installs it as OpenFHE's PRNG engine
//                                      (PseudoRandomNumberGenerator::InitPRNGEngine) and resolves the
//                                      pin_prng_* C API. Call it BEFORE anything draws randomness
//                                      (before GenCryptoContext is the safe place). Also sets
//                                      omp_set_num_threads(1); run with OMP_NUM_THREADS=1 as well.
//   pin::Prng::seed/getState/setState/calls/scriptPush/scriptRemaining   thin wrappers of the C API.
//
//   pin::Tracer                        the frontend's fhecheck::JsonTracer (utils/fhecheck-tracer.h,
//                                      installed by build_openfhe.sh) itself: trace.jsonl has its
//                                      line shapes and ids (FNV-1a content hash -> ct_n / pt_n / pk_n /
//                                      sk_n / ek_n by first appearance), written by its code.
//                                      Additionally keeps a deep copy of every ciphertext / plaintext
//                                      at the first appearance of its id (objects()).
//       auto tr = std::make_shared<pin::Tracer>(outdir + "/trace.jsonl");
//       pin::attach(cc, tr);  ... program ...  pin::detach(cc);
//       tr->idOf(ct, "ct") / tr->idOf(pt, "pt")   id of an object (assigns one if new, as the tracer does)
//       tr->note(ct) / tr->note(pt)               id + capture of an object that no traced call saw
//
//   pin::Case c(outdir, caseName, seed, generator, cc);
//       KeyPair<DCRTPoly> kp = c.keyGen();        cc->KeyGen() with PRNG replay: captures the public-key
//                                                 error pk.e, checks replayed s == secret, a == pk[1],
//                                                 b == ns*e - a*s (else pk.e = null + a note).
//       c.setKeys(kp)                             alternative: keys made elsewhere (pk.e = null)
//       Ciphertext<DCRTPoly> ct = c.encrypt(tr, pt);   cc->Encrypt(pk, pt) (traced if tr is attached)
//                                                 with PRNG replay of (u, e1, e2) = OpenFHE's (v, e0, e1)
//                                                 and a C++ self-check that pk*u + ns*e + m reproduces
//                                                 the library's ciphertext; on mismatch randomness "none".
//                                                 If the PRNG script queue is non-empty the replay is
//                                                 impossible (the queue cannot be rewound): "none".
//       c.encryptScripted(tr, pt, u, e1, e2)      the caller knows the sampler outputs (it scripted the
//                                                 PRNG): they are recorded as "scripted" after the same
//                                                 self-check (mismatch -> "none").
//       c.addInput(tr, ct)                        a hand-built input ciphertext (sets inputsArbitrary)
//       c.note("text")                            appended to pin.json "notes"
//       c.setFinal({ct, ...})
//       c.write(tr)                               writes pin.json + polys.txt: secret, public key, every
//                                                 eval key of the secret's key tag (EvalMult + all
//                                                 automorphism keys), every captured object, and
//                                                 OpenFHE's own Decrypt of every ciphertext with >= 2
//                                                 parts (untraced; asserts the PRNG is not touched).
//   pin::paramsJson(cc)                           params.json text (same fields as bgv_demo)
//
// Source references in comments and notes are to OpenFHE v1.6.1 (commit b59e1f29).
// Nothing here is trusted by the Lean checker: it recomputes everything from the dumped integers.
#pragma once
#include "openfhe.h"
#include "utils/tracing.h"
#include "utils/fhecheck-tracer.h"
#include "ciphertext-ser.h"
#include "plaintext-ser.h"
#include "cryptocontext-ser.h"
#include "scheme/bgvrns/bgvrns-ser.h"

#include <dlfcn.h>
#include <omp.h>

#include <cstdio>
#include <fstream>
#include <map>
#include <memory>
#include <ostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

namespace pin {
using namespace lbcrypto;
using E = DCRTPoly;

// ---------------------------------------------------------------------------------------------
// PRNG
// ---------------------------------------------------------------------------------------------
struct Prng {
    static void*& handle() { static void* h = nullptr; return h; }
    template <typename F>
    static F sym(const char* name) {
        if (!handle()) throw std::runtime_error("pin::Prng::init was not called");
        void* p = dlsym(handle(), name);
        if (!p) throw std::runtime_error(std::string("pin_prng symbol missing: ") + name);
        return reinterpret_cast<F>(p);
    }
    static void init(const std::string& soPath) {
        omp_set_num_threads(1);
        handle() = dlopen(soPath.c_str(), RTLD_NOW | RTLD_GLOBAL);
        if (!handle()) throw std::runtime_error("cannot dlopen " + soPath + ": " + dlerror());
        PseudoRandomNumberGenerator::InitPRNGEngine(soPath);
    }
    static void seed(uint64_t s) { sym<void (*)(uint64_t)>("pin_prng_seed")(s); }
    static uint64_t getState() { return sym<uint64_t (*)()>("pin_prng_get_state")(); }
    static void setState(uint64_t s) { sym<void (*)(uint64_t)>("pin_prng_set_state")(s); }
    static uint64_t calls() { return sym<uint64_t (*)()>("pin_prng_calls")(); }
    static size_t scriptRemaining() { return sym<size_t (*)()>("pin_prng_script_remaining")(); }
    static void scriptPush(const uint32_t* w, size_t n) {
        sym<void (*)(const uint32_t*, size_t)>("pin_prng_script_push")(w, n);
    }
};

// ---------------------------------------------------------------------------------------------
// Tracer (fhecheck-tracer.h, plus capture)
// ---------------------------------------------------------------------------------------------
struct Obj {
    std::string id;
    bool isCt = false;
    Ciphertext<E> ct;  // deep copy (isCt)
    E ptElem;          // copy of the plaintext's DCRTPoly (!isCt)
    size_t towers = 0, nsd = 0, level = 0;
    std::string sf;
    std::string encoding;  // plaintexts: encoding type as OpenFHE prints it
};

class Tracer;

// The frontend's JsonFunctionTracer (fhecheck-tracer.h, unmodified), plus: every ciphertext and
// plaintext is captured (deep copy) before its line is written.
class FunctionTracer : public fhecheck::JsonFunctionTracer {
    using Base = fhecheck::JsonFunctionTracer;

public:
    FunctionTracer(Tracer* tr, int depth);
    void registerInput(Ciphertext<E> c, std::string name, bool b = false) override { cap(c); Base::registerInput(c, name, b); }
    void registerInput(ConstCiphertext<E> c, std::string name, bool b = false) override { cap(c); Base::registerInput(c, name, b); }
    void registerInput(Plaintext p, std::string name, bool b = false) override { capPt(p); Base::registerInput(p, name, b); }
    void registerInput(ConstPlaintext p, std::string name, bool b = false) override { capPt(p); Base::registerInput(p, name, b); }
    Ciphertext<E> registerOutput(Ciphertext<E> c, std::string name) override { cap(c); return Base::registerOutput(c, name); }
    Plaintext registerOutput(Plaintext p, std::string name) override { capPt(p); return Base::registerOutput(p, name); }
    ConstCiphertext<E> registerOutput(ConstCiphertext<E> c, std::string name) override {
        cap(c);
        return Base::registerOutput(c, name);
    }
    std::vector<Ciphertext<E>> registerOutput(std::vector<Ciphertext<E>> cs, std::string name) override {
        for (auto& c : cs) cap(c);
        return Base::registerOutput(cs, name);
    }
    using Base::registerInput;
    using Base::registerOutput;

private:
    template <typename C>
    void cap(const C& c);
    template <typename P>
    void capPt(const P& p);
    Tracer* m_ptr;
};

// The frontend's JsonTracer (same line shapes, same ids: 64-bit FNV-1a content hashes numbered in
// order of first appearance, key events included), plus capture.
class Tracer : public fhecheck::JsonTracer {
public:
    explicit Tracer(const std::string& path) : Tracer(std::make_shared<std::ofstream>(path)) {}
    explicit Tracer(std::shared_ptr<std::ostream> out) : fhecheck::JsonTracer(out), m_o(std::move(out)) {}

    // id + capture (first appearance only)
    template <typename C>
    std::string note(const C& c) { return noteCt(c); }
    template <typename C>
    std::string noteCt(const C& c) {
        std::string id = fhecheck::JsonTracer::idOf(ConstCiphertext<E>(c), "ct");
        if (!m_idx.count(id)) {
            Obj o;
            o.id   = id;
            o.isCt = true;
            o.ct   = std::make_shared<CiphertextImpl<E>>(*c);
            auto& el = c->GetElements();
            o.towers = el.empty() ? 0 : el[0].GetNumOfElements();
            o.nsd    = c->GetNoiseScaleDeg();
            o.level  = c->GetLevel();
            o.sf     = c->GetScalingFactorInt().ToString();
            m_idx[id] = m_objs.size();
            m_objs.push_back(std::move(o));
        }
        return id;
    }
    template <typename P>
    std::string notePt(const P& p) {
        std::string id = fhecheck::JsonTracer::idOf(ConstPlaintext(p), "pt");
        if (!m_idx.count(id)) {
            Obj o;
            o.id     = id;
            o.ptElem = p->template GetElement<E>();
            o.towers = o.ptElem.GetNumOfElements();
            o.nsd    = p->GetNoiseScaleDeg();
            o.level  = p->GetLevel();
            o.sf     = p->GetScalingFactorInt().ToString();
            o.encoding = fhecheck::encName(p->GetEncodingType());  // as the tracer writes "enc"
            m_idx[id]  = m_objs.size();
            m_objs.push_back(std::move(o));
        }
        return id;
    }
    std::string idOf(const Ciphertext<E>& c, const std::string&) {
        return fhecheck::JsonTracer::idOf(ConstCiphertext<E>(c), "ct");
    }
    std::string idOf(const Plaintext& p, const std::string&) {
        return fhecheck::JsonTracer::idOf(ConstPlaintext(p), "pt");
    }
    const std::vector<Obj>& objects() const { return m_objs; }
    void flush() { m_o->flush(); }

protected:
    // fhecheck::JsonTracer::createFunctionTracer, returning the capturing function tracer
    std::unique_ptr<lbcrypto::FunctionTracer<E>> createFunctionTracer(std::string fn) override {
        std::lock_guard<std::recursive_mutex> g(mu());
        if (foreign()) return std::make_unique<NullFunctionTracer<E>>();
        out() << "{\"ev\":\"begin\",\"fn\":\"" << fn << "\",\"d\":" << m_depth << "}\n";
        return std::make_unique<FunctionTracer>(this, m_depth++);
    }

private:
    std::shared_ptr<std::ostream> m_o;
    std::unordered_map<std::string, size_t> m_idx;
    std::vector<Obj> m_objs;
};

inline FunctionTracer::FunctionTracer(Tracer* tr, int depth) : fhecheck::JsonFunctionTracer(tr, depth), m_ptr(tr) {}
template <typename C>
void FunctionTracer::cap(const C& c) {
    if (c) m_ptr->noteCt(c);
}
template <typename P>
void FunctionTracer::capPt(const P& p) {
    if (p) m_ptr->notePt(p);
}

inline void attach(const CryptoContext<E>& cc, std::shared_ptr<Tracer> tr) {
    cc->setTracer(std::shared_ptr<lbcrypto::Tracer<E>>(tr));
}
inline void detach(const CryptoContext<E>& cc) {
    cc->setTracer(std::make_shared<NullTracer<E>>());
}

// ---------------------------------------------------------------------------------------------
// params.json (same as bgv_demo paramsJson)
// ---------------------------------------------------------------------------------------------
using fhecheck::scalName;

// params.json: exactly what the frontend's tracer writes (fhecheck::paramsJson)
inline std::string paramsJson(const CryptoContext<E>& cc) { return fhecheck::paramsJson(*cc); }

// ---------------------------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------------------------
inline std::string jstr(const std::string& s) {
    std::string r = "\"";
    for (unsigned char c : s) {
        if (c == '"') r += "\\\"";
        else if (c == '\\') r += "\\\\";
        else if (c == '\n') r += "\\n";
        else if (c == '\t') r += "\\t";
        else if (c < 0x20 || c >= 0x7f) { char b[8]; snprintf(b, sizeof b, "\\u%04x", c); r += b; }
        else r += (char)c;
    }
    return r + "\"";
}

// Signed integer vector of a "small" RNS polynomial: every limb must hold the same centred vector.
// Returns false if the limbs disagree or a centred value is not small (|v| >= 2^31).
inline bool centredSmall(const E& x, std::vector<int64_t>& out) {
    E c(x);
    c.SetFormat(Format::COEFFICIENT);
    size_t n = c.GetRingDimension();
    out.assign(n, 0);
    for (size_t l = 0; l < c.GetNumOfElements(); l++) {
        const NativePoly& z = c.GetElementAtIndex(l);
        uint64_t q          = z.GetModulus().ConvertToInt();
        for (size_t i = 0; i < n; i++) {
            uint64_t v = z[i].ConvertToInt();
            int64_t s  = v > q / 2 ? -(int64_t)(q - v) : (int64_t)v;
            if (s >= (int64_t(1) << 31) || s <= -(int64_t(1) << 31)) return false;
            if (l == 0) out[i] = s;
            else if (out[i] != s) return false;
        }
    }
    return true;
}

class PolyWriter {
public:
    explicit PolyWriter(const std::string& path) : m_f(fopen(path.c_str(), "w")) {
        if (!m_f) throw std::runtime_error("cannot write " + path);
        setvbuf(m_f, nullptr, _IOFBF, 1 << 22);
    }
    ~PolyWriter() { if (m_f) fclose(m_f); }
    void close() { if (m_f) { fclose(m_f); m_f = nullptr; } }
    // all limbs of an RNS polynomial, coefficient representation
    void rns(const std::string& name, const E& x) {
        E c(x);
        c.SetFormat(Format::COEFFICIENT);
        for (size_t l = 0; l < c.GetNumOfElements(); l++) native(name, l, c.GetElementAtIndex(l));
    }
    // one NativePoly (must be in coefficient representation)
    void native(const std::string& name, size_t limb, const NativePoly& z, uint64_t modOverride = 0) {
        uint64_t q = modOverride ? modOverride : z.GetModulus().ConvertToInt();
        fprintf(m_f, "%s %zu %llu", name.c_str(), limb, (unsigned long long)q);
        for (size_t i = 0; i < z.GetLength(); i++) {
            uint64_t v = z[i].ConvertToInt();
            if (v >= q) throw std::runtime_error("residue out of range in " + name);
            fprintf(m_f, " %llu", (unsigned long long)v);
        }
        fputc('\n', m_f);
    }
    void sgn(const std::string& name, const std::vector<int64_t>& v) {
        fprintf(m_f, "%s 0 0", name.c_str());
        for (auto x : v) fprintf(m_f, " %lld", (long long)x);
        fputc('\n', m_f);
    }

private:
    FILE* m_f;
};

// ---------------------------------------------------------------------------------------------
// Case
// ---------------------------------------------------------------------------------------------
class Case {
public:
    struct Enc {
        std::string ct, pt, how;
        bool have = false;
        std::vector<int64_t> u, e1, e2;
    };

    Case(std::string outdir, std::string name, uint64_t seed, std::string generator, CryptoContext<E> cc)
        : m_out(std::move(outdir)), m_name(std::move(name)), m_seed(seed), m_gen(std::move(generator)), m_cc(cc) {
        m_cp = std::dynamic_pointer_cast<CryptoParametersBGVRNS>(cc->GetCryptoParameters());
        if (!m_cp) throw std::runtime_error("not a BGVRNS context");
    }

    // Notes may quote OpenFHE exception texts, which carry the absolute path of a source file:
    // only the part from the last "/src/" or "/include/" on is kept (the build directory is not
    // part of the record).
    void note(const std::string& s0) {
        std::string s;
        size_t i = 0;
        while (i < s0.size()) {
            if (s0[i] == '/' && (i == 0 || s0[i - 1] == ' ')) {
                size_t e = i;
                while (e < s0.size() && s0[e] != ' ' && s0[e] != ':') e++;
                std::string tok = s0.substr(i, e - i);
                size_t k = tok.rfind("/src/");
                if (k == std::string::npos) k = tok.rfind("/include/");
                s += k == std::string::npos ? tok.substr(tok.rfind('/') + 1) : tok.substr(k + 1);
                i = e;
            }
            else
                s += s0[i++];
        }
        m_notes.push_back(s);
    }
    const std::vector<std::string>& notes() const { return m_notes; }
    void setFinal(const std::vector<Ciphertext<E>>& f) { m_final = f; }
    void setKeys(const KeyPair<E>& kp) { m_kp = kp; }
    const KeyPair<E>& keys() const { return m_kp; }
    void setInputsArbitrary(bool b) { m_arbitrary = b; }

    // The sampler OpenFHE uses for the secret and for the encryption randomness v
    // (v1.6.1: base-pke.cpp:60-76, rns-pke.cpp:168-169).
    E drawSecretLike(const std::shared_ptr<E::Params>& params, bool forKey) const {
        const auto& dgg = m_cp->GetDiscreteGaussianGenerator();
        E::TugType tug;
        switch (m_cp->GetSecretKeyDist()) {
            case GAUSSIAN: return E(dgg, params, Format::EVALUATION);
            case SPARSE_TERNARY:
                // KeyGen uses h = 192 (base-pke.cpp:72); EncryptZeroCore uses the plain TUG for
                // every non-GAUSSIAN distribution (rns-pke.cpp:168-169)
                return forKey ? E(tug, params, Format::EVALUATION, 192) : E(tug, params, Format::EVALUATION);
            default: return E(tug, params, Format::EVALUATION);
        }
    }

    // cc->KeyGen() with PRNG replay (v1.6.1 base-pke.cpp:48-103: s, a, e, then the key tags).
    KeyPair<E> keyGen() {
        bool scripted = Prng::scriptRemaining() > 0;
        uint64_t st0  = Prng::getState();
        m_kp          = m_cc->KeyGen();
        uint64_t st1  = Prng::getState();
        if (scripted) {
            note("keyGen: PRNG script queue was in use, pk.e not captured");
            return m_kp;
        }
        const auto paramsPK = m_cp->GetParamsPK();
        const auto ns       = m_cp->GetNoiseScale();
        const auto& dgg     = m_cp->GetDiscreteGaussianGenerator();
        const auto& pk      = m_kp.publicKey->GetPublicElements();
        size_t sizeQ        = m_cp->GetElementParams()->GetParams().size();
        size_t sizePK       = paramsPK->GetParams().size();
        // v1.6.1 (base-pke.cpp:48-103): s, a, e are drawn first, then the KeyPair constructor draws
        // the key tags (GenerateUniqueKeyID, privatekey.h:62). v1.3.1 drew the tags first. Both
        // orders are tried: `prefix` words before s, `suffix` words after e.
        for (int prefix : {0, 4, 8, 12}) {
            Prng::setState(st0);
            std::uniform_int_distribution<uint32_t> d(0, std::numeric_limits<uint32_t>::max());
            for (int i = 0; i < prefix; i++) d(PseudoRandomNumberGenerator::GetPRNG());
            E s = drawSecretLike(paramsPK, true);
            E::DugType dug;
            E a(dug, paramsPK, Format::EVALUATION);
            E e(dgg, paramsPK, Format::EVALUATION);
            int suffix = -1;
            for (int k = 0; k <= 32; k++) {
                if (Prng::getState() == st1) { suffix = k; break; }
                d(PseudoRandomNumberGenerator::GetPRNG());
            }
            if (suffix < 0) continue;
            E b(ns * e - a * s);
            E sDrop(s);
            if (sizePK > sizeQ) sDrop.DropLastElements(sizePK - sizeQ);
            if (sDrop == m_kp.secretKey->GetPrivateElement() && a == pk[1] && b == pk[0]) {
                if (!centredSmall(e, m_pkE)) throw std::runtime_error("keyGen replay: e is not a small vector");
                m_havePkE = true;
                note("keyGen: PRNG replay matched (" + std::to_string(prefix) + " words before s, then s, a, e over " +
                     std::to_string(sizePK) + " limbs (paramsPK), then " + std::to_string(suffix) +
                     " key-tag words; secret stored over " +
                     std::to_string(m_kp.secretKey->GetPrivateElement().GetNumOfElements()) +
                     " limbs); checked in C++: replayed s == secret, a == pk[1], ns*e - a*s == pk[0]");
                break;
            }
        }
        Prng::setState(st1);
        if (!m_havePkE) note("keyGen: PRNG REPLAY DID NOT MATCH for any key-tag placement; pk.e = null");
        return m_kp;
    }

    // cc->Encrypt(pk, pt) with PRNG replay of OpenFHE's (v, e0, e1) (rns-pke.cpp:152-200).
    Ciphertext<E> encrypt(const std::shared_ptr<Tracer>& tr, Plaintext pt) {
        bool scripted    = Prng::scriptRemaining() > 0;
        uint64_t st0     = Prng::getState();
        Ciphertext<E> ct = m_cc->Encrypt(m_kp.publicKey, pt);
        uint64_t st1     = Prng::getState();
        Enc en;
        en.ct  = tr->noteCt(ct);
        en.pt  = tr->notePt(pt);
        en.how = "none";
        if (scripted) {
            note("encrypt " + en.ct + ": PRNG script queue in use, randomness not replayable");
        }
        else {
            Prng::setState(st0);
            const auto params = pt->GetElement<E>().GetParams();
            const auto& dgg   = m_cp->GetDiscreteGaussianGenerator();
            E v               = drawSecretLike(params, false);
            E e0(dgg, params, Format::EVALUATION);
            E e1(dgg, params, Format::EVALUATION);
            bool stOk = Prng::getState() == st1;
            Prng::setState(st1);
            if (stOk && checkEnc(ct, pt, v, e0, e1)) {
                if (!centredSmall(v, en.u) || !centredSmall(e0, en.e1) || !centredSmall(e1, en.e2))
                    throw std::runtime_error("encrypt replay: sampler output is not a small vector");
                en.have = true;
                en.how  = "prng-replay";
            }
            else {
                note("encrypt " + en.ct + ": PRNG REPLAY DID NOT MATCH (" +
                     (stOk ? "state ok, ciphertext differs" : "different number of draws") + "); randomness none");
            }
        }
        m_encs.push_back(std::move(en));
        return ct;
    }

    // The caller scripted the PRNG and knows the sampler outputs.
    Ciphertext<E> encryptScripted(const std::shared_ptr<Tracer>& tr, Plaintext pt, const std::vector<int64_t>& u,
                                  const std::vector<int64_t>& e1, const std::vector<int64_t>& e2) {
        Ciphertext<E> ct = m_cc->Encrypt(m_kp.publicKey, pt);
        Enc en;
        en.ct  = tr->noteCt(ct);
        en.pt  = tr->notePt(pt);
        en.how = "none";
        const auto params = pt->GetElement<E>().GetParams();
        if (checkEnc(ct, pt, fromSigned(u, params), fromSigned(e1, params), fromSigned(e2, params))) {
            en.have = true;
            en.how  = "scripted";
            en.u = u; en.e1 = e1; en.e2 = e2;
        }
        else {
            note("encryptScripted " + en.ct + ": the claimed (u, e1, e2) do not reproduce the ciphertext; none");
        }
        m_encs.push_back(std::move(en));
        return ct;
    }

    // A hand-built input ciphertext (not an encryption).
    std::string addInput(const std::shared_ptr<Tracer>& tr, const Ciphertext<E>& ct) {
        m_arbitrary = true;
        return tr->noteCt(ct);
    }

    static E fromSigned(const std::vector<int64_t>& v, const std::shared_ptr<E::Params>& params) {
        E r(params, Format::COEFFICIENT, true);
        for (size_t l = 0; l < r.GetNumOfElements(); l++) {
            NativePoly z = r.GetElementAtIndex(l);
            uint64_t q   = z.GetModulus().ConvertToInt();
            for (size_t i = 0; i < v.size(); i++) z[i] = v[i] < 0 ? q - (uint64_t)(-v[i]) : (uint64_t)v[i];
            r.SetElementAtIndex(l, std::move(z));
        }
        r.SetFormat(Format::EVALUATION);
        return r;
    }

    // ct == (pk0|_l * v + ns*e0 + m, pk1|_l * v + ns*e1) with OpenFHE's DCRTPoly arithmetic
    bool checkEnc(const Ciphertext<E>& ct, const Plaintext& pt, const E& v, const E& e0, const E& e1) const {
        const auto& pk = m_kp.publicKey->GetPublicElements();
        const auto ns  = m_cp->GetNoiseScale();
        E m            = pt->GetElement<E>();
        m.SetFormat(Format::EVALUATION);
        E p0 = pk[0].Clone(), p1 = pk[1].Clone();
        size_t sizeQ = p0.GetNumOfElements(), sizeQl = m.GetNumOfElements();
        if (sizeQl > sizeQ) return false;
        if (sizeQl != sizeQ) {
            p0.DropLastElements(sizeQ - sizeQl);
            p1.DropLastElements(sizeQ - sizeQl);
        }
        E c0 = p0 * v + ns * e0 + m;
        E c1 = p1 * v + ns * e1;
        const auto& cv = ct->GetElements();
        return cv.size() == 2 && cv[0] == c0 && cv[1] == c1;
    }

    // -----------------------------------------------------------------------------------------
    void write(const std::shared_ptr<Tracer>& tr) {
        tr->flush();
        detach(m_cc);  // nothing below is traced
        PolyWriter pw(m_out + "/polys.txt");
        std::ostringstream j;
        const uint64_t t = m_cp->GetPlaintextModulus();
        const auto qp    = m_cp->GetElementParams()->GetParams();
        j << "{\n \"format\": \"openfhe-pin/v1\",\n \"case\": " << jstr(m_name) << ",\n \"seed\": \"" << m_seed
          << "\",\n \"generator\": " << jstr(m_gen) << ",\n \"N\": " << m_cc->GetRingDimension() << ", \"t\": \"" << t
          << "\",\n \"qs\": [";
        for (size_t i = 0; i < qp.size(); i++) j << (i ? ", " : "") << "\"" << qp[i]->GetModulus() << "\"";
        j << "],\n \"special\": [";
        bool hybrid = m_cp->GetKeySwitchTechnique() == HYBRID && m_cp->GetParamsP();
        if (hybrid) {
            auto p = m_cp->GetParamsP()->GetParams();
            for (size_t i = 0; i < p.size(); i++) j << (i ? ", " : "") << "\"" << p[i]->GetModulus() << "\"";
        }
        j << "],\n \"scaling\": \"" << scalName(m_cp->GetScalingTechnique()) << "\",\n \"dnum\": "
          << m_cp->GetNumPartQ() << ", \"towersPerDigit\": " << m_cp->GetNumPerPartQ() << ",\n";

        // secret
        const E& s = m_kp.secretKey->GetPrivateElement();
        std::vector<int64_t> sv;
        if (!centredSmall(s, sv))
            throw std::runtime_error("secret key limbs are not one small integer vector");  // in-exporter assertion
        pw.sgn("s", sv);
        pw.rns("s.rns", s);
        {
            int64_t mx = 0; size_t hw = 0;
            for (auto x : sv) { mx = std::max<int64_t>(mx, std::llabs(x)); hw += x != 0; }
            note("secret: " + std::to_string(s.GetNumOfElements()) + " limbs, max |coefficient| " +
                 std::to_string(mx) + ", Hamming weight " + std::to_string(hw) +
                 "; every limb is the same centred integer vector (asserted)");
        }
        j << " \"secret\": \"s\",\n \"secretRns\": \"s.rns\",\n";
        // public key
        const auto& pk = m_kp.publicKey->GetPublicElements();
        pw.rns("pk.b", pk[0]);
        pw.rns("pk.a", pk[1]);
        if (m_havePkE) pw.sgn("pk.e", m_pkE);
        j << " \"public\": {\"b\": \"pk.b\", \"a\": \"pk.a\", \"e\": " << (m_havePkE ? "\"pk.e\"" : "null")
          << ", \"randomness\": \"" << (m_havePkE ? "prng-replay" : "none") << "\"},\n";
        note("public key: " + std::to_string(pk[0].GetNumOfElements()) + " limbs; ciphertext chain (params.json qs): " +
             std::to_string(qp.size()) + " limbs");

        // eval keys
        j << " \"evalKeys\": [";
        bool first = true;
        auto dumpKey = [&](const EvalKey<E>& ek, const std::string& base, const std::string& head) {
            const auto& bv = ek->GetBVector();
            const auto& av = ek->GetAVector();
            j << (first ? "\n  " : ",\n  ") << "{" << head << "\"digits\": [";
            first = false;
            for (size_t d = 0; d < bv.size(); d++) {
                std::string bn = base + ".b" + std::to_string(d), an = base + ".a" + std::to_string(d);
                pw.rns(bn, bv[d]);
                pw.rns(an, av[d]);
                j << (d ? ", " : "") << "{\"b\": \"" << bn << "\", \"a\": \"" << an << "\"}";
            }
            j << "]}";
            return bv.empty() ? size_t(0) : bv[0].GetNumOfElements();
        };
        const std::string tag = m_kp.secretKey->GetKeyTag();
        size_t keyLimbs = 0, nRelin = 0, nRot = 0;
        try {
            const auto& mk = CryptoContextImpl<E>::GetEvalMultKeyVector(tag);
            for (size_t i = 0; i < mk.size(); i++) {
                // mk[i] switches s^(i+2) -> s (EvalMultKeysGen); i = 0 is the relinearization key
                std::string head = i == 0 ? "\"kind\": \"relin\", " :
                                            "\"kind\": \"relin\", \"power\": " + std::to_string(i + 2) + ", ";
                keyLimbs = dumpKey(mk[i], i == 0 ? "ekm" : "ekm" + std::to_string(i + 2), head);
                nRelin++;
            }
        }
        catch (const std::exception&) {
        }
        try {
            const auto& am = CryptoContextImpl<E>::GetEvalAutomorphismKeyMap(tag);
            for (const auto& kv : am) {
                keyLimbs = dumpKey(kv.second, "eka" + std::to_string(kv.first),
                                   "\"kind\": \"rot\", \"index\": " + std::to_string(kv.first) + ", ");
                nRot++;
            }
        }
        catch (const std::exception&) {
        }
        j << (first ? "" : "\n ") << "],\n";
        note("eval keys: " + std::to_string(nRelin) + " EvalMult key(s), " + std::to_string(nRot) +
             " automorphism key(s), each digit over " + std::to_string(keyLimbs) + " limbs (Q then P)");

        // encryptions
        j << " \"encryptions\": [";
        for (size_t i = 0; i < m_encs.size(); i++) {
            const Enc& en = m_encs[i];
            std::string b = "enc" + std::to_string(i + 1);
            j << (i ? ",\n  " : "\n  ") << "{\"ct\": \"" << en.ct << "\", \"pt\": \"" << en.pt << "\", ";
            if (en.have) {
                pw.sgn(b + ".u", en.u);
                pw.sgn(b + ".e1", en.e1);
                pw.sgn(b + ".e2", en.e2);
                j << "\"u\": \"" << b << ".u\", \"e1\": \"" << b << ".e1\", \"e2\": \"" << b << ".e2\", ";
            }
            else
                j << "\"u\": null, \"e1\": null, \"e2\": null, ";
            j << "\"randomness\": \"" << en.how << "\"}";
        }
        j << (m_encs.empty() ? "" : "\n ") << "],\n";

        // objects
        uint64_t calls0 = Prng::handle() ? Prng::calls() : 0;
        j << " \"objects\": {";
        const auto& objs = tr->objects();
        size_t nDec = 0, nDecErr = 0;
        for (size_t k = 0; k < objs.size(); k++) {
            const Obj& o = objs[k];
            j << (k ? ",\n  " : "\n  ") << "\"" << o.id << "\": ";
            if (!o.isCt) {
                pw.rns(o.id + ".p", o.ptElem);
                j << "{\"kind\": \"pt\", \"towers\": " << o.towers << ", \"nsd\": " << o.nsd << ", \"sf\": \"" << o.sf
                  << "\", \"level\": " << o.level << ", \"encoding\": " << jstr(o.encoding) << ", \"poly\": \""
                  << o.id << ".p\"}";
                continue;
            }
            const auto& el = o.ct->GetElements();
            j << "{\"kind\": \"ct\", \"towers\": " << o.towers << ", \"parts\": " << el.size() << ", \"nsd\": " << o.nsd
              << ", \"sf\": \"" << o.sf << "\", \"level\": " << o.level << ", \"polys\": [";
            for (size_t i = 0; i < el.size(); i++) {
                std::string n = o.id + "." + std::to_string(i);
                pw.rns(n, el[i]);
                j << (i ? ", " : "") << "\"" << n << "\"";
            }
            j << "]";
            if (el.size() >= 2 && el[0].GetFormat() != Format::EVALUATION) j << ", \"format\": \"COEFFICIENT\"";
            if (el.size() < 2) {
                j << ", \"decrypt\": null}";
                continue;
            }
            try {
                NativePoly raw;
                auto dr = m_cc->GetScheme()->Decrypt(o.ct, m_kp.secretKey, &raw);
                if (raw.GetFormat() != Format::COEFFICIENT) raw.SetFormat(Format::COEFFICIENT);
                // raw's own modulus is t (poly-impl.h:626-635 builds it over ILNativeParams(c, ptm, 1))
                if (raw.GetModulus().ConvertToInt() != t)
                    throw std::runtime_error("Decrypt output modulus is not t");
                pw.native(o.id + ".dec", 0, raw);
                std::string q0name = "null";
                NativePoly rq;
                if (el[0].GetFormat() == Format::EVALUATION && phaseQ0(o.ct, rq)) {
                    // our re-computation of the polynomial Decrypt reduces mod t; only exported
                    // if reducing it the way OpenFHE does gives exactly Decrypt's output
                    NativePoly chk = rq.DecryptionCRTInterpolate(t);
                    bool same      = chk.GetLength() == raw.GetLength();
                    for (size_t i = 0; same && i < raw.GetLength(); i++) same = chk[i] == raw[i];
                    if (same) {
                        pw.native(o.id + ".decq", 0, rq);
                        q0name = "\"" + o.id + ".decq\"";
                    }
                    else
                        note(o.id + ": recomputed switched phase does not reduce to Decrypt's output; rawQ0 = null");
                }
                j << ", \"decrypt\": {\"raw\": \"" << o.id << ".dec\", \"rawQ0\": " << q0name << ", \"sf\": \""
                  << dr.scalingFactorInt << "\"}}";
                nDec++;
            }
            catch (const std::exception& ex) {
                j << ", \"decrypt\": null, \"decryptError\": " << jstr(ex.what()) << "}";
                nDecErr++;
            }
        }
        j << (objs.empty() ? "" : "\n ") << "},\n";
        if (Prng::handle() && Prng::calls() != calls0)
            throw std::runtime_error("Decrypt consumed PRNG output");  // must not draw
        note("decrypt: " + std::to_string(nDec) + " ciphertext(s) decrypted with cc->GetScheme()->Decrypt (untraced, " +
             "no PRNG draw: asserted), " + std::to_string(nDecErr) + " threw. `raw` is PKEBGVRNS::Decrypt's NativePoly " +
             "(bgvrns-pke.cpp:48-102): the phase c0 + c1 s (+ c2 s^2 ...) mod Q_l, ModReduce'd to one tower, read mod q0 " +
             "centred, reduced to [0, t) (NativePoly::DecryptionCRTInterpolate, poly-impl.h:626-635 -> NativeVector::Mod, " +
             "mubintvecnat.cpp:260-264); its own modulus is t. `rawQ0` is NOT returned by the library: the exporter " +
             "recomputes the one-tower polynomial (same DecryptCore formula and DCRTPoly::ModReduce calls, modulus q0) " +
             "and exports it only if DecryptionCRTInterpolate(t) of it equals `raw` coefficient by coefficient. " +
             "Decrypt is attempted for every ciphertext with >= 2 parts (FORMAT.md says 2 or 3; more parts occur only " +
             "in the threepart:* programs).");

        // build + ksInfo
        j << " \"build\": {\"WITH_REDUCED_NOISE\": "
#if defined(WITH_REDUCED_NOISE)
          << "true"
#else
          << "false"
#endif
          << ", \"WITH_OPENMP\": "
#if defined(WITH_OPENMP)
          << "true"
#else
          << "false"
#endif
          << ", \"NATIVEINT\": " << NATIVEINT << ", \"HAVE_INT128\": "
#if defined(HAVE_INT128)
          << "true"
#else
          << "false"
#endif
          << ", \"MATHBACKEND\": " << MATHBACKEND << ", \"WITH_NATIVEOPT\": "
#if defined(WITH_NATIVEOPT)
          << "true"
#else
          << "false"
#endif
          << ", \"clang\": "
#if defined(__clang__)
          << "true"
#else
          << "false"
#endif
          << ", \"ompMaxThreads\": " << omp_get_max_threads() << "},\n";
        j << " \"ksInfo\": {\"numPartQ\": " << m_cp->GetNumPartQ() << ", \"numPerPartQ\": " << m_cp->GetNumPerPartQ()
          << ", \"numberOfQPartitions\": " << (hybrid ? m_cp->GetNumberOfQPartitions() : 0) << ", \"sizeQ\": "
          << qp.size() << ", \"sizeP\": " << (hybrid ? m_cp->GetParamsP()->GetParams().size() : 0)
          << ", \"keyLimbs\": " << keyLimbs << ",\n            \"perLevel\": [";
        if (hybrid) {
            // KeySwitchHYBRID::EvalKeySwitchPrecomputeCore, keyswitch-hybrid.cpp:314-316
            uint32_t alpha = m_cp->GetNumPerPartQ();
            for (size_t l = 1; l <= qp.size(); l++) {
                uint32_t numPartQl = ceil((static_cast<double>(l)) / alpha);
                if (numPartQl > m_cp->GetNumberOfQPartitions()) numPartQl = m_cp->GetNumberOfQPartitions();
                j << (l > 1 ? ", " : "") << "{\"towers\": " << l << ", \"numPartitions\": " << numPartQl
                  << ", \"digitTowers\": [";
                for (uint32_t part = 0; part < numPartQl; part++) {
                    size_t sz = part == numPartQl - 1 ? l - alpha * part :
                                                        m_cp->GetParamsPartQ(part)->GetParams().size();
                    j << (part ? "," : "") << sz;
                }
                j << "], \"complTowers\": [";
                for (uint32_t part = 0; part < numPartQl; part++)
                    j << (part ? "," : "") << m_cp->GetParamsComplPartQ(l - 1, part)->GetParams().size();
                j << "]}";
            }
        }
        j << "]},\n";
        j << " \"inputsArbitrary\": " << (m_arbitrary ? "true" : "false") << ",\n";
        j << " \"final\": [";
        for (size_t i = 0; i < m_final.size(); i++) j << (i ? ", " : "") << "\"" << tr->idOf(m_final[i], "ct") << "\"";
        j << "],\n \"notes\": [";
        for (size_t i = 0; i < m_notes.size(); i++) j << (i ? ",\n  " : "\n  ") << jstr(m_notes[i]);
        j << "\n ]\n}\n";
        pw.close();
        std::ofstream f(m_out + "/pin.json");
        f << j.str();
    }

    // The one-tower polynomial PKEBGVRNS::Decrypt reduces mod t (EVALUATION branch,
    // bgvrns-pke.cpp:56-75), recomputed with the same calls. False if it cannot be formed.
    bool phaseQ0(const Ciphertext<E>& ct, NativePoly& out) const {
        const auto& cv = ct->GetElements();
        const E& s     = m_kp.secretKey->GetPrivateElement();
        size_t sizeQ = s.GetNumOfElements(), sizeQl = cv[0].GetNumOfElements();
        if (sizeQl == 0 || sizeQl > sizeQ) return false;
        E scopy(s);
        scopy.DropLastElements(sizeQ - sizeQl);
        E sPower(scopy);
        E b(cv[0]);
        b.SetFormat(Format::EVALUATION);
        for (size_t i = 1; i < cv.size(); i++) {
            E ci = cv[i];
            ci.SetFormat(Format::EVALUATION);
            b += sPower * ci;
            sPower *= scopy;
        }
        b.SetFormat(Format::COEFFICIENT);
        for (size_t i = sizeQl - 1; i > 0; --i)
            b.ModReduce(m_cp->GetPlaintextModulus(), m_cp->GettModqPrecon(), m_cp->GetNegtInvModq(i),
                        m_cp->GetNegtInvModqPrecon(i), m_cp->GetqlInvModq(i), m_cp->GetqlInvModqPrecon(i));
        out = b.GetElementAtIndex(0);
        return true;
    }

private:
    std::string m_out, m_name;
    uint64_t m_seed;
    std::string m_gen;
    CryptoContext<E> m_cc;
    std::shared_ptr<CryptoParametersBGVRNS> m_cp;
    KeyPair<E> m_kp;
    bool m_havePkE = false, m_arbitrary = false;
    std::vector<int64_t> m_pkE;
    std::vector<Enc> m_encs;
    std::vector<Ciphertext<E>> m_final;
    std::vector<std::string> m_notes;
};

}  // namespace pin
