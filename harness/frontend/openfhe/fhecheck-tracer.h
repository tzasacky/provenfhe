//==================================================================================
// fhecheck-tracer.h -- UNTRUSTED glue for lean-fhe's fhe_check OpenFHE frontend.
//
// Canonical copy: harness/frontend/openfhe/fhecheck-tracer.h in lean-fhe. openfhe/build_openfhe.sh
// copies it to src/pke/include/utils/fhecheck-tracer.h of upstream OpenFHE v1.6.1 after applying
// openfhe/openfhe-v1.6.1-tracer.patch (which adds the ENABLE_TRACER hooks and includes this file
// from cryptocontextfactory.cpp). It only OBSERVES: no hook changes a value OpenFHE computes.
//
// A Tracer for the ENABLE_TRACER hooks that writes one JSON object per line (read by
// harness/frontend/openfhe/extract.py):
//   {"ev":"begin","fn":"<OpenFHE function>","d":<nesting depth>}
//   {"ev":"in"|"out","d":..,"name":"..","kind":"ct","id":"ct_7","towers":3,"parts":2,"nsd":1,"sf":1}
//   {"ev":"in"|"out","d":..,"name":"..","kind":"pt","id":"pt_2","towers":3,"nsd":1,"sf":1,"level":0,
//    "enc":"packed","t":65537}
//   {"ev":"in"|"out","d":..,"name":"..","kind":"pk"|"sk"|"ek","id":"ek_3","tag":"<keyTag>"[,"index":5]}
//   {"ev":"in","d":..,"name":"..","kind":"int","v":5}
//   {"ev":"end","d":..}
//   {"ev":"error","what":"..."}      (the trace is unreliable; the extractor refuses it)
// Ids are content identities: "ct_<k>" names the k-th distinct SHA-256 digest (FIPS 180-4) of the
// object's content, i.e. every coefficient of every tower plus the metadata that changes what the
// library computes with it (ciphertext: format, moduli, level, noiseScaleDeg, scalingFactorInt,
// slots, encoding type, key tag; plaintext: the same for its DCRTPoly element plus the encoding
// type and its plaintext modulus t). The digest is RECOMPUTED at every registration (every traced
// use), so any change made outside the traced API (GetElements()/SetElements(), SetLevel,
// EvalAddInPlaceNoCheck, ... -- traced or not) gives the object a new id, which no traced
// operation produced: the extractor refuses it. Key ids ("pk_1", "sk_1", "ek_1") are content
// identities too (public elements; private element; the A and B vectors of an evaluation key),
// also recomputed at every use (no per-object cache), so the extractor can establish where each
// key used by the program came from (key provenance) and an in-place change of a stored key
// (SetAVector/SetBVector) is a key whose generation is not in the trace.
// The digest is collision resistant; the hash itself never appears in the trace (only the
// counter id), so the trace format does not depend on the hash function.
//
// Parameters: a tracer that watches its context (watch(cc); MaybeAutoTrace does this) records a
// fingerprint of the context's parameters (paramsJson without the FindLevelsToDrop tables) when it
// starts and compares it at the start of every top-level traced call; a change (a parameter
// setter called on the context after params.json was written) writes an "error" event, so the
// extractor refuses the trace.
//
// Threads: the tracer records the thread that created it. A traced call from any other thread,
// or from inside an active OpenMP parallel region, cannot be placed in the call tree reliably:
// it is not traced, and an "error" event is written instead (once), so that the extractor
// refuses the whole trace. All writes are serialised by a mutex, so concurrent calls cannot
// corrupt the file or crash the tracer. Run traced programs with OMP_NUM_THREADS=1.
//
// Global activation for unmodified programs: if the environment variable FHECHECK_TRACE_DIR is
// set when a BGVRNS or BFVRNS CryptoContext is registered with CryptoContextFactory
// (GenCryptoContext, or a deserialized context that is not yet known), the context gets a
// JsonTracer writing
//   $FHECHECK_TRACE_DIR/p<pid>.ctx<k>.trace.jsonl   and   p<pid>.ctx<k>.params.json
// (k = 1, 2, ... per process), params in the format of `bgv_demo dump` resp. `bfv_demo dump`
// (paramsJson below: "scheme" is "BGV" or "BFV").
//
// Tracer version: every params.json (paramsJson, both schemes) records "tracer":
// FHECHECK_TRACER_VERSION, and the extractors refuse a trace whose recorded version is not the
// version of the canonical header next to them (a trace from a stale OpenFHE install: rebuild
// with harness/frontend/openfhe/build_openfhe.sh). The version is tied to this file's content, so
// it cannot silently go stale: it is the SHA-256 of this file with the 64 hex digits of the
// #define below replaced by 64 '0's (harness/frontend/openfhe/tracer_version.py; after editing
// this file run `tracer_version.py --update-header` and regenerate the patch). A compile
// definition from build_openfhe.sh would not reach programs compiled against the installed header
// (bgv_demo, bfv_demo, user programs, which run paramsJson inline), and a generated header would
// differ from this canonical copy; a stale value here makes every new trace refused (fail closed)
// and harness/frontend/tests/run.sh checks the value. Only params.json carries it, not a trace
// event: a first trace line would shift every trace line number the extracted files record.
//==================================================================================
#ifndef SRC_PKE_INCLUDE_UTILS_FHECHECK_TRACER_H_
#define SRC_PKE_INCLUDE_UTILS_FHECHECK_TRACER_H_

#define FHECHECK_TRACER_VERSION "a3587ef6c3164c313d1dda0e7b3ae6b561bed4198b211acb5c2d95ef4dbf9252"

#include "config_core.h"

#ifdef ENABLE_TRACER

    #include "cryptocontext.h"
    #include "scheme/bgvrns/bgvrns-cryptoparameters.h"
    #include "scheme/bfvrns/bfvrns-cryptoparameters.h"
    #include "utils/tracing.h"

    #include <atomic>
    #include <cstdint>
    #include <cstdlib>
    #include <cstring>
    #include <fstream>
    #include <map>
    #include <memory>
    #include <mutex>
    #include <ostream>
    #include <sstream>
    #include <string>
    #include <thread>
    #include <unordered_map>
    #include <unistd.h>
    #ifdef _OPENMP
        #include <omp.h>
    #endif

namespace lbcrypto {
// Defined (not static, declared in no OpenFHE header) in pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp
// (v1.6.1: :98-198, default argument keySwitch = false there) and exported by libOPENFHEpke. It
// decides how many limbs HPSPOVERQLEVELED drops inside EvalMult / EvalSquare / RelinearizeCore;
// paramsJson evaluates it on the context (observation only: it reads the parameters).
uint32_t FindLevelsToDrop(uint32_t multiplicativeDepth, std::shared_ptr<CryptoParametersBase<DCRTPoly>> cryptoParams,
                          uint32_t dcrtBits, bool keySwitch);
}  // namespace lbcrypto

namespace fhecheck {
using namespace lbcrypto;
using E = DCRTPoly;

// SHA-256 (FIPS 180-4), streaming; the content identity of every traced object.
class Sha256 {
public:
    Sha256() {
        static const uint32_t h0[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                       0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
        for (int i = 0; i < 8; i++)
            m_h[i] = h0[i];
    }
    void update(const unsigned char* p, size_t n) {
        m_len += n;
        while (n > 0) {
            size_t k = 64 - m_fill;
            if (k > n)
                k = n;
            std::memcpy(m_buf + m_fill, p, k);
            m_fill += k;
            p += k;
            n -= k;
            if (m_fill == 64) {
                block(m_buf);
                m_fill = 0;
            }
        }
    }
    // little-endian 64-bit word
    void word(uint64_t v) {
        unsigned char b[8];
        for (int i = 0; i < 8; i++)
            b[i] = static_cast<unsigned char>(v >> (8 * i));
        update(b, 8);
    }
    std::string hex() {
        uint64_t bits = m_len * 8;
        unsigned char pad = 0x80;
        update(&pad, 1);
        unsigned char z = 0;
        while (m_fill != 56)
            update(&z, 1);
        unsigned char lb[8];
        for (int i = 0; i < 8; i++)
            lb[i] = static_cast<unsigned char>(bits >> (56 - 8 * i));
        update(lb, 8);
        static const char* d = "0123456789abcdef";
        std::string s;
        for (int i = 0; i < 8; i++)
            for (int j = 28; j >= 0; j -= 4)
                s += d[(m_h[i] >> j) & 0xf];
        return s;
    }

private:
    static uint32_t rotr(uint32_t x, int n) {
        return (x >> n) | (x << (32 - n));
    }
    void block(const unsigned char* p) {
        static const uint32_t K[64] = {
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
            0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
            0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
            0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
            0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
        uint32_t w[64];
        for (int i = 0; i < 16; i++)
            w[i] = (uint32_t(p[4 * i]) << 24) | (uint32_t(p[4 * i + 1]) << 16) | (uint32_t(p[4 * i + 2]) << 8) |
                   uint32_t(p[4 * i + 3]);
        for (int i = 16; i < 64; i++) {
            uint32_t s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
            uint32_t s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i]        = w[i - 16] + s0 + w[i - 7] + s1;
        }
        uint32_t a = m_h[0], b = m_h[1], c = m_h[2], d = m_h[3], e = m_h[4], f = m_h[5], g = m_h[6], h = m_h[7];
        for (int i = 0; i < 64; i++) {
            uint32_t t1 = h + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i];
            uint32_t t2 = (rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
            h           = g;
            g           = f;
            f           = e;
            e           = d + t1;
            d           = c;
            c           = b;
            b           = a;
            a           = t1 + t2;
        }
        m_h[0] += a;
        m_h[1] += b;
        m_h[2] += c;
        m_h[3] += d;
        m_h[4] += e;
        m_h[5] += f;
        m_h[6] += g;
        m_h[7] += h;
    }
    uint32_t m_h[8];
    unsigned char m_buf[64];
    size_t m_fill   = 0;
    uint64_t m_len  = 0;
};

class JsonTracer;
// The context's parameters as paramsJson prints them, without the FindLevelsToDrop tables (defined below).
inline std::string paramsFingerprint(const CryptoContextImpl<DCRTPoly>& cc);

class JsonFunctionTracer : public NullFunctionTracer<E> {
public:
    JsonFunctionTracer(JsonTracer* tr, int depth) : m_tr(tr), m_d(depth) {}
    ~JsonFunctionTracer() override;
    void registerInput(Ciphertext<E> c, std::string name, bool = false) override { ct("in", c, name); }
    void registerInput(ConstCiphertext<E> c, std::string name, bool = false) override { ct("in", c, name); }
    void registerInput(Plaintext p, std::string name, bool = false) override { pt(p, name, "in"); }
    void registerInput(ConstPlaintext p, std::string name, bool = false) override { pt(p, name, "in"); }
    void registerInput(int64_t v, std::string name, bool = false) override { num(std::to_string(v), name); }
    void registerInput(size_t v, std::string name, bool = false) override { num(std::to_string(v), name); }
    void registerInput(const std::vector<int32_t>& v, std::string name, bool = false) override { vec(v, name); }
    void registerInput(const std::vector<int64_t>& v, std::string name, bool = false) override { vec(v, name); }
    void registerInput(const std::vector<uint32_t>& v, std::string name, bool = false) override { vec(v, name); }
    // Keys (key provenance).
    void registerInput(const PublicKey<E> k, std::string name, bool = false) override { key("in", k, name); }
    void registerInput(const PrivateKey<E> k, std::string name, bool = false) override { key("in", k, name); }
    void registerInput(const EvalKey<E> k, std::string name, bool = false) override { key("in", k, name); }
    void registerInput(const std::shared_ptr<std::map<uint32_t, EvalKey<E>>>& m, std::string name,
                       bool = false) override {
        if (m)
            for (const auto& kv : *m)
                key("in", kv.second, name, static_cast<int64_t>(kv.first));
    }
    Ciphertext<E> registerOutput(Ciphertext<E> c, std::string name) override {
        ct("out", c, name);
        return c;
    }
    Plaintext registerOutput(Plaintext p, std::string name) override {
        pt(p, name, "out");
        return p;
    }
    ConstCiphertext<E> registerOutput(ConstCiphertext<E> c, std::string name) override {
        ct("out", c, name);
        return c;
    }
    std::vector<Ciphertext<E>> registerOutput(std::vector<Ciphertext<E>> cs, std::string name) override {
        for (auto& c : cs)
            ct("out", c, name);
        return cs;
    }
    KeyPair<E> registerOutput(KeyPair<E> kp, std::string name) override {
        key("out", kp.publicKey, name);
        key("out", kp.secretKey, name);
        return kp;
    }
    PublicKey<E> registerOutput(PublicKey<E> k, std::string name) override {
        key("out", k, name);
        return k;
    }
    PrivateKey<E> registerOutput(PrivateKey<E> k, std::string name) override {
        key("out", k, name);
        return k;
    }
    EvalKey<E> registerOutput(EvalKey<E> k, std::string name) override {
        key("out", k, name);
        return k;
    }
    // A vector of evaluation keys (EvalMultKeysGen: the key for s^(i+2)); "index" = position.
    std::vector<EvalKey<E>> registerOutput(std::vector<EvalKey<E>> ks, std::string name) override {
        for (size_t i = 0; i < ks.size(); i++)
            key("out", ks[i], name, static_cast<int64_t>(i));
        return ks;
    }
    // A map automorphism index -> key (rotation / automorphism key generation).
    std::shared_ptr<std::map<uint32_t, EvalKey<E>>> registerOutput(std::shared_ptr<std::map<uint32_t, EvalKey<E>>> m,
                                                                   std::string name) override {
        if (m)
            for (const auto& kv : *m)
                key("out", kv.second, name, static_cast<int64_t>(kv.first));
        return m;
    }
private:
    template <typename C>
    void ct(const char* io, const C& c, const std::string& name);
    template <typename P>
    void pt(const P& p, const std::string& name, const char* io);
    void num(const std::string& v, const std::string& name);
    template <typename T>
    void vec(const std::vector<T>& v, const std::string& name);
    template <typename K>
    void key(const char* io, const K& k, const std::string& name, int64_t index = -1);
    JsonTracer* m_tr;
    int m_d;
};

class JsonTracer : public Tracer<E> {
public:
    explicit JsonTracer(std::shared_ptr<std::ostream> out)
        : m_out(std::move(out)), m_owner(std::this_thread::get_id()) {}
    std::ostream& out() { return *m_out; }
    std::recursive_mutex& mu() { return m_mu; }
    int m_depth = 0;

    static void mix(Sha256& h, uint64_t v) {
        h.word(v);
    }
    static void mixStr(Sha256& h, const std::string& s) {
        mix(h, s.size());
        h.update(reinterpret_cast<const unsigned char*>(s.data()), s.size());
    }
    static void mixPoly(Sha256& h, const DCRTPoly& e) {
        mix(h, static_cast<uint64_t>(e.GetFormat()));
        mix(h, e.GetNumOfElements());
        std::vector<unsigned char> buf;
        for (const auto& tw : e.GetAllElements()) {
            mix(h, tw.GetModulus().ConvertToInt());
            const auto& v = tw.GetValues();
            mix(h, v.GetLength());
            buf.resize(8 * v.GetLength());
            for (size_t i = 0; i < v.GetLength(); i++) {
                uint64_t x = v[i].ConvertToInt();
                for (int j = 0; j < 8; j++)
                    buf[8 * i + j] = static_cast<unsigned char>(x >> (8 * j));
            }
            h.update(buf.data(), buf.size());
        }
    }
    static std::string hashOf(const ConstCiphertext<E>& c) {
        Sha256 h;
        mix(h, 0xC7);
        mix(h, c->GetElements().size());
        for (const auto& e : c->GetElements())
            mixPoly(h, e);
        mix(h, c->GetLevel());
        mix(h, c->GetNoiseScaleDeg());
        mix(h, c->GetScalingFactorInt().ConvertToInt());
        mix(h, c->GetSlots());
        mix(h, static_cast<uint64_t>(c->GetEncodingType()));
        mixStr(h, c->GetKeyTag());
        return h.hex();
    }
    static uint64_t ptModulus(const ConstPlaintext& p) {
        auto ep = p->GetEncodingParams();
        return ep ? static_cast<uint64_t>(ep->GetPlaintextModulus()) : 0;
    }
    static std::string hashOf(const ConstPlaintext& p) {
        Sha256 h;
        mix(h, 0x97);
        mixPoly(h, p->GetElement<DCRTPoly>());
        mix(h, p->GetLevel());
        mix(h, p->GetNoiseScaleDeg());
        mix(h, p->GetScalingFactorInt().ConvertToInt());
        mix(h, static_cast<uint64_t>(p->GetEncodingType()));
        mix(h, ptModulus(p));
        return h.hex();
    }
    static std::string hashOf(const PublicKey<E>& k) {
        Sha256 h;
        mix(h, 0x9B);
        mix(h, k->GetPublicElements().size());
        for (const auto& e : k->GetPublicElements())
            mixPoly(h, e);
        mixStr(h, k->GetKeyTag());
        return h.hex();
    }
    static std::string hashOf(const PrivateKey<E>& k) {
        Sha256 h;
        mix(h, 0x5C);
        mixPoly(h, k->GetPrivateElement());
        mixStr(h, k->GetKeyTag());
        return h.hex();
    }
    // Every BGV/BFV evaluation key is an EvalKeyRelinImpl; for another kind GetAVector throws and
    // the key has no content identity: "" (the caller poisons the trace).
    static std::string hashOf(const EvalKey<E>& k) {
        Sha256 h;
        mix(h, 0xE7);
        try {
            mix(h, k->GetAVector().size());
            for (const auto& e : k->GetAVector())
                mixPoly(h, e);
            mix(h, k->GetBVector().size());
            for (const auto& e : k->GetBVector())
                mixPoly(h, e);
        }
        catch (...) {
            return "";
        }
        mixStr(h, k->GetKeyTag());
        return h.hex();
    }

    std::string label(const std::string& prefix, const std::string& digest) {
        std::string h = prefix + ":" + digest;
        auto it       = m_ids.find(h);
        if (it != m_ids.end())
            return it->second;
        std::string id = prefix + "_" + std::to_string(++m_cnt[prefix]);
        m_ids[h]       = id;
        return id;
    }
    // Recomputed at every call (every traced use), for every kind of object (no cache).
    template <typename T>
    std::string idOf(const T& obj, const std::string& prefix) {
        std::string d = hashOf(obj);
        if (d.empty()) {
            poison("an evaluation key that is not an EvalKeyRelinImpl has no content identity");
            d = "unidentified";
        }
        return label(prefix, d);
    }

    // Writes an "error" event (once): the extractor refuses a trace that contains one.
    void poison(const std::string& what) {
        if (m_poisoned)
            return;
        m_poisoned = true;
        *m_out << "{\"ev\":\"error\",\"what\":\"" << what << "\"}\n";
        m_out->flush();
    }
    // Writes the "error" event (once) and returns true if the current call must not be traced.
    bool foreign() {
        bool par = false;
    #ifdef _OPENMP
        par = omp_in_parallel() != 0;
    #endif
        if (std::this_thread::get_id() == m_owner && !par)
            return false;
        poison(
            "a traced OpenFHE call ran on another thread or inside an OpenMP parallel region; the call tree is not "
            "reliable (run with OMP_NUM_THREADS=1)");
        return true;
    }

    // Watch the parameters of `cc` (the context this tracer is set on): see the header comment.
    void watch(const std::shared_ptr<CryptoContextImpl<DCRTPoly>>& cc) {
        std::lock_guard<std::recursive_mutex> g(m_mu);
        m_cc     = cc;
        m_params = cc ? paramsFingerprint(*cc) : "";
    }

protected:
    std::unique_ptr<FunctionTracer<E>> createFunctionTracer(std::string fn) override {
        std::lock_guard<std::recursive_mutex> g(m_mu);
        if (foreign())
            return std::make_unique<NullFunctionTracer<E>>();
        if (m_depth == 0 && !m_params.empty()) {
            auto cc = m_cc.lock();
            if (cc && paramsFingerprint(*cc) != m_params)
                poison("the parameters of the CryptoContext changed after params.json was written (a parameter setter "
                       "was called on the context before " +
                       fn + "); params.json does not describe the context the program ran with");
        }
        *m_out << "{\"ev\":\"begin\",\"fn\":\"" << fn << "\",\"d\":" << m_depth << "}\n";
        return std::make_unique<JsonFunctionTracer>(this, m_depth++);
    }

private:
    std::shared_ptr<std::ostream> m_out;
    std::thread::id m_owner;
    std::recursive_mutex m_mu;
    bool m_poisoned = false;
    std::unordered_map<std::string, std::string> m_ids;
    std::unordered_map<std::string, size_t> m_cnt;
    std::weak_ptr<CryptoContextImpl<DCRTPoly>> m_cc;
    std::string m_params;
};

inline JsonFunctionTracer::~JsonFunctionTracer() {
    std::lock_guard<std::recursive_mutex> g(m_tr->mu());
    m_tr->out() << "{\"ev\":\"end\",\"d\":" << m_d << "}\n";
    m_tr->m_depth--;
    if (m_d == 0)
        m_tr->out().flush();
}

template <typename C>
void JsonFunctionTracer::ct(const char* io, const C& c, const std::string& name) {
    if (!c)
        return;
    std::lock_guard<std::recursive_mutex> g(m_tr->mu());
    auto& el = c->GetElements();
    m_tr->out() << "{\"ev\":\"" << io << "\",\"d\":" << m_d << ",\"name\":\"" << name << "\",\"kind\":\"ct\",\"id\":\""
                << m_tr->idOf(ConstCiphertext<E>(c), "ct")
                << "\",\"towers\":" << (el.empty() ? 0 : el[0].GetNumOfElements()) << ",\"parts\":" << el.size()
                << ",\"nsd\":" << c->GetNoiseScaleDeg() << ",\"sf\":" << c->GetScalingFactorInt() << "}\n";
}

inline std::string encName(PlaintextEncodings e) {
    switch (e) {
        case PACKED_ENCODING:
            return "packed";
        case COEF_PACKED_ENCODING:
            return "coefpacked";
        case STRING_ENCODING:
            return "string";
        case CKKS_PACKED_ENCODING:
            return "ckkspacked";
        default:
            return "other" + std::to_string(static_cast<int>(e));
    }
}

template <typename P>
void JsonFunctionTracer::pt(const P& p, const std::string& name, const char* io) {
    if (!p)
        return;
    std::lock_guard<std::recursive_mutex> g(m_tr->mu());
    m_tr->out() << "{\"ev\":\"" << io << "\",\"d\":" << m_d << ",\"name\":\"" << name << "\",\"kind\":\"pt\",\"id\":\""
                << m_tr->idOf(ConstPlaintext(p), "pt")
                << "\",\"towers\":" << p->template GetElement<DCRTPoly>().GetNumOfElements()
                << ",\"nsd\":" << p->GetNoiseScaleDeg() << ",\"sf\":" << p->GetScalingFactorInt()
                << ",\"level\":" << p->GetLevel() << ",\"enc\":\"" << encName(p->GetEncodingType())
                << "\",\"t\":" << JsonTracer::ptModulus(ConstPlaintext(p)) << "}\n";
}

template <typename K>
void JsonFunctionTracer::key(const char* io, const K& k, const std::string& name, int64_t index) {
    if (!k)
        return;
    std::lock_guard<std::recursive_mutex> g(m_tr->mu());
    using T          = typename K::element_type;
    const char* kind = std::is_base_of<PublicKeyImpl<E>, T>::value  ? "pk" :
                       std::is_base_of<PrivateKeyImpl<E>, T>::value ? "sk" :
                                                                      "ek";
    std::string id;
    if constexpr (std::is_base_of<EvalKeyImpl<E>, T>::value)
        id = m_tr->idOf(EvalKey<E>(k), "ek");
    else
        id = m_tr->idOf(k, kind);  // content identity, recomputed at every use
    std::string tag;
    for (unsigned char c : k->GetKeyTag())  // keyTags are hex strings; keep only safe characters
        if (std::isalnum(c) || c == '-' || c == '_')
            tag += static_cast<char>(c);
    m_tr->out() << "{\"ev\":\"" << io << "\",\"d\":" << m_d << ",\"name\":\"" << name << "\",\"kind\":\"" << kind
                << "\",\"id\":\"" << id << "\",\"tag\":\"" << tag << "\"";
    if (index >= 0)
        m_tr->out() << ",\"index\":" << index;
    m_tr->out() << "}\n";
}

inline void JsonFunctionTracer::num(const std::string& v, const std::string& name) {
    std::lock_guard<std::recursive_mutex> g(m_tr->mu());
    m_tr->out() << "{\"ev\":\"in\",\"d\":" << m_d << ",\"name\":\"" << name << "\",\"kind\":\"int\",\"v\":" << v
                << "}\n";
}

template <typename T>
void JsonFunctionTracer::vec(const std::vector<T>& v, const std::string& name) {
    std::lock_guard<std::recursive_mutex> g(m_tr->mu());
    m_tr->out() << "{\"ev\":\"in\",\"d\":" << m_d << ",\"name\":\"" << name << "\",\"kind\":\"ints\",\"v\":[";
    for (size_t i = 0; i < v.size(); i++)
        m_tr->out() << (i ? "," : "") << v[i];
    m_tr->out() << "]}\n";
}

inline std::string scalName(ScalingTechnique s) {
    switch (s) {
        case FIXEDMANUAL:
            return "FIXEDMANUAL";
        case FIXEDAUTO:
            return "FIXEDAUTO";
        case FLEXIBLEAUTO:
            return "FLEXIBLEAUTO";
        case FLEXIBLEAUTOEXT:
            return "FLEXIBLEAUTOEXT";
        case NORESCALE:
            return "NORESCALE";
        default:
            return "OTHER";
    }
}

inline void primesJson(std::ostream& o, const std::vector<std::shared_ptr<ILNativeParams>>& p) {
    for (size_t i = 0; i < p.size(); i++)
        o << (i ? ", " : "") << "{\"q\": " << p[i]->GetModulus() << ", \"psi\": " << p[i]->GetRootOfUnity()
          << ", \"bits\": " << p[i]->GetModulus().GetMSB() << "}";
}

// Build configuration that changes the arithmetic the extractors model (both schemes).
inline std::string buildJson() {
    std::ostringstream o;
    o << "{\"WITH_REDUCED_NOISE\": " <<
    #ifdef WITH_REDUCED_NOISE
        "true"
    #else
        "false"
    #endif
      << ", \"NATIVEINT\": " << NATIVEINT << ", \"HAVE_INT128\": " <<
    #ifdef HAVE_INT128
        "true"
    #else
        "false"
    #endif
      << "}";
    return o.str();
}

inline std::string secretDistName(SecretKeyDist d) {
    return d == GAUSSIAN ? "GAUSSIAN" : d == UNIFORM_TERNARY ? "UNIFORM_TERNARY" : "SPARSE_TERNARY";
}

inline std::string multName(MultiplicationTechnique m) {
    switch (m) {
        case BEHZ:
            return "BEHZ";
        case HPS:
            return "HPS";
        case HPSPOVERQ:
            return "HPSPOVERQ";
        case HPSPOVERQLEVELED:
            return "HPSPOVERQLEVELED";
        default:
            return "OTHER";
    }
}

// The fields of a BFVrns context that extract_bfv.py needs, read through OpenFHE's API
// (= `bfv_demo dump`): N, t, the primes of Q, the special primes P (HYBRID), the auxiliary basis of
// the multiplication (HPS family: R; BEHZ: B, m_sk, gamma), the extra prime of EXTENDED
// encryption, and the library's own FindLevelsToDrop evaluated on this context for every
// noiseScaleDeg up to 64 (levels = nsd - 1, dcrtBits = MSB(q_0) as its callers compute it).
inline std::string paramsJsonBFV(const CryptoContextImpl<DCRTPoly>& cc, const std::shared_ptr<CryptoParametersBFVRNS>& cp,
                                 bool withDrops = true) {
    const uint32_t MAX_NSD = 64;
    std::ostringstream o;
    auto q       = cp->GetElementParams()->GetParams();
    size_t sizeQ = q.size();
    auto mt      = cp->GetMultiplicationTechnique();
    o << "{\n  \"tracer\": \"" FHECHECK_TRACER_VERSION "\",\n";
    o << "  \"scheme\": \"BFV\",\n";
    o << "  \"N\": " << cc.GetRingDimension() << ",\n";
    o << "  \"t\": " << cp->GetPlaintextModulus() << ",\n";
    o << "  \"qs\": [";
    primesJson(o, q);
    o << "],\n  \"special\": [";
    if (cp->GetKeySwitchTechnique() == HYBRID && cp->GetParamsP())
        primesJson(o, cp->GetParamsP()->GetParams());
    o << "],\n";
    o << "  \"keySwitch\": \"" << (cp->GetKeySwitchTechnique() == HYBRID ? "HYBRID" : "BV") << "\",\n";
    o << "  \"dnum\": " << cp->GetNumPartQ() << ",\n";
    o << "  \"towersPerDigit\": " << cp->GetNumPerPartQ() << ",\n";
    o << "  \"digitSizeBV\": " << cp->GetDigitSize() << ",\n";
    o << "  \"multiplicationTechnique\": \"" << multName(mt) << "\",\n";
    // the auxiliary basis of the multiplication, as PrecomputeCRTTables built it
    o << "  \"auxR\": [";
    if (mt == HPS)
        primesJson(o, cp->GetParamsRl(0)->GetParams());
    else if (mt == HPSPOVERQ || mt == HPSPOVERQLEVELED)
        primesJson(o, cp->GetParamsRl(sizeQ - 1)->GetParams());
    o << "],\n  \"behzBsk\": [";
    if (mt == BEHZ) {
        auto& b = cp->GetModuliBsk();  // {b_1 .. b_k, m_sk}
        for (size_t i = 0; i < b.size(); i++)
            o << (i ? ", " : "") << b[i];
    }
    o << "],\n";
    o << "  \"behzGamma\": " << (mt == BEHZ ? cp->Getgamma() : 0) << ",\n";
    o << "  \"extendedPrime\": ";
    if (cp->GetEncryptionTechnique() == EXTENDED)
        o << cp->GetParamsQr()->GetParams().back()->GetModulus();
    else
        o << 0;
    o << ",\n";
    o << "  \"sigma\": " << cp->GetDistributionParameter() << ",\n";
    o << "  \"assuranceMeasure\": " << cp->GetAssuranceMeasure() << ",\n";
    o << "  \"thresholdParties\": " << cp->GetThresholdNumOfParties() << ",\n";
    o << "  \"secretKeyDist\": \"" << secretDistName(cp->GetSecretKeyDist()) << "\",\n";
    o << "  \"encryptionTechnique\": \"" << (cp->GetEncryptionTechnique() == STANDARD ? "STANDARD" : "EXTENDED")
      << "\",\n";
    o << "  \"noiseScale\": " << cp->GetNoiseScale() << ",\n";
    o << "  \"multiplicativeDepth\": " << cp->GetMultiplicativeDepth() << ",\n";
    o << "  \"maxRelinSkDeg\": " << cp->GetMaxRelinSkDeg() << ",\n";
    uint32_t dcrtBits = q[0]->GetModulus().GetMSB();
    std::shared_ptr<CryptoParametersBase<DCRTPoly>> base = cp;
    if (withDrops) {  // a function of the fields above only (the watch fingerprint omits it)
        o << "  \"levelsToDrop\": {\"dcrtBits\": " << dcrtBits << ", \"mul\": [";
        for (uint32_t d = 0; d < MAX_NSD; d++)
            o << (d ? "," : "") << FindLevelsToDrop(d, base, dcrtBits, false);
        o << "], \"keySwitch\": [";
        for (uint32_t d = 0; d < MAX_NSD; d++)
            o << (d ? "," : "") << FindLevelsToDrop(d, base, dcrtBits, true);
        o << "]},\n";
    }
    o << "  \"PREMode\": \"" << cp->GetPREMode() << "\",\n";
    o << "  \"multipartyMode\": \"" << cp->GetMultipartyMode() << "\",\n";
    o << "  \"stdLevel\": \"" << cp->GetStdLevel() << "\",\n";
    o << "  \"build\": " << buildJson() << "\n}\n";
    return o.str();
}

// The fields fhe_check's extractor needs, read through OpenFHE's API (= `bgv_demo dump`).
// For a BFVrns context: paramsJsonBFV (= `bfv_demo dump`).
inline std::string paramsJson(const CryptoContextImpl<DCRTPoly>& cc, bool withDrops = true) {
    if (auto bfv = std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc.GetCryptoParameters()))
        return paramsJsonBFV(cc, bfv, withDrops);
    auto cp = std::dynamic_pointer_cast<CryptoParametersBGVRNS>(cc.GetCryptoParameters());
    if (!cp)
        throw std::runtime_error("not a BGVRNS or BFVRNS context");
    std::ostringstream o;
    auto q = cp->GetElementParams()->GetParams();
    o << "{\n  \"tracer\": \"" FHECHECK_TRACER_VERSION "\",\n";
    o << "  \"scheme\": \"BGV\",\n";
    o << "  \"N\": " << cc.GetRingDimension() << ",\n";
    o << "  \"t\": " << cp->GetPlaintextModulus() << ",\n";
    o << "  \"qs\": [";
    for (size_t i = 0; i < q.size(); i++)
        o << (i ? ", " : "") << "{\"q\": " << q[i]->GetModulus() << ", \"psi\": " << q[i]->GetRootOfUnity()
          << ", \"bits\": " << q[i]->GetModulus().GetMSB() << "}";
    o << "],\n";
    o << "  \"special\": [";
    if (cp->GetKeySwitchTechnique() == HYBRID && cp->GetParamsP()) {
        auto p = cp->GetParamsP()->GetParams();
        for (size_t i = 0; i < p.size(); i++)
            o << (i ? ", " : "") << "{\"q\": " << p[i]->GetModulus() << ", \"psi\": " << p[i]->GetRootOfUnity()
              << ", \"bits\": " << p[i]->GetModulus().GetMSB() << "}";
    }
    o << "],\n";
    o << "  \"keySwitch\": \"" << (cp->GetKeySwitchTechnique() == HYBRID ? "HYBRID" : "BV") << "\",\n";
    o << "  \"dnum\": " << cp->GetNumPartQ() << ",\n";
    o << "  \"towersPerDigit\": " << cp->GetNumPerPartQ() << ",\n";
    o << "  \"digitSizeBV\": " << cp->GetDigitSize() << ",\n";
    o << "  \"scaling\": \"" << scalName(cp->GetScalingTechnique()) << "\",\n";
    o << "  \"sigma\": " << cp->GetDistributionParameter() << ",\n";
    o << "  \"assuranceMeasure\": " << cp->GetAssuranceMeasure() << ",\n";
    o << "  \"secretKeyDist\": \""
      << (cp->GetSecretKeyDist() == GAUSSIAN        ? "GAUSSIAN" :
          cp->GetSecretKeyDist() == UNIFORM_TERNARY ? "UNIFORM_TERNARY" :
                                                      "SPARSE_TERNARY")
      << "\",\n";
    o << "  \"encryptionTechnique\": \"" << (cp->GetEncryptionTechnique() == STANDARD ? "STANDARD" : "EXTENDED")
      << "\",\n";
    o << "  \"noiseScale\": " << cp->GetNoiseScale() << ",\n";
    o << "  \"multiplicativeDepth\": " << cp->GetMultiplicativeDepth() << ",\n";
    o << "  \"PREMode\": \"" << cp->GetPREMode() << "\",\n";
    o << "  \"multipartyMode\": \"" << cp->GetMultipartyMode() << "\",\n";
    o << "  \"stdLevel\": \"" << cp->GetStdLevel() << "\",\n";
    // build configuration that changes the arithmetic the extractor models
    o << "  \"build\": {\"WITH_REDUCED_NOISE\": " <<
    #ifdef WITH_REDUCED_NOISE
        "true"
    #else
        "false"
    #endif
      << ", \"NATIVEINT\": " << NATIVEINT << ", \"HAVE_INT128\": " <<
    #ifdef HAVE_INT128
        "true"
    #else
        "false"
    #endif
      << "}\n}\n";
    return o.str();
}

inline std::string paramsFingerprint(const CryptoContextImpl<DCRTPoly>& cc) {
    return paramsJson(cc, false);
}

// Called by CryptoContextFactory::AddContext for every newly registered context.
template <typename Element>
inline void MaybeAutoTrace(const std::shared_ptr<CryptoContextImpl<Element>>&) {}

template <>
inline void MaybeAutoTrace<DCRTPoly>(const std::shared_ptr<CryptoContextImpl<DCRTPoly>>& cc) {
    const char* dir = std::getenv("FHECHECK_TRACE_DIR");
    if (!dir || !*dir || !cc)
        return;
    if (!std::dynamic_pointer_cast<CryptoParametersBGVRNS>(cc->GetCryptoParameters()) &&
        !std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc->GetCryptoParameters()))
        return;
    static std::atomic<int> counter{0};
    int k            = ++counter;
    std::string base = std::string(dir) + "/p" + std::to_string(::getpid()) + ".ctx" + std::to_string(k);
    {
        std::ofstream f(base + ".params.json");
        f << paramsJson(*cc);
    }
    auto tracer = std::make_shared<JsonTracer>(std::make_shared<std::ofstream>(base + ".trace.jsonl"));
    tracer->watch(cc);
    cc->setTracer(tracer);
}

}  // namespace fhecheck

#endif  // ENABLE_TRACER
#endif  // SRC_PKE_INCLUDE_UTILS_FHECHECK_TRACER_H_
