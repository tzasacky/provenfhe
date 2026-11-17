// pin_dump_bfv.h -- UNTRUSTED. Exporter side of the openfhe-pin harness for BFV cases
// (format: harness/openfhe-pin/FORMAT.md, section "BFV cases"). Header-only; it reuses the PRNG
// wrapper, the capturing tracer and the polys.txt writer of pin_dump.h unchanged and adds
// pin::CaseBfv, the BFV counterpart of pin::Case.
//
//   pin::CaseBfv c(outdir, caseName, seed, generator, cc, defaults);
//       defaults: which of the three technique setters were never called (multDefault, ksDefault,
//       encDefault of pin.json "bfv")
//       c.keyGen()                     cc->KeyGen() with PRNG replay (bfvrns-pke.cpp:52-106: s, a, e
//                                      over GetParamsPK, b = ns*e - a*s, ns = 1); pk.e is recorded if
//                                      the replay reproduces the secret and both public elements
//       c.encrypt(tr, pt)              cc->Encrypt(pk, pt) with PRNG replay of (u, e1, e2) = OpenFHE's
//                                      (v, e0, e1) (rns-pke.cpp:152-200) and a C++ self-check:
//                                      STANDARD  c0 = b*u + e1 + TimesQovert(p), c1 = a*u + e2 over the
//                                                limbs of the plaintext (bfvrns-pke.cpp:167-223)
//                                      EXTENDED  the same modulo Q*r followed by ScaleAndRoundPOverQ of
//                                                both components (the entry gets "extended": true)
//                                      on mismatch: randomness "none" and a note
//       c.encryptScripted(tr, pt, u, e1, e2)   the caller scripted the PRNG; same self-check
//       c.encryptSecret(tr, pt)        cc->Encrypt(sk, pt): recorded with randomness "none"
//       c.addInput(tr, ct)             a hand-built input (sets inputsArbitrary)
//       c.phase(ct)                    exact integer phase [c0 + c1 s (+ c2 s^2)]_{Q_l}, centred
//       c.write(tr)                    pin.json + polys.txt
// Source references are to OpenFHE v1.6.1 (commit b59e1f29). Nothing here is trusted by the Lean
// checker: it recomputes everything from the dumped integers.
#pragma once
#include "pin_dump.h"
#include "scheme/bfvrns/bfvrns-ser.h"

#include <cmath>
#include <cstring>
#include <iostream>
#include <set>

namespace pin {

inline std::string readFile(const std::string& path) {
    std::ifstream f(path);
    if (!f) return "";
    std::stringstream ss;
    ss << f.rdbuf();
    std::string s = ss.str();
    while (!s.empty() && (s.back() == '\n' || s.back() == ' ')) s.pop_back();
    return s;
}

struct BfvDefaults {
    bool mult = true, ks = true, enc = true;
};

class CaseBfv {
public:
    struct Enc {
        std::string ct, pt, how;
        bool have = false, extended = false, havePre = false;
        std::vector<int64_t> u, e1, e2;
        E pre0, pre1;  // EXTENDED: the pair over Q*r before ScaleAndRoundPOverQ
        E tqt;         // the library's TimesQovert of the stored plaintext (coefficient form)
        bool haveTqt = false;
    };

    // The library's own TimesQovert of the stored plaintext, exactly as PKEBFVRNS::Encrypt does it
    // (bfvrns-pke.cpp:176-205): over the plaintext's own limbs (STANDARD) or, for EXTENDED, of the
    // CRT-lift to Q*r; coefficient form. No PRNG draw, nothing traced (plain DCRTPoly calls).
    E timesQovert(const Plaintext& pt) const {
        const auto elemPar = m_cp->GetElementParams();
        size_t sizeQ = elemPar->GetParams().size();
        E m          = pt->GetElement<E>();
        auto encPar  = m.GetParams();
        size_t level = sizeQ - encPar->GetParams().size();
        std::vector<NativeInteger> tInvModq = m_cp->GettInvModq();
        NativeInteger negQModt = m_cp->GetNegQModt(level), negQModtPrecon = m_cp->GetNegQModtPrecon(level);
        if (extended()) {
            encPar = m_cp->GetParamsQr();
            m.SetFormat(Format::COEFFICIENT);
            Poly big = m.CRTInterpolate();
            m        = E(big, encPar);
            tInvModq = m_cp->GettInvModqr();
            negQModt = m_cp->GetNegQrModt();
            negQModtPrecon = m_cp->GetNegQrModtPrecon();
        }
        m.SetFormat(Format::COEFFICIENT);
        m.TimesQovert(encPar, tInvModq, m_cp->GetPlaintextModulus(), negQModt, negQModtPrecon);
        return m;
    }
    void addTqt(Enc& en, const Plaintext& pt) const {
        en.tqt     = timesQovert(pt);
        en.haveTqt = true;
    }

    CaseBfv(std::string outdir, std::string name, uint64_t seed, std::string generator, CryptoContext<E> cc,
            BfvDefaults dflt)
        : m_out(std::move(outdir)), m_name(std::move(name)), m_seed(seed), m_gen(std::move(generator)), m_cc(cc),
          m_dflt(dflt) {
        m_cp = std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc->GetCryptoParameters());
        if (!m_cp) throw std::runtime_error("not a BFVRNS context");
    }

    // Notes may quote OpenFHE exception texts, which carry the absolute path of a source file:
    // only the part from the last "/src/" or "/include/" on is kept.
    void note(const std::string& s0) {
        std::string s;
        size_t i = 0;
        while (i < s0.size()) {
            if (s0[i] == '/' && (i == 0 || s0[i - 1] == ' ' || s0[i - 1] == '(' || s0[i - 1] == '\n')) {
                size_t e = i;
                while (e < s0.size() && s0[e] != ' ' && s0[e] != ':' && s0[e] != ')' && s0[e] != '\n') e++;
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
    void setFinal(const std::vector<Ciphertext<E>>& f) { m_final = f; }
    void setKeys(const KeyPair<E>& kp) { m_kp = kp; }
    const KeyPair<E>& keys() const { return m_kp; }
    void setInputsArbitrary(bool b) { m_arbitrary = b; }
    void setFloatFacts(const std::string& json) { m_float = json; }
    bool havePkE() const { return m_havePkE; }
    const std::vector<int64_t>& pkE() const { return m_pkE; }
    const std::shared_ptr<CryptoParametersBFVRNS>& cp() const { return m_cp; }

    E drawSecretLike(const std::shared_ptr<E::Params>& params, bool forKey) const {
        const auto& dgg = m_cp->GetDiscreteGaussianGenerator();
        E::TugType tug;
        switch (m_cp->GetSecretKeyDist()) {
            case GAUSSIAN: return E(dgg, params, Format::EVALUATION);
            case SPARSE_TERNARY:
                return forKey ? E(tug, params, Format::EVALUATION, 192) : E(tug, params, Format::EVALUATION);
            default: return E(tug, params, Format::EVALUATION);
        }
    }

    // cc->KeyGen() with PRNG replay (bfvrns-pke.cpp:52-106).
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
        size_t sizeSk       = m_kp.secretKey->GetPrivateElement().GetNumOfElements();
        size_t sizePK       = paramsPK->GetParams().size();
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
            if (sizePK > sizeSk) sDrop.DropLastElements(sizePK - sizeSk);
            if (sDrop == m_kp.secretKey->GetPrivateElement() && a == pk[1] && b == pk[0]) {
                if (!centredSmall(e, m_pkE)) throw std::runtime_error("keyGen replay: e is not a small vector");
                m_havePkE = true;
                note("keyGen: PRNG replay matched (" + std::to_string(prefix) + " words before s, then s, a, e over " +
                     std::to_string(sizePK) + " limbs (GetParamsPK), then " + std::to_string(suffix) +
                     " key-tag words; secret stored over " + std::to_string(sizeSk) +
                     " limbs); checked in C++: replayed s == secret, a == pk[1], ns*e - a*s == pk[0], ns = " +
                     std::to_string(ns));
                break;
            }
        }
        Prng::setState(st1);
        if (!m_havePkE) note("keyGen: PRNG REPLAY DID NOT MATCH for any key-tag placement; pk.e = null");
        return m_kp;
    }

    // The REAL cc->KeyGen() on a scripted PRNG: the ternary draws of s and the Gaussian draws of e are
    // the given words (sWords: N words, eWords: 2N words; they must make the samplers emit sV, eV),
    // the key-tag words and the uniform draws of a are the words the seeded stream would have given.
    // Checked: the secret is sV and pk[0] == eV - pk[1]*s. pk.e = eV, randomness "scripted".
    KeyPair<E> keyGenScripted(const std::vector<int64_t>& sV, const std::vector<int64_t>& eV,
                              const std::vector<uint32_t>& sWords, const std::vector<uint32_t>& eWords) {
        const auto paramsPK = m_cp->GetParamsPK();
        uint64_t st = Prng::getState(), c0 = Prng::calls();
        { KeyPair<E> tmp(std::make_shared<PublicKeyImpl<E>>(m_cc), std::make_shared<PrivateKeyImpl<E>>(m_cc)); }
        size_t tagWords = Prng::calls() - c0;
        c0 = Prng::calls();
        { E sd = drawSecretLike(paramsPK, true); }
        size_t nS = Prng::calls() - c0;
        c0 = Prng::calls();
        { E::DugType dug; E a(dug, paramsPK, Format::EVALUATION); }
        size_t aWords = Prng::calls() - c0;
        if (nS != sWords.size()) throw std::runtime_error("keyGenScripted: the secret sampler draws " + std::to_string(nS) + " words");
        Prng::setState(st);
        std::vector<uint32_t> script;
        auto raw = [] { return (uint32_t)PseudoRandomNumberGenerator::GetPRNG()(); };
        for (size_t i = 0; i < tagWords; i++) script.push_back(raw());
        for (size_t i = 0; i < nS; i++) raw();
        script.insert(script.end(), sWords.begin(), sWords.end());
        for (size_t i = 0; i < aWords; i++) script.push_back(raw());
        script.insert(script.end(), eWords.begin(), eWords.end());
        c0 = Prng::calls();
        Prng::scriptPush(script.data(), script.size());
        m_kp = m_cc->KeyGen();
        if (Prng::scriptRemaining() != 0 || Prng::calls() - c0 != script.size())
            throw std::runtime_error("keyGenScripted: KeyGen did not consume the script exactly");
        const auto& pk = m_kp.publicKey->GetPublicElements();
        E s = Case::fromSigned(sV, paramsPK), e = Case::fromSigned(eV, paramsPK);
        E b(m_cp->GetNoiseScale() * e - pk[1] * s);
        E sDrop(s);
        size_t sizeSk = m_kp.secretKey->GetPrivateElement().GetNumOfElements(), sizePK = paramsPK->GetParams().size();
        if (sizePK > sizeSk) sDrop.DropLastElements(sizePK - sizeSk);
        if (!(sDrop == m_kp.secretKey->GetPrivateElement()) || !(b == pk[0]))
            throw std::runtime_error("keyGenScripted: the scripted s, e were not produced");
        m_pkE     = eV;
        m_havePkE = true;
        m_pkHow   = "scripted";
        note("keyGen: the REAL cc->KeyGen() on a scripted PRNG (" + std::to_string(tagWords) + " key-tag words and " +
             std::to_string(aWords) + " words of the uniform a from the seeded stream; s and e scripted); checked in C++: "
             "secret == scripted s, pk[0] == e - pk[1]*s");
        return m_kp;
    }

    bool extended() const { return m_cp->GetEncryptionTechnique() == EXTENDED; }
    // the parameters EncryptZeroCore samples over
    std::shared_ptr<E::Params> encParams(const Plaintext& pt) const {
        return extended() ? m_cp->GetParamsQr() : pt->GetElement<E>().GetParams();
    }

    Ciphertext<E> encrypt(const std::shared_ptr<Tracer>& tr, Plaintext pt) {
        bool scripted    = Prng::scriptRemaining() > 0;
        uint64_t st0     = Prng::getState();
        Ciphertext<E> ct = m_cc->Encrypt(m_kp.publicKey, pt);
        uint64_t st1     = Prng::getState();
        Enc en;
        en.ct       = tr->noteCt(ct);
        en.pt       = tr->notePt(pt);
        en.how      = "none";
        en.extended = extended();
        if (scripted) {
            note("encrypt " + en.ct + ": PRNG script queue in use, randomness not replayable");
        }
        else {
            Prng::setState(st0);
            const auto params = encParams(pt);
            const auto& dgg   = m_cp->GetDiscreteGaussianGenerator();
            E v               = drawSecretLike(params, false);
            E e0(dgg, params, Format::EVALUATION);
            E e1(dgg, params, Format::EVALUATION);
            bool stOk = Prng::getState() == st1;
            Prng::setState(st1);
            if (stOk && checkEnc(ct, pt, v, e0, e1, &en)) {
                if (!centredSmall(v, en.u) || !centredSmall(e0, en.e1) || !centredSmall(e1, en.e2))
                    throw std::runtime_error("encrypt replay: sampler output is not a small vector");
                en.have = true;
                en.how  = "prng-replay";
            }
            else {
                note("encrypt " + en.ct + ": PRNG REPLAY DID NOT MATCH (" +
                     (stOk ? "state ok, the encryption relation does not reproduce the ciphertext" :
                             "different number of draws") +
                     "); randomness none");
            }
        }
        addTqt(en, pt);
        m_encs.push_back(std::move(en));
        return ct;
    }

    Ciphertext<E> encryptScripted(const std::shared_ptr<Tracer>& tr, Plaintext pt, const std::vector<int64_t>& u,
                                  const std::vector<int64_t>& e1, const std::vector<int64_t>& e2) {
        Ciphertext<E> ct = m_cc->Encrypt(m_kp.publicKey, pt);
        Enc en;
        en.ct       = tr->noteCt(ct);
        en.pt       = tr->notePt(pt);
        en.how      = "none";
        en.extended = extended();
        const auto params = encParams(pt);
        if (checkEnc(ct, pt, Case::fromSigned(u, params), Case::fromSigned(e1, params), Case::fromSigned(e2, params), &en)) {
            en.have = true;
            en.how  = "scripted";
            en.u = u; en.e1 = e1; en.e2 = e2;
        }
        else {
            note("encryptScripted " + en.ct + ": the claimed (u, e1, e2) do not reproduce the ciphertext; none");
        }
        addTqt(en, pt);
        m_encs.push_back(std::move(en));
        return ct;
    }

    // Encryption with the PRIVATE key (bfvrns-pke.cpp:108-165): no (u, e1, e2); recorded as "none".
    Ciphertext<E> encryptSecret(const std::shared_ptr<Tracer>& tr, Plaintext pt) {
        Ciphertext<E> ct = m_cc->Encrypt(m_kp.secretKey, pt);
        Enc en;
        en.ct  = tr->noteCt(ct);
        en.pt  = tr->notePt(pt);
        en.how = "none";
        note("encrypt " + en.ct + ": Encrypt with the PRIVATE key (c1 uniform, c0 = e - c1*s + TimesQovert(p)); "
             "there is no (u, e1, e2): randomness none");
        addTqt(en, pt);
        m_encs.push_back(std::move(en));
        return ct;
    }

    std::string addInput(const std::shared_ptr<Tracer>& tr, const Ciphertext<E>& ct) {
        m_arbitrary = true;
        return tr->noteCt(ct);
    }

    // The library's own steps of PKEBFVRNS::Encrypt(DCRTPoly, PublicKey) (bfvrns-pke.cpp:167-223) on
    // the claimed sampler outputs, with OpenFHE's DCRTPoly arithmetic; true iff it reproduces ct.
    bool checkEnc(const Ciphertext<E>& ct, const Plaintext& pt, const E& v, const E& e0, const E& e1,
                  Enc* en = nullptr) const {
        const auto& pk     = m_kp.publicKey->GetPublicElements();
        const auto ns      = m_cp->GetNoiseScale();
        const auto elemPar = m_cp->GetElementParams();
        size_t sizeQ       = elemPar->GetParams().size();
        E m                = pt->GetElement<E>();
        size_t sizeP       = m.GetNumOfElements();
        if (sizeP > sizeQ) return false;
        size_t level = sizeQ - sizeP;
        auto encPar  = m.GetParams();
        std::vector<NativeInteger> tInvModq = m_cp->GettInvModq();
        NativeInteger negQModt = m_cp->GetNegQModt(level), negQModtPrecon = m_cp->GetNegQModtPrecon(level);
        m.SetFormat(Format::COEFFICIENT);
        if (extended()) {
            encPar = m_cp->GetParamsQr();
            Poly big = m.CRTInterpolate();
            m        = E(big, encPar);
            tInvModq = m_cp->GettInvModqr();
            negQModt = m_cp->GetNegQrModt();
            negQModtPrecon = m_cp->GetNegQrModtPrecon();
            m.SetFormat(Format::COEFFICIENT);
        }
        size_t sizeEnc = encPar->GetParams().size();
        E p0 = pk[0].Clone(), p1 = pk[1].Clone();
        size_t sizePk = p0.GetNumOfElements();
        if (sizeEnc > sizePk) return false;
        if (sizeEnc != sizePk) {
            p0.DropLastElements(sizePk - sizeEnc);
            p1.DropLastElements(sizePk - sizeEnc);
        }
        if (v.GetNumOfElements() != sizeEnc) return false;
        E c0 = p0 * v + ns * e0;
        E c1 = p1 * v + ns * e1;
        m.TimesQovert(encPar, tInvModq, m_cp->GetPlaintextModulus(), negQModt, negQModtPrecon);
        m.SetFormat(Format::EVALUATION);
        c0 += m;
        E p0c, p1c;
        if (extended()) {
            c0.SetFormat(Format::COEFFICIENT);
            c1.SetFormat(Format::COEFFICIENT);
            p0c = c0;
            p1c = c1;
            c0.ScaleAndRoundPOverQ(elemPar, m_cp->GetrInvModq());
            c1.ScaleAndRoundPOverQ(elemPar, m_cp->GetrInvModq());
            c0.SetFormat(Format::EVALUATION);
            c1.SetFormat(Format::EVALUATION);
        }
        const auto& cv = ct->GetElements();
        if (cv.size() != 2) return false;
        E x0 = cv[0], x1 = cv[1];
        x0.SetFormat(Format::EVALUATION);
        x1.SetFormat(Format::EVALUATION);
        bool ok = x0 == c0 && x1 == c1;
        if (ok && en && extended()) {
            en->pre0    = p0c;
            en->pre1    = p1c;
            en->havePre = true;
        }
        return ok;
    }

    // Exact phase [c0 + c1 s (+ c2 s^2 ...)]_{Q_l} as a big-integer polynomial in [0, Q_l).
    Poly phase(const Ciphertext<E>& c) const {
        std::vector<E> cv = c->GetElements();
        E s               = m_kp.secretKey->GetPrivateElement();
        size_t sizeQl     = cv[0].GetNumOfElements();
        if (s.GetNumOfElements() > sizeQl) s.DropLastElements(s.GetNumOfElements() - sizeQl);
        for (auto& x : cv) x.SetFormat(Format::EVALUATION);
        E ph = cv[0], sp = s;
        for (size_t i = 1; i < cv.size(); i++) {
            ph += cv[i] * sp;
            sp *= s;
        }
        ph.SetFormat(Format::COEFFICIENT);
        return ph.CRTInterpolate();
    }

    static std::string mulName(MultiplicationTechnique m) { return fhecheck::multName(m); }

    // -----------------------------------------------------------------------------------------
    void write(const std::shared_ptr<Tracer>& tr) {
        tr->flush();
        detach(m_cc);  // nothing below is traced
        PolyWriter pw(m_out + "/polys.txt");
        std::ostringstream j;
        const uint64_t t = m_cp->GetPlaintextModulus();
        const auto qp    = m_cp->GetElementParams()->GetParams();
        const size_t L   = qp.size();
        const auto mt    = m_cp->GetMultiplicationTechnique();
        const bool hybrid = m_cp->GetKeySwitchTechnique() == HYBRID && m_cp->GetParamsP();
        const uint32_t digitSize = m_cp->GetDigitSize();
        auto listOf = [&](const std::vector<std::shared_ptr<ILNativeParams>>& p) {
            std::string r;
            for (size_t i = 0; i < p.size(); i++) r += std::string(i ? ", " : "") + "\"" + p[i]->GetModulus().ToString() + "\"";
            return r;
        };
        j << "{\n \"format\": \"openfhe-pin/v1\", \"scheme\": \"BFV\",\n \"case\": " << jstr(m_name) << ",\n \"seed\": \""
          << m_seed << "\",\n \"generator\": " << jstr(m_gen) << ",\n \"N\": " << m_cc->GetRingDimension()
          << ", \"t\": \"" << t << "\",\n \"qs\": [" << listOf(qp) << "],\n \"special\": [";
        if (hybrid) j << listOf(m_cp->GetParamsP()->GetParams());
        j << "],\n";
        // top-level copies of bfv.dnum / bfv.towersPerDigit (same keys as a BGV pin.json)
        uint32_t dnum = hybrid ? m_cp->GetNumPartQ() : (uint32_t)L;
        uint32_t tpd  = hybrid ? m_cp->GetNumPerPartQ() : 1;
        j << " \"dnum\": " << dnum << ", \"towersPerDigit\": " << tpd << ",\n";
        j << " \"bfv\": {\n  \"mult\": \"" << mulName(mt) << "\", \"multDefault\": " << (m_dflt.mult ? "true" : "false")
          << ",\n  \"ks\": \"" << (hybrid ? "HYBRID" : "BV") << "\", \"ksDefault\": " << (m_dflt.ks ? "true" : "false")
          << ",\n  \"enc\": \"" << (extended() ? "EXTENDED" : "STANDARD") << "\", \"encDefault\": "
          << (m_dflt.enc ? "true" : "false") << ",\n  \"dnum\": " << dnum << ", \"towersPerDigit\": " << tpd
          << ",\n  \"digitSizeBV\": " << digitSize << ",\n  \"auxR\": [";
        if (mt == HPS) j << listOf(m_cp->GetParamsRl(0)->GetParams());
        else if (mt == HPSPOVERQ || mt == HPSPOVERQLEVELED) j << listOf(m_cp->GetParamsRl(L - 1)->GetParams());
        j << "],\n  \"behzBsk\": [";
        if (mt == BEHZ) {
            const auto& b = m_cp->GetModuliBsk();
            for (size_t i = 0; i < b.size(); i++) j << (i ? ", " : "") << "\"" << b[i] << "\"";
        }
        j << "],\n  \"behzMtilde\": \"" << (mt == BEHZ ? 65536 : 0) << "\",\n  \"behzGamma\": \""
          << (mt == BEHZ ? m_cp->Getgamma() : 0) << "\",\n  \"extendedPrime\": \"";
        if (extended()) j << m_cp->GetParamsQr()->GetParams().back()->GetModulus();
        else j << 0;
        j << "\",\n";
        {
            // as params.json (fhecheck::paramsJsonBFV): the library's FindLevelsToDrop on this context
            const uint32_t MAX_NSD = 64;
            uint32_t dcrtBits = qp[0]->GetModulus().GetMSB();
            std::shared_ptr<CryptoParametersBase<E>> base = m_cp;
            j << "  \"levelsToDrop\": {\"dcrtBits\": " << dcrtBits << ", \"mul\": [";
            for (uint32_t d = 0; d < MAX_NSD; d++) j << (d ? "," : "") << FindLevelsToDrop(d, base, dcrtBits, false);
            j << "], \"keySwitch\": [";
            for (uint32_t d = 0; d < MAX_NSD; d++) j << (d ? "," : "") << FindLevelsToDrop(d, base, dcrtBits, true);
            j << "]},\n";
        }
        j << "  \"multiplicativeDepth\": " << m_cp->GetMultiplicativeDepth() << ", \"maxRelinSkDeg\": "
          << m_cp->GetMaxRelinSkDeg() << ",\n  \"secretKeyDist\": \""
          << fhecheck::secretDistName(m_cp->GetSecretKeyDist()) << "\",\n  \"noiseScale\": \"" << m_cp->GetNoiseScale()
          << "\"\n },\n";
        {
            // the tables of the HPS-family ScaleAndRound (bfvrns-cryptoparameters.cpp:432-481), read from
            // the context; BEHZ contexts do not compute them (the block is inside `if (multTech != BEHZ)`, :128)
            const auto& il = m_cp->GettQHatInvModqDivqModt();
            const auto& fl = m_cp->GettQHatInvModqDivqFrac();
            const auto& ih = m_cp->GettQHatInvModqBDivqModt();
            const auto& fh = m_cp->GettQHatInvModqBDivqFrac();
            auto hex = [](double d) {
                uint64_t u;
                std::memcpy(&u, &d, sizeof u);
                char b[20];
                snprintf(b, sizeof b, "%016llx", (unsigned long long)u);
                return std::string(b);
            };
            if (il.empty() || fl.empty()) {
                j << " \"decryptTables\": null,\n";
                note("decryptTables: null: the context has no HPS-family decryption tables (" + mulName(mt) +
                     ": bfvrns-cryptoparameters.cpp:128 computes them only for multTech != BEHZ)");
            }
            else {
                j << " \"decryptTables\": {\"t\": \"" << t << "\", \"qs\": [" << listOf(qp) << "],\n  \"intLo\": [";
                for (size_t i = 0; i < il.size(); i++) j << (i ? ", " : "") << "\"" << il[i] << "\"";
                j << "],\n  \"fracLo\": [";
                for (size_t i = 0; i < fl.size(); i++) j << (i ? ", " : "") << "\"" << hex(fl[i]) << "\"";
                j << "],\n  \"intHi\": [";
                for (size_t i = 0; i < ih.size(); i++) j << (i ? ", " : "") << "\"" << ih[i] << "\"";
                j << "],\n  \"fracHi\": [";
                for (size_t i = 0; i < fh.size(); i++) j << (i ? ", " : "") << "\"" << hex(fh[i]) << "\"";
                j << "]},\n";
            }
        }
        if (mt == BEHZ)
            note("behzMtilde: 65536 is the constant m_mtilde of rns-cryptoparameters.h (no accessor); behzGamma: "
                 "Getgamma()");

        // secret
        const E& s = m_kp.secretKey->GetPrivateElement();
        std::vector<int64_t> sv;
        if (!centredSmall(s, sv)) throw std::runtime_error("secret key limbs are not one small integer vector");
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
        const auto& pk = m_kp.publicKey->GetPublicElements();
        pw.rns("pk.b", pk[0]);
        pw.rns("pk.a", pk[1]);
        if (m_havePkE) pw.sgn("pk.e", m_pkE);
        j << " \"public\": {\"b\": \"pk.b\", \"a\": \"pk.a\", \"e\": " << (m_havePkE ? "\"pk.e\"" : "null")
          << ", \"randomness\": \"" << (m_havePkE ? m_pkHow : std::string("none")) << "\"},\n";
        note("public key: " + std::to_string(pk[0].GetNumOfElements()) + " limbs" +
             (extended() ? " (EXTENDED: Q then the extra prime r = extendedPrime, GetParamsQr)" : "") +
             "; ciphertext chain: " + std::to_string(L) + " limbs");

        // eval keys
        j << " \"evalKeys\": [";
        bool first = true;
        size_t keyLimbs = 0, nRelin = 0, nRot = 0;
        auto dumpKey = [&](const EvalKey<E>& ek, const std::string& base, const std::string& head) {
            const auto& bv = ek->GetBVector();
            const auto& av = ek->GetAVector();
            // BV with a digit size: key j belongs to limb i, power k (keyswitch-bv.cpp:70-90)
            std::vector<std::pair<uint32_t, uint32_t>> lk;
            if (!hybrid && digitSize > 0) {
                for (uint32_t i = 0; i < s.GetNumOfElements(); i++) {
                    uint32_t msb = s.GetElementAtIndex(i).GetModulus().GetMSB();
                    uint32_t nw  = msb / digitSize + (msb % digitSize ? 1 : 0);
                    for (uint32_t k = 0; k < nw; k++) lk.emplace_back(i, k);
                }
                if (lk.size() != bv.size())
                    throw std::runtime_error("BV digit keys: " + std::to_string(bv.size()) + " keys, expected " +
                                             std::to_string(lk.size()));
            }
            j << (first ? "\n  " : ",\n  ") << "{" << head << "\"digits\": [";
            first = false;
            for (size_t d = 0; d < bv.size(); d++) {
                std::string bn = base + ".b" + std::to_string(d), an = base + ".a" + std::to_string(d);
                pw.rns(bn, bv[d]);
                pw.rns(an, av[d]);
                j << (d ? ", " : "") << "{\"b\": \"" << bn << "\", \"a\": \"" << an << "\"";
                if (!lk.empty()) j << ", \"limb\": " << lk[d].first << ", \"power\": " << lk[d].second;
                j << "}";
            }
            j << "]}";
            keyLimbs = bv.empty() ? 0 : bv[0].GetNumOfElements();
        };
        const std::string tag = m_kp.secretKey->GetKeyTag();
        try {
            const auto& mk = CryptoContextImpl<E>::GetEvalMultKeyVector(tag);
            for (size_t i = 0; i < mk.size(); i++) {
                std::string head = i == 0 ? "\"kind\": \"relin\", \"index\": 0, " :
                                            "\"kind\": \"relin\", \"index\": 0, \"power\": " + std::to_string(i + 2) + ", ";
                dumpKey(mk[i], i == 0 ? "ekm" : "ekm" + std::to_string(i + 2), head);
                nRelin++;
            }
        }
        catch (const std::runtime_error& e) {
            if (std::string(e.what()).find("BV digit keys") != std::string::npos) throw;
        }
        catch (const std::exception&) {
        }
        try {
            const auto& am = CryptoContextImpl<E>::GetEvalAutomorphismKeyMap(tag);
            for (const auto& kv : am) {
                dumpKey(kv.second, "eka" + std::to_string(kv.first),
                        "\"kind\": \"rot\", \"index\": " + std::to_string(kv.first) + ", ");
                nRot++;
            }
        }
        catch (const std::runtime_error& e) {
            if (std::string(e.what()).find("BV digit keys") != std::string::npos) throw;
        }
        catch (const std::exception&) {
        }
        j << (first ? "" : "\n ") << "],\n";
        note("eval keys: " + std::to_string(nRelin) + " EvalMult key(s), " + std::to_string(nRot) +
             " automorphism key(s), each entry over " + std::to_string(keyLimbs) + " limbs (" +
             (hybrid ? "HYBRID: Q then P" :
                       digitSize ? "BV with digit size " + std::to_string(digitSize) + ": Q; entry = (limb, power)" :
                                   "BV: the limbs of the secret, i.e. Q, with EXTENDED encryption Q then r; entry j = limb j") +
             "); relin keys carry \"index\": 0");

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
            j << "\"randomness\": \"" << en.how << "\"" << (en.extended ? ", \"extended\": true" : "");
            if (en.haveTqt) {
                pw.rns(b + ".tqt", en.tqt);
                j << ", \"timesQovert\": \"" << b << ".tqt\"";
            }
            if (en.havePre) {
                pw.rns(b + ".pre0", en.pre0);
                pw.rns(b + ".pre1", en.pre1);
                j << ", \"extendedPre\": [\"" << b << ".pre0\", \"" << b << ".pre1\"]";
            }
            j << "}";
        }
        j << (m_encs.empty() ? "" : "\n ") << "],\n";
        if (extended() && !m_encs.empty())
            note("EXTENDED encryption: (u, e1, e2) are the sampler outputs over Q*r (r = extendedPrime); the exporter "
                 "checked in C++ that the library's own steps (CRT-lift of the plaintext to Q*r, c0 = b*u + e1 + "
                 "TimesQovert_{Q*r}(p), c1 = a*u + e2 with the public key over Q*r, then ScaleAndRoundPOverQ of both "
                 "components, bfvrns-pke.cpp:182-214) reproduce the ciphertext for every entry with randomness "
                 "prng-replay/scripted");

        // objects
        uint64_t calls0 = Prng::handle() ? Prng::calls() : 0;
        j << " \"objects\": {";
        const auto& objs = tr->objects();
        size_t nDec = 0, nDecErr = 0, nDecFull = 0, nDecLow = 0, nNonCanon = 0, nPhase = 0, nDecodeErr = 0;
        std::set<std::string> decodeIds;
        for (const auto& en : m_encs) decodeIds.insert(en.ct);
        for (const auto& f : m_final) decodeIds.insert(tr->idOf(f, "ct"));
        uint64_t maxNonCanon = 0;
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
            // components not in EVALUATION format as the library holds them (the dump is in coefficient
            // form either way): the 3-part output of EvalMult / EvalSquare is left in COEFFICIENT format
            if (!el.empty() && el[0].GetFormat() != Format::EVALUATION) j << ", \"format\": \"COEFFICIENT\"";
            if (el.size() < 2 || el.size() > 3) {
                j << ", \"decrypt\": null}";
                continue;
            }
            try {
                NativePoly raw;
                m_cc->GetScheme()->Decrypt(o.ct, m_kp.secretKey, &raw);
                if (raw.GetFormat() != Format::COEFFICIENT) raw.SetFormat(Format::COEFFICIENT);
                if (raw.GetModulus().ConvertToInt() != t)
                    throw std::runtime_error("Decrypt output modulus is " + raw.GetModulus().ToString() + ", not t");
                // BEHZ's ScaleAndRound (dcrtpoly-impl.h:1652-1696) returns (s + (s mod gamma)) >> 26 with
                // s in [0, t*gamma): a value in [0, t], i.e. possibly the NON-CANONICAL residue t for 0.
                // The dump stores canonical residues; the number of such coefficients is noted.
                // `raw` is written exactly as the library returns it (rawReduced: false): with modulus t when
                // every coefficient is below t, else as an exact integer line (modulus 0, values in [0, t]).
                bool canon = true;
                for (size_t i = 0; i < raw.GetLength(); i++) {
                    uint64_t v = raw[i].ConvertToInt();
                    if (v >= t) {
                        canon = false;
                        nNonCanon++;
                        if (v > maxNonCanon) maxNonCanon = v;
                    }
                }
                if (canon)
                    pw.native(o.id + ".dec", 0, raw);
                else {
                    std::vector<int64_t> rv(raw.GetLength());
                    for (size_t i = 0; i < rv.size(); i++) rv[i] = (int64_t)raw[i].ConvertToInt();
                    pw.sgn(o.id + ".dec", rv);
                }
                j << ", \"decrypt\": {\"raw\": \"" << o.id << ".dec\", \"rawReduced\": false";
                // The intermediates of PKEBFVRNS::Decrypt (bfvrns-pke.cpp:225-278). DecryptCore is not
                // reachable from outside the scheme object, so it is RECOMPUTED here with the library's own
                // DCRTPoly calls in the order of PKERNS::DecryptCore (rns-pke.cpp:202-221), and the rest of
                // Decrypt is replayed on it; the intermediates are exported only if that replay returns
                // exactly the NativePoly the library's Decrypt returned.
                {
                    const E& sk = m_kp.secretKey->GetPrivateElement();
                    size_t sizeQl = el[0].GetParams()->GetParams().size();
                    E scopy = sk.CloneTowers(0, sizeQl - 1);
                    E sPower(scopy);
                    E b(el[0]);
                    b.SetFormat(Format::EVALUATION);
                    E ci;
                    for (size_t i = 1; i < el.size(); i++) {
                        ci = el[i];
                        ci.SetFormat(Format::EVALUATION);
                        b.MultAccEqNoCheck(sPower, ci);
                        sPower *= scopy;
                    }
                    E phase(b);
                    phase.SetFormat(Format::COEFFICIENT);
                    NativePoly mine, switched;
                    std::string branch;
                    if (sizeQl == L) {
                        b.SetFormat(Format::COEFFICIENT);
                        if (mt == BEHZ) {
                            branch = "behz-gamma";
                            mine   = b.ScaleAndRound(m_cp->GetModuliQ(), m_cp->GetPlaintextModulus(), m_cp->Gettgamma(),
                                                     m_cp->GettgammaQHatInvModq(), m_cp->GettgammaQHatInvModqPrecon(),
                                                     m_cp->GetNegInvqModtgamma(), m_cp->GetNegInvqModtgammaPrecon());
                        }
                        else {
                            branch = "hps-float";
                            mine   = b.ScaleAndRound(m_cp->GetPlaintextModulus(), m_cp->GettQHatInvModqDivqModt(),
                                                     m_cp->GettQHatInvModqDivqModtPrecon(),
                                                     m_cp->GettQHatInvModqBDivqModt(),
                                                     m_cp->GettQHatInvModqBDivqModtPrecon(),
                                                     m_cp->GettQHatInvModqDivqFrac(), m_cp->GettQHatInvModqBDivqFrac());
                        }
                    }
                    else {
                        branch = "compressed";
                        size_t diffQl = L - sizeQl;
                        for (size_t l = 0; l + 1 < sizeQl; ++l) b.DropLastElementAndScale(m_cp->GetqlInvModq(diffQl + l));
                        b.SetFormat(Format::COEFFICIENT);
                        switched           = b.GetElementAtIndex(0);
                        NativePoly element = switched;
                        const NativeInteger q = element.GetModulus();
                        element = element.MultiplyAndRound(NativeInteger(t), q);
                        element.SwitchModulus(NativeInteger(t), 1, 0, 0);
                        mine = element;
                    }
                    bool same = mine.GetLength() == raw.GetLength();
                    for (size_t i = 0; same && i < raw.GetLength(); i++)
                        same = mine[i].ConvertToInt() == raw[i].ConvertToInt();
                    if (same) {
                        pw.rns(o.id + ".phase", phase);
                        j << ", \"phase\": \"" << o.id << ".phase\", \"branch\": \"" << branch << "\"";
                        if (branch == "compressed") {
                            pw.native(o.id + ".sw", 0, switched);
                            j << ", \"switched\": \"" << o.id << ".sw\"";
                        }
                        nPhase++;
                    }
                    else {
                        j << ", \"phase\": null, \"branch\": \"" << branch << "\"";
                        note(o.id + ": the replay of PKEBFVRNS::Decrypt on the recomputed DecryptCore output does NOT "
                             "return the library's NativePoly; decrypt.phase = null");
                    }
                }
                // the decoded plaintext, as the library returns it, for the final and the fresh ciphertexts
                if (decodeIds.count(o.id)) {
                    try {
                        Plaintext dp;
                        m_cc->Decrypt(m_kp.secretKey, o.ct, &dp);
                        bool coef = dp->GetEncodingType() == COEF_PACKED_ENCODING;
                        const std::vector<int64_t>& vals = coef ? dp->GetCoefPackedValue() : dp->GetPackedValue();
                        j << ", \"encoding\": " << jstr(fhecheck::encName(dp->GetEncodingType())) << ", \"decoded\": [";
                        for (size_t i = 0; i < vals.size(); i++) j << (i ? "," : "") << "\"" << vals[i] << "\"";
                        j << "]";
                    }
                    catch (const std::exception& ex) {
                        j << ", \"decoded\": null";
                        nDecodeErr++;
                        std::cerr << "decode " << o.id << ": " << ex.what() << "\n";
                    }
                }
                j << "}}";
                nDec++;
                (o.towers == L ? nDecFull : nDecLow)++;
            }
            catch (const std::exception& ex) {
                std::string w = ex.what();
                size_t p      = w.rfind('/');  // drop an absolute source path
                size_t q      = w.find(' ');
                if (!w.empty() && w[0] == '/' && p != std::string::npos && (q == std::string::npos || p < q))
                    w = w.substr(p + 1);
                j << ", \"decrypt\": null, \"decryptError\": " << jstr(w) << "}";
                nDecErr++;
            }
        }
        j << (objs.empty() ? "" : "\n ") << "},\n";
        if (Prng::handle() && Prng::calls() != calls0) throw std::runtime_error("Decrypt consumed PRNG output");
        note("decrypt: " + std::to_string(nDec) + " ciphertext(s) with 2 or 3 parts decrypted with "
             "cc->GetScheme()->Decrypt (untraced, no PRNG draw: asserted), " + std::to_string(nDecErr) +
             " threw. `raw` is PKEBFVRNS::Decrypt's NativePoly (bfvrns-pke.cpp:225-278), modulus t, before Decode. " +
             std::to_string(nDecFull) + " at all " + std::to_string(L) + " limbs (" +
             (mt == BEHZ ? "BEHZ: the gamma-corrected integer ScaleAndRound" :
                           "HPS family: DCRTPoly::ScaleAndRound with a binary64 sum of fractional parts, "
                           "dcrtpoly-impl.h:1218-1490") +
             "), " + std::to_string(nDecLow) +
             " at fewer limbs (the phase is switched to one limb by DropLastElementAndScale, then "
             "MultiplyAndRound(t, q_0), :254-275)");
        note("decrypt intermediates: decrypt.phase (" + std::to_string(nPhase) + " of " + std::to_string(nDec) +
             ") is the DCRTPoly c0 + c1*s (+ c2*s^2) over the ciphertext's limbs, coefficient form, RECOMPUTED with the "
             "library's DCRTPoly calls in the order of PKERNS::DecryptCore (rns-pke.cpp:202-221; the scheme's own "
             "DecryptCore is not reachable from outside) and exported only if replaying the rest of PKEBFVRNS::Decrypt "
             "on it (branch hps-float / behz-gamma: the same DCRTPoly::ScaleAndRound call with the context's tables; "
             "compressed: DropLastElementAndScale per limb, then MultiplyAndRound(t, q_0), decrypt.switched = the one-limb "
             "polynomial in between) returns exactly the NativePoly of the library's Decrypt. decrypt.decoded (final "
             "and fresh ciphertexts): the values of cc->Decrypt(sk, ct, &pt) after Decode (packed: GetPackedValue, "
             "slots, signed; coefpacked: GetCoefPackedValue), untraced; " + std::to_string(nDecodeErr) + " decode call(s) threw");
        if (nNonCanon)
            note("decrypt: " + std::to_string(nNonCanon) + " coefficient(s) of the library's NativePoly were >= t (largest " +
                 std::to_string(maxNonCanon) + ", t = " + std::to_string(t) +
                 "): stored exactly (rawReduced: false), so those `raw` lines are exact integer lines (modulus 0)");

        // build
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
          << ", \"ompMaxThreads\": " << omp_get_max_threads() << ",\n           \"float\": "
          << (m_float.empty() ? std::string("null") : m_float) << "},\n";
        if (m_float.empty())
            note("build.float is null: no float_facts.json next to the exporter (export/build_cpp_bfv.sh writes it)");
        // ksInfo (as for BGV; perLevel only for HYBRID)
        j << " \"ksInfo\": {\"numPartQ\": " << m_cp->GetNumPartQ() << ", \"numPerPartQ\": " << m_cp->GetNumPerPartQ()
          << ", \"numberOfQPartitions\": " << (hybrid ? m_cp->GetNumberOfQPartitions() : 0) << ", \"sizeQ\": " << L
          << ", \"sizeP\": " << (hybrid ? m_cp->GetParamsP()->GetParams().size() : 0) << ", \"keyLimbs\": " << keyLimbs
          << ",\n            \"perLevel\": [";
        if (hybrid) {
            uint32_t alpha = m_cp->GetNumPerPartQ();
            for (size_t l = 1; l <= L; l++) {
                uint32_t numPartQl = ceil((static_cast<double>(l)) / alpha);
                if (numPartQl > m_cp->GetNumberOfQPartitions()) numPartQl = m_cp->GetNumberOfQPartitions();
                j << (l > 1 ? ", " : "") << "{\"towers\": " << l << ", \"numPartitions\": " << numPartQl
                  << ", \"digitTowers\": [";
                for (uint32_t part = 0; part < numPartQl; part++) {
                    size_t sz = part == numPartQl - 1 ? l - alpha * part : m_cp->GetParamsPartQ(part)->GetParams().size();
                    j << (part ? "," : "") << sz;
                }
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

private:
    std::string m_out, m_name;
    uint64_t m_seed;
    std::string m_gen;
    CryptoContext<E> m_cc;
    BfvDefaults m_dflt;
    std::shared_ptr<CryptoParametersBFVRNS> m_cp;
    KeyPair<E> m_kp;
    bool m_havePkE = false, m_arbitrary = false;
    std::vector<int64_t> m_pkE;
    std::vector<Enc> m_encs;
    std::vector<Ciphertext<E>> m_final;
    std::vector<std::string> m_notes;
    std::string m_float, m_pkHow = "prng-replay";
};

}  // namespace pin
