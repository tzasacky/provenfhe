// pin_adv_bfv.h -- UNTRUSTED. The adversarial programs of pin_export_bfv (--prog advplain:<v>,
// advmul:<v>); included by pin_export_bfv.cpp after `struct Run`. What each family does is described below.
//
//   advplain:allmax        p = (t-1, ..., t-1)
//   advplain:signpos<k>    p_j = t-1 where mu_j = sign(cos(pi (2k-1)(2j+1)/(2N))) = +1, else 0   (k = 1, 2, .. or "h" = N/2)
//   advplain:signneg<k>    p_j = t-1 where mu_j = -1, else 0
//   advplain:keyaware      p_j in {0, t-1} chosen from the ACTUAL noise e and message m of the fresh
//                          ciphertext (the exporter knows the secret) so that one coefficient of the
//                          product's noise  p*e - (Q mod t) * floor(p*m / t)  is as large as possible
//   advmul:scripted        two real cc->Encrypt calls whose sampler outputs (u, e1, e2) are scripted
//                          through the PRNG to the extreme values the samplers can emit, signs aligned
//                          with the secret and the public-key error; then EvalMult
//   advmul:scriptedsq      one such encryption, EvalSquare and EvalMult(x, x)
//   advmul:scriptedkey     as scripted, and the key generation is scripted too: s in {-1, 1}^N, public-key
//   advmul:scriptedkeysq   error constant at the extreme value (the largest fresh noise the samplers allow)
//   advmul:handbuilt       hand-built inputs (floor(Q/t) m + e - a s, a) (inputsArbitrary): |e_j| equal to
//                          the declared input bound, a_j ~ +-Q/2 with signs aligned to s; EvalMult
//   advmul:handbuiltneg    the same with the opposite alignment in the second operand
//   advmul:handbuiltsq     EvalSquare of one such input
//   advmul:handbuiltkey    handbuilt under a scripted key (s in {-1, 1}^N: ||s||_1 = N)
//   advplain:handmax       a hand-built input with e = (-bound, ..), message and plaintext operand all t-1:
//                          both terms of the plaintext-product noise at their largest, with the same sign
// Every program notes the measured noises (exact big-integer arithmetic with the secret).

namespace adv {
using BI = BigInteger;

// The stored coefficients of a plaintext (limb 0), asserted to be in [0, t).
static std::vector<uint64_t> ptCoeffs(const Plaintext& p, uint64_t t) {
    DCRTPoly e = p->GetElement<DCRTPoly>();
    e.SetFormat(Format::COEFFICIENT);
    const NativePoly& z = e.GetElementAtIndex(0);
    std::vector<uint64_t> r(z.GetLength());
    for (size_t i = 0; i < r.size(); i++) {
        r[i] = z[i].ConvertToInt();
        if (r[i] >= t) throw std::runtime_error("adv: stored plaintext coefficient not in [0, t)");
    }
    return r;
}

struct Noise {
    std::vector<BI> mag;     // |e_i|
    std::vector<int> sign;   // sign of e_i (-1, 0, 1)
    BI inf;                  // max |e_i|
    BI Q;
};

// e = [phase - floor(Q_l/t) m]_{Q_l}, centred, for the ciphertext's own Q_l.
static Noise noiseOf(Run& R, const Ct& ct, const std::vector<uint64_t>& m) {
    Poly ph = R.c->phase(ct);
    Noise z;
    z.Q      = ph.GetModulus();
    BI delta = z.Q / BI(R.t), half = z.Q >> 1;
    z.mag.resize(ph.GetLength());
    z.sign.assign(ph.GetLength(), 0);
    z.inf = BI(0);
    for (size_t i = 0; i < ph.GetLength(); i++) {
        BI d = ph[i].ModSub((delta * BI(m[i])).Mod(z.Q), z.Q);
        if (d > half) { d = z.Q - d; z.sign[i] = -1; }
        else if (d > BI(0)) z.sign[i] = 1;
        z.mag[i] = d;
        if (d > z.inf) z.inf = d;
    }
    return z;
}

// The library's raw decryption mod t (untraced).
static std::vector<uint64_t> rawDec(Run& R, const Ct& ct) {
    pin::detach(R.cc);
    NativePoly raw;
    R.cc->GetScheme()->Decrypt(ct, R.c->keys().secretKey, &raw);
    pin::attach(R.cc, R.tr);
    std::vector<uint64_t> r(raw.GetLength());
    for (size_t i = 0; i < r.size(); i++) r[i] = raw[i].ConvertToInt() % R.t;
    return r;
}

static std::string bitsOf(const BI& x) {
    return x.ToString() + " (" + std::to_string(x.GetMSB()) + " bits)";
}

// Noise of `ct` relative to the library's own decryption of it.
static void noteOut(Run& R, const std::string& what, const Ct& ct) {
    if (!ct) return;
    Noise z = noiseOf(R, ct, rawDec(R, ct));
    BI lim  = z.Q / BI(2 * R.t);
    R.c->note("adv: " + what + ": noise ||[phase - floor(Q/t) dec]_Q||_inf = " + bitsOf(z.inf) + "; Q/(2t) = " +
              bitsOf(lim) + " (dec = the library's own decryption of this ciphertext)");
}

// ---- the samplers: which PRNG words make them emit which value -----------------------------------
template <typename T>
static T firstOf(const std::vector<T>& v) { return v[0]; }
template <typename P>
static auto firstOf(const P& p) -> decltype(p.get()[0]) { return p.get()[0]; }

static int64_t dggOn(const DCRTPoly::DggType& dgg, uint64_t x) {
    uint32_t w[2] = {static_cast<uint32_t>(x), static_cast<uint32_t>(x >> 32)};
    pin::Prng::scriptPush(w, 2);
    int64_t v;
    try { v = firstOf(dgg.GenerateIntVector(1)); }
    catch (const std::exception&) { v = (x >> 63) ? 1000 : -1000; }
    if (pin::Prng::scriptRemaining() != 0) throw std::runtime_error("adv: dgg did not consume exactly 2 words");
    return v;
}
static bool minX(const DCRTPoly::DggType& dgg, int64_t v, uint64_t& out) {
    if (dggOn(dgg, ~0ULL) < v) return false;
    uint64_t lo = 0, hi = ~0ULL;
    while (lo < hi) {
        uint64_t mid = lo + (hi - lo) / 2;
        if (dggOn(dgg, mid) >= v) hi = mid; else lo = mid + 1;
    }
    out = lo;
    return true;
}
// value -> smallest x = w0 + 2^32 w1 that makes the real DGG emit it (the sampler is monotone in x)
static std::map<int64_t, uint64_t> probeGauss(const DCRTPoly::DggType& dgg) {
    std::map<int64_t, uint64_t> m;
    int64_t cur = dggOn(dgg, 0);
    uint64_t xs = 0;
    while (true) {
        if (std::llabs(cur) < 1000) m[cur] = xs;
        uint64_t nx;
        if (!minX(dgg, cur + 1, nx)) break;
        xs  = nx;
        cur = dggOn(dgg, nx);
        if (m.size() > 200) throw std::runtime_error("adv: too many Gaussian values");
    }
    return m;
}
// std::uniform_int_distribution<int>(-1, 1) of libstdc++ on one 32-bit word (probed): 1 -> -1, 0x55555556 -> 0, 0xAAAAAAAB -> +1
static std::vector<uint32_t> ternWords(const std::vector<int64_t>& v) {
    std::vector<uint32_t> w;
    for (auto x : v) w.push_back(x < 0 ? 1u : x == 0 ? 0x55555556u : 0xAAAAAAABu);
    return w;
}
static std::vector<uint32_t> gaussWords(const std::vector<int64_t>& v, const std::map<int64_t, uint64_t>& g) {
    std::vector<uint32_t> w;
    for (auto x : v) {
        auto it = g.find(x);
        if (it == g.end()) throw std::runtime_error("adv: the Gaussian sampler cannot emit " + std::to_string(x));
        w.push_back((uint32_t)it->second);
        w.push_back((uint32_t)(it->second >> 32));
    }
    return w;
}

// For target coefficient 0 of x*y in Z[X]/(X^N + 1): (x*y)_0 = x_0 y_0 - sum_{j>=1} x_j y_{N-j}.
// Returns sigma with sigma_j = the sign with which y enters next to x_j.
static std::vector<int64_t> partner(const std::vector<int64_t>& y) {
    size_t n = y.size();
    std::vector<int64_t> s(n);
    s[0] = y[0];
    for (size_t j = 1; j < n; j++) s[j] = -y[n - j];
    return s;
}

static DCRTPoly fromBig(const std::vector<BI>& v, const std::shared_ptr<DCRTPoly::Params>& params) {
    DCRTPoly r(params, Format::COEFFICIENT, true);
    for (size_t l = 0; l < r.GetNumOfElements(); l++) {
        NativePoly z = r.GetElementAtIndex(l);
        BI q(z.GetModulus().ConvertToInt());
        for (size_t i = 0; i < v.size(); i++) z[i] = NativeInteger(v[i].Mod(q).ConvertToInt<uint64_t>());
        r.SetElementAtIndex(l, std::move(z));
    }
    r.SetFormat(Format::EVALUATION);
    return r;
}

static std::vector<int64_t> secretVec(Run& R) {
    std::vector<int64_t> sv;
    if (!pin::centredSmall(R.c->keys().secretKey->GetPrivateElement(), sv))
        throw std::runtime_error("adv: secret is not a small vector");
    return sv;
}
// Hand-built input ciphertexts c = (floor(Q/t) m + e - a s, a): every e_j = dirE * bin with bin the input
// bound extract_bfv.py declares for STANDARD encryption, Be*(1 + 2*N*Bs) + ceil(r*(t-1)/t) (Be = 39 =
// ceil(3.19 * 12.006...), Bs = 1, r = Q mod t); a_j = dirA * sign_j * ((Q-1)/2 - rho_j) (centred),
// rho_j < 2^16, sign_j aligned with the secret so that coefficient 0 of the INTEGER product a*s of the
// centred representatives is dirA * about ||s||_1 * Q/2.
struct Hand {
    Run& R;
    Plaintext pm;
    std::vector<uint64_t> m;
    BI Q, bin, delta, halfm;
    std::vector<int64_t> sg;
    DCRTPoly sk;
    Ct tmpl;
    Hand(Run& r, Plaintext p) : R(r), pm(p) {
        m = ptCoeffs(pm, R.t);
        const auto params = R.cp->GetElementParams();
        Q      = params->GetModulus();
        BI rr  = Q.Mod(BI(R.t));
        BI dev = (rr * BI(R.t - 1) + BI(R.t - 1)) / BI(R.t);
        bin    = BI((uint64_t)39 * (1 + 2 * (uint64_t)R.N)) + dev;
        delta  = Q / BI(R.t);
        halfm  = (Q - BI(1)) >> 1;
        sg     = partner(secretVec(R));
        sk     = R.c->keys().secretKey->GetPrivateElement();
        sk.SetFormat(Format::EVALUATION);
        pin::detach(R.cc);
        tmpl = R.cc->Encrypt(R.c->keys().publicKey, pm);  // only its metadata is kept (untraced)
        pin::attach(R.cc, R.tr);
    }
    Ct mk(int dirA, int dirE) {
        const auto params = R.cp->GetElementParams();
        std::vector<BI> a(R.N), c0(R.N);
        for (uint32_t j = 0; j < R.N; j++) {
            int sj = sg[j] > 0 ? 1 : sg[j] < 0 ? -1 : (R.rng.below(2) ? 1 : -1);
            BI mag = halfm - BI(R.rng.below(1 << 16));
            a[j]   = dirA * sj > 0 ? mag : Q - mag;
            BI x   = (delta * BI(m[j])).Mod(Q);
            c0[j]  = dirE > 0 ? x.ModAdd(bin, Q) : x.ModSub(bin, Q);
        }
        DCRTPoly A = fromBig(a, params), C0 = fromBig(c0, params);
        C0 -= A * sk;
        Ct ct = tmpl->Clone();
        ct->SetElements({C0, A});
        ct->SetNoiseScaleDeg(1);
        R.c->addInput(R.tr, ct);
        Noise nz = noiseOf(R, ct, m);
        if (nz.inf != bin) throw std::runtime_error("adv: hand-built input noise is not exactly the declared bound");
        return R.last = ct;
    }
    std::string describe() const {
        return "HAND-BUILT inputs (inputsArbitrary; not encryptions): c = (floor(Q/t) m + e - a s, a) with every e_j = +-" +
               bin.ToString() + " = the input bound extract_bfv.py declares for STANDARD encryption (39*(1 + 2N) + "
               "ceil((Q mod t)(t-1)/t)), a_j = +-((Q-1)/2 - rho_j), rho_j < 2^16, signs aligned with the secret so that "
               "coefficient 0 of the INTEGER product a*s of the centred representatives is about ||s||_1 * Q/2 (the "
               "integer phase is far from the centred phase: the mulLift / mulRound terms). The extractor is run with "
               "--assume-fresh-inputs.";
    }
};
}  // namespace adv

// advmul:scriptedkey*: the REAL cc->KeyGen() with s in {-1, 1}^N (Hamming weight N, seeded signs) and the
// public-key error constant at the most negative value the Gaussian sampler can emit.
static KeyPair<DCRTPoly> advKeyGen(pin::CaseBfv& c, const CryptoContext<DCRTPoly>& cc, uint64_t seed) {
    using namespace adv;
    const uint32_t N = cc->GetRingDimension();
    const auto& dgg  = c.cp()->GetDiscreteGaussianGenerator();
    uint64_t st = pin::Prng::getState();
    auto g      = probeGauss(dgg);
    pin::Prng::setState(st);
    Rng rng{seed * 0x9E3779B97F4A7C15ULL + 77};
    std::vector<int64_t> sV(N), eV(N, g.begin()->first);
    for (auto& x : sV) x = rng.below(2) ? 1 : -1;
    KeyPair<DCRTPoly> kp = c.keyGenScripted(sV, eV, ternWords(sV), gaussWords(eV, g));
    c.note("advmul: scripted key generation: s in {-1, 1}^N (||s||_1 = N), public-key error constant " +
           std::to_string(g.begin()->first) + " (the most negative value the sampler emits; ||e_pk||_1 = " +
           std::to_string(-g.begin()->first) + "*N)");
    return kp;
}

// ---------------------------------------------------------------------------------------------
static std::vector<Ct> advPlain(Run& R, const std::string& var) {
    using namespace adv;
    const uint32_t N = R.N;
    const uint64_t t = R.t;
    Plaintext pm = R.mk();
    if (var == "handmax") {
        // noise of the product = p*e - (Q mod t)*floor(p*m/t): with m = p = (t-1, ..) and e = (-bin, ..) both
        // terms of coefficient N-1 have the same sign and every summand is at its largest
        if (R.cp->GetEncryptionTechnique() != STANDARD) throw std::runtime_error("advplain:handmax: STANDARD only");
        Hand H(R, pm);
        Ct ct = H.mk(+1, -1);
        Plaintext pp = R.packedOfPoly(std::vector<uint64_t>(N, t - 1));
        Ct out       = R.mulp(ct, pp);
        R.c->note("advplain:handmax: " + H.describe() + " Here e_j = -" + H.bin.ToString() +
                  " for every j, the message is the --msg plaintext, and the plaintext operand has every coefficient t-1.");
        R.c->note("adv: input: noise ||[phase - floor(Q/t) m]_Q||_inf = " + bitsOf(H.bin));
        noteOut(R, "EvalMult(ct, pt) output", out);
        return {out ? out : ct};
    }
    Ct ct        = R.enc(pm);
    std::vector<uint64_t> m = ptCoeffs(pm, t);
    Noise e = noiseOf(R, ct, m);
    std::vector<uint64_t> p(N, 0);
    std::string how;
    if (var == "allmax") {
        p.assign(N, t - 1);
        how = "every coefficient t-1";
    }
    else if (var.rfind("signpos", 0) == 0 || var.rfind("signneg", 0) == 0) {
        bool pos       = var[4] == 'p';
        std::string ks = var.substr(7);
        uint32_t k     = ks == "h" ? N / 2 : (uint32_t)std::stoul(ks);
        if (k < 1 || k > N) throw std::runtime_error("advplain: k out of range");
        const long double pi = 3.14159265358979323846264338327950288L;
        size_t nmax = 0;
        for (uint32_t j = 0; j < N; j++) {
            long double c = cosl(pi * (long double)(2 * k - 1) * (long double)(2 * j + 1) / (long double)(2 * N));
            bool plus = c >= 0;
            p[j] = (plus == pos) ? t - 1 : 0;
            nmax += p[j] != 0;
        }
        how = "mu_j = sign(cos(pi (2k-1)(2j+1)/(2N))), k = " + std::to_string(k) + "; p_j = t-1 where mu_j = " +
              (pos ? "+1" : "-1") + ", else 0 (" + std::to_string(nmax) + " nonzero coefficients)";
    }
    else if (var == "keyaware") {
        // noise of the product: p*e - r*floor(p*m/t) (r = Q mod t), i.e. about p * (e - (r/t) m):
        // w_j = t*e_j - r*m_j (exact), and coefficient i of p*w = sum_{j<=i} p_j w_{i-j} - sum_{j>i} p_j w_{N+i-j}
        BI r = e.Q.Mod(BI(t));
        std::vector<long double> w(N);
        for (uint32_t j = 0; j < N; j++) {
            long double ej = (long double)e.sign[j] * e.mag[j].ConvertToDouble();
            w[j] = (long double)t * ej - r.ConvertToDouble() * (long double)m[j];
        }
        long double best = -1;
        uint32_t bi = 0;
        int bs = 1;
        for (uint32_t i = 0; i < N; i++) {
            long double sp = 0, sn = 0;
            for (uint32_t j = 0; j < N; j++) {
                long double term = j <= i ? w[i - j] : -w[N + i - j];
                if (term > 0) sp += term; else sn -= term;
            }
            if (sp > best) { best = sp; bi = i; bs = 1; }
            if (sn > best) { best = sn; bi = i; bs = -1; }
        }
        size_t nmax = 0;
        for (uint32_t j = 0; j < N; j++) {
            long double term = j <= bi ? w[bi - j] : -w[N + bi - j];
            p[j] = (bs > 0 ? term > 0 : term < 0) ? t - 1 : 0;
            nmax += p[j] != 0;
        }
        how = "key-aware: p_j in {0, t-1} matched to the signs of w = t*e - (Q mod t)*m of the fresh ciphertext so that "
              "coefficient " + std::to_string(bi) + " of p*w is " + (bs > 0 ? "maximal" : "minimal") + " (" +
              std::to_string(nmax) + " nonzero coefficients)";
    }
    else
        throw std::runtime_error("unknown advplain variant " + var);
    Plaintext pp = R.packedOfPoly(p);
    Ct out       = R.mulp(ct, pp);
    R.c->note("advplain:" + var + ": plaintext operand with stored polynomial " + how +
              ", made with MakePackedPlaintext (slots = PackedEncoding::Decode of that polynomial; encoded result asserted)");
    R.c->note("adv: fresh input: noise ||[phase - floor(Q/t) m]_Q||_inf = " + bitsOf(e.inf));
    noteOut(R, "EvalMult(ct, pt) output", out);
    return {out ? out : ct};
}

static std::vector<Ct> advMul(Run& R, const std::string& var) {
    using namespace adv;
    const uint32_t N = R.N;
    const uint64_t t = R.t;
    auto& cc = R.cc;
    if (R.cp->GetEncryptionTechnique() != STANDARD) throw std::runtime_error("advmul: STANDARD encryption only");
    std::vector<int64_t> s = secretVec(R);
    Plaintext pm = R.mk();
    std::vector<uint64_t> m = ptCoeffs(pm, t);
    Ct out, out2;
    if (var == "scripted" || var == "scriptedsq" || var == "scriptedkey" || var == "scriptedkeysq") {
        if (!R.c->havePkE()) throw std::runtime_error("advmul: the public-key error was not captured");
        const auto& dgg = R.cp->GetDiscreteGaussianGenerator();
        uint64_t st = pin::Prng::getState();
        auto g      = probeGauss(dgg);
        pin::Prng::setState(st);
        int64_t lo = g.begin()->first, hi = g.rbegin()->first;
        std::vector<int64_t> sgS = partner(s), sgE = partner(R.c->pkE());
        auto mk = [&](int dir) {
            // (u*e_pk + e1 + e2*s)_0 = dir * (||e_pk||_1 + sum |e2_j s_..| + |e1_0|), every other draw extreme too
            std::vector<int64_t> u(N), e1(N), e2(N);
            for (uint32_t j = 0; j < N; j++) {
                int64_t a = sgE[j] > 0 ? 1 : sgE[j] < 0 ? -1 : 1;
                u[j]      = dir * a;
                int64_t b = sgS[j] > 0 ? 1 : sgS[j] < 0 ? -1 : 1;
                e2[j]     = dir * b > 0 ? hi : lo;
                e1[j]     = dir > 0 ? hi : lo;
            }
            auto wu = ternWords(u), w1 = gaussWords(e1, g), w2 = gaussWords(e2, g);
            uint64_t c0 = pin::Prng::calls();
            pin::Prng::scriptPush(wu.data(), wu.size());
            pin::Prng::scriptPush(w1.data(), w1.size());
            pin::Prng::scriptPush(w2.data(), w2.size());
            Ct ct = R.last = R.c->encryptScripted(R.tr, pm, u, e1, e2);
            if (pin::Prng::scriptRemaining() != 0 || pin::Prng::calls() - c0 != 5ull * N)
                throw std::runtime_error("advmul: Encrypt did not consume exactly the scripted 5N words");
            return ct;
        };
        R.c->note("advmul:" + var + ": the REAL cc->Encrypt(pk, pt) on scripted PRNG words: u in {-1, 1}^N aligned with the "
                  "public-key error, e2 in {" + std::to_string(lo) + ", " + std::to_string(hi) +
                  "}^N (the extreme values the library's discrete Gaussian sampler can emit, probed on this build) aligned "
                  "with the secret, e1 constant at the extreme, so that coefficient 0 of u*e_pk + e1 + e2*s is "
                  "+-(||e_pk||_1 + ~" + std::to_string(hi) + "..|" + std::to_string(lo) + "| * ||s||_1 + extreme)");
        Ct a = mk(+1);
        R.c->note("adv: input 1: noise ||[phase - floor(Q/t) m]_Q||_inf = " + bitsOf(noiseOf(R, a, m).inf));
        if (var == "scripted" || var == "scriptedkey") {
            Ct b = mk(-1);
            R.c->note("adv: input 2: noise = " + bitsOf(noiseOf(R, b, m).inf));
            out = R.mul(a, b);
        }
        else {
            out  = R.sq(a);
            out2 = R.mul(a, a);
        }
    }
    else if (var == "handbuilt" || var == "handbuiltneg" || var == "handbuiltsq" || var == "handbuiltkey") {
        Hand H(R, pm);
        R.c->note("advmul:" + var + ": " + H.describe());
        Ct a = H.mk(+1, +1);
        R.c->note("adv: input 1: noise ||[phase - floor(Q/t) m]_Q||_inf = " + bitsOf(H.bin) + " (= the declared bound)");
        if (var == "handbuiltsq") {
            out = R.sq(a);
        }
        else {
            Ct b = var == "handbuiltneg" ? H.mk(-1, +1) : H.mk(+1, -1);
            R.c->note("adv: input 2: noise = " + bitsOf(H.bin));
            out = R.mul(a, b);
        }
    }
    else
        throw std::runtime_error("unknown advmul variant " + var);
    noteOut(R, "product", out);
    if (out2) noteOut(R, "EvalMult(x, x)", out2);
    std::vector<Ct> fin = {out ? out : R.last};
    if (out2) fin.push_back(out2);
    return fin;
}
