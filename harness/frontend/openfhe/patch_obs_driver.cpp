// patch_obs_driver.cpp -- UNTRUSTED. The behavioural half of check_patch_observation.sh: one
// deterministic program, compiled against pristine OpenFHE v1.6.1 and against the tracer-patched
// build (ENABLE_TRACER=ON), whose printed digests must be identical line for line.
//
//   patch_obs_driver LIBPINPRNG none            no tracer (pristine build, or patched with none set)
//   patch_obs_driver LIBPINPRNG json TRACEDIR   patched build only: every context traced (the
//                                               fhecheck JsonTracer for BGV/BFV as bgv_demo installs
//                                               it, before KeyGen; OpenFHE's SimpleTracer for CKKS)
//
// Randomness: OpenFHE's external-PRNG hook (PseudoRandomNumberGenerator::InitPRNGEngine, upstream
// v1.6.1) loads harness/openfhe-pin/cpp/pin_prng.cpp, reseeded at the start of every context; run
// with OMP_NUM_THREADS=1. Every operation is wrapped: an exception prints "EXC <message>" (it is
// compared like a value). Printed per result: a 64-bit FNV-1a digest of every coefficient of every
// tower of every component plus format, level and noiseScaleDeg (ciphertexts), or the decrypted
// values (hexfloat for CKKS); and the number of PRNG words drawn so far in the context.
#include "openfhe.h"
#if __has_include("utils/fhecheck-tracer.h") && defined(ENABLE_TRACER)
    #include "utils/fhecheck-tracer.h"
    #include "utils/simpletracer.h"
    #define PATCHED 1
#else
    #define PATCHED 0
#endif

#include <dlfcn.h>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using namespace lbcrypto;

static void (*g_seed)(uint64_t)  = nullptr;
static uint64_t (*g_calls)(void) = nullptr;
static std::string g_mode;
static std::string g_dir;
static int g_ctx = 0;

struct Fnv {
    uint64_t h = 1469598103934665603ULL;
    void add(uint64_t v) {
        for (int i = 0; i < 8; i++) {
            h ^= (v >> (8 * i)) & 0xff;
            h *= 1099511628211ULL;
        }
    }
};

static std::string hex(uint64_t v) {
    char b[20];
    std::snprintf(b, sizeof b, "%016llx", (unsigned long long)v);
    return b;
}

static std::string digest(const Ciphertext<DCRTPoly>& c) {
    if (!c)
        return "null";
    Fnv f;
    const auto& els = c->GetElements();
    f.add(els.size());
    for (const auto& e : els) {
        f.add(e.GetFormat() == Format::EVALUATION ? 1 : 0);
        const auto& tw = e.GetAllElements();
        f.add(tw.size());
        for (const auto& p : tw) {
            f.add(p.GetModulus().ConvertToInt());
            const auto& v = p.GetValues();
            for (size_t i = 0; i < v.GetLength(); i++)
                f.add(v[i].ConvertToInt());
        }
    }
    f.add(c->GetLevel());
    f.add(c->GetNoiseScaleDeg());
    return hex(f.h) + " level " + std::to_string(c->GetLevel()) + " towers " +
           std::to_string(els.empty() ? 0 : els[0].GetNumOfElements()) + " parts " + std::to_string(els.size());
}

// An exception message without what differs between two checkouts of the same code: the
// directory before "src/{pke,core,binfhe}/" and the ":l.<line>" suffix of the file name (the patch shifts lines).
static std::string excMsg(const std::exception& e) {
    std::string w = e.what();
    size_t c      = w.find(':');  // the file name ends at the first colon
    for (const char* d : {"/src/pke/", "/src/core/", "/src/binfhe/"}) {
        size_t k = w.rfind(d, c);
        if (k != std::string::npos && k < c) {
            w = w.substr(k + 1);
            break;
        }
    }
    size_t l = w.find(":l.");
    if (l != std::string::npos) {
        size_t m = l + 3;
        while (m < w.size() && std::isdigit((unsigned char)w[m]))
            m++;
        w = w.substr(0, l) + w.substr(m);
    }
    return "EXC " + w.substr(0, 400);
}

static void line(const std::string& name, const std::string& v) {
    std::cout << "ctx" << g_ctx << " " << name << ": " << v << " | prng " << (g_calls ? g_calls() : 0) << "\n";
}

// run f; print its digest or the exception
static Ciphertext<DCRTPoly> op(const std::string& name, std::function<Ciphertext<DCRTPoly>()> f) {
    try {
        auto c = f();
        line(name, digest(c));
        return c;
    }
    catch (const std::exception& e) {
        line(name, excMsg(e));
        return nullptr;
    }
}

static void dec(const CryptoContext<DCRTPoly>& cc, const PrivateKey<DCRTPoly>& sk, const std::string& name,
                const Ciphertext<DCRTPoly>& c, bool ckks, bool coef = false) {
    if (!c)
        return;
    try {
        Plaintext p;
        cc->Decrypt(sk, c, &p);
        std::ostringstream o;
        if (ckks) {
            p->SetLength(8);
            o << std::hexfloat;
            for (auto x : p->GetRealPackedValue())
                o << x << " ";
        }
        else {
            if (!coef)
                p->SetLength(8);
            Fnv f;
            const auto& v = coef ? p->GetCoefPackedValue() : p->GetPackedValue();
            for (auto x : v)
                f.add((uint64_t)x);
            o << hex(f.h) << " ";
            for (size_t i = 0; i < v.size() && i < 8; i++)
                o << v[i] << " ";
        }
        line("dec " + name, o.str());
    }
    catch (const std::exception& e) {
        line("dec " + name, excMsg(e));
    }
}

static void trace(const CryptoContext<DCRTPoly>& cc, bool ckks) {
#if PATCHED
    if (g_mode != "json")
        return;
    std::string f = g_dir + "/ctx" + std::to_string(g_ctx) + (ckks ? ".simple.txt" : ".trace.jsonl");
    if (ckks) {
        IF_TRACE(cc->setTracer(std::make_shared<SimpleTracer<DCRTPoly>>(std::make_shared<std::ofstream>(f))));
    }
    else {
        auto tr = std::make_shared<fhecheck::JsonTracer>(std::make_shared<std::ofstream>(f));
        tr->watch(cc);
        IF_TRACE(cc->setTracer(tr));
    }
#else
    (void)cc;
    (void)ckks;
#endif
}

// the integer schemes: the same program for BGV and BFV
static void integerProgram(CryptoContext<DCRTPoly> cc, bool bgv) {
    trace(cc, false);
    auto kp = cc->KeyGen();
    cc->EvalMultKeyGen(kp.secretKey);
    cc->EvalRotateKeyGen(kp.secretKey, {1, 2, -1, -2});
    cc->EvalSumKeyGen(kp.secretKey);
    line("keygen", "done");
    std::vector<int64_t> va = {1, 2, 3, 4, 5, 6, 7, 8}, vb = {5, 6, 7, 8, -1, -2, -3, -4}, vc = {3, 1, 4, 1, 5, 9, 2, 6};
    auto pa = cc->MakePackedPlaintext(va), pb = cc->MakePackedPlaintext(vb), pc = cc->MakePackedPlaintext(vc);
    auto pk = cc->MakeCoefPackedPlaintext(vc);
    auto ca  = op("enc pk a", [&] { return cc->Encrypt(kp.publicKey, pa); });
    auto cb  = op("enc pk b", [&] { return cc->Encrypt(kp.publicKey, pb); });
    auto csk = op("enc sk c", [&] { return cc->Encrypt(kp.secretKey, pc); });
    auto ccf = op("enc pk coef", [&] { return cc->Encrypt(kp.publicKey, pk); });
    std::vector<std::pair<std::string, Ciphertext<DCRTPoly>>> rs;
    auto R = [&](const std::string& n, std::function<Ciphertext<DCRTPoly>()> f) {
        auto c = op(n, f);
        rs.emplace_back(n, c);
        return c;
    };
    R("add", [&] { return cc->EvalAdd(ca, cb); });
    R("sub", [&] { return cc->EvalSub(ca, csk); });
    R("addPlain", [&] { return cc->EvalAdd(ca, pc); });
    R("subPlain", [&] { return cc->EvalSub(ca, pc); });
    R("negate", [&] { return cc->EvalNegate(cb); });
    auto m  = R("mult", [&] { return cc->EvalMult(ca, cb); });
    auto mn = R("multNoRelin", [&] { return cc->EvalMultNoRelin(ca, csk); });
    R("relin", [&] { return cc->Relinearize(mn); });
    auto sq = R("square", [&] { return cc->EvalSquare(m); });
    R("mult3", [&] { return cc->EvalMult(sq, csk); });
    R("multPlain", [&] { return cc->EvalMult(ca, pb); });
    R("rotate+1", [&] { return cc->EvalRotate(m, 1); });
    R("atIndex-2", [&] { return cc->EvalAtIndex(ca, -2); });
    R("sum", [&] { return cc->EvalSum(ca, 8); });
    R("innerProduct", [&] { return cc->EvalInnerProduct(ca, cb, 8); });
    R("addMany", [&] { return cc->EvalAddMany({ca, cb, csk}); });
    R("multMany", [&] { return cc->EvalMultMany({ca, cb, csk}); });
    R("addInPlace", [&] {
        auto x = cc->EvalAdd(ca, cb);
        cc->EvalAddInPlace(x, csk);
        return x;
    });
    if (bgv) {
        R("modReduce", [&] { return cc->ModReduce(m); });
        R("levelReduce", [&] { return cc->LevelReduce(ca, nullptr, 1); });
    }
    R("compress", [&] { return cc->Compress(sq, 1); });
    auto kp2 = cc->KeyGen();
    auto ek  = cc->KeySwitchGen(kp.secretKey, kp2.secretKey);
    auto ks  = op("keySwitch", [&] { return cc->KeySwitch(ca, ek); });
    for (auto& [n, c] : rs)
        dec(cc, kp.secretKey, n, c, false);
    dec(cc, kp.secretKey, "enc sk c", csk, false);
    dec(cc, kp.secretKey, "enc pk coef", ccf, false, true);
    dec(cc, kp2.secretKey, "keySwitch", ks, false);
}

static void guarded(const std::function<void()>& f) {
    try {
        f();
    }
    catch (const std::exception& e) {
        line("context", excMsg(e));
        g_ctx++;
    }
}

static void bgv(ScalingTechnique sc, KeySwitchTechnique ks, uint32_t n) {
    g_seed(1000 + g_ctx);
    CCParams<CryptoContextBGVRNS> p;
    p.SetMultiplicativeDepth(3);
    p.SetPlaintextModulus(65537);
    p.SetScalingTechnique(sc);
    p.SetKeySwitchTechnique(ks);
    if (ks == BV && sc == FIXEDMANUAL)
        p.SetScalingModSize(55);  // BV with digit size 0 needs a declared prime size in BGV
    else if (ks == BV)
        p.SetDigitSize(16);  // ... and the automatic modes, which take none, a digit size
    if (n) {
        p.SetRingDim(n);
        p.SetSecurityLevel(HEStd_NotSet);
    }
    auto cc = GenCryptoContext(p);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    cc->Enable(ADVANCEDSHE);
    std::cout << "ctx" << g_ctx << " BGV scal " << sc << " ks " << ks << " N " << cc->GetRingDimension() << "\n";
    integerProgram(cc, true);
    g_ctx++;
}

static void bfv(MultiplicationTechnique mt, KeySwitchTechnique ks, uint32_t n) {
    g_seed(1000 + g_ctx);
    CCParams<CryptoContextBFVRNS> p;
    p.SetMultiplicativeDepth(3);
    p.SetPlaintextModulus(65537);
    p.SetMultiplicationTechnique(mt);
    p.SetKeySwitchTechnique(ks);
    if (n) {
        p.SetRingDim(n);
        p.SetSecurityLevel(HEStd_NotSet);
    }
    auto cc = GenCryptoContext(p);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    cc->Enable(ADVANCEDSHE);
    std::cout << "ctx" << g_ctx << " BFV mult " << mt << " ks " << ks << " N " << cc->GetRingDimension() << "\n";
    integerProgram(cc, false);
    g_ctx++;
}

static void ckks(ScalingTechnique sc) {
    g_seed(1000 + g_ctx);
    CCParams<CryptoContextCKKSRNS> p;
    p.SetMultiplicativeDepth(3);
    p.SetScalingModSize(50);
    p.SetFirstModSize(60);
    p.SetBatchSize(8);
    p.SetScalingTechnique(sc);
    p.SetRingDim(4096);
    p.SetSecurityLevel(HEStd_NotSet);
    auto cc = GenCryptoContext(p);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    cc->Enable(ADVANCEDSHE);
    std::cout << "ctx" << g_ctx << " CKKS scal " << sc << " N " << cc->GetRingDimension() << "\n";
    trace(cc, true);
    auto kp = cc->KeyGen();
    cc->EvalMultKeyGen(kp.secretKey);
    cc->EvalRotateKeyGen(kp.secretKey, {1, -1});
    cc->EvalSumKeyGen(kp.secretKey);
    std::vector<double> va = {0.5, 1.25, -2, 3, 0.125, -0.75, 1, 2}, vb = {1, 2, 3, 4, 5, 6, 7, 8};
    auto pa = cc->MakeCKKSPackedPlaintext(va), pb = cc->MakeCKKSPackedPlaintext(vb);
    auto ca = op("enc a", [&] { return cc->Encrypt(kp.publicKey, pa); });
    auto cb = op("enc b", [&] { return cc->Encrypt(kp.secretKey, pb); });
    std::vector<std::pair<std::string, Ciphertext<DCRTPoly>>> rs;
    auto R = [&](const std::string& n, std::function<Ciphertext<DCRTPoly>()> f) {
        auto c = op(n, f);
        rs.emplace_back(n, c);
        return c;
    };
    R("add", [&] { return cc->EvalAdd(ca, cb); });
    R("addConst", [&] { return cc->EvalAdd(ca, 1.5); });
    R("subPlain", [&] { return cc->EvalSub(ca, pb); });
    auto m = R("mult", [&] { return cc->EvalMult(ca, cb); });
    R("multConst", [&] { return cc->EvalMult(ca, 0.25); });
    auto r = R("rescale", [&] { return cc->Rescale(m); });
    R("square", [&] { return cc->EvalSquare(r ? r : m); });
    R("rotate", [&] { return cc->EvalRotate(ca, 1); });
    R("sum", [&] { return cc->EvalSum(ca, 8); });
    R("levelReduce", [&] { return cc->LevelReduce(ca, nullptr, 1); });
    for (auto& [n, c] : rs)
        dec(cc, kp.secretKey, n, c, true);
    g_ctx++;
}

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "usage: patch_obs_driver LIBPINPRNG none|json [TRACEDIR]\n";
        return 2;
    }
    g_mode = argv[2];
    if (g_mode == "json") {
        if (!PATCHED || argc < 4) {
            std::cerr << "json mode needs the patched build and a TRACEDIR\n";
            return 2;
        }
        g_dir = argv[3];
    }
    PseudoRandomNumberGenerator::InitPRNGEngine(argv[1]);
    void* h = dlopen(argv[1], RTLD_LAZY);
    g_seed  = (void (*)(uint64_t))dlsym(h, "pin_prng_seed");
    g_calls = (uint64_t(*)(void))dlsym(h, "pin_prng_calls");
    if (!g_seed || !g_calls) {
        std::cerr << "pin_prng symbols not found\n";
        return 2;
    }
    for (auto ks : {BV, HYBRID}) {
        for (auto sc : {FIXEDMANUAL, FIXEDAUTO, FLEXIBLEAUTO, FLEXIBLEAUTOEXT})
            guarded([&] { bgv(sc, ks, 4096); });
        for (auto mt : {HPS, BEHZ, HPSPOVERQ, HPSPOVERQLEVELED})
            guarded([&] { bfv(mt, ks, 4096); });
    }
    guarded([&] { bgv(FLEXIBLEAUTOEXT, HYBRID, 0); });  // OpenFHE's own (secure) ring dimension
    guarded([&] { bfv(HPSPOVERQLEVELED, BV, 0); });
    guarded([&] { ckks(FIXEDMANUAL); });
    guarded([&] { ckks(FLEXIBLEAUTO); });
    std::cout << "contexts " << g_ctx << "\n";
    return 0;
}
