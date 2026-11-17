// bfv_time.cpp -- UNTRUSTED timing driver for harness/frontend/levelbfv/depth_table.py.
//
//   bfv_time [--t T] [--depth D] [--progdepth K] [--ks BV|HYBRID|default] [--reps R]
//
// Builds the same context as `bfv_demo run --t T --depth D [--ks HYBRID]` (CCParams<BFVRNS> with
// only the plaintext modulus and the multiplicative depth set, plus the key-switching technique
// when it is not "default": OpenFHE v1.6.1's defaults are HPSPOVERQLEVELED, BV with digit size 0,
// STANDARD encryption, 60-bit primes, HEStd_128_classic) and runs bfv_demo's `chain` program of
// depth K on it: y = (a*b)^(2^(K-1)), i.e. EvalMult(a, b) followed by K-1 EvalSquare, each
// relinearized. The evaluation is repeated R times on the same two input ciphertexts; ONLY the
// evaluation is timed (no parameter generation, key generation, encryption or decryption in the
// timed region; one untimed warm-up evaluation first). No tracer is installed: with the traced
// build of OpenFHE this is its NullTracer, as in `bgv_demo --time`.
// Prints one JSON line: N, the number of limbs of Q and of P, log2 Q, the times in milliseconds
// (as measured, in order), their median and minimum, and whether the last result decrypts to the
// cleartext result mod t (slots 0..7).
//
// Build: see depth_table.py (--build), or
//   c++ -std=gnu++17 -O2 -fopenmp -I$I/include/openfhe{,/core,/pke,/binfhe,/cereal} bfv_time.cpp \
//       -o bfv_time -L$I/lib -Wl,-rpath,$I/lib -lOPENFHEpke -lOPENFHEcore
// with $I an OpenFHE v1.6.1 install (build_openfhe.sh). Run with OMP_NUM_THREADS=1.

#include "openfhe.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <iostream>
#include <string>
#include <vector>

using namespace lbcrypto;

int main(int argc, char** argv) {
    uint32_t depth = 1, pd = 0, reps = 5;
    uint64_t t = 65537;
    std::string ks = "default";
    for (int i = 1; i + 1 < argc; i += 2) {
        std::string k = argv[i], v = argv[i + 1];
        if (k == "--depth") depth = std::stoul(v);
        else if (k == "--progdepth") pd = std::stoul(v);
        else if (k == "--t") t = std::stoull(v);
        else if (k == "--ks") ks = v;
        else if (k == "--reps") reps = std::stoul(v);
        else { std::cerr << "unknown option " << k << "\n"; return 2; }
    }
    if (!pd) pd = depth;

    CCParams<CryptoContextBFVRNS> params;
    params.SetMultiplicativeDepth(depth);
    params.SetPlaintextModulus(t);
    if (ks == "HYBRID") params.SetKeySwitchTechnique(HYBRID);
    else if (ks == "BV") params.SetKeySwitchTechnique(BV);
    else if (ks != "default") { std::cerr << "unknown key-switching technique " << ks << "\n"; return 2; }
    CryptoContext<DCRTPoly> cc = GenCryptoContext(params);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    auto cp = std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc->GetCryptoParameters());

    auto kp = cc->KeyGen();
    cc->EvalMultKeyGen(kp.secretKey);
    std::vector<int64_t> va = {1, 2, 3, 4, 5, 6, 7, 8}, vb = {5, 6, 7, 8, -1, -2, -3, -4};
    auto ca = cc->Encrypt(kp.publicKey, cc->MakePackedPlaintext(va));
    auto cb = cc->Encrypt(kp.publicKey, cc->MakePackedPlaintext(vb));

    auto eval = [&]() {
        auto res = cc->EvalMult(ca, cb);
        for (uint32_t d = 1; d < pd; d++) res = cc->EvalSquare(res);
        return res;
    };
    Ciphertext<DCRTPoly> res = eval();  // warm-up, untimed
    std::vector<double> ms;
    for (uint32_t r = 0; r < reps; r++) {
        auto t0 = std::chrono::steady_clock::now();
        res     = eval();
        auto t1 = std::chrono::steady_clock::now();
        ms.push_back(std::chrono::duration<double, std::milli>(t1 - t0).count());
    }

    // cleartext result mod t, in 128-bit arithmetic (t may be 40 bits)
    auto mulmod = [&](uint64_t x, uint64_t y) { return (uint64_t)((unsigned __int128)x * y % t); };
    bool ok = true;
    Plaintext dec;
    cc->Decrypt(kp.secretKey, res, &dec);
    dec->SetLength(va.size());
    auto got = dec->GetPackedValue();
    for (size_t i = 0; i < va.size(); i++) {
        auto red = [&](int64_t x) { int64_t r = x % (int64_t)t; return (uint64_t)(r < 0 ? r + (int64_t)t : r); };
        uint64_t w = mulmod(red(va[i]), red(vb[i]));
        for (uint32_t d = 1; d < pd; d++) w = mulmod(w, w);
        if (red(got[i]) != w) ok = false;
    }

    double log2Q = 0;
    for (auto& p : cp->GetElementParams()->GetParams()) log2Q += std::log2((double)p->GetModulus().ConvertToInt<uint64_t>());
    size_t sizeP = cp->GetParamsP() ? cp->GetParamsP()->GetParams().size() : 0;
    std::vector<double> sorted = ms;
    std::sort(sorted.begin(), sorted.end());
    std::cout << "{\"N\": " << cc->GetRingDimension() << ", \"limbs\": " << cp->GetElementParams()->GetParams().size()
              << ", \"special\": " << sizeP << ", \"log2Q\": " << log2Q << ", \"t\": " << t << ", \"depth\": " << depth
              << ", \"progdepth\": " << pd << ", \"ks\": \"" << ks << "\", \"reps\": " << reps << ", \"ms\": [";
    for (size_t i = 0; i < ms.size(); i++) std::cout << (i ? ", " : "") << ms[i];
    std::cout << "], \"medianMs\": " << sorted[sorted.size() / 2] << ", \"minMs\": " << sorted.front()
              << ", \"decryptsToCleartext\": " << (ok ? "true" : "false") << "}\n";
    return 0;
}
