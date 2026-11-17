// frontier_time.cpp -- UNTRUSTED timing driver for harness/eval/frontier (built against the
// PRISTINE OpenFHE v1.6.1 install, no tracer).
//
//   frontier_time --scheme BGV|BFV [--scal TECH] [--mult M] [--ks BV|HYBRID] [--depth C]
//                 [--progdepth D] [--prog chain|poly] [--t T] [--qbits S] [--firstbits F]
//                 [--dnum K] [--ringdim N] [--evaladd A] [--kscount K] [--reps R]
//
// Builds the context exactly as frontier_bgv.cpp / frontier_bfv.cpp do for the same options
// (CCParams setters only, security level kept, so OpenFHE generates the same primes), runs the
// same program (chain or poly; frontier_bgv.cpp documents both), once untimed as a warm-up and
// then R times; ONLY the homomorphic evaluation is in the timed region (no key generation,
// encryption or decryption). Prints one JSON line: N, the primes of Q and of P (so the caller can
// assert that the timed context is the certified one), per-run milliseconds, their minimum and
// median, and whether the last result decrypts to the cleartext result (slots 0..7).
// Run it with OMP_NUM_THREADS=1 (single-threaded).

#include "openfhe.h"

#include <algorithm>
#include <chrono>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using namespace lbcrypto;

int main(int argc, char** argv) {
    std::string scheme = "BGV", scal = "FIXEDMANUAL", mult = "default", ks = "default", prog = "chain";
    uint32_t depth = 1, pd = 0, qbits = 0, firstbits = 0, dnum = 0, ringdim = 0, evaladd = 0, kscount = 0, reps = 5;
    uint64_t t = 65537;
    for (int i = 1; i + 1 < argc; i += 2) {
        std::string k = argv[i], v = argv[i + 1];
        if (k == "--scheme") scheme = v;
        else if (k == "--scal") scal = v;
        else if (k == "--mult") mult = v;
        else if (k == "--ks") ks = v;
        else if (k == "--depth") depth = std::stoul(v);
        else if (k == "--progdepth") pd = std::stoul(v);
        else if (k == "--prog") prog = v;
        else if (k == "--t") t = std::stoull(v);
        else if (k == "--qbits") qbits = std::stoul(v);
        else if (k == "--firstbits") firstbits = std::stoul(v);
        else if (k == "--dnum") dnum = std::stoul(v);
        else if (k == "--ringdim") ringdim = std::stoul(v);
        else if (k == "--evaladd") evaladd = std::stoul(v);
        else if (k == "--kscount") kscount = std::stoul(v);
        else if (k == "--reps") reps = std::stoul(v);
        else { std::cerr << "unknown option " << k << "\n"; return 2; }
    }
    if (!pd) pd = depth;
    const bool bgv = scheme == "BGV";
    CryptoContext<DCRTPoly> cc;
    if (bgv) {
        CCParams<CryptoContextBGVRNS> p;
        p.SetMultiplicativeDepth(depth);
        p.SetPlaintextModulus(t);
        if (dnum) p.SetNumLargeDigits(dnum);
        if (qbits) p.SetScalingModSize(qbits);
        if (firstbits) p.SetFirstModSize(firstbits);
        if (ringdim) p.SetRingDim(ringdim);
        if (evaladd) p.SetEvalAddCount(evaladd);
        if (kscount) p.SetKeySwitchCount(kscount);
        if (scal == "FIXEDMANUAL") p.SetScalingTechnique(FIXEDMANUAL);
        else if (scal == "FIXEDAUTO") p.SetScalingTechnique(FIXEDAUTO);
        else if (scal == "FLEXIBLEAUTO") p.SetScalingTechnique(FLEXIBLEAUTO);
        else if (scal == "FLEXIBLEAUTOEXT") p.SetScalingTechnique(FLEXIBLEAUTOEXT);
        else if (scal != "default") { std::cerr << "unknown scaling technique\n"; return 2; }
        cc = GenCryptoContext(p);
    } else {
        CCParams<CryptoContextBFVRNS> p;
        p.SetMultiplicativeDepth(depth);
        p.SetPlaintextModulus(t);
        if (dnum) p.SetNumLargeDigits(dnum);
        if (qbits) p.SetScalingModSize(qbits);
        if (ringdim) p.SetRingDim(ringdim);
        if (mult == "HPS") p.SetMultiplicationTechnique(HPS);
        else if (mult == "HPSPOVERQ") p.SetMultiplicationTechnique(HPSPOVERQ);
        else if (mult == "HPSPOVERQLEVELED") p.SetMultiplicationTechnique(HPSPOVERQLEVELED);
        else if (mult == "BEHZ") p.SetMultiplicationTechnique(BEHZ);
        else if (mult != "default") { std::cerr << "unknown multiplication technique\n"; return 2; }
        if (ks == "HYBRID") p.SetKeySwitchTechnique(HYBRID);
        else if (ks == "BV") p.SetKeySwitchTechnique(BV);
        else if (ks != "default") { std::cerr << "unknown key-switching technique\n"; return 2; }
        cc = GenCryptoContext(p);
    }
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    cc->Enable(ADVANCEDSHE);
    auto cp = std::dynamic_pointer_cast<CryptoParametersRNS>(cc->GetCryptoParameters());
    const bool manual = bgv && cp->GetScalingTechnique() == FIXEDMANUAL;

    auto kp = cc->KeyGen();
    cc->EvalMultKeyGen(kp.secretKey);
    cc->EvalRotateKeyGen(kp.secretKey, {1, 2, 4, -1});
    std::vector<int64_t> va = {1, 2, 3, 4, 5, 6, 7, 8}, vb = {5, 6, 7, 8, -1, -2, -3, -4};
    auto ca = cc->Encrypt(kp.publicKey, cc->MakePackedPlaintext(va));
    auto cb = cc->Encrypt(kp.publicKey, cc->MakePackedPlaintext(vb));
    const size_t S = 8, R = cc->GetRingDimension() / 2;
    auto mod = [&](int64_t x) { int64_t r = x % (int64_t)t; return r < 0 ? r + (int64_t)t : r; };
    auto rowv = [&](const std::vector<int64_t>& v) { std::vector<int64_t> r(R, 0); for (size_t i = 0; i < v.size(); i++) r[i] = mod(v[i]); return r; };
    auto rot = [&](const std::vector<int64_t>& v, size_t k) { std::vector<int64_t> r(R); for (size_t i = 0; i < R; i++) r[i] = v[(i + k) % R]; return r; };
    auto zipR = [&](const std::vector<int64_t>& x, const std::vector<int64_t>& y, int op) {
        std::vector<int64_t> r(R);
        for (size_t i = 0; i < R; i++) r[i] = mod(op == 0 ? x[i] + y[i] : x[i] * y[i]);
        return r;
    };
    auto coef = [&](uint32_t j) { std::vector<int64_t> c(S); for (size_t i = 0; i < S; i++) c[i] = (int64_t)((3 * j + 5 * i + 1) % 17) - 8; return c; };
    // plaintexts are made outside the timed region
    std::vector<Plaintext> pc(pd);
    for (uint32_t j = 0; j < pd; j++) pc[j] = cc->MakePackedPlaintext(coef(j));

    std::vector<int64_t> want;
    if (prog == "chain") {
        want = zipR(rowv(va), rowv(vb), 2);
        for (uint32_t d = 1; d < pd; d++) want = zipR(want, want, 2);
    } else if (prog == "poly") {
        auto wu = zipR(rowv(va), rowv(vb), 2);
        for (size_t k : {1, 2, 4}) wu = zipR(wu, rot(wu, k), 0);
        want = zipR(wu, rowv(coef(pd - 1)), 0);
        for (int32_t j = (int32_t)pd - 2; j >= 0; j--) want = zipR(zipR(want, wu, 2), rowv(coef(j)), 0);
    } else { std::cerr << "unknown prog\n"; return 2; }

    auto program = [&]() -> Ciphertext<DCRTPoly> {
        Ciphertext<DCRTPoly> res;
        if (prog == "chain") {
            res = cc->EvalMult(ca, cb);
            if (manual) cc->ModReduceInPlace(res);
            for (uint32_t d = 1; d < pd; d++) {
                res = cc->EvalSquare(res);
                if (manual) cc->ModReduceInPlace(res);
            }
        } else {
            auto u = cc->EvalMult(ca, cb);
            if (manual) cc->ModReduceInPlace(u);
            for (int32_t k : {1, 2, 4}) u = cc->EvalAdd(u, cc->EvalRotate(u, k));
            res = cc->EvalAdd(u, pc[pd - 1]);
            for (int32_t j = (int32_t)pd - 2; j >= 0; j--) {
                auto uj = u;
                if (manual && res->GetLevel() > u->GetLevel()) uj = cc->LevelReduce(u, nullptr, res->GetLevel() - u->GetLevel());
                res = cc->EvalMult(res, uj);
                if (manual) cc->ModReduceInPlace(res);
                res = cc->EvalAdd(res, pc[j]);
            }
        }
        return res;
    };
    Ciphertext<DCRTPoly> last = program();  // warm-up
    std::vector<double> ms;
    for (uint32_t r = 0; r < reps; r++) {
        auto t0 = std::chrono::steady_clock::now();
        last = program();
        auto t1 = std::chrono::steady_clock::now();
        ms.push_back(std::chrono::duration<double, std::milli>(t1 - t0).count());
    }
    Plaintext pt;
    cc->Decrypt(kp.secretKey, last, &pt);
    pt->SetLength(S);
    auto got = pt->GetPackedValue();
    bool ok = true;
    for (size_t i = 0; i < S; i++) ok = ok && mod(got[i]) == want[i];
    std::vector<double> sorted = ms;
    std::sort(sorted.begin(), sorted.end());
    double median = sorted.size() % 2 ? sorted[sorted.size() / 2] : (sorted[sorted.size() / 2 - 1] + sorted[sorted.size() / 2]) / 2;
    std::ostringstream o;
    o << "{\"N\": " << cc->GetRingDimension() << ", \"Q\": [";
    const auto& qs = cp->GetElementParams()->GetParams();
    for (size_t i = 0; i < qs.size(); i++) o << (i ? ", " : "") << "\"" << qs[i]->GetModulus().ConvertToInt() << "\"";
    o << "], \"P\": [";
    if (cp->GetKeySwitchTechnique() == HYBRID && cp->GetParamsP()) {
        const auto& ps = cp->GetParamsP()->GetParams();
        for (size_t i = 0; i < ps.size(); i++) o << (i ? ", " : "") << "\"" << ps[i]->GetModulus().ConvertToInt() << "\"";
    }
    o << "], \"minMs\": " << sorted.front() << ", \"medianMs\": " << median << ", \"ms\": [";
    for (size_t i = 0; i < ms.size(); i++) o << (i ? ", " : "") << ms[i];
    o << "], \"decryptsCorrectly\": " << (ok ? "true" : "false") << "}";
    std::cout << o.str() << std::endl;
    return ok ? 0 : 3;
}
