// tamper_demo.cpp -- UNTRUSTED test driver for the fhe_check OpenFHE frontend (tests only).
//
// Small UNMODIFIED-style OpenFHE programs, traced through FHECHECK_TRACE_DIR (fhecheck-tracer.h,
// MaybeAutoTrace), that change a ciphertext, plaintext, key or parameter through the PUBLIC API
// outside the traced calls. Each must be REFUSED by the extractor (extract.py / extract_bfv.py):
// see tests/tamper/README and make_tamper.sh, which records the traces committed under
// harness/frontend/tests/tamper/.
//
//   FHECHECK_TRACE_DIR=DIR OMP_NUM_THREADS=1 tamper_demo SCHEME MODE
//   SCHEME: bfv | bgv      MODE: one of the names below
//
//   honest      y = a*b + c, Decrypt(y)                                   (extracted; y is an output)
//   nocheck     y = a*b + c; y' = EvalMultNoCheck(y, 3) (untraced); Decrypt(y')
//   addnocheck  y = a*b + c; EvalAddInPlaceNoCheck(y, y) (untraced); Decrypt(y)
//   elements    y = a*b + c; y->GetElements()[0] += y->GetElements()[0]; Decrypt(y)
//   setlevel    y = a*b + c; y->SetLevel(y->GetLevel() + 1); Decrypt(y)
//   midmutate   x = a*b; x->GetElements()[0] += x->GetElements()[0]; y = x + c; Decrypt(y)
//   ptelement   p = MakePackedPlaintext; p->GetElement<DCRTPoly>() += itself; y = a*p; Decrypt(y)
//   ptother     p from a second context with another t; y = a*p (in the first context); Decrypt(y)
//   relinkey    EvalMultKeyGen, then SetBVector of the stored relinearization key (B doubled); y = a*b
//   setparam    after KeyGen and Encrypt: GetEncodingParams()->SetPlaintextModulus(t'); y = a*b
#include "openfhe.h"

#include <iostream>
#include <string>

using namespace lbcrypto;

template <typename P>
static CryptoContext<DCRTPoly> make(uint64_t t) {
    P params;
    params.SetMultiplicativeDepth(2);
    params.SetPlaintextModulus(t);
    params.SetRingDim(1024);
    params.SetSecurityLevel(HEStd_NotSet);
    params.SetKeySwitchTechnique(HYBRID);
    auto cc = GenCryptoContext(params);
    cc->Enable(PKE);
    cc->Enable(KEYSWITCH);
    cc->Enable(LEVELEDSHE);
    return cc;
}

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "usage: tamper_demo bfv|bgv MODE\n";
        return 2;
    }
    std::string scheme = argv[1], mode = argv[2];
    bool bfv           = scheme == "bfv";
    auto mk = [&](uint64_t t) { return bfv ? make<CCParams<CryptoContextBFVRNS>>(t) : make<CCParams<CryptoContextBGVRNS>>(t); };
    auto cc = mk(65537);
    auto kp = cc->KeyGen();
    cc->EvalMultKeyGen(kp.secretKey);
    std::vector<int64_t> va = {1, 2, 3, 4}, vb = {5, 6, 7, 8}, vc = {2, 2, 2, 2};
    auto pa = cc->MakePackedPlaintext(va), pb = cc->MakePackedPlaintext(vb), pc = cc->MakePackedPlaintext(vc);
    auto a = cc->Encrypt(kp.publicKey, pa), b = cc->Encrypt(kp.publicKey, pb), c = cc->Encrypt(kp.publicKey, pc);
    Ciphertext<DCRTPoly> y;
    if (mode == "honest" || mode == "nocheck" || mode == "addnocheck" || mode == "elements" || mode == "setlevel") {
        y = cc->EvalAdd(cc->EvalMult(a, b), c);
        if (mode == "nocheck")
            y = cc->EvalMultNoCheck(y, NativeInteger(3));
        else if (mode == "addnocheck")
            cc->EvalAddInPlaceNoCheck(y, y);
        else if (mode == "elements")
            y->GetElements()[0] += y->GetElements()[0];
        else if (mode == "setlevel")
            y->SetLevel(y->GetLevel() + 1);
    }
    else if (mode == "midmutate") {
        auto x = cc->EvalMult(a, b);
        x->GetElements()[0] += x->GetElements()[0];
        y = cc->EvalAdd(x, c);
    }
    else if (mode == "ptelement") {
        auto p = cc->MakePackedPlaintext(vb);
        p->GetElement<DCRTPoly>() += p->GetElement<DCRTPoly>();
        y = cc->EvalMult(a, p);
    }
    else if (mode == "ptother") {
        auto cc2 = mk(786433);
        auto p   = cc2->MakePackedPlaintext(vb);
        y        = cc->EvalMult(a, p);
    }
    else if (mode == "relinkey") {
        auto& keys = CryptoContextImpl<DCRTPoly>::GetEvalMultKeyVector(kp.secretKey->GetKeyTag());
        auto bv    = keys[0]->GetBVector();
        for (auto& e : bv)
            e += e;
        keys[0]->SetBVector(std::move(bv));
        y = cc->EvalMult(a, b);
    }
    else if (mode == "setparam") {
        cc->GetEncodingParams()->SetPlaintextModulus(786433);
        y = cc->EvalMult(a, b);
    }
    else {
        std::cerr << "unknown mode " << mode << "\n";
        return 2;
    }
    Plaintext out;
    try {
        cc->Decrypt(kp.secretKey, y, &out);
    }
    catch (const std::exception& e) {
        std::cerr << "Decrypt threw: " << e.what() << "\n";
    }
    std::cout << "ok " << scheme << " " << mode << "\n";
    return 0;
}
