// dump.cpp -- UNTRUSTED. Calls the real DCRTPoly::SwitchCRTBasis and DCRTPoly::ScaleAndRound of
// OpenFHE v1.6.1 with the library's own precomputed tables, and writes inputs, outputs and the
// double tables (as hexadecimal bit patterns) as JSON on stdout, for check.py to compare with the
// model of Challenge/BFVMul/Float.lean evaluated in Python.
//
//   dump <HPS|HPSPOVERQ|HPSPOVERQLEVELED> <ringDim> <depth> <qbits> <seed>
//
// Build: see run.sh (links the OpenFHE installed by harness/frontend/openfhe/build_openfhe.sh).
#include "openfhe.h"
#include <cstring>
#include <iostream>
#include <random>

using namespace lbcrypto;

static std::string hexd(double d) {
    uint64_t u;
    std::memcpy(&u, &d, 8);
    char buf[32];
    snprintf(buf, sizeof buf, "\"%016llx\"", (unsigned long long)u);
    return buf;
}
static void jd(const char* name, const std::vector<double>& v, bool comma = true) {
    std::cout << "\"" << name << "\": [";
    for (size_t i = 0; i < v.size(); i++) std::cout << (i ? "," : "") << hexd(v[i]);
    std::cout << "]" << (comma ? ",\n" : "\n");
}
static void jmods(const char* name, const std::shared_ptr<ILDCRTParams<BigInteger>>& p) {
    std::cout << "\"" << name << "\": [";
    for (size_t i = 0; i < p->GetParams().size(); i++)
        std::cout << (i ? "," : "") << p->GetParams()[i]->GetModulus();
    std::cout << "],\n";
}
static void jpoly(const char* name, const DCRTPoly& x, bool comma = true) {
    std::cout << "\"" << name << "\": [";
    for (size_t i = 0; i < x.GetNumOfElements(); i++) {
        std::cout << (i ? ",[" : "[");
        const auto& e = x.GetElementAtIndex(i);
        for (size_t j = 0; j < e.GetLength(); j++) std::cout << (j ? "," : "") << e[j];
        std::cout << "]";
    }
    std::cout << "]" << (comma ? ",\n" : "\n");
}
// A polynomial in coefficient format over `p`: extreme residues first, then uniform ones.
static DCRTPoly mk(const std::shared_ptr<ILDCRTParams<BigInteger>>& p, std::mt19937_64& g) {
    std::vector<NativePoly> v;
    for (const auto& pi : p->GetParams()) {
        NativePoly e(pi, Format::COEFFICIENT, true);
        uint64_t q = pi->GetModulus().ConvertToInt();
        uint64_t sp[] = {0, 1, q - 1, q - 2, q / 2, q / 2 + 1, q / 3, (uint64_t)1 << 53, ((uint64_t)1 << 53) + 1};
        for (size_t j = 0; j < e.GetLength(); j++) {
            uint64_t a = g();
            // rows 0..8: the same extreme value in every limb; rows 9..63: an extreme value per limb
            uint64_t val = j < 9 ? sp[j] % q : (j < 64 ? sp[a % 9] % q : a % q);
            e[j] = NativeInteger(val);
        }
        v.push_back(std::move(e));
    }
    return DCRTPoly(v);
}

int main(int argc, char** argv) {
    if (argc < 6) return 2;
    std::string tech = argv[1];
    CCParams<CryptoContextBFVRNS> P;
    P.SetPlaintextModulus(65537);
    P.SetMultiplicativeDepth(atoi(argv[3]));
    P.SetScalingModSize(atoi(argv[4]));
    P.SetSecurityLevel(HEStd_NotSet);
    P.SetRingDim(atoi(argv[2]));
    P.SetMultiplicationTechnique(tech == "HPS" ? HPS : tech == "HPSPOVERQ" ? HPSPOVERQ : HPSPOVERQLEVELED);
    auto cc = GenCryptoContext(P);
    cc->Enable(PKE);
    cc->Enable(LEVELEDSHE);
    auto cp = std::dynamic_pointer_cast<CryptoParametersBFVRNS>(cc->GetCryptoParameters());
    std::mt19937_64 g(atoll(argv[5]));
    auto pQ = cp->GetElementParams();
    size_t k = pQ->GetParams().size();
    std::cout << "{\"tech\": \"" << tech << "\", \"t\": 65537,\n";
    jmods("Q", pQ);
    jd("qInv", cp->GetqInv());
    jd("rInv", cp->GetrInv());
    if (tech == "HPS") {
        auto pR = cp->GetParamsRl();
        auto pQR = cp->GetParamsQlRl();
        jmods("R", pR);
        jd("fracQ", cp->GettRSHatInvModsDivsFrac());      // scaling by t/Q into R
        // SwitchCRTBasis Q -> R
        DCRTPoly x = mk(pQ, g);
        DCRTPoly y = x.SwitchCRTBasis(pR, cp->GetQlHatInvModq(), cp->GetQlHatInvModqPrecon(), cp->GetQlHatModr(),
                                      cp->GetalphaQlModr(), cp->GetModrBarrettMu(), cp->GetqInv());
        jpoly("sw_in", x);
        jpoly("sw_out", y);
        // ScaleAndRound QR -> R
        DCRTPoly z = mk(pQR, g);
        DCRTPoly w = z.ScaleAndRound(pR, cp->GettRSHatInvModsDivsModr(), cp->GettRSHatInvModsDivsFrac(),
                                     cp->GetModrBarrettMu());
        jpoly("sr_in", z);
        jpoly("sr_out", w);
        // SwitchCRTBasis R -> Q
        DCRTPoly x2 = mk(pR, g);
        DCRTPoly y2 = x2.SwitchCRTBasis(pQ, cp->GetRlHatInvModr(), cp->GetRlHatInvModrPrecon(), cp->GetRlHatModq(),
                                        cp->GetalphaRlModq(), cp->GetModqBarrettMu(), cp->GetrInv());
        jpoly("swb_in", x2);
        jpoly("swb_out", y2, false);
    }
    else {
        size_t l = k - 1;
        auto pR = cp->GetParamsRl(l);
        auto pQR = cp->GetParamsQlRl(l);
        jmods("R", pR);
        jd("fracR", cp->GettQlSlHatInvModsDivsFrac(l));    // scaling by t/P into Q
        // SwitchCRTBasis Q -> R (operand 1)
        DCRTPoly x = mk(pQ, g);
        DCRTPoly y = x.SwitchCRTBasis(pR, cp->GetQlHatInvModq(l), cp->GetQlHatInvModqPrecon(l), cp->GetQlHatModr(l),
                                      cp->GetalphaQlModr(l), cp->GetModrBarrettMu(), cp->GetqInv());
        jpoly("sw_in", x);
        jpoly("sw_out", y);
        // ScaleAndRound QR -> Q (limbs of Q first, then R: the layout ExpandCRTBasis produces)
        DCRTPoly z = mk(pQR, g);
        DCRTPoly w = z.ScaleAndRound(cp->GetParamsQl(l), cp->GettQlSlHatInvModsDivsModq(l),
                                     cp->GettQlSlHatInvModsDivsFrac(l), cp->GetModqBarrettMu());
        jpoly("sr_in", z);
        jpoly("sr_out", w);
        if (tech == "HPSPOVERQLEVELED" && k >= 2) {
            // internal drop of one limb: ScaleAndRound Q -> Q_{k-1}
            size_t l1 = k - 2;
            jd("fracDrop", cp->GetQlQHatInvModqDivqFrac(l1));
            DCRTPoly z1 = mk(pQ, g);
            DCRTPoly w1 = z1.ScaleAndRound(cp->GetParamsQl(l1), cp->GetQlQHatInvModqDivqModq(l1),
                                           cp->GetQlQHatInvModqDivqFrac(l1), cp->GetModqBarrettMu());
            jpoly("drop_in", z1);
            jpoly("drop_out", w1);
        }
        std::cout << "\"end\": 0\n";
    }
    std::cout << "}\n";
    return 0;
}
