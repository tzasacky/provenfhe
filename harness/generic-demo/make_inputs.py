#!/usr/bin/env python3
"""Write the hand-written fhe-check/v1 inputs of the generic demo (no library involved).

Every number below is chosen here, from textbook conventions, not read from any library:
NTT-friendly primes found by a deterministic Miller-Rabin search, an error bound B_e = 19
(6 sigma for sigma = 3.2, a common textbook choice; DECLARED, not derived), a ternary secret.
The inputs are deterministic: running this script twice writes the same files.

    python3 -I harness/generic-demo/make_inputs.py [OUTDIR]   # default OUTDIR: inputs/ here
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "inputs")
os.makedirs(OUT, exist_ok=True)


def is_prime(n):
    """Deterministic Miller-Rabin for n < 3.3e24 (bases: the first 13 primes)."""
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    for p in small:
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def ntt_primes(bits, N, count, exclude=()):
    """The `count` largest primes below 2^bits with q = 1 (mod 2N), descending."""
    m = 2 * N
    q = ((1 << bits) - 1) // m * m + 1
    out = []
    while len(out) < count:
        if q not in exclude and is_prime(q):
            out.append(q)
        q -= m
    return out


def odd_primes(bits, count, exclude=()):
    """The `count` largest primes below 2^bits (any residue), descending."""
    q = (1 << bits) - 1
    out = []
    while len(out) < count:
        if q not in exclude and is_prime(q):
            out.append(q)
        q -= 2
    return out


def dump(name, obj):
    with open(os.path.join(OUT, name), "w") as f:
        json.dump(obj, f, indent=1)
        f.write("\n")


BE = 19  # declared error bound (6 sigma, sigma = 3.2); an ASSUMPTION of the certificate

# ---------------------------------------------------------------------------------------------
# 1. BGV, textbook parameters, uniform digit layout, centred representatives.
N_BGV, T_BGV = 16384, 65537
bgv_q0 = ntt_primes(60, N_BGV, 1)
bgv_qs = ntt_primes(50, N_BGV, 3, exclude=bgv_q0)
bgv_special = ntt_primes(61, N_BGV, 1, exclude=bgv_q0 + bgv_qs)
# Fresh public-key encryption (b*u + t*e1 + m, a*u + t*e2), m lifted to [0, t), every error
# within BE and u ternary: centred phase <= (t-1) + t*BE*(2N+1) (the formula of
# Challenge.FreshNoise at Bp = t-1, Bk = B1 = B2 = BE, Bu = Bs = 1).
bgv_input_noise = (T_BGV - 1) + T_BGV * BE * (2 * N_BGV + 1)


def bgv_file(body, outputs, note):
    return {
        "format": "fhe-check/v1",
        "source": {"tool": "hand-written (harness/generic-demo/make_inputs.py)", "note": note},
        "params": {
            "scheme": "BGV",
            "N": N_BGV,
            "t": T_BGV,
            "limbs": [str(q) for q in bgv_q0 + bgv_qs],
            "special": [str(q) for q in bgv_special],
            "secretBound": 1,
            "inputNoise": str(bgv_input_noise),
            "keyNoise": str(T_BGV * BE),
        },
        "noiseDerivation": {
            "errorBound": BE,
            "errorBoundSource": "DECLARED textbook bound 6*sigma, sigma = 3.2 (no library)",
            "inputNoiseFormula": "(t-1) + t*Be*(2N+1): textbook LSB-form BGV public-key encryption",
            "keyNoiseFormula": "t*Be: key-switching keys b = -a*s' + t*e + g*target",
        },
        "keySwitching": {
            "method": "hybrid",
            "variant": "centred",
            "digits": {"kind": "consecutive", "towersPerDigit": 1},
        },
        "modSwitch": {"method": "t-corrected-centred"},
        "program": {
            "inputs": [
                {"name": "a", "parts": 2, "level": 4, "key": 1},
                {"name": "b", "parts": 2, "level": 4, "key": 1},
                {"name": "c", "parts": 2, "level": 4, "key": 1},
                {"name": "p", "parts": 1, "level": 2},
            ],
            "body": body,
            "outputs": outputs,
        },
    }


bgv_body = [
    {"op": "mul", "dst": "x", "a": "a", "b": "b"},
    {"op": "relin", "dst": "x", "a": "x"},
    {"op": "modSwitch", "dst": "x", "a": "x"},
    {"op": "automorph", "dst": "y", "a": "x", "g": 5},
    {"op": "keySwitch", "dst": "y", "a": "y"},
    {"op": "add", "dst": "z", "a": "x", "b": "y"},
    {"op": "dropLimbs", "dst": "c1", "a": "c", "k": 1},
    {"op": "mul", "dst": "w", "a": "z", "b": "c1"},
    {"op": "relin", "dst": "w", "a": "w"},
    {"op": "modSwitch", "dst": "w", "a": "w"},
    {"op": "mulPlain", "dst": "out", "a": "w", "p": "p"},
]
dump("bgv_textbook_chain.fhecheck.json",
     bgv_file(bgv_body, ["out"], "(a*b + rot5(a*b)) * c * p, two multiplicative levels"))

# The same chain asked for two more products than its moduli pay for: NOT CERTIFIED.
bgv_deep = bgv_body[:-1] + [
    {"op": "mul", "dst": "v", "a": "w", "b": "w"},
    {"op": "relin", "dst": "v", "a": "v"},
    {"op": "mul", "dst": "out", "a": "v", "b": "v"},
    {"op": "relin", "dst": "out", "a": "out"},
]
dump("bgv_textbook_chain_too_deep.fhecheck.json",
     bgv_file(bgv_deep, ["out"], "the chain above with two further squarings and no modulus left to switch"))

# ---------------------------------------------------------------------------------------------
# 2. BFV with BEHZ multiplication (integer-only RNS; Bajard-Eynard-Hasan-Zucca 2016).
N_BFV, T_BFV = 8192, 65537
bfv_qs = ntt_primes(50, N_BFV, 3)
bfv_special = ntt_primes(55, N_BFV, 1, exclude=bfv_qs)
behz_B = odd_primes(52, 4, exclude=bfv_qs + bfv_special)
behz_msk = odd_primes(53, 1, exclude=bfv_qs + bfv_special + behz_B)[0]
# BFV fresh encryption error e*u + e1 + e2*s with every error within BE: <= BE*(2N+1); plus
# the rounding of Delta*m vs Q*m/t, at most t - 1 for m in [0, t). DECLARED.
bfv_input_noise = BE * (2 * N_BFV + 1) + (T_BFV - 1)
dump("bfv_behz.fhecheck.json", {
    "format": "fhe-check/v1",
    "source": {"tool": "hand-written (harness/generic-demo/make_inputs.py)",
               "note": "(a*b + rot5(a*b)) + p, then two modulus switches; BEHZ multiplication"},
    "params": {
        "scheme": "BFV",
        "N": N_BFV,
        "t": T_BFV,
        "limbs": [str(q) for q in bfv_qs],
        "special": [str(q) for q in bfv_special],
        "secretBound": 1,
        "inputNoise": str(bfv_input_noise),
        "keyNoise": BE,
    },
    # HYBRID key switching (special primes) with CANONICAL representatives: the BFV certificate
    # requires the declared layout to be the one the library's key switch uses
    # (`Challenge.RealizeBFV.ksDeclOK?`: canonical with special primes; one limb per digit without).
    "keySwitching": {"method": "hybrid", "variant": "canonical",
                     "digits": {"kind": "consecutive", "towersPerDigit": 1}},
    "modSwitch": {"method": "round"},
    "bfv": {
        "multiplication": {"technique": "BEHZ", "auxBasis": [str(b) for b in behz_B],
                           "mSk": str(behz_msk), "mTilde": "65536",
                           "source": "hand-written: BEHZ with base B (4 primes), m_sk, m~ = 2^16"},
        "plainAdd": {"method": "delta", "source": "hand-written: textbook floor(Q/t)*p"},
    },
    "program": {
        "inputs": [
            {"name": "a", "parts": 2, "level": 3, "key": 1},
            {"name": "b", "parts": 2, "level": 3, "key": 1},
            {"name": "p", "parts": 1, "level": 3},
        ],
        "body": [
            {"op": "mul", "dst": "x", "a": "a", "b": "b"},
            {"op": "relin", "dst": "x", "a": "x"},
            {"op": "automorph", "dst": "y", "a": "x", "g": 5},
            {"op": "keySwitch", "dst": "y", "a": "y"},
            {"op": "add", "dst": "z", "a": "x", "b": "y"},
            {"op": "addPlain", "dst": "z", "a": "z", "p": "p"},
            # two modulus switches, so the output has ONE limb: the library's BEHZ decryption is
            # proved at the full chain and at one limb; between them OpenFHE reads a table that is
            # empty under BEHZ (fhe_check answers UNSUPPORTED there)
            {"op": "modSwitch", "dst": "w", "a": "z"},
            {"op": "modSwitch", "dst": "out", "a": "w"},
        ],
        "outputs": ["out"],
    },
})

# ---------------------------------------------------------------------------------------------
# 3. BFV BEHZ at the locked tiny parameters (Challenge.BFV.tinyBFV, Challenge.CertifyBFV.behzTech,
#    program mulProg): the tool's bound must equal the locked #guard of Challenge/CertifyBFV.lean,
#    `summary (certifyBFV? (tinyIn mulProg (some behzTech) true)) == some (109100936, ...)`.
dump("bfv_tiny_behz_guard.fhecheck.json", {
    "format": "fhe-check/v1",
    "source": {"tool": "hand-written (Challenge.CertifyBFV.tinyIn mulProg behzTech)"},
    "params": {"scheme": "BFV", "N": 4, "t": 17, "limbs": ["65537", "786433"], "special": [],
               "secretBound": 1, "inputNoise": "64", "keyNoise": 64},
    # no special primes: BV key switching, one limb per digit (what `ksDeclOK?` requires there; the
    # representatives flag is not read without special primes)
    "keySwitching": {"method": "hybrid", "variant": "centred",
                     "digits": {"kind": "consecutive", "towersPerDigit": 1}},
    "modSwitch": {"method": "round"},
    "bfv": {"multiplication": {"technique": "BEHZ", "auxBasis": ["1000003", "1000033"],
                               "mSk": "1000037", "mTilde": "65536", "source": "behzTech"}},
    "program": {
        "inputs": [{"name": "a", "parts": 2, "level": 2}, {"name": "b", "parts": 2, "level": 2}],
        "body": [{"op": "mul", "dst": "c", "a": "a", "b": "b"},
                 {"op": "relin", "dst": "c", "a": "c"}],
        "outputs": ["c"],
    },
})
