#!/usr/bin/env python3
"""Writes tests/negative/*.json: small mutations of the OpenFHE depth-2 example (and two hand-made
programs), each exercising one rejection path of fhe_check. Run with `python3 -I`."""
import copy
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
base = json.load(open(os.path.join(HERE, "..", "examples", "openfhe_depth2_fixedmanual.fhecheck.json")))
out = os.path.join(HERE, "negative")


def w(name, doc):
    with open(os.path.join(out, name + ".json"), "w") as f:
        if isinstance(doc, str):
            f.write(doc)
        else:
            json.dump(doc, f, indent=1)
            f.write("\n")


def mut(f):
    d = copy.deepcopy(base)
    f(d)
    return d


# composite ciphertext modulus: 35156991246337 * 3 is not prime
w("composite_modulus", mut(lambda d: d["params"]["limbs"][1].update(q=str(35144106147841 * 3))))
# a special prime equal to a ciphertext prime (SpecialOK: coprime to every q)
w("special_not_coprime", mut(lambda d: d["params"]["special"][0].update(q=d["params"]["limbs"][0]["q"])))
# two equal primes
w("duplicate_prime", mut(lambda d: d["params"]["limbs"][2].update(q=d["params"]["limbs"][0]["q"])))
# t shares a factor with a prime: t = q_0
w("t_not_coprime", mut(lambda d: d["params"].update(t=int(d["params"]["limbs"][0]["q"]))))
# inputNoise below t/2 (msgRange)
w("input_noise_below_t_half", mut(lambda d: d["params"].update(inputNoise="1000")))
# N not a power of two
w("n_not_pow2", mut(lambda d: d["params"].update(N=12288)))
# input declared above the chain (3 limbs)
w("bad_level", mut(lambda d: d["program"]["inputs"][0].update(level=4)))
# operand never defined
w("undefined_operand", mut(lambda d: d["program"]["body"][0].update(b="nope")))
OK_BODY = [{"op": "add", "dst": "s", "a": "ct_1", "b": "ct_2"}, {"op": "mulConst", "dst": "y", "a": "s", "c": "-3"}]


def ok(f=lambda d: None):
    def g(d):
        d["program"].update(body=copy.deepcopy(OK_BODY), outputs=["y"])
        d.pop("provenance", None)
        f(d)
    return mut(g)


# output never defined
w("undefined_output", ok(lambda d: d["program"].update(outputs=["ghost"])))
# relin of a 2-part ciphertext
w("relin_two_parts", mut(lambda d: d["program"]["body"].insert(2, {"op": "relin", "dst": "x", "a": "ct_5"})))
# modulus switch of the unrelinearized product
w("modswitch_three_parts", mut(lambda d: d["program"].update(
    body=[{"op": "mul", "dst": "p", "a": "ct_1", "b": "ct_2"}, {"op": "modSwitch", "dst": "q", "a": "p"}],
    outputs=["q"])))
# unsupported ops
w("unsupported_rescale", mut(lambda d: d["program"]["body"].append({"op": "rescale", "dst": "z", "a": "ct_8"})))
w("unsupported_unknown_op", mut(lambda d: d["program"]["body"].append({"op": "bootstrap", "dst": "z", "a": "ct_8"})))
w("unsupported_scheme_ckks", mut(lambda d: d["params"].update(scheme="CKKS")))
w("unsupported_modswitch_method", mut(lambda d: d["modSwitch"].update(method="t-corrected-canonical")))
w("unsupported_ks_variant", mut(lambda d: d["keySwitching"].update(variant="lattigo-exact")))
# the frontend's expect disagrees with Source.step
w("expect_mismatch", ok(lambda d: d["program"]["body"][1].update(expect={"level": 2, "parts": 2})))
# digits that do not partition the level
w("bad_digits", mut(lambda d: d["keySwitching"].update(digits={"kind": "explicit", "perLevel": {"1": [[0]], "2": [[0, 1]], "3": [[0, 1]]}})))
# noise overflow in a two-op program: one add of two inputs is fine, squaring twice is not
w("noise_overflow", mut(lambda d: d["program"].update(
    body=[{"op": "square", "dst": "a", "a": "ct_1"}, {"op": "square", "dst": "b", "a": "a"}], outputs=["b"])))
# a small accepted program: (a + b) * 3, no key switching
w("ok_add_mulconst", ok())
# plaintext operations and dropLimbs: (a*p + q) with declared plaintext bounds t-1, then drop a limb
PLAIN = [{"op": "mulPlain", "dst": "u", "a": "ct_1", "p": "pt"}, {"op": "addPlain", "dst": "v", "a": "u", "p": "pt"},
         {"op": "subPlain", "dst": "w", "a": "v", "p": "pt"}, {"op": "dropLimbs", "dst": "y", "a": "w", "k": 1}]


def plain(f=lambda d: None):
    def g(d):
        d["program"]["inputs"].append({"name": "pt", "parts": 1, "level": 3, "bound": "65536"})
        # the plaintext's scaling factor (FIXEDMANUAL: 1), so that user-level decryption is covered
        d["scaling"]["inputFactors"].append({"name": "pt", "factor": 1})
        d["program"].update(body=copy.deepcopy(PLAIN), outputs=["y"])
        d.pop("provenance", None)
        f(d)
    return mut(g)


w("ok_plain_ops", plain())
# a modulus switch of the plaintext operand (1 part): charged msBudgetOne = ceil(t/2), certified
def plain_ms(d):
    d["program"]["body"] = [{"op": "modSwitch", "dst": "c1", "a": "ct_1"}, {"op": "modSwitch", "dst": "p1", "a": "pt"},
                            {"op": "mulPlain", "dst": "y", "a": "c1", "p": "p1"}]
w("ok_plain_modswitch", plain(plain_ms))
# decryption: an unknown method; and an output whose bound fits Q/2 at its level (3 limbs) while the
# phase switched to one limb does not fit q0/2 (the window is t/q0 wide: c * inputNoise just below Q/2)
w("unsupported_decryption_method", ok(lambda d: d["decryption"].update(method="round-then-guess")))
def dec_over(d):
    Q = 1
    for l in d["params"]["limbs"]:
        Q *= int(l["q"])
    c = (Q // 2 - 1) // int(d["params"]["inputNoise"])
    d["program"].update(body=[{"op": "mulConst", "dst": "y", "a": "ct_1", "c": str(c)}], outputs=["y"])
    d.pop("provenance", None)
w("decrypt_switch_overflow", mut(dec_over))
def dec_over_textbook(d):
    dec_over(d)
    d["decryption"] = {"method": "at-output-level"}
w("decrypt_textbook_ok", mut(dec_over_textbook))
# --kappa: an input that is neither a fresh encryption nor a bounded plaintext
w("kappa_input_not_fresh", ok(lambda d: d["freshEncryption"].update(inputs=["ct_1"])))
# the plaintext declared with two components
w("plain_two_parts", plain(lambda d: d["program"]["inputs"][-1].update(parts=2)))
# dropping every limb
w("droplimbs_all", plain(lambda d: d["program"]["body"][3].update(k=3)))
# A finding on the small sample parameters (Spec.FullParams.exampleBGV31, Challenge/Budget.lean):
# two 30-bit primes, one 30-bit special prime. One limb per digit gives ksBudget ~ 2^35 and a
# certified mul+relin (bound 2^56 + 34787976413); a single two-limb digit gives a budget above Q.
def example_bgv31(alpha):
    return {"format": "fhe-check/v1", "source": {"tool": "hand-written (Spec.FullParams.exampleBGV31)"},
            "params": {"scheme": "BGV", "N": 16384, "t": 65537, "limbs": ["1073872897", "1074266113"],
                       "special": ["1077477377"], "secretBound": 1, "inputNoise": str(2 ** 21),
                       "keyNoise": str(2 ** 21)},
            "keySwitching": {"method": "hybrid", "variant": "centred",
                             "digits": {"kind": "consecutive", "towersPerDigit": alpha}},
            "modSwitch": {"method": "t-corrected-centred"},
            "program": {"inputs": [{"name": "a", "parts": 2, "level": 2}, {"name": "b", "parts": 2, "level": 2}],
                        "body": [{"op": "mul", "dst": "c", "a": "a", "b": "b"}, {"op": "relin", "dst": "c", "a": "c"}],
                        "outputs": ["c"]}}


for name, alpha in (("one_limb_digits", 1), ("two_limb_digit", 2)):
    with open(os.path.join(HERE, "..", "examples", f"exampleBGV31_{name}.fhecheck.json"), "w") as f:
        json.dump(example_bgv31(alpha), f, indent=1)
        f.write("\n")
# security note (log2(Q*P) against the HomomorphicEncryption.org table; never part of the verdict):
# the certified (a + b) * 3 at N = 8192 (the primes are = 1 mod 2^15, so also = 1 mod 2*8192):
# log2(Q*P) = 255 > 218, the 128-bit cap at 2^13; and at the toy N = 512 (no row in the table)
w("security_above_cap", ok(lambda d: d["params"].update(N=8192)))
w("security_toy_n", ok(lambda d: d["params"].update(N=512)))
# the depth-2 example at N = 8192: NOT CERTIFIED, and its uniform "+k bits" fix at this N exceeds the
# 128-bit cap, so the fix at 2N = 16384 is computed (the file has freshEncryption)
w("security_fix_above_cap", mut(lambda d: d["params"].update(N=8192)))
# Not generated here: negative/security_openfhe_flexibleautoext_chain_depth6.json, OpenFHE's default
# FLEXIBLEAUTOEXT at depth 6 (N = 2^14; its +7-bit fix gives log2(Q*P) = 460.32 > 438), made by
#   bgv_demo run DIR --scal FLEXIBLEAUTOEXT --depth 6 --prog chain
#   python3 -I openfhe/extract.py --params DIR/params.json --trace DIR/trace.jsonl \
#     --artifact openfhe_flexibleautoext_chain_depth6
# the l2 description of fresh encryptions (--kappa K --l2; Challenge.FreshNoiseL2): test values only,
# as an extractor might supply them: sub-Gaussian proxy 11 >= sigma^2 = 3.19^2 for the Gaussian e1, e2
# (an ASSUMPTION: Micciancio-Peikert), 1 for ternary u, and ||e_pk||_2^2 <= 11*N (an ASSUMPTION
# about the key); the secret's S2 is left to the tool (N * 1^2)
def l2(d, **kw):
    N = d["params"]["N"]
    d["freshEncryption"]["l2"] = dict({"keyErrorSq": str(11 * N), "uProxy": 1, "e1Proxy": 11, "e2Proxy": 11,
                                       "source": "test values (assumed): proxies 11 >= 3.19^2, 1 for ternary; ||e_pk||_2^2 <= 11*N"}, **kw)
w("l2_supplied", mut(lambda d: l2(d)))
w("l2_malformed", mut(lambda d: l2(d, e1Proxy="eleven")))
# the declared bound of the STORED plaintext polynomial (freshEncryption.plaintextBound; the fresh
# noise of `fhe_check --kappa` is Bp + t*eps): the depth-2 example with Bp = 2^33 keeps its
# certificate with a smaller margin, with Bp = 2^34 it loses it (the example itself declares t - 1)
w("fresh_plaintext_bound_2p33", mut(lambda d: d["freshEncryption"].update(plaintextBound=2 ** 33)))
w("fresh_plaintext_bound_2p34", mut(lambda d: d["freshEncryption"].update(plaintextBound=2 ** 34)))
# the declared bound on the sampler means (freshEncryption.mean = num/den): a zero denominator
w("fresh_mean_den_zero", mut(lambda d: d["freshEncryption"]["mean"].update(den=0)))
# a non-centred modulus-switching method declared by a program WITHOUT any modulus switch (the
# certified (a + b) * 3): refused all the same (Challenge.Certify.certify?_centred)
w("unsupported_modswitch_method_no_switch", ok(lambda d: d["modSwitch"].update(method="t-corrected-canonical")))
# explicit per-level digit tables on the depth-2 example (3 limbs). Top-level digits {0,1},{2}: the
# lower levels are their cuts ({0,1}; {0}), the layout restricts from the top level. Top-level
# digits {0},{1,2} with the single digit {0,1} at level 2 (the cut would be {0},{1}): it does not.
w("explicit_digits_restrict", mut(lambda d: d["keySwitching"].update(
    digits={"kind": "explicit", "perLevel": {"1": [[0]], "2": [[0, 1]], "3": [[0, 1], [2]]}})))
w("unsupported_digits_not_restricting", mut(lambda d: d["keySwitching"].update(
    digits={"kind": "explicit", "perLevel": {"1": [[0]], "2": [[0, 1]], "3": [[0], [1, 2]]}})))
# an even special modulus (twice special[0]: still coprime to the chain, to t and to special[1]) on
# the certified (a + b) * 3, which never key-switches: Spec.Budget.specialOK? requires odd
w("special_even", ok(lambda d: d["params"]["special"][0].update(q=str(2 * int(d["params"]["special"][0]["q"])))))
# key noise against the restriction of top-level key-switching keys (Spec.Certify.keysRestrict?:
# 2*floor(keyNoise/t)*t < q0*P), on the certified (a + b) * 3: the smallest keyNoise that fails
# it (k*t with k the smallest integer with 2*k*t >= q0*P), and that value minus one
def key_noise(delta):
    def g(d):
        P = 1
        for s in d["params"]["special"]:
            P *= int(s["q"])
        q0P, t = int(d["params"]["limbs"][0]["q"]) * P, d["params"]["t"]
        d["params"]["keyNoise"] = str((q0P + 2 * t - 1) // (2 * t) * t - delta)
    return ok(g)
w("key_noise_not_restricting", key_noise(0))
w("ok_key_noise_restricting_boundary", key_noise(1))
# malformed inputs
w("malformed_json", '{"format": "fhe-check/v1", "params": {')
w("malformed_bigint", mut(lambda d: d["params"].update(inputNoise="12e5")))
w("malformed_missing_field", mut(lambda d: d["params"].pop("keyNoise")))
w("format_v0", mut(lambda d: d.update(format="fhe-check/v0")))
w("extraction_error", {"format": "fhe-check/v1", "error": "line 7: unknown OpenFHE call"})


# machine words (Challenge.Word.ksWordOK?): checked for source.tool = "openfhe"
def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d, r = d // 2, r + 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
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


def primes_below(top, step, count, avoid):
    found, q = [], (top - 1) // step * step + 1
    while len(found) < count:
        if is_prime(q) and q not in avoid:
            found.append(q)
        q -= step
    return found


# a 61-bit ciphertext prime (= 1 mod 2N), as v1.6.1's FIXEDAUTO parameter generation produces
# (the machine-word side condition): UNSUPPORTED for an OpenFHE file
q61 = primes_below(2 ** 61, 2 * base["params"]["N"], 1, set())[0]
assert q61 >= 2 ** 60
w("word_modulus_61bit", mut(lambda d: d["params"]["limbs"][2].update(q=str(q61))))
# the same file from another frontend: not refused by the OpenFHE word check
w("word_modulus_61bit_not_openfhe",
  mut(lambda d: (d["params"]["limbs"][2].update(q=str(q61)), d["source"].update(tool="hand-written"))))
# 300 ciphertext primes of 60 bits: the 128-bit sums of ApproxSwitchCRTBasis are outside Challenge.Word.ksWordOK? (the proved bound)
special = {int(s["q"]) for s in base["params"]["special"]}
qs300 = primes_below(2 ** 60, 2 * base["params"]["N"], 300, special)
w("word_ks_accumulator", mut(lambda d: d["params"].update(limbs=[{"q": str(q), "psi": "0"} for q in qs300])))


# the BGV packed-encoding window t - 1 <= floor(q0/2) (item E1, the BGV side of the BFV packed-encoding window)
def t_above(d):
    q0 = int(d["params"]["limbs"][0]["q"])
    t = q0 // 2 + 2
    while not is_prime(t):
        t += 1
    d["params"].update(t=t, inputNoise=str(t * 10 ** 6))


w("word_t_above_q0_half", mut(t_above))


# A declared input bound above params.inputNoise. BGV analyses every input at min(declared bound,
# inputNoise) (Spec.InputsOK), so the theorem's hypothesis on such an input is inputNoise, not the
# declared bound: fhe_check refuses (UNSUPPORTED). At exactly inputNoise it is certified.
def input_bound(delta):
    return ok(lambda d: d["program"]["inputs"][0].update(bound=str(int(d["params"]["inputNoise"]) + delta)))


w("ok_input_bound_at_input_noise", input_bound(0))
w("input_bound_above_input_noise", input_bound(1))
# the same for a plaintext operand
w("plain_bound_above_input_noise", plain(lambda d: d["program"]["inputs"][-1].update(bound=str(2 * int(d["params"]["inputNoise"])))))
