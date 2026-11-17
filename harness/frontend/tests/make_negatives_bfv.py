#!/usr/bin/env python3
"""Writes tests/negative-bfv/*.json: small mutations of extracted OpenFHE BFV examples, each
exercising one path of fhe_check's BFV frontend handling (expected verdicts: tests/expected-bfv.tsv).
Run with `python3 -I`."""
import copy
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
EX = os.path.join(HERE, "..", "examples")
out = os.path.join(HERE, "negative-bfv")
os.makedirs(out, exist_ok=True)
# HPS + HYBRID, depth 1: ct_4 = mul ct_1 ct_2; ct_5 = relin ct_4 (inputs ct_1, ct_2, ct_3; 2 limbs)
base = json.load(open(os.path.join(EX, "openfhe_bfv_hps_hybrid_chain_d1.fhecheck.json")))
# HPS + HYBRID with plaintext operations: mul, relin, mulPlain, addPlain, subPlain
plain = json.load(open(os.path.join(EX, "openfhe_bfv_hps_hybrid_plain_d2.fhecheck.json")))


def w(name, doc):
    with open(os.path.join(out, name + ".json"), "w") as f:
        json.dump(doc, f, indent=1)
        f.write("\n")


def mut(f, src=base):
    d = copy.deepcopy(src)
    d.pop("provenance", None)
    d.pop("crossCheck", None)
    f(d)
    return d


def body(d, b, outputs):
    d["program"].update(body=b, outputs=outputs)


M = lambda d: d["bfv"]["multiplication"]  # noqa: E731

# the unmodified base, without provenance: certified
w("bfv_ok_hps_mul_relin", mut(lambda d: None))
# a technique name the format does not have
w("bfv_wrong_technique", mut(lambda d: M(d).update(technique="HPSQOVERP")))
# HPS without its auxiliary basis
w("bfv_missing_aux_basis", mut(lambda d: M(d).pop("auxBasis")))
# an auxiliary basis too small for the scaled tensor product (one prime instead of three)
w("bfv_aux_basis_too_small", mut(lambda d: M(d).update(auxBasis=M(d)["auxBasis"][:1])))
# an auxiliary prime equal to a ciphertext prime
w("bfv_aux_basis_not_coprime", mut(lambda d: M(d).update(auxBasis=[d["params"]["limbs"][0]["q"]] + M(d)["auxBasis"][1:])))
# no $.bfv object at all
w("bfv_missing_bfv_object", mut(lambda d: d.pop("bfv")))
# a composite ciphertext modulus
w("bfv_nonprime_limb", mut(lambda d: d["params"]["limbs"][1].update(q=str(int(d["params"]["limbs"][1]["q"]) * 3))))
# a plaintext (1 component) used as an operand of a ciphertext product
# (the declared-input path: without the freshEncryption section, which would refuse the shape
# before the check this file is for)
def pt_as_ct(d):
    d.pop("freshEncryption", None)
    d["program"]["inputs"][1].update(parts=1, bound="65536")
w("bfv_plaintext_as_ciphertext", mut(pt_as_ct))
# a ciphertext used as the plaintext operand of addPlain
def ct_as_pt(d):
    d["program"]["body"][3]["p"] = "ct_1"
w("bfv_ciphertext_as_plaintext", mut(ct_as_pt, plain))
# an output left under a rotated key (automorph without the key switch)
w("bfv_output_rotated_key", mut(lambda d: body(d, [{"op": "automorph", "dst": "r", "a": "ct_1", "g": 5}], ["r"])))
# the same with the key switch: certified
w("bfv_ok_rotation", mut(lambda d: body(d, [{"op": "automorph", "dst": "r", "a": "ct_1", "g": 5},
                                            {"op": "keySwitch", "dst": "y", "a": "r"}], ["y"])))
# modulus switching: declared as rounding (certified) and with a BGV method
MS = [{"op": "modSwitch", "dst": "y", "a": "ct_1"}]
w("bfv_ok_modswitch_round", mut(lambda d: body(d, copy.deepcopy(MS), ["y"])))
def ms_bgv(d):
    body(d, copy.deepcopy(MS), ["y"])
    d["modSwitch"] = {"method": "t-corrected-centred"}
w("bfv_modswitch_bgv_method", mut(ms_bgv))
# dropLimbs is not a BFV operation (Spec.TraceBFV)
w("bfv_droplimbs", mut(lambda d: body(d, [{"op": "dropLimbs", "dst": "y", "a": "ct_1", "k": 1}], ["y"])))
# the BGV decryption that switches the phase to one limb
w("bfv_decryption_switch_to_one_limb", mut(lambda d: d.update(decryption={"method": "switch-to-one-limb"})))
# duplicated names: two inputs with the same name; a destination that redefines an input
w("bfv_duplicate_input_name", mut(lambda d: d["program"]["inputs"][1].update(name="ct_1")))
# relinearizing a 2-component ciphertext
w("bfv_relin_two_parts", mut(lambda d: body(d, [{"op": "relin", "dst": "y", "a": "ct_1"}], ["y"])))
# an output that is still 3 components (no relinearization)
w("bfv_output_three_parts", mut(lambda d: body(d, d["program"]["body"][:1], ["ct_4"])))
# the frontend's expect disagrees with Source.step
w("bfv_expect_mismatch", mut(lambda d: d["program"]["body"][1].update(expect={"level": 1, "parts": 2})))
# noise overflow: three more squarings on two 60-bit limbs
def overflow(d):
    b = d["program"]["body"]
    cur = "ct_5"
    for i in range(3):
        b += [{"op": "square", "dst": f"s{i}_3", "a": cur}, {"op": "relin", "dst": f"s{i}", "a": f"s{i}_3"}]
        cur = f"s{i}"
    d["program"]["outputs"] = [cur]
w("bfv_noise_overflow", mut(overflow))
# an input ciphertext whose declared noise bound is already beyond what decrypts
def big_input(d):
    Q = 1
    for l in d["params"]["limbs"]:
        Q *= int(l["q"])
    d["program"]["inputs"][0]["bound"] = str(Q // (2 * d["params"]["t"]) + 1)
def big_input_declared(d):
    d.pop("freshEncryption", None)
    big_input(d)
w("bfv_input_bound_too_large", mut(big_input_declared))
# negative maxInternalDrop
w("bfv_negative_internal_drop", mut(lambda d: M(d).update(maxInternalDrop=-1)))
# plaintext operations, as OpenFHE performs them: bfv.plainAdd.method = "ceil"
w("bfv_plainadd_ceil", mut(lambda d: None, plain))
# ... declared "rounded" (NOT what OpenFHE does; shows the verdict the checker gives for that declaration)
w("bfv_plainadd_declared_rounded", mut(lambda d: d["bfv"]["plainAdd"].update(method="rounded"), plain))
# ... with no declaration of how plaintexts are added
w("bfv_plainadd_missing", mut(lambda d: d["bfv"].pop("plainAdd"), plain))
# ... with a method the format does not have
w("bfv_plainadd_unknown_method", mut(lambda d: d["bfv"]["plainAdd"].update(method="truncate"), plain))
# a plaintext bound above t - 1 is accepted as declared and makes the product larger (certified or not: see expected)
w("bfv_plain_bound_huge", mut(lambda d: [i.update(bound=str(2 ** 100)) for i in d["program"]["inputs"] if i["parts"] == 1], plain))
# an extraction error document
w("bfv_extraction_error", {"format": "fhe-check/v1", "error": "UNSUPPORTED: BV key switching with digit size 20 != 0 (base-2^w digits) is not mapped"})
# key switching declared with an unknown variant
w("bfv_unsupported_ks_variant", mut(lambda d: d["keySwitching"].update(variant="bv-base-w")))
# BV as extracted (no special prime, one limb per digit, centred): rotation only
bv = json.load(open(os.path.join(EX, "openfhe_bfv_hps_bv_chain_d1.fhecheck.json")))
w("bfv_ok_bv_rotation", mut(lambda d: body(d, [{"op": "automorph", "dst": "r", "a": "ct_1", "g": 5},
                                               {"op": "keySwitch", "dst": "y", "a": "r"}], ["y"]), bv))
# square under a P-over-Q technique (the extractor emits mul a a instead; the contract of `square` is not met)
pq = json.load(open(os.path.join(EX, "openfhe_bfv_hpspoverq_hybrid_chain_d2.fhecheck.json")))
def pq_square(d):
    for i in d["program"]["body"]:
        if i["op"] == "mul" and i["a"] == i.get("b") :
            i["op"] = "square"
            del i["b"]
w("bfv_square_under_poverq", mut(pq_square, pq))
# The leveled technique (HPSPOVERQLEVELED + BV, depth 2: mul, relin, mul, relin; the library drops
# one limb inside the second relinearization: internalDrops = [0, 0, 0, 1]).
lv = json.load(open(os.path.join(EX, "openfhe_bfv_hpspoverqleveled_bv_chain_d2.fhecheck.json")))
assert M(lv)["internalDrops"] == [0, 0, 0, 1] and [i["op"] for i in lv["program"]["body"]] == ["mul", "relin", "mul", "relin"]
# ... without its per-instruction internal drops (the two maxima alone are not enough)
w("bfv_leveled_missing_internal_drop", mut(lambda d: M(d).pop("internalDrops"), lv))
# ... with neither the drops nor the maxima
def no_drop(d):
    M(d).pop("internalDrops")
    M(d).pop("maxInternalDrop")
    M(d).pop("maxInternalDropKS")
w("bfv_leveled_missing_internal_drops_and_maxima", mut(no_drop, lv))
# ... with one entry too few / too many (one entry per instruction of the body)
w("bfv_leveled_internal_drops_too_short", mut(lambda d: M(d).update(internalDrops=M(d)["internalDrops"][:-1]), lv))
w("bfv_leveled_internal_drops_too_long", mut(lambda d: M(d).update(internalDrops=M(d)["internalDrops"] + [0]), lv))
# ... with a negative entry, and with a drop that is not below the number of limbs
w("bfv_leveled_internal_drops_negative", mut(lambda d: M(d).update(internalDrops=[0, 0, 0, -1]), lv))
w("bfv_leveled_internal_drop_all_limbs", mut(lambda d: M(d).update(internalDrops=[0, 0, 0, 3], maxInternalDrop=3), lv))
w("bfv_leveled_internal_drop_all_limbs_mul", mut(lambda d: M(d).update(internalDrops=[3, 0, 0, 0], maxInternalDrop=3), lv))
# ... with the maxima as the only declaration of the drops removed (the maxima are optional)
def no_maxima(d):
    M(d).pop("maxInternalDrop")
    M(d).pop("maxInternalDropKS")
w("bfv_ok_leveled_without_maxima", mut(no_maxima, lv))
# ... with a maximum BELOW a declared drop (the maxima are a cross-check of internalDrops)
w("bfv_leveled_max_internal_drop_inconsistent", mut(lambda d: M(d).update(maxInternalDrop=0), lv))
# ... the same for the key-switch maximum: a rotation with a declared drop of 1, maxInternalDropKS = 0
def rot_drop(d, mx):
    body(d, [{"op": "automorph", "dst": "r", "a": "ct_1", "g": 5}, {"op": "keySwitch", "dst": "y", "a": "r"}], ["y"])
    M(d).update(internalDrops=[0, 1], maxInternalDrop=0, maxInternalDropKS=mx)
w("bfv_leveled_max_internal_drop_ks_inconsistent", mut(lambda d: rot_drop(d, 0), lv))
# ... and consistent: a key switch (rotation) with an internal drop of 1 (ksLeveled with btgt = secretBound)
w("bfv_ok_leveled_rotation_drop1", mut(lambda d: rot_drop(d, 1), lv))
# ... a drop declared at an instruction that is not a mul, square, relin or keySwitch
def drop_at_add(d):
    body(d, [{"op": "add", "dst": "y", "a": "ct_1", "b": "ct_2"}], ["y"])
    M(d).update(internalDrops=[1], maxInternalDrop=1)
w("bfv_leveled_internal_drop_at_add", mut(drop_at_add, lv))
# ... a program with no mul, square, relin or keySwitch needs no internalDrops (all zero)
def add_only(d):
    body(d, [{"op": "add", "dst": "y", "a": "ct_1", "b": "ct_2"}], ["y"])
    no_drop(d)
w("bfv_ok_leveled_no_drops_needed", mut(add_only, lv))
# ... AN UNDERSTATED DROP: the file declares 0 where the traced run dropped 1 limb. fhe_check CANNOT
# detect this from the file: the drops are an input ASSUMPTION, and the budget of that relinearization
# is then ksBoundAt instead of ksLeveled (compare the bound with the example's). What establishes the
# drops is the extractor's three-way check (run.sh 9g: a trace tampered this way is refused).
w("bfv_leveled_understated_drop", mut(lambda d: M(d).update(internalDrops=[0, 0, 0, 0], maxInternalDrop=0), lv))
# internal drops declared under a technique that has none (HPS): refused; all zero: accepted
w("bfv_internal_drops_under_hps", mut(lambda d: M(d).update(internalDrops=[0, 1])))
w("bfv_ok_internal_drops_zero_under_hps", mut(lambda d: M(d).update(internalDrops=[0, 0])))
# Coverage that the hand-written SEAL-shaped files (bfv_seal_*, removed with SEAL) used to give,
# re-derived from OpenFHE v1.6.1 runs:
# ... a plaintext addition declared "delta" (the library adds floor(Q/t)*p; budget 0)
w("bfv_plainadd_delta", mut(lambda d: d["bfv"]["plainAdd"].update(method="delta"), plain))
# ... HPS with floatTolerant = false (the idealised exact algorithm; slacks PROVED, stepOK_mul_hps)
w("bfv_hps_idealised", mut(lambda d: M(d).update(floatTolerant=False)))
# ... HPSPOVERQLEVELED, floatTolerant = false, a drop of 1 inside the second RELINEARIZATION
# (`lv`: drops [0, 0, 0, 1]; the library drops nothing inside its multiplications). Until the
# per-instruction budget (2026-11-14) this file was NOT CERTIFIED (overflow 17.29 bits): the one
# budget charged the drop-1 multiplication slack to every product; it is now a legitimate positive
# (the key switch with its drop, Challenge.BFVMul.stepOK_relin_leveled_tol, and P-over-Q products).
w("bfv_ok_leveled_relin_drop1_idealised", mut(lambda d: M(d).update(floatTolerant=False), lv))
# ... what that file was for, a MULTIPLICATION with an internal drop under the idealised
# leveled algorithm (Challenge.BFVMul.stepOK_mul_leveled), on real OpenFHE runs of the default
# context (levelbfv/inputs; chain of depth 3, the library drops one limb inside body[4]):
# CERTIFIED with parameters generated for depth 4, NOT CERTIFIED at OpenFHE's own depth-3 ones
# (the overflow is at body[4], the product with the drop)
LB0 = os.path.join(HERE, "..", "levelbfv", "inputs")
w("bfv_ok_leveled_mul_drop1_idealised", mut(lambda d: M(d).update(floatTolerant=False),
  json.load(open(os.path.join(LB0, "default_bv_t16_chain_d3_x1.fhecheck.json")))))
w("bfv_leveled_mul_drop1_idealised_overflow", mut(lambda d: M(d).update(floatTolerant=False),
  json.load(open(os.path.join(LB0, "default_bv_t16_chain_d3_x0.fhecheck.json")))))
# ... the textbook technique on a squaring chain (mul, relin, square, relin)
hbv2 = json.load(open(os.path.join(EX, "openfhe_bfv_hps_bv_chain_d2.fhecheck.json")))
def textbook(d):
    d["bfv"]["multiplication"] = {"technique": "textbook", "source": "test: the exact BFV product (no RNS approximation)"}
w("bfv_textbook_squarings", mut(textbook, hbv2))
# ... the same with two more squarings (square, relin, square, relin appended): the noise overflows
def textbook_more(d):
    textbook(d)
    b = d["program"]["body"]
    last, n = "ct_7", 8
    for _ in range(2):
        b.append({"op": "square", "dst": "ct_%d" % n, "a": last, "expect": {"level": 3, "parts": 3}})
        b.append({"op": "relin", "dst": "ct_%d" % (n + 1), "a": "ct_%d" % n, "expect": {"level": 3, "parts": 2}})
        last, n = "ct_%d" % (n + 1), n + 2
    d["program"]["outputs"] = [last]
w("bfv_textbook_squarings_overflow", mut(textbook_more, hbv2))
# The library's floating-point decryption (OpenFHE ScaleAndRound(t), HPS family, full-limb output;
# outside its proved margin): real OpenFHE runs of the per-instruction
# measurement (levelbfv/inputs), default context, chain of depth 1.
LB = os.path.join(HERE, "..", "levelbfv", "inputs")
# ... t = 1125899915231233 (about 2^50), 5 limbs: the worst-case magnitude 2k(t-1) + ... exceeds
# 2^53 (outside the precision condition of the proved decryption statement): the certificate is withheld
w("bfv_libdecrypt_t50_5limbs", mut(lambda d: None, json.load(open(os.path.join(LB, "default_bv_t50_chain_d1_x2.fhecheck.json")))))
# ... the same t at 3 limbs: within the condition with less than one bit to spare (a NOTE, certified)
w("bfv_libdecrypt_t50_3limbs_note", mut(lambda d: None, json.load(open(os.path.join(LB, "default_bv_t50_chain_d1_x0.fhecheck.json")))))
# ... t = 1099512938497 (about 2^40), 5 limbs: unaffected
w("bfv_libdecrypt_t40_5limbs", mut(lambda d: None, json.load(open(os.path.join(LB, "default_bv_t40_chain_d1_x3.fhecheck.json")))))
# A nonzero internal drop declared at a multiplication BELOW the top level (the library drops limbs
# only at the top level; Challenge.CertifyBFV.stepChecks rejects it): INVALID INPUT
lvc = json.load(open(os.path.join(EX, "openfhe_bfv_hpspoverqleveled_hybrid_compress_d3.fhecheck.json")))
def drop_below_top(d):
    ops = [i["op"] for i in d["program"]["body"]]
    k = [j for j, o in enumerate(ops) if o == "mul"][-1]   # the product after Compress (level 2 of 3)
    ds = [0] * len(ops); ds[k] = 1
    M(d).update(internalDrops=ds, maxInternalDrop=1)
w("bfv_leveled_internal_drop_below_top", mut(drop_below_top, lvc))
# BEHZ below the top level (Spec.DecryptBFVLib): OpenFHE's low-limb decryption reads m_qlInvModq,
# which is empty under BEHZ, so 1 < level < L is UNSUPPORTED; at one limb the loop does not run and
# the routine is proved (Challenge.BFVDecryptLib.outputLibOK?): CERTIFIED
behz3 = json.load(open(os.path.join(EX, "openfhe_bfv_behz_bv_chain_d2.fhecheck.json")))  # 3 limbs
w("bfv_behz_modswitch_level2", mut(lambda d: body(d, [{"op": "modSwitch", "dst": "y", "a": "ct_1"}], ["y"]), behz3))
w("bfv_ok_behz_modswitch_level1", mut(lambda d: body(d, [{"op": "modSwitch", "dst": "y1", "a": "ct_1"},
                                                         {"op": "modSwitch", "dst": "y", "a": "y1"}], ["y"]), behz3))
# a 61-bit special prime (Challenge.Word.ksWordOK?): outside the word-arithmetic model of the
# proof (Barrett constant, NTT tables); UNSUPPORTED for an OpenFHE file. 2305843009211662337 is
# the largest prime below 2^61 that is 1 mod 2^15 (= 2N).
w("bfv_word_modulus_61bit", mut(lambda d: d["params"]["special"][0].update(q="2305843009211662337")))
