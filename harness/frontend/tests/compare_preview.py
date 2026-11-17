#!/usr/bin/env python3
"""Compare fhe_check's verdicts with the untrusted Python preview (preview_check.py) on every
example and negative test. The formulas coincide (same refAnalyze rules, same budget formulas:
Spec.Budget.ksBoundAt maximised over the levels the program key-switches at, which equals
ksBudget's maximum over all levels on these examples; ceil(t(1+N*Bs)/2)); every verdict difference must be listed in
KNOWN with its explanation, or this script fails. Usage: compare_preview.py FHE_CHECK FILE..."""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PREVIEW = os.path.join(HERE, "..", "preview_check.py")

# name -> (fhe_check verdict, preview verdict, why they differ)
KNOWN = {
    "composite_modulus": ("NOT CERTIFIED", "CERTIFIED-or-reject",
        "the preview reports ParamsOK clauses separately and runs the noise analysis anyway; fhe_check refuses on schemeParamsOK? first"),
    "special_not_coprime": ("NOT CERTIFIED", "CERTIFIED-or-reject", "the preview does not check SpecialOK (special primes coprime to the chain and t)"),
    "duplicate_prime": ("NOT CERTIFIED", "CERTIFIED-or-reject", "same: distinctness is only reported by the preview"),
    "t_not_coprime": ("NOT CERTIFIED", "CERTIFIED-or-reject", "same: coprimality is only reported by the preview"),
    "input_noise_below_t_half": ("NOT CERTIFIED", "CERTIFIED-or-reject", "same: msgRange is only reported by the preview"),
    "n_not_pow2": ("NOT CERTIFIED", "CERTIFIED-or-reject", "same: N_pow2 is only reported by the preview"),
    "bad_level": ("NOT CERTIFIED", "CERTIFIED-or-reject",
        "the preview does not check input declarations (Source.Decl.ok); fhe_check (refAnalyze) does"),
    "undefined_output": ("NOT CERTIFIED", "crash", "the preview raises KeyError on an undefined output"),
    "modswitch_three_parts": ("CERTIFIED", "NOT CERTIFIED", "fhe_check certifies a 3-part modSwitch at msBudgetAt P 3 (Challenge.Budget.modSwitch_realizable_parts); the untrusted preview has no budget for it and rejects"),
    "input_bound_above_input_noise": ("UNSUPPORTED", "CERTIFIED", "the preview analyses the input at min(declared bound, inputNoise), as the locked analysis does; fhe_check refuses a declared bound above inputNoise because the theorem's hypothesis is then inputNoise, not the declared bound"),
    "plain_bound_above_input_noise": ("UNSUPPORTED", "CERTIFIED", "same, for a plaintext operand"),
    "unsupported_rescale": ("UNSUPPORTED", "NOT CERTIFIED", "both refuse; the preview reports unknown ops as a reject"),
    "unsupported_unknown_op": ("UNSUPPORTED", "NOT CERTIFIED", "both refuse; the preview reports unknown ops as a reject"),
    "unsupported_scheme_ckks": ("UNSUPPORTED", "CERTIFIED-or-reject", "the preview does not read params.scheme"),
    "unsupported_modswitch_method": ("UNSUPPORTED", "CERTIFIED-or-reject", "the preview ignores modSwitch.method (always uses the centred budget)"),
    "unsupported_decryption_method": ("UNSUPPORTED", "CERTIFIED-or-reject", "the preview treats an unknown decryption method as at-output-level"),
    "unsupported_ks_variant": ("UNSUPPORTED", "CERTIFIED-or-reject", "the preview treats an unknown variant as canonical"),
    "bad_digits": ("INVALID INPUT", "crash", "the preview reads only consecutive digits and raises on explicit ones"),
    "undefined_operand": ("NOT CERTIFIED", "crash", "the preview raises KeyError on an undefined operand; fhe_check reports it via Source.step"),
    "malformed_json": ("INVALID INPUT", "crash", "the preview raises on malformed JSON"),
    "malformed_bigint": ("INVALID INPUT", "crash", "the preview raises on a non-decimal big integer"),
    "malformed_missing_field": ("INVALID INPUT", "crash", "the preview raises on a missing field"),
    "format_v0": ("INVALID INPUT", "CERTIFIED-or-reject", "the preview does not check the format tag"),
    "extraction_error": ("INVALID INPUT", "extraction-failed", "same meaning, different words"),
    "word_ks_accumulator": ("UNSUPPORTED", "CERTIFIED", "the preview does not model OpenFHE's machine words (Challenge.Word.ksWordOK?)"),
    "word_modulus_61bit": ("UNSUPPORTED", "CERTIFIED", "the preview does not model OpenFHE's machine words (Challenge.Word.ksWordOK?)"),
    "word_t_above_q0_half": ("UNSUPPORTED", "NOT CERTIFIED", "both refuse; fhe_check first on OpenFHE's packed-encoding window t - 1 <= floor(q0/2)"),
    # user-level decryption policy: an OpenFHE-extracted input whose user-level decryption is not
    # covered is NOT CERTIFIED; the preview checks the phase only
    "decrypt_textbook_ok": ("NOT CERTIFIED", "CERTIFIED", "textbook decryption declared: user-level decryption (certify?_user, switched decryption) not covered, withheld for an OpenFHE input; the preview checks the phase only"),
    "scaling_factor_mismatch": ("NOT CERTIFIED", "CERTIFIED", "Spec.Scaling.scaleOK? fails: user-level decryption not covered, withheld for an OpenFHE input; the preview checks the phase only"),
    "scaling_unmarked_adjustment": ("NOT CERTIFIED", "CERTIFIED", "same (scaleOK? fails)"),
    "scaling_zero_factor": ("NOT CERTIFIED", "CERTIFIED", "same (scaleOK? fails)"),
    "expect_mismatch": ("NOT CERTIFIED", "NOT CERTIFIED", ""),
    "unsupported_modswitch_method_no_switch": ("UNSUPPORTED", "CERTIFIED-or-reject", "the preview ignores modSwitch.method (always uses the centred budget)"),
    "explicit_digits_restrict": ("NOT CERTIFIED", "crash", "the preview reads only consecutive digits and raises on explicit ones"),
    "unsupported_digits_not_restricting": ("UNSUPPORTED", "crash", "the preview reads only consecutive digits and raises on explicit ones"),
    "special_even": ("NOT CERTIFIED", "CERTIFIED-or-reject", "the preview does not check SpecialOK (special primes odd, coprime to the chain and t)"),
    "key_noise_not_restricting": ("NOT CERTIFIED", "CERTIFIED-or-reject", "the preview does not check Spec.Certify.keysRestrict? (key noise against q0*P)"),
    "fresh_mean_den_zero": ("INVALID INPUT", "CERTIFIED-or-reject", "the preview does not read freshEncryption"),
    "l2_malformed": ("INVALID INPUT", "CERTIFIED-or-reject", "the preview does not read freshEncryption.l2"),
}


def preview(path):
    """(verdict, figures): figures = output log2 bounds (accept) or the failing step's log2 bound."""
    r = subprocess.run([sys.executable, "-I", PREVIEW, path], capture_output=True, text=True)
    if r.returncode != 0:
        return "crash", None
    d = json.loads(r.stdout)
    n = d.get("noise", d)
    v = {"accept": "CERTIFIED", "reject": "NOT CERTIFIED"}.get(n["verdict"], n["verdict"])
    if n["verdict"] == "accept":
        return v, [o["log2B"] for o in n["outputs"]]
    steps = n.get("steps") or []
    return v, ([steps[-1]["log2B"]] if steps and steps[-1]["marginBits"] < 0 else None)


def figures(rep):
    if rep["verdict"] == "CERTIFIED":
        return [o["boundLog2"] for o in rep["outputs"]]
    f = (rep.get("failure") or {}).get("firstFailing")
    return [f["boundLog2"]] if f and f.get("overflowBits") is not None else None


def main():
    exe, files = sys.argv[1], sys.argv[2:]
    bad = 0
    for f in files:
        name = os.path.basename(f).replace(".fhecheck.json", "").replace(".json", "")
        r = subprocess.run([exe, "--json", f], capture_output=True, text=True)
        rep = json.loads(r.stdout)
        fv = rep["verdict"]
        pv, pfig = preview(f)
        if fv == pv:
            ffig = figures(rep)
            if pfig is not None and ffig is not None:
                if [round(x, 2) for x in pfig] != [round(x, 2) for x in ffig]:
                    print(f"MISMATCH  {name}: log2 bounds fhe_check {ffig}, preview {pfig}")
                    bad += 1
                    continue
                print(f"agree     {name}: {fv}, log2 bounds {ffig}")
            else:
                print(f"agree     {name}: {fv}")
            continue
        k = KNOWN.get(name)
        if k and k[0] == fv and (k[1] == pv or (k[1] == "CERTIFIED-or-reject" and pv in ("CERTIFIED", "NOT CERTIFIED"))):
            print(f"known     {name}: fhe_check {fv}, preview {pv}: {k[2]}")
        else:
            print(f"MISMATCH  {name}: fhe_check {fv}, preview {pv}")
            bad += 1
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
