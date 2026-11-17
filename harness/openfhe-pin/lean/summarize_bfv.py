#!/usr/bin/env python3
"""UNTRUSTED. Markdown statistics of the BFV result lines of openfhe_pin.

  summarize_bfv.py RESULTS.jsonl [MORE.jsonl ...]

Tables: (1) per-check counts, split into checks DECIDED AGAINST A TRUSTED DEFINITION (the literal
definition, or a mirror proved sound or equal: FHE/Pin/BFV/Sound.lean, Keys.lean, FHE/Pin/Force.lean)
and checks that are MIRRORED ONLY (a formula on the data with no trusted counterpart, or glue);
(2) tightness: bits of slack log2(bound / measured) per operation kind and technique, for the
noise bound (`f.bound`) and for every contract number (`e.step`), with the multiplication
contract against the charged, the textbook and the idealised budget; (3) the verdict table;
(4) decryption: how close to a rounding boundary the library's Decrypt still agrees with exact
rounding."""
import collections
import json
import statistics
import sys

# Checks whose verdict is not a decision of a trusted definition.
MIRRORED = {
    "c.predict": "library model of Encrypt (no trusted BFV encryption definition)",
    "c.support": "sampler supports (declared bounds 1 / 39)",
    "c.stored": "encoder convention",
    "d.pubkey": "b + a*s = e (no trusted BFV public-key predicate)",
    "d.limbs": "bookkeeping", "b.shape": "bookkeeping", "load": "loader", "load.params": "loader",
    "load.prog": "loader", "load.secret": "loader", "load.declared": "declarations against the dump",
    "load.layout": "loader", "x.refusal": "refusal classification", "info.build": "information",
    "f.certified-consistent": "consistency of the lines of one case",
}
TRUSTED = {
    "a.decrypt": "Spec.Scheme.bfvDecrypt (literal; forced = decryptBFVA_spec) vs OpenFHE's Decrypt",
    "c.fresh": "Spec.Scheme.BFVEncrypts (literal; forced = inputCtOKb_sound)",
    "c.input": "Spec.Correct.Encrypts / Spec.TraceBFV.PlainOK (literal; forced = inputOKb_sound)",
    "c.inputs": "Spec.TraceBFV.InputsOK (conjunction of c.input)",
    "d.key": "Spec.Budget.GadgetKeysOK (literal; forced = BFV.gadgetKeysCheck_sound)",
    "e.step": "Spec.TraceBFV.StepOK (stepOKb_sound) at Challenge.CertifyBFV.budgetBFV",
    "f.bound": "noise of BFVEncrypts (noiseA_spec) vs Challenge.BFV.refBoundBFV",
    "f.decok": "Challenge.BFV.decOK of the measured noise",
    "f.refAnalyze": "Challenge.BFV.refAnalyzeBFV = the per-variable replay",
    "f.budget": "Challenge.CertifyBFV.budgetBFV = the certificate's budget",
    "f.verdict": "Challenge.CertifyBFV.certifyBFV? (information)",
    "b.msg": "Spec.Source.step (stepA_spec) vs Spec.Scheme.bfvDecrypt",
    "b.raw": "Spec.Source.step vs OpenFHE's Decrypt", "b.output": "Spec.Source.eval vs OpenFHE's Decrypt",
    "b.eval": "Spec.Source.eval (literal)", "b.step": "Spec.Source.step", "b.outputs": "Spec.Source.eval",
    "b.decls": "Spec.Source.Decl.ok",
}


def stats(xs):
    xs = sorted(xs)
    if not xs:
        return "-", "-", "-"
    return f"{xs[0]:.2f}", f"{statistics.median(xs):.2f}", f"{xs[-1]:.2f}"


def table(title, header, rows):
    print(f"\n### {title}\n")
    print("| " + " | ".join(header) + " |")
    print("|" + "|".join("---" for _ in header) + "|")
    for r in rows:
        print("| " + " | ".join(str(x) for x in r) + " |")


def main():
    rows = []
    for p in sys.argv[1:]:
        for l in open(p):
            if l.strip():
                d = json.loads(l)
                if d.get("scheme") == "BFV":
                    rows.append(d)
    cases = sorted(set(d["case"] for d in rows))
    print(f"# openfhe_pin, BFV: {len(cases)} cases, {len(rows)} lines")
    ns = collections.Counter()
    seen = set()
    for d in rows:
        if d["case"] not in seen:
            seen.add(d["case"])
            ns[(d.get("N"), d.get("mult"), d.get("ks"))] += 1
    table("Cases", ["N", "technique", "key switching", "cases"], [(*k, v) for k, v in sorted(ns.items(), key=str)])

    # 1. per-check counts
    per = collections.defaultdict(lambda: [0, 0, 0])
    for d in rows:
        c = d["check"]
        mirrored = c in MIRRORED or d.get("mirroredOnly") or c.endswith(".error") or \
            (c == "d.key" and d.get("ok") is None)
        if c.endswith("literal-vs-forced"):
            cls, key = "T", (c, "literal+forced")
        elif mirrored:
            cls, key = "M", (c + (" (composite modSwitch)" if d.get("composite") else ""), d.get("impl"))
        else:
            cls, key = "T", (c + (" (synthetic operand or result)" if c == "e.step" and (d.get("synthetic") or d.get("operandSynthetic")) else ""), d.get("impl"))
        ok = d.get("ok")
        per[(cls, *key)][0 if ok is True else 1 if ok is False else 2] += 1
    for cls, name in (("T", "decided against a TRUSTED definition (literal, or a mirror proved sound / equal)"),
                      ("M", "MIRRORED ONLY (no trusted counterpart, or glue)")):
        rs = [(k[1], k[2], v[0], v[1], v[2],
               (TRUSTED if cls == "T" else MIRRORED).get(k[1].split(" (")[0], "literal and forced modes agree" if "literal-vs" in k[1] else ""))
              for k, v in sorted(per.items()) if k[0] == cls]
        tot = [sum(r[i] for r in rs) for i in (2, 3, 4)]
        table(f"Checks {name}", ["check", "impl", "ok", "FAIL", "null", "what"],
              rs + [("**total**", "", *tot, "")])

    # 2. tightness
    fb = collections.defaultdict(list)
    for d in rows:
        if d["check"] == "f.bound" and d.get("ok") is True and d.get("slackBits") is not None and not d.get("tainted"):
            fb[(d["op"], d["mult"])].append(d["slackBits"])
    table("Noise bound: bits of slack log2(refBoundBFV / measured noise), per operation kind and technique "
          "(lines with ok = true, analyzer accepts up to there)",
          ["op", "technique", "n", "min", "median", "max"],
          [(k[0], k[1], len(v), *stats(v)) for k, v in sorted(fb.items())])
    fbd = collections.defaultdict(list)
    for d in rows:
        if d["check"] == "f.bound" and d.get("ok") is True and d.get("slackBits") is not None and not d.get("tainted") \
                and d.get("op") != "plaintext":
            fbd[(d.get("depth", 0), d["mult"])].append(d["slackBits"])
    table("Noise bound by multiplicative depth", ["depth", "technique", "n", "min", "median", "max"],
          [(k[0], k[1], len(v), *stats(v)) for k, v in sorted(fbd.items())])
    es = collections.defaultdict(list)
    for d in rows:
        if d["check"] == "e.step" and d.get("ok") is True and d.get("slackBits") is not None and d["op"] not in ("mul", "square"):
            es[(d["op"], d["mult"] if d["op"] not in ("relin", "keySwitch") else d["mult"] + " / " + d["ks"]
                + (f" / drop {d['levelsDropped']}" if d.get("levelsDropped") else ""))].append(d["slackBits"])
    table("Step contracts other than the product: bits of slack log2(budget / measured)",
          ["op", "technique", "n", "min", "median", "max"],
          [(k[0], k[1], len(v), *stats(v)) for k, v in sorted(es.items())])
    ksl = collections.defaultdict(list)
    for d in rows:
        if d["check"] == "e.step" and d.get("ok") is True and d["op"] in ("relin", "keySwitch") and d.get("slackBitsAtLevel") is not None:
            ksl[(d["op"], d["ks"], bool(d.get("levelsDropped")))].append(d["slackBitsAtLevel"])
    table("Key switching against Spec.BudgetBFV.ksBoundAt at the operand's level (negative: above it, "
          "as after an internal drop of HPSPOVERQLEVELED, which the budget covers by ksLeveled)",
          ["op", "key switching", "internal drop", "n", "min", "median", "max"],
          [(*k, len(v), *stats(v)) for k, v in sorted(ksl.items())])
    mu = collections.defaultdict(lambda: collections.defaultdict(list))
    for d in rows:
        if d["check"] == "e.step" and d.get("ok") is not None and d["op"] in ("mul", "square") and "roundMeasured" in d:
            k = (d["op"], d["mult"] + (f" / drop {d['levelsDropped']}" if d.get("levelsDropped") else ""), d.get("N"))
            for f in ("liftSlackBits", "liftSlackBitsTextbook", "roundSlackBits", "roundSlackBitsTextbook", "roundSlackBitsIdealised"):
                if d.get(f) is not None:
                    mu[k][f].append(d[f])
            mu[k]["liftMeasured"].append(int(d["liftMeasured"]))
            mu[k]["liftBound"].append(int(d["liftBound"]))
            mu[k]["roundMeasured"].append(int(d["roundMeasured"]))
    rs = []
    for k, v in sorted(mu.items(), key=str):
        rs.append((*k, len(v["roundMeasured"]), max(v["liftMeasured"]), min(v["liftBound"]),
                   "/".join(stats(v["liftSlackBits"])), max(v["roundMeasured"]),
                   "/".join(stats(v["roundSlackBits"])), "/".join(stats(v["roundSlackBitsTextbook"])),
                   "/".join(stats(v["roundSlackBitsIdealised"]))))
    table("The multiplication contract (witness k := (Ψ − Φ)/Q): lift ‖k‖ against E.mulLift, rounding ⌈2‖D‖/Q⌉ "
          "against E.mulRound (charged), the textbook value and the idealised (floatTol = false) value; "
          "bits of slack min/median/max (negative: the measured value is ABOVE that budget)",
          ["op", "technique", "N", "n", "max ‖k‖", "E.mulLift", "lift slack", "max ⌈2‖D‖/Q⌉", "slack vs charged",
           "slack vs textbook", "slack vs idealised"], rs)
    fr = collections.defaultdict(list)
    for d in rows:
        if d["check"] == "c.fresh" and d.get("impl") == "forced" and d.get("slackBits") is not None and d.get("ok") is True:
            fr[(d["enc"], d.get("declared"))].append(d["slackBits"])
    table("Fresh ciphertexts: bits of slack log2(input bound / measured noise)",
          ["encryption", "bound declared by a program", "n", "min", "median", "max"],
          [(*k, len(v), *stats(v)) for k, v in sorted(fr.items(), key=str)])

    # 3. verdicts
    vt = collections.defaultdict(lambda: [0, 0, [], 0])
    viol = []
    for d in rows:
        if d["check"] == "f.verdict":
            k = (d["mult"], d["ks"], ",".join(d.get("assumed", [])) or "-") if d.get("certified") else (d["mult"], d["ks"], "")
            v = vt[k]
            if d.get("certified"):
                v[0] += 1
                v[2] += [o["marginBits"] for o in d.get("outputs", []) if o.get("marginBits") is not None]
                if d.get("stepFailures", 0) + d.get("boundFailures", 0) + d.get("inputFailures", 0) > 0:
                    v[3] += 1
                    viol.append((d["case"], d.get("stepFailures"), d.get("boundFailures"), d.get("inputFailures")))
            else:
                v[1] += 1
    table("Verdicts of Challenge.CertifyBFV.certifyBFV? (margin: log2(largest noise decOK accepts / bound), per output)",
          ["technique", "key switching", "assumed", "CERTIFIED", "NOT CERTIFIED", "margin bits min/median/max",
           "CERTIFIED with a violation"],
          [(k[0], k[1], k[2] or "(not certified)", v[0], v[1], "/".join(stats(v[2])), v[3]) for k, v in sorted(vt.items())])
    if viol:
        print("\nCERTIFIED programs with a violated step contract / noise above the bound / input outside its bound:")
        for c, a, b, i in viol:
            print(f"* `{c}`: {a} step, {b} bound, {i} input")
    rz = collections.Counter()
    for d in rows:
        if d["check"] == "f.verdict" and not d.get("certified"):
            for r in d.get("reasons", []):
                rz[r.split(" at body")[0]] += 1
    if rz:
        table("Why NOT CERTIFIED", ["reason", "programs"], sorted(rz.items()))
    rf = collections.Counter(d.get("class") for d in rows if d["check"] == "x.refusal")
    if rf:
        table("Extractor refusals (x.refusal)", ["class", "cases"], sorted(rf.items(), key=str))

    # 4. decryption
    ad = [d for d in rows if d["check"] == "a.decrypt" and d.get("impl") == "forced" and "mismatches" in d]
    mism = [d for d in ad if d["mismatches"] > 0]
    agree_min = min((d["tieDistMin"] for d in ad if d["mismatches"] == 0 and d.get("tieDistMin") is not None), default=None)
    print(f"\n### Decryption\n\n{len(ad)} ciphertexts decrypted by OpenFHE; trusted `bfvDecrypt` = OpenFHE's `Decrypt` on "
          f"{len(ad) - len(mism)}; they differ on {len(mism)} "
          f"({sum(1 for d in mism if d.get('ok') is False)} failing, {sum(1 for d in mism if d.get('ok') is None)} null).")
    if agree_min is not None:
        print(f"Smallest distance of t·Φ/Q from a rounding boundary at which the two still agree on every coefficient: {agree_min:.3g}.")
    if mism:
        mx = max(d["tieDistMismatchMax"] for d in mism if d.get("tieDistMismatchMax") is not None)
        print(f"Largest distance from a rounding boundary of a coefficient on which they differ: {mx:.3g} "
              f"(the library's rounding error is at least that).")
        by = collections.Counter((d["mult"], d.get("noiseFor"), d.get("ok")) for d in mism)
        table("Differing decryptions", ["technique", "noise measured for", "verdict", "ciphertexts"],
              [(*k, v) for k, v in sorted(by.items(), key=str)])
    fails = collections.Counter((d["check"], d.get("op")) for d in rows if d.get("ok") is False)
    if fails:
        table("FAILING lines", ["check", "op", "lines"], [(*k, v) for k, v in sorted(fails.items(), key=str)])


if __name__ == "__main__":
    main()
