#!/usr/bin/env python3
"""Machine-readable counts of one conformance run (UNTRUSTED statistics; no verdict is decided here).

    counts.py TMPDIR > counts.json

TMPDIR is the working directory of harness/openfhe-pin/run.sh (difftest.sh): results.jsonl (BGV),
bfv.jsonl, summary.json and bfv-summary.json (written by verdict.py / verdict_bfv.py). run.sh calls
this at the end and, with COUNTS_JSON=<path>, copies the result there; harness/openfhe-pin/counts.sh
regenerates the committed copy harness/openfhe-pin/results/difftest-counts.json.

Every `ok` below was computed by the Lean checker (openfhe_pin); this script only counts lines.

  bgv.perCheck / bfv.perCheck      ok / fail / null lines per check name (e.g. a.switched, d.key,
                                   e.step), exactly the verdict scripts' perCheck
  bgv.algo.comparisons             the gate line's "algo: N operations": comparison executions, one
                                   per (recorded operation, execution mode)
  bgv.algo.limbs / coeffs          limbs / coefficients of those comparisons (every mode)
  bgv.algo.byCheck[c]              per check: comparisons, distinct recorded operations (distinct
                                   (case, id)), and comparisons per execution mode (`impl`)
  bfv.certified...                 programs that pass certifyBFV? (f.verdict certified), split by ring
                                   dimension and by what the certificate records (`assumed`); NOT the
                                   tool's printed verdict (fhe_check additionally needs the library
                                   decryption check)
  bfv.runLibrary                   algo.runLibrary: programs executed through the locked
                                   Challenge.CertifyBFV.runLibrary (ok true), with instructions,
                                   ciphertexts and coefficients compared, and the programs that were
                                   not executed, by reason and ring dimension
  bfv.idealMul                     the `exact (Fl.exactSums)` variant of algo.variant.mul: coefficients
                                   on which the idealised (exact) multiplication differs from the
                                   library's output, over the coefficients compared
"""
import collections
import json
import os
import sys


def lines(path):
    if not os.path.exists(path):
        return
    with open(path) as f:
        for l in f:
            l = l.strip()
            if l:
                yield json.loads(l)


def algo_counts(rows):
    by = collections.defaultdict(lambda: {"comparisons": 0, "limbs": 0, "coeffs": 0, "ops": set(),
                                          "byImpl": collections.Counter(), "differing": 0})
    for d in rows:
        c = d.get("check", "")
        if (not c.startswith("algo.") or c.startswith("algo.variant") or c.startswith("algo.runLibrary")
                or c in ("algo.coverage", "algo.info")):
            continue
        if d.get("ok") is not True and d.get("ok") is not False:
            continue
        b = by[c]
        b["comparisons"] += 1
        b["limbs"] += d.get("limbs", 0)
        b["coeffs"] += d.get("coeffs", 0)
        b["ops"].add((d.get("case"), d.get("id")))
        b["byImpl"][d.get("impl", "?")] += 1
        b["differing"] += d.get("ok") is False
    return {c: {"comparisons": b["comparisons"], "distinctOperations": len(b["ops"]), "limbs": b["limbs"],
                "coeffs": b["coeffs"], "differing": b["differing"], "byImpl": dict(sorted(b["byImpl"].items()))}
            for c, b in sorted(by.items())}


def main():
    tmp = sys.argv[1]
    out = {"format": "openfhe-pin-counts/v1", "source": "harness/openfhe-pin/difftest.sh (run.sh GATE=1)"}
    for scheme, res, summ in (("bgv", "results.jsonl", "summary.json"), ("bfv", "bfv.jsonl", "bfv-summary.json")):
        s = json.load(open(os.path.join(tmp, summ))) if os.path.exists(os.path.join(tmp, summ)) else {}
        rows = list(lines(os.path.join(tmp, res)))
        if scheme == "bfv":
            rows = [d for d in rows if d.get("scheme") == "BFV"]
        o = {k: s[k] for k in ("cases", "lines", "ok", "fail", "null", "programs", "refused") if k in s}
        o["perCheck"] = s.get("perCheck", {})
        ac = algo_counts(rows)
        cmp_ = {c: v for c, v in ac.items() if c != "algo.layout"}  # layout: a glue equality, not a ciphertext
        o["algo"] = {"comparisons": sum(v["comparisons"] for v in cmp_.values()),
                     "distinctOperations": sum(v["distinctOperations"] for v in cmp_.values()),
                     "limbs": sum(v["limbs"] for v in cmp_.values()),
                     "coeffs": sum(v["coeffs"] for v in cmp_.values()),
                     "differing": sum(v["differing"] for v in cmp_.values()),
                     "byCheck": ac}
        if scheme == "bgv":
            o["algo"]["gateLine"] = {"ops": s.get("algoOps"), "limbs": s.get("algoLimbs"), "coeffs": s.get("algoCoeffs")}
        cases_n = {}
        for d in rows:
            if d.get("case") is not None and d.get("N") is not None:
                cases_n[d["case"]] = d["N"]
        o["casesByN"] = dict(sorted(collections.Counter(cases_n.values()).items()))
        if scheme == "bfv":
            ver = {d["case"]: d for d in rows if d.get("check") == "f.verdict"}
            cert = [c for c, d in ver.items() if d.get("certified")]
            byn = collections.Counter(cases_n.get(c) for c in cert)
            by_asm = collections.Counter(",".join(ver[c].get("assumed", [])) or "none" for c in cert)
            ideal = [c for c in cert if "idealised" in ver[c].get("assumed", [])]
            o["certified"] = len(cert)
            o["notCertified"] = len(ver) - len(cert)
            o["certifiedByN"] = {str(k): v for k, v in sorted(byn.items())}
            o["certifiedByAssumed"] = dict(sorted(by_asm.items()))
            o["certifiedIdealised"] = len(ideal)
            o["certifiedIdealisedByN"] = {str(k): v for k, v in sorted(collections.Counter(cases_n.get(c) for c in ideal).items())}
            rl = [d for d in rows if d.get("check") == "algo.runLibrary"]
            ran = [d for d in rl if d.get("ok") is True]
            bad = [d for d in rl if d.get("ok") is False]
            why = collections.Counter()
            for d in rl:
                if d.get("ok") is None:
                    w = d.get("why", "")
                    k = ("not certified" if "not certified" in w else
                         "N above the literal limit" if "-max-n" in w else
                         "no program" if "no program" in w else w[:60])
                    why[(k, cases_n.get(d.get("case")))] += 1
            ran_cases = {d["case"] for d in ran}
            o["runLibrary"] = {
                "lines": len(rl),
                "programsRun": len(ran),
                "programsDiffering": len(bad),
                "programsRunByN": {str(k): v for k, v in sorted(collections.Counter(cases_n.get(d["case"]) for d in ran).items())},
                "instructions": sum(d.get("instructions", 0) for d in ran),
                "instructionsByN": {str(k): sum(d.get("instructions", 0) for d in ran if cases_n.get(d["case"]) == k)
                                    for k in sorted({cases_n.get(d["case"]) for d in ran}, key=str)},
                "ciphertexts": sum(d.get("ciphertexts", 0) for d in ran),
                "coeffs": sum(d.get("coeffs", 0) for d in ran),
                "ciphertextsDiffering": sum(d.get("ciphertextsDiffering", 0) for d in ran + bad),
                "notRun": [{"reason": k[0], "N": k[1], "programs": v} for k, v in sorted(why.items(), key=str)],
                "certifiedNotRun": sorted(set(cert) - ran_cases),
                "certifiedNotRunIdealised": len([c for c in set(cert) - ran_cases if c in ideal]),
            }
            v = [d for d in rows if d.get("check") == "algo.variant.mul" and d.get("variant") == "exact (Fl.exactSums)"]
            vf = [d for d in rows if d.get("check") == "algo.variant.mul" and (d.get("variant") or "").startswith("A64fma")]
            o["idealMul"] = {"products": len(v), "coeffs": sum(d.get("coeffs", 0) for d in v),
                             "coeffsDiffering": sum(d.get("mismatches", 0) for d in v),
                             "fmaProducts": len(vf), "fmaCoeffs": sum(d.get("coeffs", 0) for d in vf),
                             "fmaCoeffsDiffering": sum(d.get("mismatches", 0) for d in vf)}
            for k in ("coeffs",):
                if o["idealMul"][k]:
                    o["idealMul"]["percentDiffering"] = round(100 * o["idealMul"]["coeffsDiffering"] / o["idealMul"][k], 1)
                if o["idealMul"]["fmaCoeffs"]:
                    o["idealMul"]["fmaPercentDiffering"] = round(100 * o["idealMul"]["fmaCoeffsDiffering"] / o["idealMul"]["fmaCoeffs"], 1)
        out[scheme] = o
    json.dump(out, sys.stdout, indent=1, sort_keys=False)
    print()


if __name__ == "__main__":
    main()
