#!/usr/bin/env python3
"""UNTRUSTED. Summary of a real-size openfhe-pin run (one checker process per case, run.sh).

  summarize.py --suite DIR --results DIR [--json OUT.json] [--md OUT.md]

Reads DIR/<case>/params.json (configuration), RESULTS/<case>.jsonl (result lines,
harness/openfhe-pin/FORMAT.md) and RESULTS/<case>.time (wall seconds, peak RSS in KB, written by
/usr/bin/time). Reports, per case and in total: check lines ok / fail / null; the bit-exact
comparisons (`algo.*` lines that carry `coeffs` and `mismatches`, `algo.variant.*` excluded):
operations, coefficients compared, coefficients differing, split by implementation tier (only lines
with a verdict: an `"ok": null` line such as `algo.decrypt.exact`, the library's decryption against
EXACT rounding on a value that is not an encryption under s, is information, not a comparison
with a claimed result); wall time
and peak memory. Every comparison of the suite is over ALL coefficients of every limb (no
sampling); `algo.mul.spot` is a sampled cross-check of the array mirror against the locked scalar
functions and is counted as a check line, not as a bit-exact comparison.

Only pass/fail/null counts are reported for any check (no measured norms, no ratios to bounds).
Lines with "ok": false are listed in full (check, case, id, why/first).
"""
import argparse
import collections
import json
import os

TIERS = [("forced", "proved"), ("staged", "proved"), ("limb", "trusted"), ("crt", "trusted"),
         ("literal", "trusted"), ("int", "trusted"), ("exact", "trusted"), ("mirror-only", "mirror"),
         ("glue", "glue")]


def tier(impl):
    impl = impl or ""
    if impl.startswith("staged=locked"):
        return "proved"
    for p, t in TIERS:
        if impl.startswith(p):
            return t
    return "other"


def config(params):
    if params.get("scheme") == "BFV":
        tech = f"{params.get('multiplicationTechnique')}/{params.get('keySwitch')}"
        if params.get("encryptionTechnique") not in (None, "STANDARD"):
            tech += "/" + params["encryptionTechnique"]
    else:
        tech = f"{params.get('scaling')}/{params.get('keySwitch')}"
    return {"scheme": params.get("scheme"), "technique": tech, "depth": params.get("multiplicativeDepth"),
            "t": params.get("t"), "N": params.get("N"), "limbs": len(params.get("qs", [])),
            "limbBits": sorted({q.get("bits") for q in params.get("qs", [])}),
            "special": len(params.get("special", [])), "dnum": params.get("dnum")}


def summarize_case(path):
    c = {"lines": 0, "ok": 0, "fail": 0, "null": 0, "ops": 0, "coeffs": 0, "mism": 0,
         "byTier": collections.Counter(), "perCheck": collections.defaultdict(collections.Counter),
         "failures": [], "program": None, "verdict": None}
    if not os.path.exists(path):
        return None
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        j = json.loads(line)
        c["lines"] += 1
        k = {True: "ok", False: "fail", None: "null"}[j.get("ok")]
        c[k] += 1
        chk = j.get("check", "?")
        c["perCheck"][chk][k] += 1
        if j.get("ok") is False:
            c["failures"].append({"check": chk, "id": j.get("id"), "impl": j.get("impl"),
                                  "why": j.get("why"), "first": j.get("first")})
        if chk == "load.prog":
            c["program"] = j.get("ok")
        if chk == "x.refusal":
            c["program"] = False
        if (chk.startswith("algo.") and not chk.startswith("algo.variant") and "coeffs" in j and "mismatches" in j
                and j.get("ok") is not None):
            c["ops"] += 1
            c["coeffs"] += int(j["coeffs"])
            c["mism"] += int(j["mismatches"])
            c["byTier"][tier(j.get("impl"))] += int(j["coeffs"])
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--suite", required=True)
    ap.add_argument("--results", required=True)
    ap.add_argument("--json")
    ap.add_argument("--md")
    a = ap.parse_args()
    names = sorted(n for n in os.listdir(a.suite) if os.path.isdir(os.path.join(a.suite, n)))
    rows = []
    tot = collections.Counter()
    per_check = collections.defaultdict(collections.Counter)
    failures = []
    unfinished = []
    for n in names:
        params = json.load(open(os.path.join(a.suite, n, "params.json")))
        cfg = config(params)
        c = summarize_case(os.path.join(a.results, n + ".jsonl"))
        tm = os.path.join(a.results, n + ".time")
        wall, rss = None, None
        if os.path.exists(tm):
            tl = open(tm).read().strip().splitlines()
            parts = tl[-1].split("\t") if tl else []
            if len(parts) == 3:
                wall, rss = float(parts[1]), int(parts[2])
        if c is None or c["lines"] == 0:
            unfinished.append(n)
            # a terminated case keeps its wall time and peak memory (GNU time's last line) when it has them
            rows.append(dict(case=n, **cfg, finished=False, wallSeconds=wall,
                             peakRSSMB=None if rss is None else round(rss / 1024)))
            continue
        for k in ("lines", "ok", "fail", "null", "ops", "coeffs", "mism"):
            tot[k] += c[k]
        for chk, cnt in c["perCheck"].items():
            per_check[chk].update(cnt)
        for f in c["failures"]:
            failures.append(dict(case=n, **f))
        rows.append(dict(case=n, **cfg, finished=True, lines=c["lines"], ok=c["ok"], fail=c["fail"],
                         null=c["null"], bitExactOps=c["ops"], coeffsCompared=c["coeffs"], coeffsDiffering=c["mism"],
                         coeffsByTier=dict(c["byTier"]), program=c["program"], wallSeconds=wall,
                         peakRSSMB=None if rss is None else round(rss / 1024)))
    out = {"format": "openfhe-pin-realsize-summary/v1", "cases": len(names), "finished": len(names) - len(unfinished),
           "unfinished": unfinished, "totals": dict(tot), "sampled": False,
           "perCheck": {k: dict(v) for k, v in sorted(per_check.items())}, "failures": failures, "rows": rows}
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)
    md = ["| case | scheme | technique | depth | N | limbs (bits) | lines ok / fail / null | bit-exact ops | coefficients (all) | differing | wall s | peak MB |",
          "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        if not r["finished"]:
            md.append(f"| {r['case']} | {r['scheme']} | {r['technique']} | {r['depth']} | {r['N']} | {r['limbs']} | not finished" + (f" (terminated at {r['wallSeconds']:.0f} s)" if r.get('wallSeconds') else "") + " | | | | | |")
            continue
        md.append(f"| {r['case']} | {r['scheme']} | {r['technique']} | {r['depth']} | {r['N']} | "
                  f"{r['limbs']} ({'/'.join(map(str, r['limbBits']))}) | {r['ok']} / {r['fail']} / {r['null']} | "
                  f"{r['bitExactOps']} | {r['coeffsCompared']:,} | {r['coeffsDiffering']} | "
                  f"{r['wallSeconds']:.0f} | {r['peakRSSMB']} |" if r['wallSeconds'] is not None else
                  f"{r['limbs']} | {r['ok']} / {r['fail']} / {r['null']} | {r['bitExactOps']} | {r['coeffsCompared']:,} | {r['coeffsDiffering']} | | |")
    md.append(f"| **total** ({out['finished']} of {out['cases']}) | | | | | | {tot['ok']} / {tot['fail']} / {tot['null']} | "
              f"{tot['ops']} | {tot['coeffs']:,} | {tot['mism']} | | |")
    if a.md:
        open(a.md, "w").write("\n".join(md) + "\n")
    print(f"{out['finished']}/{out['cases']} cases; lines {tot['lines']} (ok {tot['ok']}, fail {tot['fail']}, "
          f"null {tot['null']}); bit-exact {tot['ops']} operations, {tot['coeffs']} coefficients, {tot['mism']} differing; "
          f"{len(failures)} failing lines")


if __name__ == "__main__":
    main()
