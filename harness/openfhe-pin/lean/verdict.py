#!/usr/bin/env python3
"""UNTRUSTED. The verdict of an openfhe_pin run (used by ../run.sh and ../difftest.sh).

  verdict.py RESULTS.jsonl EXPECTED_FAIL.tsv [--live] [--gate] [--refusals EXPECTED_REFUSALS.tsv]
             [--summary OUT.json]

Reads the result lines of `openfhe_pin --with-algo` and decides:
  * every failing (check, case) pair is listed in EXPECTED_FAIL.tsv, and every listed pair fails
    (with --live a listed pair may pass; with --gate the list must be EMPTY);
  * every case without an extracted program has exactly one `x.refusal` line, and it passed (the
    extractor refused with an expected message and the data shows the reason); with --refusals,
    the (case, class) pairs are exactly those of the file;
  * coverage that must not silently disappear: at least one `c.stored.exceeds` line (a stored
    plaintext larger than t - 1 for which the encryption relation holds), at least one `e.step`
    modSwitch with 3 components within its own budget and above the 2-component budget, the
    encryption relation `c.encrypt` on every recorded encryption, and bit-exact comparisons of
    every `algo.*` family that the fixtures exercise.
Prints the counts; writes them as JSON with --summary. Exit 0 iff all of the above hold."""
import collections
import json
import sys


def main():
    args = sys.argv[1:]
    live = "--live" in args
    gate = "--gate" in args
    refusals = args[args.index("--refusals") + 1] if "--refusals" in args else None
    summary = args[args.index("--summary") + 1] if "--summary" in args else None
    res, expf = args[0], args[1]
    st = collections.Counter()
    per = collections.defaultdict(lambda: [0, 0, 0])
    got = collections.Counter()
    cases = set()
    noprog = set()
    refused = {}
    algo = collections.defaultdict(lambda: [0, 0, 0, 0])  # ops, limbs, coeffs, failing
    enc = [0, 0, 0]          # c.encrypt lines (forced): relation holds / fails / not checkable
    exceeds = [0, 0]         # c.stored.exceeds ok / fail
    ms3 = [0, 0, 0]          # e.step modSwitch with 3 parts: ok, fail, of the ok ones above the 2-part budget
    for l in open(res):
        d = json.loads(l)
        c, ok = d["check"], d.get("ok")
        cases.add(d["case"])
        k = 0 if ok is True else 1 if ok is False else 2
        st[k] += 1
        per[c][k] += 1
        if ok is False:
            got[(c, d["case"])] += 1
        if c == "load.prog" and ok is None:
            noprog.add(d["case"])
        if c == "x.refusal":
            refused.setdefault(d["case"], []).append((d.get("class", "?"), ok, d.get("message", "")))
        if c.startswith("algo.") and not c.startswith("algo.variant") and c not in ("algo.coverage", "algo.layout", "algo.trace"):
            a = algo[c]
            if ok is not None:
                a[0] += 1
                a[1] += d.get("limbs", 0)
                a[2] += d.get("coeffs", 0)
            if ok is False:
                a[3] += 1
        if c == "c.encrypt" and d.get("impl") == "forced":
            enc[k] += 1
        if c == "c.stored.exceeds":
            exceeds[0 if ok is True else 1] += 1
        if c == "e.step" and d.get("op") == "modSwitch" and d.get("operandParts", 0) >= 3:
            if ok is True:
                ms3[0] += 1
                ms3[2] += 1 if d.get("exceeds2PartBudget") else 0
            elif ok is False:
                ms3[1] += 1
    exp = set()
    for l in open(expf):
        l = l.rstrip("\n")
        if l and not l.startswith("#"):
            f = l.split("\t")
            exp.add((f[0], f[1]))
    problems = []
    unexpected = sorted(k for k in got if k not in exp)
    missing = sorted(k for k in exp if k not in got)
    for k in unexpected[:40]:
        problems.append("UNEXPECTED FAIL %s %s" % k)
    if not live:
        for k in missing[:40]:
            problems.append("EXPECTED FAIL NOW PASSES (update fixtures/EXPECTED_FAIL.tsv) %s %s" % k)
    if gate and exp:
        problems.append(f"the expected-fail list is not empty ({len(exp)} entries)")
    # refusals
    for c in sorted(noprog):
        r = refused.get(c, [])
        if len(r) != 1 or r[0][1] is not True:
            problems.append(f"REFUSAL NOT TESTED {c}: {r}")
    for c in sorted(set(refused) - noprog):
        problems.append(f"x.refusal line for a case that has a program: {c}")
    classes = collections.Counter(r[0][0] for r in refused.values())
    if refusals is not None:
        want = {}
        for l in open(refusals):
            l = l.rstrip("\n")
            if l and not l.startswith("#"):
                f = l.split("\t")
                want[f[0]] = f[1]
        have = {c: r[0][0] for c, r in refused.items()}
        for c in sorted(set(want) | set(have)):
            if want.get(c) != have.get(c):
                problems.append(f"REFUSAL LIST: {c}: expected {want.get(c)}, the run has {have.get(c)}")
    # coverage that must not disappear
    if not live:
        if exceeds[0] == 0:
            problems.append("no c.stored.exceeds line: no stored plaintext above t - 1 was exercised")
        if ms3[2] == 0:
            problems.append("no 3-component modSwitch above the 2-component budget was exercised (e.step)")
        for fam in ("algo.encrypt", "algo.add", "algo.sub", "algo.addPlain", "algo.subPlain", "algo.negate",
                    "algo.mulConst", "algo.mulPlain", "algo.tensor", "algo.tensorN", "algo.relin", "algo.rotate",
                    "algo.modReduce", "algo.levelReduce", "algo.morph"):
            if algo[fam][0] == 0:
                problems.append(f"no {fam} comparison was run")
    if exceeds[1] or enc[1]:
        problems.append("the encryption relation fails on a recorded encryption")
    ops = sum(a[0] for a in algo.values())
    limbs = sum(a[1] for a in algo.values())
    coeffs = sum(a[2] for a in algo.values())
    out = {
        "cases": len(cases), "lines": sum(st.values()), "ok": st[0], "fail": st[1], "null": st[2],
        "failingPairs": len(got), "expectedFail": len(exp), "unexpected": len(unexpected),
        "expectedButPassing": len(missing),
        "programs": len(cases) - len(noprog), "refused": len(noprog), "refusalClasses": dict(sorted(classes.items())),
        "encryptions": enc[0] + enc[1] + enc[2], "encryptRelationHolds": enc[0],
        "storedExceedsTMinus1": exceeds[0],
        "modSwitch3Parts": ms3[0] + ms3[1], "modSwitch3PartsAbove2PartBudget": ms3[2],
        "algoOps": ops, "algoLimbs": limbs, "algoCoeffs": coeffs,
        "algoFailing": sum(a[3] for a in algo.values()),
        "algoByCheck": {k: {"ops": v[0], "limbs": v[1], "coeffs": v[2], "failing": v[3]} for k, v in sorted(algo.items())},
        "perCheck": {k: {"ok": v[0], "fail": v[1], "null": v[2]} for k, v in sorted(per.items())},
        "problems": problems,
    }
    if summary:
        json.dump(out, open(summary, "w"), indent=1)
    print(f"cases: {out['cases']} ({out['programs']} with an extracted program, {out['refused']} refused by the "
          f"extractor: {', '.join(f'{k} {v}' for k, v in sorted(classes.items())) or 'none'})")
    print(f"check lines: {out['lines']}: {st[0]} ok / {st[1]} FAIL / {st[2]} null")
    print(f"failing (check, case) pairs: {len(got)}; expected (fixtures/EXPECTED_FAIL.tsv): {len(exp)}; "
          f"unexpected: {len(unexpected)}; expected but now passing: {len(missing)}")
    print(f"encryptions: {out['encryptions']}; ciphertext = encrypt t b a p u e1 e2 holds on {enc[0]}; "
          f"stored plaintext norm above t-1 (relation holds): {exceeds[0]}")
    print(f"modSwitch of 3-component values (e.step): {ms3[0]} within msBudgetAt 3, of which {ms3[2]} above the "
          f"2-component budget; failing: {ms3[1]}")
    print(f"algo: {ops} operations, {limbs} limbs, {coeffs} coefficients compared bit-exactly; "
          f"{out['algoFailing']} differing")
    for p in problems:
        print("  " + p)
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
