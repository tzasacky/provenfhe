#!/usr/bin/env python3
"""UNTRUSTED. The verdict of an openfhe_pin run on BFV cases.

  verdict_bfv.py RESULTS.jsonl EXPECTED_FAIL.tsv [--live] [--gate] [--refusals EXPECTED_REFUSALS-bfv.tsv]
                 [--summary OUT.json] [--write-refusals OUT.tsv]

Reads the result lines with `"scheme": "BFV"` (other lines are ignored: a mixed run is judged for
its BGV part by verdict.py) and decides:
  * every failing (check, case) pair is listed in EXPECTED_FAIL.tsv (`check<TAB>case`), and every
    listed pair fails (with --live a listed pair may pass; with --gate the list must be EMPTY);
  * every case without an extracted program has exactly one `x.refusal` line, and it passed; with
    --refusals, the (case, class, message) triples are exactly those of the file
    (`case<TAB>class<TAB>message`);
  * every case with a program has one `f.verdict` line, one `f.certified-consistent` line and a
    passing `f.refAnalyze` line, and NO CERTIFIED program has a failing `e.step`, `f.bound` or
    `c.input` line (checked here from the lines themselves, independently of the checker's own
    `f.certified-consistent`);
  * coverage that must not silently disappear (not with --live): at least one decided line of
    each of a.decrypt, c.fresh, c.input, c.predict, d.key, e.step (mul, relin, keySwitch,
    addPlain or subPlain, modSwitch), f.bound, and a CERTIFIED and a NOT CERTIFIED program.
--write-refusals writes the refusal list of this run (for export/make_fixtures_bfv.sh).
Prints the counts; writes them as JSON with --summary. Exit 0 iff all of the above hold."""
import collections
import json
import sys


def main():
    args = sys.argv[1:]
    live = "--live" in args
    gate = "--gate" in args
    opt = lambda k: args[args.index(k) + 1] if k in args else None
    refusals, summary, wref = opt("--refusals"), opt("--summary"), opt("--write-refusals")
    res, expf = args[0], args[1]
    st = collections.Counter()
    per = collections.defaultdict(lambda: [0, 0, 0])
    got = collections.Counter()
    cases, noprog = set(), set()
    refused = {}
    verdict = {}                                   # case -> f.verdict line
    consistent = {}
    refana = {}
    bad = collections.defaultdict(list)            # case -> failing e.step / f.bound / c.input ids
    cov = collections.Counter()
    for l in open(res):
        d = json.loads(l)
        if d.get("scheme") != "BFV":
            continue
        c, ok, case = d["check"], d.get("ok"), d["case"]
        cases.add(case)
        k = 0 if ok is True else 1 if ok is False else 2
        st[k] += 1
        per[c][k] += 1
        if ok is False:
            got[(c, case)] += 1
            if c in ("e.step", "f.bound", "c.input"):
                bad[case].append(f"{c}:{d.get('id')}")
        if c == "load.prog" and ok is None:
            noprog.add(case)
        if c == "x.refusal":
            refused.setdefault(case, []).append((d.get("class", "?"), ok, d.get("message", "")))
        if c == "f.verdict":
            verdict[case] = d
        if c == "f.certified-consistent":
            consistent[case] = ok
        if c == "f.refAnalyze":
            refana[case] = ok
        if ok is not None:
            cov[c] += 1
            if c == "e.step":
                cov["e.step:" + str(d.get("op"))] += 1
    exp = set()
    for l in open(expf):
        l = l.rstrip("\n")
        if l and not l.startswith("#"):
            f = l.split("\t")
            exp.add((f[0], f[1]))
    problems = []
    unexpected = sorted(k for k in got if k not in exp)
    missing = sorted(k for k in exp if k not in got)
    for k in unexpected[:60]:
        problems.append("UNEXPECTED FAIL %s %s" % k)
    if len(unexpected) > 60:
        problems.append(f"... and {len(unexpected) - 60} more unexpected failing pairs")
    if not live:
        for k in missing[:40]:
            problems.append("EXPECTED FAIL NOW PASSES %s %s" % k)
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
    if wref:
        with open(wref, "w") as f:
            for c in sorted(refused):
                f.write(f"{c}\t{refused[c][0][0]}\t{refused[c][0][2]}\n")
    if refusals is not None:
        want = {}
        for l in open(refusals):
            l = l.rstrip("\n")
            if l and not l.startswith("#"):
                f = l.split("\t")
                want[f[0]] = (f[1], f[2] if len(f) > 2 else None)
        have = {c: (r[0][0], r[0][2]) for c, r in refused.items()}
        for c in sorted(set(want) | set(have)):
            w, h = want.get(c), have.get(c)
            if w is None or h is None or w[0] != h[0] or (w[1] is not None and w[1] != h[1]):
                problems.append(f"REFUSAL LIST: {c}: expected {w}, the run has {h}")
    # programs
    progs = cases - noprog
    certified = sorted(c for c in progs if verdict.get(c, {}).get("certified") is True)
    notcert = sorted(c for c in progs if verdict.get(c, {}).get("certified") is False)
    for c in sorted(progs):
        if c not in verdict:
            problems.append(f"NO f.verdict LINE {c}")
        if c not in consistent:
            problems.append(f"NO f.certified-consistent LINE {c}")
        if refana.get(c) is not True:
            problems.append(f"f.refAnalyze does not pass on {c}: the per-variable replay is not refAnalyzeBFV")
    violated = [c for c in certified if bad.get(c)]
    for c in violated:
        problems.append(f"CERTIFIED PROGRAM WITH A VIOLATION {c}: {', '.join(bad[c][:6])}")
    for c in certified:
        if verdict[c].get("toolAgrees") is False:
            problems.append(f"fhe_check's pipeline and certifyBFV? disagree on {c}")
    assumed = collections.Counter(",".join(verdict[c].get("assumed", [])) or "none" for c in certified)
    if not live:
        need = ["a.decrypt", "c.fresh", "c.input", "c.predict", "d.key", "f.bound", "e.step:mul", "e.step:relin",
                "e.step:keySwitch", "e.step:modSwitch"]
        for n in need:
            if cov[n] == 0:
                problems.append(f"no decided {n} line: the coverage disappeared")
        if cov["e.step:addPlain"] + cov["e.step:subPlain"] == 0:
            problems.append("no decided e.step addPlain/subPlain line")
        if not certified:
            problems.append("no CERTIFIED program")
        if not notcert:
            problems.append("no NOT CERTIFIED program")
    out = {
        "cases": len(cases), "lines": sum(st.values()), "ok": st[0], "fail": st[1], "null": st[2],
        "failingPairs": len(got), "expectedFail": len(exp), "unexpected": len(unexpected),
        "expectedButPassing": len(missing),
        "programs": len(progs), "refused": len(noprog), "refusalClasses": dict(sorted(classes.items())),
        "certified": len(certified), "notCertified": len(notcert), "certifiedByAssumption": dict(sorted(assumed.items())),
        "certifiedWithViolation": len(violated),
        "perCheck": {k: {"ok": v[0], "fail": v[1], "null": v[2]} for k, v in sorted(per.items())},
        "problems": problems,
    }
    if summary:
        json.dump(out, open(summary, "w"), indent=1)
    print(f"BFV cases: {out['cases']} ({out['programs']} with an extracted program, {out['refused']} refused by the "
          f"extractor: {', '.join(f'{k} {v}' for k, v in sorted(classes.items())) or 'none'})")
    print(f"check lines: {out['lines']}: {st[0]} ok / {st[1]} FAIL / {st[2]} null")
    print(f"failing (check, case) pairs: {len(got)}; expected: {len(exp)}; unexpected: {len(unexpected)}; "
          f"expected but now passing: {len(missing)}")
    print(f"verdicts: {len(certified)} CERTIFIED ({', '.join(f'{k}: {v}' for k, v in sorted(assumed.items())) or '-'}), "
          f"{len(notcert)} NOT CERTIFIED; CERTIFIED programs with a violated step contract, a noise above its "
          f"bound or an input outside its bound: {len(violated)}")
    for p in problems:
        print("  " + p)
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
