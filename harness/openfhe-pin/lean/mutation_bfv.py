#!/usr/bin/env python3
"""UNTRUSTED. The table of lean/mutation_bfv.sh.

  mutation_bfv.py OUTDIR SURVIVORS.tsv MUTANT...

OUTDIR holds none.jsonl/none.rc (baseline) and NAME.jsonl/NAME.rc per mutant. For a surviving
mutant the headroom is printed: over the lines its perturbation applies to, the largest measured
value against the smallest bound of the mutant run (bits), with the line where the ratio is
smallest."""
import collections
import json
import math
import os
import sys

# mutant -> (check, ops or None, measured field, bound field): the lines it perturbs
WHERE = {
    "mulround-half": [("e.step", ("mul", "square"), "roundMeasured", "roundBound")],
    "mulround-textbook": [("e.step", ("mul", "square"), "roundMeasured", "roundBound")],
    "mulround-zero": [("e.step", ("mul", "square"), "roundMeasured", "roundBound")],
    "mullift-zero": [("e.step", ("mul", "square"), "liftMeasured", "liftBound")],
    "mullift-half": [("e.step", ("mul", "square"), "liftMeasured", "liftBound")],
    "ks-half": [("e.step", ("relin", "keySwitch"), "measured", "bound")],
    "ks-zero": [("e.step", ("relin", "keySwitch"), "measured", "bound")],
    "ks-noleveled": [("e.step", ("relin", "keySwitch"), "measured", "bound")],
    "ms-half": [("e.step", ("modSwitch",), "measured", "bound")],
    "ms-zero": [("e.step", ("modSwitch",), "measured", "bound")],
    "plainadd-zero": [("e.step", ("addPlain", "subPlain"), "measured", "bound")],
    "plainadd-rounded": [("e.step", ("addPlain", "subPlain"), "measured", "bound")],
    "wrong-technique": [("e.step", ("mul", "square"), "roundMeasured", "roundBound"),
                        ("e.step", ("mul", "square"), "liftMeasured", "liftBound")],
    "slack-idealised": [("e.step", ("mul", "square"), "roundMeasured", "roundBound"),
                        ("e.step", ("mul", "square"), "liftMeasured", "liftBound"),
                        ("e.step", ("relin", "keySwitch"), "measured", "bound")],
    "fresh-half": [("c.fresh", None, "measured", "bound"), ("c.input", ("Encrypts",), "measured", "bound")],
    "bound-no-carry": [("f.bound", None, "measured", "bound")],
    "bound-mul-k0": [("f.bound", ("mul", "square", "relin"), "measured", "bound")],
    "delta-round": [("f.bound", None, "measured", "bound")],
}


def bits(x):
    return math.log2(x) if x > 0 else float("-inf")


def load(path):
    rows = []
    if os.path.exists(path):
        for l in open(path):
            if l.strip():
                rows.append(json.loads(l))
    return rows


def headroom(rows, mutant):
    out = []
    for check, ops, mf, bf in WHERE.get(mutant, []):
        best = None
        n = 0
        for d in rows:
            if d.get("check") != check or d.get("impl") == "literal" or (ops and d.get("op") not in ops):
                continue
            if mf not in d or bf not in d or d.get("ok") is not True:
                continue
            m, b = int(d[mf]), int(d[bf])
            n += 1
            r = bits(b) - bits(m) if m > 0 and b > 0 else (float("inf") if m == 0 else float("-inf"))
            if best is None or r < best[0]:
                best = (r, m, b, d["case"], d["id"], d.get("op"))
        if best is None:
            out.append(f"{check} {'/'.join(ops) if ops else ''} [{mf}]: no such line on this case list (the mutant has nothing to act on)")
        else:
            r, m, b, case, vid, op = best
            out.append(f"{check} {'/'.join(ops) if ops else ''} [{mf}] on {n} lines: smallest headroom "
                       f"{r:.2f} bits (measured {m} = 2^{bits(m):.2f} against the perturbed bound {b} = 2^{bits(b):.2f}; "
                       f"{case} {vid} {op})")
    return out


def main():
    out, survf, mutants = sys.argv[1], sys.argv[2], sys.argv[3:]
    expected = {}
    if os.path.exists(survf):
        for l in open(survf):
            l = l.rstrip("\n")
            if l and not l.startswith("#"):
                f = l.split("\t")
                expected[f[0]] = f[1] if len(f) > 1 else ""
    rc = 0
    base_rc = open(os.path.join(out, "none.rc")).read().strip()
    base = load(os.path.join(out, "none.jsonl"))
    nfail = sum(1 for d in base if d.get("ok") is False)
    if base_rc != "0" or nfail:
        print(f"BASELINE FAILS ({nfail} failing lines; see {out}/none.log)")
        rc = 1
    else:
        print(f"baseline: {len(set(d['case'] for d in base))} cases, {len(base)} lines, 0 failing")
    print(f"{'mutant':<18} {'verdict':<9} {'fails':<7} failing checks (count)")
    caught, surviving = 0, []
    for m in mutants:
        rows = load(os.path.join(out, m + ".jsonl"))
        code = open(os.path.join(out, m + ".rc")).read().strip() if os.path.exists(os.path.join(out, m + ".rc")) else "?"
        c = collections.Counter(d["check"] for d in rows if d.get("ok") is False)
        n = sum(c.values())
        # a mutant is caught by a failing CHECK, not by a crash
        errors = sum(v for k, v in c.items() if k.endswith(".error") or k == "load")
        if code == "1" and n > 0 and n > errors:
            v = "CAUGHT"
            caught += 1
            if m in expected:
                print(f"  NOTE {m} is listed as an expected survivor but is caught: update the list")
                rc = 1
        else:
            v = "SURVIVES"
            surviving.append((m, rows))
            if m not in expected:
                rc = 1
        print(f"{m:<18} {v:<9} {n:<7} {' '.join(f'{k}({v})' for k, v in sorted(c.items()))}")
    for m, rows in surviving:
        print(f"SURVIVOR {m}{'' if m in expected else ' (NOT in the expected list)'}: {expected.get(m, '')}")
        for h in headroom(rows, m):
            print("    " + h)
    print(f"bfv mutants: {caught} caught of {len(mutants)}"
          f" ({len(surviving)} surviving: {', '.join(m for m, _ in surviving) or 'none'})")
    sys.exit(rc)


if __name__ == "__main__":
    main()
