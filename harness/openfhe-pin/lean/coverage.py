#!/usr/bin/env python3
"""Coverage cross-check of the OpenFHE extractors against the recorded conformance fixtures
(UNTRUSTED glue; harness/openfhe-pin/difftest.sh runs it on the committed fixtures).

    coverage.py RESULTS.jsonl [RESULTS.jsonl ...]

Rule: an extractor may only emit an instruction shape that has been executed on real OpenFHE
v1.6.1 runs AND accepted there by the trusted step contract. A shape is

    (scheme, op, operand shapes, technique[, key switching])

with operand shapes the numbers of components of the operands (1 = a plaintext operand), and the
technique the BFV multiplication technique (HPS, HPSPOVERQ, HPSPOVERQLEVELED, BEHZ) or the BGV
scaling technique. EMITTABLE below lists every shape the extractors can emit, read from
harness/frontend/openfhe/extract.py and extract_bfv.py (their instruction mappings and refusals).
The script fails if
  * an EMITTABLE shape has no `e.step` line with "ok": true in the results (UNCOVERED: add a
    fixture that exercises it, or make the extractor refuse it), or
  * an `e.step` line has a shape that is not in EMITTABLE (the table is stale: the extractor emits
    something this list does not know), or
  * some `e.step` line of a shape fails (that shape is not accepted everywhere).
`--allow FILE` lists shapes (one per line, as printed) whose absence is accepted, with the reason
after a TAB; each such line is printed in the summary.
"""
import json
import sys
from itertools import product

BFV_TECH = ("HPS", "HPSPOVERQ", "HPSPOVERQLEVELED", "BEHZ")
BGV_TECH = ("FIXEDMANUAL", "FIXEDAUTO", "FLEXIBLEAUTO", "FLEXIBLEAUTOEXT")
KS = ("HYBRID", "BV")


def bfv_emittable():
    out = set()
    for tech in BFV_TECH:
        for op in ("add", "sub"):
            out.add(("BFV", op, (2, 2), tech, None))
            out.add(("BFV", op, (3, 3), tech, None))      # sums of unrelinearised products (PRODUCT_RULE)
        for op in ("addPlain", "subPlain", "mulPlain"):
            out.add(("BFV", op, (2, 1), tech, None))
        out.add(("BFV", "mul", (2, 2), tech, None))
        if tech in ("HPS", "BEHZ"):
            out.add(("BFV", "square", (2,), tech, None))   # P-over-Q squarings are emitted as mul a a
        out.add(("BFV", "mulConst", (2,), tech, None))      # EvalNegate
        out.add(("BFV", "mulConst", (3,), tech, None))      # EvalNegate of an unrelinearised product
        out.add(("BFV", "automorph", (2,), tech, None))
        if tech in ("HPSPOVERQ", "HPSPOVERQLEVELED"):
            # Compress: under HPS and BEHZ OpenFHE v1.6.1 throws ("not currently supported"), the
            # traced call has no output and the extractor refuses the trace (compress-threw)
            out.add(("BFV", "modSwitch", (2,), tech, None))
            out.add(("BFV", "copy", (2,), tech, None))      # Compress to the same number of limbs
        for ks in KS:
            out.add(("BFV", "relin", (3,), tech, ks))
            out.add(("BFV", "keySwitch", (2,), tech, ks))
    return out


def shape_of(d):
    if d.get("check") != "e.step":
        return None
    scheme = d.get("scheme", "BGV")
    ops = tuple(d.get("operandsParts") or ())
    if scheme == "BFV":
        ks = d.get("ks") if d.get("op") in ("relin", "keySwitch") else None
        return ("BFV", d.get("op"), ops, d.get("mult"), ks)
    return None   # BGV: see the module docstring of FORMAT.md; not enumerated here yet


def fmt(s):
    return f"{s[0]} {s[1]} {list(s[2])} {s[3]}" + (f" {s[4]}" if s[4] else "")


def main(argv):
    allow = {}
    files = []
    it = iter(argv)
    for a in it:
        if a == "--allow":
            for line in open(next(it)):
                if line.strip() and not line.startswith("#"):
                    k, _, why = line.rstrip("\n").partition("\t")
                    allow[k.strip()] = why.strip()
        else:
            files.append(a)
    if not files:
        print(__doc__)
        return 2
    emit = bfv_emittable()
    ok, bad, seen = {}, {}, set()
    for f in files:
        for line in open(f):
            try:
                d = json.loads(line)
            except Exception:
                continue
            s = shape_of(d)
            if s is None:
                continue
            seen.add(s)
            if d.get("ok") is True:
                ok[s] = ok.get(s, 0) + 1
            elif d.get("ok") is False:
                bad.setdefault(s, []).append(d.get("case"))
    rc = 0
    stale = sorted(seen - emit, key=fmt)
    for s in stale:
        print(f"NOT IN TABLE  {fmt(s)}  (the extractor emitted it; extend EMITTABLE or refuse it)")
        rc = 1
    for s, cases in sorted(bad.items(), key=lambda x: fmt(x[0])):
        print(f"FAILING       {fmt(s)}  {len(cases)} line(s), e.g. {cases[0]}")
        rc = 1
    unc = []
    for s in sorted(emit, key=fmt):
        if ok.get(s):
            continue
        if fmt(s) in allow:
            print(f"allowed gap   {fmt(s)}  ({allow[fmt(s)]})")
            continue
        unc.append(s)
        print(f"UNCOVERED     {fmt(s)}")
        rc = 1
    print(f"coverage: {len(emit)} emittable BFV shapes, {sum(1 for s in emit if ok.get(s))} covered by an accepting "
          f"e.step line, {len(unc)} uncovered, {len([s for s in emit if not ok.get(s) and fmt(s) in allow])} allowed "
          f"gaps, {len(stale)} not in the table, {len(bad)} with a failing line")
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
