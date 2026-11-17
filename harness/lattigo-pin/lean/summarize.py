#!/usr/bin/env python3
"""Tables from lattigo_pin result lines (UNTRUSTED: statistics only; the verdicts are the
`ok` fields written by harness/lattigo-pin/lean/LattigoPin.lean).

usage: summarize.py results.jsonl [more.jsonl ...]
"""
import json
import math
import sys
from collections import defaultdict


def lg(n):
    return "-" if n <= 0 else f"{math.log2(n):.1f}"


rows = defaultdict(lambda: {"n": 0, "ok": 0, "bad": 0, "null": 0, "maxm": 0, "maxratio": 0.0,
                            "minb": None, "maxb": 0, "cases": set(), "params": set()})
for path in sys.argv[1:]:
    for line in open(path):
        r = json.loads(line)
        cls = r.get("instr") or r.get("check")
        if r.get("check") == "enc.fresh":
            cls = r["op"]
        key = ("-".join(str(r.get("case", "?")).split("-")[:2]), cls)
        x = rows[key]
        x["n"] += 1
        x["cases"].add(r.get("case"))
        if r.get("ok") is True:
            x["ok"] += 1
        elif r.get("ok") is False:
            x["bad"] += 1
        else:
            x["null"] += 1
        if "measured" in r and "bound" in r:
            m, b = int(r["measured"]), int(r["bound"])
            x["maxm"] = max(x["maxm"], m)
            x["maxb"] = max(x["maxb"], b)
            x["minb"] = b if x["minb"] is None else min(x["minb"], b)
            if b > 0:
                x["maxratio"] = max(x["maxratio"], m / b)

print("| suite | operation class | checks | cases | ok | violations | max measured (log2) | budget range (log2) | max measured/budget |")
print("|---|---|---|---|---|---|---|---|---|")
for (suite, cls), x in sorted(rows.items()):
    br = "-" if x["minb"] is None else f"{lg(x['minb'])}..{lg(x['maxb'])}"
    ratio = "-" if x["minb"] is None else (f"2^{math.log2(x['maxratio']):.1f}" if x["maxratio"] > 0 else "0")
    print(f"| {suite} | {cls} | {x['n']} | {len(x['cases'])} | {x['ok']} | {x['bad']}"
          f"{'' if not x['null'] else ' (+' + str(x['null']) + ' n/a)'} | {lg(x['maxm'])} | {br} | {ratio} |")
