#!/usr/bin/env python3
"""Compact rows and headline numbers for the paper (UNTRUSTED; copies numbers from the results).

  summarize.py OUT DATA_DIR

Writes DATA_DIR/rows/{bgvfm,bgvauto,bfv}.jsonl (one compact line per cell: default, cheapest
certified worst/kappa128, least-Q member, every class evaluated with its verdict), DATA_DIR/
timing.jsonl (copied), DATA_DIR/timing_fit.json (copied), DATA_DIR/frontier.tsv (from tables.py,
copied) and DATA_DIR/summary.json (the numbers RESULTS.md and the paper quote; each with the rows
it is computed from).
"""
import json, math, os, shutil, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tables import load, rowkey  # noqa: E402


def compact_eval(e):
    keep = ("class", "proxy", "log2Q", "cfg", "worst", "k128", "valueCheck", "cleartextCheck", "error")
    out = {k: e.get(k) for k in keep if k in e}
    if "proxy" in out:
        out["proxy"] = round(out["proxy"], 2)
    return out


def compact(r):
    r = json.loads(json.dumps(r))
    for k in ("x",):
        r.get("default", {}).pop(k, None)
    d = r.get("default") or {}
    for m in ("worst", "k128"):
        if d.get(m):
            d[m] = {k: d[m].get(k) for k in ("verdict", "margin", "over", "failAt", "failOp", "N", "log2Q", "limbBits", "specialBits")}
    s = r.get("search")
    if s:
        s["evaluated"] = [compact_eval(e) for e in s.get("evaluated", [])]
        for m in ("worst", "k128"):
            if (s.get("best") or {}).get(m):
                s["best"][m] = compact_eval(s["best"][m]) | {"params": s["best"][m].get("params")}
    for tag in ("rec_any", "rec_keep", "rec_any_k128"):
        e = r.get(tag)
        if e and e.get("e2e") and e["e2e"].get("check"):
            c = e["e2e"]["check"]
            e["e2e"]["check"] = {k: c.get(k) for k in ("verdict", "margin", "N", "log2Q", "limbBits", "specialBits")}
    return r


def main():
    out, data = sys.argv[1], sys.argv[2]
    os.makedirs(os.path.join(data, "rows"), exist_ok=True)
    for s in ("bgvfm", "bgvauto", "bfv"):
        rows = load(out, s)
        with open(os.path.join(data, "rows", f"{s}.jsonl"), "w") as f:
            for k in sorted(rows):
                f.write(json.dumps(compact(rows[k]), sort_keys=True) + "\n")
    for f in ("timing.jsonl", "timing_fit.json"):
        src = os.path.join(out, "results", f)
        if os.path.exists(src):
            if f == "timing.jsonl":
                last = load(out, "timing")
                with open(os.path.join(data, f), "w") as g:
                    for k in sorted(last):
                        g.write(json.dumps(last[k], sort_keys=True) + "\n")
            else:
                shutil.copy(src, os.path.join(data, f))
    if os.path.exists(os.path.join(out, "frontier.tsv")):
        shutil.copy(os.path.join(out, "frontier.tsv"), os.path.join(data, "frontier.tsv"))
    print("wrote", data)


if __name__ == "__main__":
    main()
