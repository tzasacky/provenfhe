#!/usr/bin/env python3
"""UNTRUSTED: the largest kappa (1..KMAX) for which fhe_check --kappa K prints CERTIFIED, per
committed default-table file (out/default_table/<technique>_d<D>.fhecheck.json), by a scan from
KMAX down (the failure bound 2^-K grows with K, so the certified set is an initial segment; the
scan does not rely on that). Also records t of each file ($.params.t).

    python3 -I harness/eval/openfhe-upstream/kappa_max.py [--kmax 256] > kappa_max.json
    (FHE_CHECK = the checker; default .lake/build/bin/fhe_check)
"""
import argparse
import json
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
FC = os.environ.get("FHE_CHECK", os.path.join(ROOT, ".lake/build/bin/fhe_check"))


def certified(f, k):
    r = json.loads(subprocess.run([FC, "--json", "--no-suggest", "--kappa", str(k), f], capture_output=True,
                                  text=True).stdout)
    return r["verdict"] == "CERTIFIED" and r.get("verdictLabel", "CERTIFIED") == "CERTIFIED"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=256)
    ap.add_argument("--dir", default=os.path.join(HERE, "out", "default_table"))
    a = ap.parse_args()
    rows = []
    for name in sorted(os.listdir(a.dir)):
        if not name.endswith(".fhecheck.json"):
            continue
        f = os.path.join(a.dir, name)
        tech, d = name[:-len(".fhecheck.json")].rsplit("_d", 1)
        ks = [k for k in range(1, a.kmax + 1) if certified(f, k)]
        rows.append({"file": os.path.relpath(f, ROOT), "technique": tech.upper(), "D": int(d),
                     "t": json.load(open(f))["params"]["t"],
                     "kappaMaxCertified": max(ks) if ks else None,
                     "kappaMinCertified": min(ks) if ks else None, "certifiedCount": len(ks)})
    print(json.dumps({"checker": os.path.relpath(FC, ROOT), "kmax": a.kmax,
                      "rows": sorted(rows, key=lambda r: (r["D"], r["technique"]))}, indent=1))


if __name__ == "__main__":
    main()
