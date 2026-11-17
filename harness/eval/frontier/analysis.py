#!/usr/bin/env python3
"""Headline numbers, the paper table and two MODELLED what-ifs, from OUT/results (UNTRUSTED).

  analysis.py OUT DATA_DIR

Writes DATA_DIR/summary.json and prints the paper table (Markdown). What-ifs (MODELLED, not
measured, not certified):
  l1credit: a BFV class cheaper than the cheapest certified one would certify with an l1 key bound
            if its deficit is at most the l1 credit, g(N) * d bits (g = log2 of the lift ratio at
            kappa = 128, Hoeffding; d products on the critical path). The deficit is known exactly
            only when the first failing instruction is at or after the last product (then it is the
            reported overflow); such cells are counted as "flips"; cells where only an earlier
            failure is within the credit are counted as "possible".
  kappa:    in how many cells the cheapest kappa = 128 class is cheaper than the worst-case one.
"""
import json, math, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tables import load, rowkey  # noqa: E402
from frontier_lib import Env, key, lib_args  # noqa: E402


def l1gain(N, kappa=128):
    S1 = 2 * N / 3 + math.sqrt(kappa * math.log(2) * N / 2)
    K = (2 + N) // 2 + 1
    K1 = (2 + math.ceil(S1)) // 2 + 1
    return math.log2(K / K1)


def last_mul_index(env, scheme, cfg):
    d = os.path.join(env.runs, scheme, key(lib_args(scheme, cfg)))
    try:
        x = json.load(open(d + "/x.json"))
    except Exception:
        return None
    body = x["program"]["body"]
    idx = [i for i, ins in enumerate(body) if ins.get("op") in ("mul", "square")]
    return idx[-1] if idx else None


def main():
    out, data = sys.argv[1], sys.argv[2]
    env = Env(out)
    timing = load(out, "timing")
    S = {}
    # ------------------------------------------------ BGV FIXEDMANUAL
    fm = load(out, "bgvfm")
    keep_ratios, keep_dbits, keep_sbits, any_ratios, any_quiet = [], [], [], [], []
    e2e_ok = e2e_n = 0
    fm_none = []
    for r in fm.values():
        tm = timing.get(rowkey(r)) or {}
        dp = r["default"].get("params") or {}
        for tag in ("rec_keep", "rec_any", "rec_any_k128"):
            e = r.get(tag) or {}
            if (e.get("rec") or {}).get("verdict") == "CERTIFIED":
                ee = e.get("e2e") or {}
                e2e_n += 1
                e2e_ok += bool((ee.get("check") or {}).get("verdict", "").startswith("CERTIFIED") and ee.get("valueCheck")
                               and ee.get("cleartextCheck") and ee.get("primesEqual") and ee.get("specialEqual"))
            elif tag != "rec_any_k128":
                fm_none.append((tag, r["prog"], r["t"], r["d"]))
        k = (r.get("rec_keep") or {}).get("rec") or {}
        if k.get("verdict") == "CERTIFIED" and k["N"] == dp.get("N") and len(k["limbs"]) == dp.get("limbs"):
            keep_dbits.append(k["log2Q"] - dp["log2Q"])
            keep_sbits.append(k["scalingModSize"])
            x = (tm.get("ratio") or {}).get("certKeepDigits")
            if x is None and tm.get("identical"):
                x = 1.0
            if x is not None:
                keep_ratios.append(x)
        x = (tm.get("ratio") or {}).get("certWorst")
        if x is not None:
            any_ratios.append(x)
            if not tm.get("highLoad"):
                any_quiet.append(x)
    S["bgvfm"] = {"cells": len(fm), "e2eValidated": e2e_ok, "e2eRecommendations": e2e_n,
                  "keepSameShape": len(keep_dbits), "keepDbits": [min(keep_dbits), max(keep_dbits)] if keep_dbits else None,
                  "keepScalingBits": [min(keep_sbits), max(keep_sbits)] if keep_sbits else None,
                  "keepRatio": [min(keep_ratios), max(keep_ratios)] if keep_ratios else None, "keepRatioN": len(keep_ratios),
                  "anyRatio": [min(any_ratios), max(any_ratios)] if any_ratios else None, "anyRatioN": len(any_ratios),
                  "anyRatioQuiet": [min(any_quiet), max(any_quiet)] if any_quiet else None, "anyRatioQuietN": len(any_quiet),
                  "noRecommendation": sorted(fm_none)}
    # ------------------------------------------------ library-in-the-loop families
    for sec in ("bgvauto", "bfv"):
        rows = load(out, sec)
        fam = {}
        for r in rows.values():
            f = fam.setdefault(r["family"], {"cells": 0, "defaultCert": 0, "defaultCertK128": 0, "defaultWrong": [], "defaultThrows": [],
                                             "none": [], "dlimbs": [], "dbits": [], "ndouble": 0, "ratios": [], "ratiosK128": [],
                                             "e2e": 0, "kappaCheaper": 0, "l1flips": 0, "l1possible": 0, "leastNeedBits": [],
                                             "ratiosQuiet": [], "ratiosQuietNdouble": [], "ratiosHighLoadN": 0})
            f["cells"] += 1
            d = r.get("default") or {}
            dp = d.get("params") or {}
            if (d.get("worst") or {}).get("verdict", "").startswith("CERTIFIED"):
                f["defaultCert"] += 1
            if (d.get("k128") or {}).get("verdict", "").startswith("CERTIFIED"):
                f["defaultCertK128"] += 1
            err = d.get("error") or ""
            if "CLEARTEXT MISMATCH" in err or "rc=3" in err:
                f["defaultWrong"].append((r["prog"], r["t"], r["d"]))
            elif err:
                f["defaultThrows"].append((r["prog"], r["t"], r["d"]))
            s = r.get("search") or {}
            b = s.get("best") or {}
            w, k = b.get("worst"), b.get("k128")
            tm = timing.get(rowkey(r)) or {}
            if not w:
                f["none"].append((r["prog"], r["t"], r["d"]))
                continue
            f["e2e"] += bool(w.get("valueCheck") and w.get("cleartextCheck"))
            wp = w["params"]
            if dp:
                f["dlimbs"].append(wp["limbs"] - dp["limbs"])
                f["dbits"].append(wp["log2Q"] - dp["log2Q"])
                f["ndouble"] += wp["N"] > dp["N"]
            x = (tm.get("ratio") or {}).get("certWorst")
            measured = x is not None
            if x is None and tm.get("identical"):
                x = 1.0
            if x is not None:
                f["ratios"].append(x)
                if not measured:
                    pass  # same setting as the default: nothing was timed
                elif tm.get("highLoad"):
                    f["ratiosHighLoadN"] += 1
                else:
                    f["ratiosQuiet"].append(x)
                    if dp and wp["N"] > dp["N"]:
                        f["ratiosQuietNdouble"].append(x)
            x = (tm.get("ratio") or {}).get("certK128")
            if x is not None:
                f["ratiosK128"].append(x)
            if k and k.get("proxy", 0) < w.get("proxy", 0) - 1e-9:
                f["kappaCheaper"] += 1
            if s.get("leastQ"):
                lq = s["leastQ"]
                f["leastNeedBits"].append(round(lq["log2Q"] - (lq.get("worst") or {}).get("margin", 0), 1))
            if sec == "bfv":
                flip = poss = False
                for e in s.get("evaluated", []):
                    if e is w or e.get("proxy", 0) >= w.get("proxy", 0):
                        continue
                    ov = (e.get("worst") or {}).get("over")
                    if ov is None:
                        continue
                    g = l1gain(e["class"][0]) * r["d"]
                    if ov <= g:
                        poss = True
                        lm = last_mul_index(env, "bfv", dict(e["cfg"], prog=r["prog"], progdepth=r["d"]))
                        fa = (e.get("worst") or {}).get("failAt")
                        if lm is not None and fa is not None and fa >= lm:
                            flip = True
                f["l1flips"] += flip
                f["l1possible"] += poss
        for name, f in fam.items():
            for k_ in ("dlimbs", "dbits", "ratios", "ratiosK128", "leastNeedBits", "ratiosQuiet", "ratiosQuietNdouble"):
                v = f[k_]
                f[k_ + "Range"] = [min(v), max(v)] if v else None
            f["ratiosQuietN"] = len(f["ratiosQuiet"])
            S[name] = f
    S["notes"] = {"ratios": "MEASURED (timing.py); ratiosQuiet*/anyRatioQuiet*: only rows whose timing ran at load <= timing.py --maxload (highLoad false); kappaCheaper, l1flips, l1possible: MODELLED/derived (analysis.py docstring)"}
    os.makedirs(data, exist_ok=True)
    json.dump(S, open(os.path.join(data, "summary.json"), "w"), indent=1, sort_keys=True, default=str)
    for k, v in S.items():
        if isinstance(v, dict):
            print(k, {kk: vv for kk, vv in v.items() if not isinstance(vv, list) or kk.endswith("Range") or len(vv) < 8})


if __name__ == "__main__":
    main()
