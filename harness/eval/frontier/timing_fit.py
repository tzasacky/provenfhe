#!/usr/bin/env python3
"""Fit the time proxy of costmodel.py on the pristine library (MEASURED inputs, MODELLED output).

  timing_fit.py OUT [--rounds R] [--reps K]

Times a fixed list of contexts (frontier_time, evaluation only, single thread, minimum of K runs,
R interleaved rounds; the 1-minute load average is recorded per round), computes the features
(A, B) of costmodel.features from the context OpenFHE generated (params-only run of the traced
driver: N, limbs, special primes, limbs per digit), fits T/(N log2 N) = a*A + b*B per group by
least squares on relative error, and writes OUT/results/timing_fit.json (raw times, loads, fit,
residuals).
"""
import argparse, json, math, os, sys
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier_lib import Env, params_only, shape, sh, lib_args  # noqa: E402
import costmodel  # noqa: E402


def configs():
    cs = []
    for d in (2, 4, 6, 8, 10, 12):
        for dnum in (0, 1, 2, d + 1):
            cs.append(("bgv", dict(scal="FIXEDMANUAL", depth=d, prog="chain", dnum=dnum)))
    for d in (4, 8):
        cs.append(("bgv", dict(scal="FIXEDMANUAL", depth=d, prog="chain", ringdim=65536 if d == 8 else 32768)))
    for d in (3, 6, 10):
        for dnum in (0, d + 1):
            cs.append(("bgv", dict(scal="FIXEDMANUAL", depth=d, prog="poly", dnum=dnum)))
    for d in (3, 6, 10):
        cs.append(("bgv", dict(scal="FLEXIBLEAUTOEXT", depth=d, prog="chain")))
    for mult in ("HPSPOVERQLEVELED", "BEHZ", "HPSPOVERQ"):
        for ks in ("BV", "HYBRID"):
            for d in (3, 6, 9):
                for c, s in ((d, 60), (d + 2, 60), (d + 2, 45), (d + 4, 36)):
                    cs.append(("bfv", dict(mult=mult, ks=ks, depth=c, qbits=s, progdepth=d, prog="chain")))
            cs.append(("bfv", dict(mult=mult, ks=ks, depth=6, progdepth=6, prog="poly")))
            if ks == "HYBRID":
                for dnum in (1, 2, 4):
                    cs.append(("bfv", dict(mult=mult, ks=ks, depth=8, progdepth=6, prog="chain", dnum=dnum)))
    return cs


def group(scheme, cfg):
    if scheme == "bgv":
        return "bgv/HYBRID"
    return f"bfv/{cfg['mult']}/{cfg['ks']}"


def feats(scheme, cfg, p):
    N, q, s = shape(p)
    L, K = len(q), len(s)
    alpha = int(p.get("towersPerDigit") or 1)
    d = cfg.get("progdepth") or cfg["depth"]
    ks = "HYBRID" if scheme == "bgv" else p.get("keySwitch", "BV")
    A, B = costmodel.features(scheme, cfg["prog"], d, L, K, alpha, ks)
    return N, L, K, alpha, A, B


def fit(rows):
    """least squares on relative error: minimise sum ((a*A + b*B)/y - 1)^2, a, b >= 0"""
    def solve(cols):
        # normal equations for weights w = 1/y
        m = len(cols)
        M = [[0.0] * m for _ in range(m)]
        v = [0.0] * m
        for r in rows:
            y = r["y"]
            x = [r[c] / y for c in cols]
            for i in range(m):
                v[i] += x[i]
                for j in range(m):
                    M[i][j] += x[i] * x[j]
        if m == 1:
            return [v[0] / M[0][0]]
        det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
        return [(v[0] * M[1][1] - v[1] * M[0][1]) / det, (M[0][0] * v[1] - M[1][0] * v[0]) / det]
    a, b = solve(["A", "B"])
    if a < 0:
        a, b = 0.0, solve(["B"])[0]
    elif b < 0:
        a, b = solve(["A"])[0], 0.0
    res = [((a * r["A"] + b * r["B"]) / r["y"]) for r in rows]
    return a, b, res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--rounds", type=int, default=2)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--refit", action="store_true", help="recompute features and fits from the stored times")
    a = ap.parse_args()
    env = Env(a.out)
    if a.refit:
        old = json.load(open(os.path.join(a.out, "results", "timing_fit.json")))
        rows = []
        for r in old["rows"]:
            p = params_only(env, r["scheme"], r["cfg"])
            N, L, K, alpha, A, B = feats(r["scheme"], r["cfg"], p)
            rows.append(dict(r, A=A, B=B))
        return finish(a, rows, old["loads"])
    cs = configs()
    with ThreadPoolExecutor(32) as ex:
        ps = list(ex.map(lambda c: params_only(env, c[0], c[1]), cs))
    todo = [(s, c, p) for (s, c), p in zip(cs, ps) if "error" not in p]
    times = {i: [] for i in range(len(todo))}
    loads = []
    for rd in range(a.rounds):
        loads.append(os.getloadavg()[0])
        for i, (s, c, p) in enumerate(todo):
            args = ["--scheme", s.upper()] + lib_args(s, c) + ["--reps", str(a.reps)]
            rc, o, e = sh([os.path.join(env.bin, "frontier_time")] + args)
            try:
                j = json.loads(o.strip().splitlines()[-1])
                N, q, sp = shape(p)
                assert j["N"] == N and j["Q"] == [str(x) for x in q] and j["P"] == [str(x) for x in sp], "timed context != traced context"
                times[i].append(j["minMs"])
            except Exception as ex_:
                times[i].append(None)
                print("ERR", s, c, repr(ex_)[:200], (o + e)[-200:], flush=True)
        print("round", rd, "load", loads[-1], flush=True)
    rows = []
    for i, (s, c, p) in enumerate(todo):
        ts = [x for x in times[i] if x]
        if not ts:
            continue
        N, L, K, alpha, A, B = feats(s, c, p)
        rows.append(dict(scheme=s, cfg=c, group=group(s, c), N=N, L=L, K=K, alpha=alpha, A=A, B=B,
                         ms=min(ts), y=min(ts) / (N * math.log2(N))))
    finish(a, rows, loads)


def finish(a, rows, loads):
    fits = {}
    # BGV: the FIXEDMANUAL rows (what fhe_check recommend searches) are fitted on their own
    for r in rows:
        if r["scheme"] == "bgv" and r["cfg"].get("scal") != "FIXEDMANUAL":
            r["group"] = "bgv-auto/HYBRID"
    for g in sorted({r["group"] for r in rows}):
        rs = [r for r in rows if r["group"] == g]
        a_, b_, res = fit(rs)
        for r, x in zip(rs, res):
            r["modelOverMeasured"] = x
        fits[g] = {"a": a_, "b": b_, "n": len(rs), "maxRelErr": max(abs(x - 1) for x in res),
                   "geoMeanAbsLogErr": math.exp(sum(abs(math.log(x)) for x in res) / len(res))}
        print(g, json.dumps(fits[g]))
    os.makedirs(os.path.join(a.out, "results"), exist_ok=True)
    json.dump({"loads": loads, "rounds": a.rounds, "reps": a.reps, "fits": fits, "rows": rows,
               "model": "T/(N log2 N) = a*A + b*B (costmodel.py)"},
              open(os.path.join(a.out, "results", "timing_fit.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
