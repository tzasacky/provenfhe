#!/usr/bin/env python3
"""Certified frontier: OpenFHE v1.6.1 defaults vs the cheapest certified settings (UNTRUSTED glue).

  frontier.py OUT SECTION [--t T,...] [--depths 1-12] [--progs chain,poly] [--workers W] [--families ...]

SECTION
  bgvfm    BGV FIXEDMANUAL (HYBRID key switching). Default context SetMultiplicativeDepth(d); then
           `fhe_check recommend` (time objective) on the default's extracted file: --digits any,
           --digits keep, and --digits any --kappa 128. Every recommendation is configured through the
           public API (SetFirstModSize, SetScalingModSize, SetNumLargeDigits, SetRingDim), run
           traced, extracted, value-checked and re-checked by a plain fhe_check (end to end).
  bgvauto  BGV FLEXIBLEAUTOEXT (OpenFHE's default scaling): library-in-the-loop search over the
           settings this mode accepts (SetEvalAddCount, SetKeySwitchCount, SetMultiplicativeDepth
           at or above the program depth); SetScalingModSize/SetFirstModSize are refused outside
           FIXEDMANUAL (gen-cryptocontext-params-validation.cpp:150-158).
  bfv      BFV, multiplication technique x key switching: library-in-the-loop search over
           SetMultiplicativeDepth c (from 1), SetScalingModSize s (24..60: every limb of Q has s
           bits), SetNumLargeDigits (HYBRID). The ring dimension is OpenFHE's (smallest secure).

Library-in-the-loop search (`lib_search`): every candidate setting is given to OpenFHE, which
generates the context (params-only run of the traced driver); contexts are grouped into cost
classes (N, limbs, special primes, limbs per digit) ordered by the time proxy of costmodel.py;
in each class the largest Q is run TRACED, extracted, value-checked and checked by a plain
fhe_check; the first CERTIFIED class is the answer (worst case; --kappa 128 alongside), then the
least scaling-mod size that still certifies in that class is found by bisection. NOT claimed:
optimality (a model orders the classes; a class whose largest Q fails is not searched further).
Claimed: every row marked CERTIFIED is a plain fhe_check verdict on the library's own run.

Writes OUT/results/<section>.jsonl (one row per cell).
"""
import argparse, json, math, os, sys, threading
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier_lib import Env, params_only, shape, traced_run, check, certified, sh, lg2  # noqa: E402
import costmodel  # noqa: E402

LOCK = threading.Lock()


def emit(env, section, row):
    with LOCK:
        os.makedirs(os.path.join(env.out, "results"), exist_ok=True)
        with open(os.path.join(env.out, "results", f"{section}.jsonl"), "a") as f:
            f.write(json.dumps(row) + "\n")
        print(section, json.dumps(row)[:300], flush=True)


def summary(p):
    N, q, s = shape(p)
    return {"N": N, "limbs": len(q), "limbBits": [round(lg2(x), 2) for x in q], "log2Q": round(sum(lg2(x) for x in q), 2),
            "special": len(s), "log2P": round(sum(lg2(x) for x in s), 2), "towersPerDigit": p.get("towersPerDigit"),
            "dnum": p.get("dnum")}


def run_and_check(env, scheme, cfg, kappas=(None, 128)):
    x, info = traced_run(env, scheme, cfg)
    if not x:
        return {"error": info.get("error"), "cfg": cfg}
    r = {"cfg": cfg, "valueCheck": info.get("valueCheck"), "cleartextCheck": info.get("cleartextCheck"), "x": x}
    for k in kappas:
        r["worst" if k is None else f"k{k}"] = check(env, x, k)
    return r


def batch_ok(N, t):
    return (t - 1) % (2 * N) == 0


def lib_search(env, scheme, prog, d, t, cands, group, ks):
    """cands: list of cfg dicts (no prog/progdepth). Returns dict with the cheapest certified class
    (worst case and kappa 128), the classes evaluated, and the least-Q member of the winning class."""
    ps = [params_only(env, scheme, c) for c in cands]
    classes = {}
    for c, p in zip(cands, ps):
        sh_ = shape(p)
        if not sh_:
            continue
        N, q, s = sh_
        if not batch_ok(N, t) or N > 65536:
            continue
        alpha = int(p.get("towersPerDigit") or 1)
        kk = (N, len(q), len(s), alpha)
        lq = sum(lg2(x) for x in q)
        classes.setdefault(kk, []).append((lq, c, p))
    order = []
    for kk, mem in classes.items():
        N, L, K, alpha = kk
        A, B = costmodel.features(scheme, prog, d, L, K, alpha, ks)
        order.append((costmodel.proxy(group, N, A, B), kk))
    order.sort()
    evaluated = []
    best = {"worst": None, "k128": None}
    for px, kk in order:
        mem = sorted(classes[kk], key=lambda m: (-m[0], m[1].get("depth", 0)))
        lq, c, p = mem[0]
        cfg = dict(c, prog=prog, progdepth=d) if scheme == "bfv" else dict(c, prog=prog, progdepth=d)
        r = run_and_check(env, scheme, cfg)
        ent = {"class": kk, "proxy": px, "log2Q": round(lq, 2), "cfg": c, "params": summary(p)}
        for m in ("worst", "k128"):
            if m in r:
                ent[m] = {k_: r[m].get(k_) for k_ in ("verdict", "margin", "over", "failAt")}
        ent["valueCheck"] = r.get("valueCheck")
        ent["cleartextCheck"] = r.get("cleartextCheck")
        if "error" in r:
            ent["error"] = r["error"]
        evaluated.append(ent)
        for m in ("worst", "k128"):
            if best[m] is None and m in r and certified(r[m]) and r.get("valueCheck") and r.get("cleartextCheck"):
                best[m] = ent
        if best["worst"] is not None:
            break
    # least Q in the winning class that still certifies (worst case): bisection over its members
    least = None
    if best["worst"] is not None:
        kk = best["worst"]["class"]
        mem = sorted(classes[kk], key=lambda m: m[0])
        lo, hi = 0, len(mem) - 1  # mem[hi] certified
        least = best["worst"]
        while lo < hi:
            mid = (lo + hi) // 2
            lq, c, p = mem[mid]
            r = run_and_check(env, scheme, dict(c, prog=prog, progdepth=d), kappas=(None,))
            if "worst" in r and certified(r["worst"]) and r.get("valueCheck") and r.get("cleartextCheck"):
                hi = mid
                least = {"class": kk, "log2Q": round(lq, 2), "cfg": c, "params": summary(p),
                         "worst": {k_: r["worst"].get(k_) for k_ in ("verdict", "margin")}}
            else:
                lo = mid + 1
    return {"best": best, "leastQ": least, "evaluated": evaluated, "classes": len(order)}


# ------------------------------------------------------------------ BFV
def bfv_cands(mult, ks, t, d):
    cs = []
    for c in range(1, d + 11):
        for s in range(24, 61):
            for dn in ((0, 1, 2, 3, 4) if ks == "HYBRID" else (0,)):
                cs.append(dict(mult=mult, ks=ks, depth=c, qbits=s, t=t, dnum=dn))
    return cs


def job_bfv(env, mult, ks, prog, t, d):
    row = {"family": f"BFV {mult} {ks}", "scheme": "bfv", "mult": mult, "ks": ks, "prog": prog, "t": t, "d": d}
    dflt = dict(mult=mult, ks=ks, depth=d, t=t)
    p = params_only(env, "bfv", dflt)
    if "error" in p:
        row["default"] = {"error": p["error"]}
    else:
        r = run_and_check(env, "bfv", dict(dflt, prog=prog, progdepth=d))
        row["default"] = {"cfg": dflt, "params": summary(p), **{k: r.get(k) for k in ("worst", "k128", "valueCheck", "cleartextCheck", "error")}}
    row["search"] = lib_search(env, "bfv", prog, d, t, bfv_cands(mult, ks, t, d), f"bfv/{mult}/{ks}", ks)
    emit(env, "bfv", row)


# ------------------------------------------------------------------ BGV auto
EVALADD = [0, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 30000, 100000, 300000, 1000000]
KSCOUNT = [0, 10, 100, 1000, 10000]


def job_bgvauto(env, scal, prog, t, d):
    row = {"family": f"BGV {scal}", "scheme": "bgv", "scal": scal, "prog": prog, "t": t, "d": d}
    dflt = dict(scal=scal, depth=d, t=t)
    p = params_only(env, "bgv", dflt)
    if "error" in p:
        row["default"] = {"error": p["error"]}
    else:
        r = run_and_check(env, "bgv", dict(dflt, prog=prog, progdepth=d))
        row["default"] = {"cfg": dflt, "params": summary(p), **{k: r.get(k) for k in ("worst", "k128", "valueCheck", "cleartextCheck", "error")}}
    cands = [dict(scal=scal, depth=c, t=t, evaladd=a, kscount=k) for c in (d, d + 1, d + 2) for a in EVALADD for k in KSCOUNT]
    row["search"] = lib_search(env, "bgv", prog, d, t, cands, "bgv-auto/HYBRID", "HYBRID")
    emit(env, "bgvauto", row)


# ------------------------------------------------------------------ BGV FIXEDMANUAL
def recommend(env, x, extra):
    rc, o, e = sh([env.fc, "recommend", "--json"] + extra + [x])
    try:
        j = json.loads(o)
    except Exception:
        return {"verdict": "ERROR", "rc": rc, "err": (o + e)[-300:]}
    keep = ["verdict", "N", "limbs", "special", "limbBits", "specialBits", "log2Q", "log2QP", "digits", "minMarginBits",
            "firstModSize", "scalingModSize", "summary", "timeModel", "objective", "base"]
    return {k: j.get(k) for k in keep}


def job_bgvfm(env, prog, t, d):
    row = {"family": "BGV FIXEDMANUAL", "scheme": "bgv", "scal": "FIXEDMANUAL", "prog": prog, "t": t, "d": d}
    dflt = dict(scal="FIXEDMANUAL", depth=d, t=t)
    p = params_only(env, "bgv", dflt)
    r = run_and_check(env, "bgv", dict(dflt, prog=prog))
    row["default"] = {"cfg": dflt, "params": summary(p) if "error" not in p else p,
                      **{k: r.get(k) for k in ("worst", "k128", "valueCheck", "cleartextCheck", "error")}}
    if "x" not in r:
        return emit(env, "bgvfm", row)
    for tag, extra, kap in (("rec_any", ["--digits", "any"], None), ("rec_keep", ["--digits", "keep"], None),
                            ("rec_any_k128", ["--digits", "any", "--kappa", "128"], 128)):
        rec = recommend(env, r["x"], extra)
        ent = {"rec": rec}
        if rec.get("verdict") == "CERTIFIED":
            cfg = dict(scal="FIXEDMANUAL", depth=d, t=t, prog=prog, firstbits=rec["firstModSize"],
                       qbits=rec["scalingModSize"], dnum=rec["digits"], ringdim=rec["N"])
            e2e = run_and_check(env, "bgv", cfg, kappas=(kap,))
            m = "worst" if kap is None else f"k{kap}"
            ent["e2e"] = {"cfg": cfg, "valueCheck": e2e.get("valueCheck"), "cleartextCheck": e2e.get("cleartextCheck"),
                          "check": e2e.get(m), "error": e2e.get("error")}
            if "x" in e2e:
                j = json.load(open(e2e["x"]))
                lim = [str(l["q"] if isinstance(l, dict) else l) for l in j["params"]["limbs"]]
                spc = [str(l["q"] if isinstance(l, dict) else l) for l in j["params"]["special"]]
                ent["e2e"]["primesEqual"] = lim == rec.get("limbs")
                ent["e2e"]["specialEqual"] = spc == rec.get("special")
        row[tag] = ent
    emit(env, "bgvfm", row)


def parse_range(s):
    a, _, b = s.partition("-")
    return list(range(int(a), int(b or a) + 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("section", choices=["bgvfm", "bgvauto", "bfv"])
    ap.add_argument("--t", default="65537,786433")
    ap.add_argument("--depths", default="1-12")
    ap.add_argument("--progs", default="chain,poly")
    ap.add_argument("--workers", type=int, default=32)
    ap.add_argument("--families", default="")
    a = ap.parse_args()
    env = Env(a.out)
    ts = [int(x) for x in a.t.split(",")]
    ds = parse_range(a.depths)
    progs = a.progs.split(",")
    jobs = []
    if a.section == "bfv":
        fams = [f.split("/") for f in (a.families or "HPSPOVERQLEVELED/BV,HPSPOVERQLEVELED/HYBRID,HPSPOVERQ/BV,HPSPOVERQ/HYBRID,BEHZ/BV,BEHZ/HYBRID").split(",")]
        jobs = [(job_bfv, (env, m, k, p, t, d)) for m, k in fams for p in progs for t in ts for d in ds]
    elif a.section == "bgvauto":
        jobs = [(job_bgvauto, (env, s, p, t, d)) for s in (a.families or "FLEXIBLEAUTOEXT").split(",") for p in progs for t in ts for d in ds]
    else:
        jobs = [(job_bgvfm, (env, p, t, d)) for p in progs for t in ts for d in ds]
    # every context the searches will ask for, generated once (params-only runs, cached on disk)
    pre = []
    if a.section == "bfv":
        pre = [("bfv", c) for m, k in fams for t in ts for c in bfv_cands(m, k, t, max(ds))]
    elif a.section == "bgvauto":
        pre = [("bgv", dict(scal=s_, depth=c, t=t, evaladd=x, kscount=k)) for s_ in (a.families or "FLEXIBLEAUTOEXT").split(",")
               for t in ts for c in range(1, max(ds) + 3) for x in EVALADD for k in KSCOUNT]
    if pre:
        with ThreadPoolExecutor(max(a.workers, 64)) as ex:
            list(ex.map(lambda sc: params_only(env, sc[0], sc[1]), pre))
        print("params-only contexts:", len(pre), flush=True)
    jobs.sort(key=lambda j: -j[1][-1])  # deepest first
    with ThreadPoolExecutor(a.workers) as ex:
        fs = [ex.submit(f, *args) for f, args in jobs]
        for f in as_completed(fs):
            try:
                f.result()
            except Exception as e:  # keep going; the row is missing and the log says why
                import traceback
                print("JOB ERROR", repr(e), traceback.format_exc()[-600:], flush=True)


if __name__ == "__main__":
    main()
