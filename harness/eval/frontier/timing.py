#!/usr/bin/env python3
"""Measured evaluation time, OpenFHE default vs the certified settings of frontier.py (MEASURED).

  timing.py OUT [--sections bgvfm,bgvauto,bfv] [--reps 5] [--workers 4] [--maxload 20] [--only-high-load]

For every row of OUT/results/<section>.jsonl whose certified setting differs from the default, the
default, the cheapest certified (worst case) and the cheapest certified at kappa = 128 contexts
are timed with frontier_time (pristine OpenFHE v1.6.1, evaluation only, OMP_NUM_THREADS=1,
minimum of --reps runs after one warm-up). The three contexts of a row are run one after the
other (interleaved: default, certified, certified kappa, default, ...; two rounds), and the
1-minute load average is recorded before each process; a row measured above --maxload is flagged
(rerun it with --only-high-load when the machine is quieter). The timed context's primes are
asserted equal to the traced run's params.json, so the timed context is the certified one.
Writes OUT/results/timing.jsonl (one line per row; reruns append, the last line wins).
"""
import argparse, json, os, sys
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier_lib import Env, params_only, shape, sh, lib_args  # noqa: E402


def rowkey(r):
    return "|".join(str(r.get(k)) for k in ("family", "prog", "t", "d"))


def load_rows(out, section):
    p = os.path.join(out, "results", f"{section}.jsonl")
    rows = {}
    if os.path.exists(p):
        for l in open(p):
            r = json.loads(l)
            rows[rowkey(r)] = r
    return list(rows.values())


def configs(section, r):
    """(default cfg, certified worst cfg, certified kappa cfg) as driver configs (scheme, cfg) or None."""
    scheme = "bfv" if section == "bfv" else "bgv"
    prog, d = r["prog"], r["d"]
    dflt = r.get("default", {}).get("cfg")
    if not dflt:
        return None
    base = dict(dflt, prog=prog, progdepth=d)
    if section == "bgvfm":
        w = (r.get("rec_any") or {}).get("e2e", {}).get("cfg")
        k = (r.get("rec_any_k128") or {}).get("e2e", {}).get("cfg")
        kp = (r.get("rec_keep") or {}).get("e2e", {}).get("cfg")
        return scheme, base, w, k, kp
    best = (r.get("search") or {}).get("best") or {}
    w = best.get("worst")
    k = best.get("k128")
    w = dict(w["cfg"], prog=prog, progdepth=d) if w else None
    k = dict(k["cfg"], prog=prog, progdepth=d) if k else None
    return scheme, base, w, k, None


def time_one(env, scheme, cfg, reps):
    args = ["--scheme", scheme.upper()] + lib_args(scheme, cfg) + ["--reps", str(reps)]
    l0 = os.getloadavg()[0]
    rc, o, e = sh([os.path.join(env.bin, "frontier_time")] + args)
    try:
        j = json.loads(o.strip().splitlines()[-1])
    except Exception:
        return {"error": (o + e)[-300:], "load": l0}
    p = params_only(env, scheme, {k: v for k, v in cfg.items() if k not in ("prog", "progdepth")})
    N, q, s = shape(p)
    same = j["N"] == N and j["Q"] == [str(x) for x in q] and j["P"] == [str(x) for x in s]
    return {"minMs": j["minMs"], "medianMs": j["medianMs"], "N": j["N"], "limbs": len(j["Q"]), "special": len(j["P"]),
            "decryptsCorrectly": j["decryptsCorrectly"], "sameContextAsTraced": same, "load": l0}


def same_cfg(a, b):
    return a is not None and b is not None and lib_args("x", a) == lib_args("x", b)


def job(env, section, r, reps, rounds):
    c = configs(section, r)
    if not c:
        return None
    scheme, base, w, k, kp = c
    todo = {"default": base}
    for name, cfg in (("certWorst", w), ("certK128", k), ("certKeepDigits", kp)):
        if cfg is not None and not same_cfg(cfg, base):
            todo[name] = cfg
    if len(todo) == 1:
        return {"row": rowkey(r), "section": section, "identical": True}
    res = {n: [] for n in todo}
    for _ in range(rounds):
        for n, cfg in todo.items():
            res[n].append(time_one(env, scheme, cfg, reps))
    out = {"row": rowkey(r), "section": section, "cfgs": todo, "runs": res}
    best = {}
    for n, rs in res.items():
        ok = [x for x in rs if "minMs" in x]
        if ok:
            best[n] = min(x["minMs"] for x in ok)
    out["minMs"] = best
    out["maxLoad"] = max(x["load"] for rs in res.values() for x in rs)
    out["allSameContext"] = all(x.get("sameContextAsTraced") for rs in res.values() for x in rs if "minMs" in x)
    out["allDecrypt"] = all(x.get("decryptsCorrectly") for rs in res.values() for x in rs if "minMs" in x)
    if "default" in best:
        out["ratio"] = {n: best[n] / best["default"] for n in best if n != "default"}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--sections", default="bgvfm,bgvauto,bfv")
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--rounds", type=int, default=2)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--maxload", type=float, default=20.0)
    ap.add_argument("--only-high-load", action="store_true")
    ap.add_argument("--filter", default="", help="substring of the row key (family|prog|t|d)")
    a = ap.parse_args()
    env = Env(a.out)
    tp = os.path.join(a.out, "results", "timing.jsonl")
    done = {}
    if os.path.exists(tp):
        for l in open(tp):
            x = json.loads(l)
            done[x["row"]] = x
    jobs = []
    for s in a.sections.split(","):
        for r in load_rows(a.out, s):
            k = rowkey(r)
            if a.filter and a.filter not in k:
                continue
            if k in done and not (a.only_high_load and done[k].get("maxLoad", 0) > a.maxload):
                continue
            if a.only_high_load and k not in done:
                continue
            jobs.append((s, r))
    jobs.sort(key=lambda j: (j[1]["d"], j[0]))
    print("rows to time:", len(jobs), flush=True)

    def run(sr):
        s, r = sr
        x = job(env, s, r, a.reps, a.rounds)
        if x is None:
            return
        x["highLoad"] = x.get("maxLoad", 0) > a.maxload
        with open(tp, "a") as f:
            f.write(json.dumps(x) + "\n")
        print(x["row"], x.get("ratio"), "load", round(x.get("maxLoad", 0), 1), flush=True)
    with ThreadPoolExecutor(a.workers) as ex:
        list(ex.map(run, jobs))


if __name__ == "__main__":
    main()
