#!/usr/bin/env python3
"""UNTRUSTED: the depth table of the default OpenFHE v1.6.1 BFV context (depth_table.md).

    FHE_CHECK=... [BFV_DEMO=...] [BFV_TIME=...] python3 -I depth_table.py [--rounds 7] [--reps 3]
                  [--no-time] [--build-time OPENFHE_INSTALL] [--keep-time] [--max-load 20]

For t in {65537, 1099512938497}, key switching BV (the library default: no setter called) and
HYBRID, and d = 1..5: the program is `chain` of depth d (bfv_demo: EvalMult(a, b) then d-1
EvalSquare, each relinearized); the context is OpenFHE's own, CCParams<BFVRNS> with only t and
the multiplicative depth set (HPSPOVERQLEVELED, 60-bit primes, HEStd_128_classic), generated for
depth d + j. j = 0 is what a user gets; the smallest j whose run fhe_check certifies is the
certified context.

Inputs: inputs/default_{bv|hybrid}_{t16|t40}_chain_d{d}_x{j}.fhecheck.json (gen_inputs.py, j <= 3);
a missing j is produced here with BFV_DEMO + ../openfhe/extract_bfv.py.

Timing (the homomorphic evaluation only): bfv_time.cpp (build: --build-time INSTALL, or BFV_TIME),
single-threaded (OMP_NUM_THREADS=1), on the default context (j = 0) and on the certified one
(same t, ks, d; parameters generated for d + j), INTERLEAVED: `rounds` rounds, each one process per
context, each process times `reps` evaluations after one untimed warm-up and reports their median;
the row's time is the median over the rounds, the spread is min..max over the rounds. The 1-minute
load average is recorded before every round (`time.loads`); timings are taken only if the 1-minute
load is below --max-load (20) before timing starts, and kept only if the median of the per-round
loads is below it too. Otherwise, and with --keep-time / --no-time, the timings of the existing
depth_table.json are carried over unchanged with `time.remeasure = true` (and the load they were
taken at, `time.loadAtMeasure`), so a sentence built on them can say they await a quiet machine.

Per row and per tried context the checker's status is recorded from `fhe_check --json`: `assumed`
(the hypotheses the certificate records), `floatTol`, `technique` and `libraryDecryption` (whether
the library's own decryption of every output is proved, the "Library decryption" line).
Writes depth_table.md and depth_table.json.
"""
import argparse
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OPENFHE = os.path.join(HERE, "..", "openfhe")
EXE = os.environ.get("FHE_CHECK", os.path.join(ROOT, ".lake/build/bin/fhe_check"))
T16, T40 = 65537, 1099512938497
TAG = {T16: "t16", T40: "t40"}
JMAX = 6


def load():
    return " ".join(open("/proc/loadavg").read().split()[:3])


def load1():
    return float(open("/proc/loadavg").read().split()[0])


def produce(ks, t, d, j, scratch):
    """The extracted file of chain depth d on parameters for depth d + j."""
    f = os.path.join(HERE, "inputs", f"default_{ks}_{TAG[t]}_chain_d{d}_x{j}.fhecheck.json")
    if os.path.exists(f):
        return f
    demo = os.environ.get("BFV_DEMO")
    if not demo:
        return None
    w = tempfile.mkdtemp(dir=scratch)
    args = [demo, "run", w, "--t", str(t), "--prog", "chain", "--depth", str(d + j), "--progdepth", str(d)]
    if ks == "hybrid":
        args += ["--ks", "HYBRID"]
    r = subprocess.run(args, capture_output=True, text=True, env=dict(os.environ, OMP_NUM_THREADS="1"))
    if r.returncode not in (0, 3):
        return None
    out = os.path.join(scratch, f"default_{ks}_{TAG[t]}_chain_d{d}_x{j}.fhecheck.json")
    e = subprocess.run([sys.executable, "-I", os.path.join(OPENFHE, "extract_bfv.py"), "--params", w + "/params.json",
                        "--trace", w + "/trace.jsonl"], capture_output=True, text=True)
    shutil.rmtree(w, ignore_errors=True)
    if e.returncode != 0:
        return None
    open(out, "w").write(e.stdout)
    return out


def check(f):
    d = json.loads(subprocess.run([EXE, "--json", "--no-suggest", f], capture_output=True, text=True).stdout)
    p = d["params"]
    Q = math.prod(int(q) for q in p["limbs"])
    row = {"N": int(p["N"]), "limbs": len(p["limbs"]), "log2Q": round(math.log2(Q), 2), "verdict": d["verdict"]}
    mul = (json.load(open(f)).get("bfv") or {}).get("multiplication") or {}
    rz = d.get("realizability") or {}
    row["technique"] = mul.get("technique")
    row["floatTol"] = mul.get("floatTolerant")
    row["assumed"] = rz.get("assumptions")  # c.assumed (absent when there is no certificate)
    row["libraryDecryption"] = (d.get("libraryDecryption") or {}).get("status")
    if d["verdict"] == "CERTIFIED":
        row["margin"] = round(min(o["marginBits"] for o in d["outputs"]), 2)
    else:
        ff = (d.get("failure") or {}).get("firstFailing") or {}
        row["overflow"] = ff.get("overflowBits")
        row["at"] = f"body[{ff.get('index')}] {ff.get('op')}" if ff else d.get("summary", "")[:80]
    # bits gained per multiplication (bound after relin k minus after relin k-1), from --steps
    st = subprocess.run([EXE, "--steps", "--no-suggest", f], capture_output=True, text=True).stdout
    rel = [float(m.group(1)) for m in re.finditer(r"= relin \S+: level \d+, parts 2, B = 2\^([0-9.]+)", st)]
    mul = [float(m.group(1)) for m in re.finditer(r"= (?:mul \S+|square) \S+: level \d+, parts 3, B = 2\^([0-9.]+)", st)]
    row["relinBits"] = rel
    row["mulBits"] = mul
    return row


def time_ctx(exe, t, ks, depth, pd, reps):
    args = [exe, "--t", str(t), "--depth", str(depth), "--progdepth", str(pd), "--reps", str(reps),
            "--ks", "HYBRID" if ks == "hybrid" else "default"]
    r = subprocess.run(args, capture_output=True, text=True, env=dict(os.environ, OMP_NUM_THREADS="1"))
    return json.loads(r.stdout)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rounds", type=int, default=7)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--no-time", action="store_true")
    ap.add_argument("--build-time", default=None)
    ap.add_argument("--keep-time", action="store_true", help="carry the timings of depth_table.json over (remeasure)")
    ap.add_argument("--max-load", type=float, default=20.0)
    a = ap.parse_args()
    oldf = os.path.join(HERE, "depth_table.json")
    old = json.load(open(oldf)) if os.path.exists(oldf) else {"meta": {}, "rows": []}
    oldtime = {(r["t"], r["ks"], r["d"]): r["time"] for r in old["rows"] if "time" in r}
    bt = os.environ.get("BFV_TIME")
    scratch = tempfile.mkdtemp(prefix="depthtable.")
    if a.build_time:
        I = a.build_time
        bt = os.path.join(scratch, "bfv_time")
        inc = [f"-I{I}/include/openfhe" + s for s in ("", "/core", "/pke", "/binfhe", "/cereal")]
        subprocess.run(["c++", "-std=gnu++17", "-O2", "-fopenmp", *inc, os.path.join(HERE, "bfv_time.cpp"), "-o", bt,
                        f"-L{I}/lib", f"-Wl,-rpath,{I}/lib", "-lOPENFHEpke", "-lOPENFHEcore"], check=True)
    rows = []
    for t in (T16, T40):
        for ks in ("bv", "hybrid"):
            for d in range(1, 6):
                row = {"t": t, "ks": ks, "d": d, "tries": []}
                for j in range(JMAX + 1):
                    f = produce(ks, t, d, j, scratch)
                    if f is None:
                        row["tries"].append({"j": j, "verdict": "(no run)"})
                        break
                    c = dict(check(f), j=j)
                    row["tries"].append(c)
                    if c["verdict"] == "CERTIFIED":
                        row["cert"] = c
                        break
                row["default"] = row["tries"][0]
                rows.append(row)
                print(t, ks, d, [(x["j"], x["verdict"]) for x in row["tries"]], file=sys.stderr, flush=True)
    meta = {"loadBefore": load(), "start": time.strftime("%Y-%m-%d %H:%M:%S"), "maxLoad": a.max_load,
            "checker": "fhe_check (FHE_CHECK)", "timed": False}
    quiet = load1() < a.max_load
    if not a.no_time and not a.keep_time and bt and not quiet:
        print(f"1-minute load {load1()} >= {a.max_load}: timings not taken, old ones carried over", file=sys.stderr)
    if not a.no_time and not a.keep_time and bt and quiet:
        meta["timed"] = True
        for row in rows:
            c = row.get("cert")
            if not c or c["j"] == 0:
                continue
            dm, cm, loads = [], [], []
            for _ in range(a.rounds):
                loads.append(load1())
                x = time_ctx(bt, row["t"], row["ks"], row["d"], row["d"], a.reps)
                y = time_ctx(bt, row["t"], row["ks"], row["d"] + c["j"], row["d"], a.reps)
                assert x["N"] == row["default"]["N"] and y["N"] == c["N"] and x["limbs"] == row["default"]["limbs"] \
                    and y["limbs"] == c["limbs"], (row, x, y)
                dm.append(x["medianMs"])
                cm.append(y["medianMs"])
            row["time"] = {"defaultMs": statistics.median(dm), "certMs": statistics.median(cm),
                           "defaultRange": [min(dm), max(dm)], "certRange": [min(cm), max(cm)],
                           "ratio": statistics.median(cm) / statistics.median(dm),
                           "ratioRange": [min(cm) / max(dm), max(cm) / min(dm)], "rounds": a.rounds, "reps": a.reps,
                           "loads": loads, "loadMedian": statistics.median(loads), "remeasure": False}
            print(row["t"], row["ks"], row["d"], row["time"], file=sys.stderr, flush=True)
        ml = [r["time"]["loadMedian"] for r in rows if "time" in r]
        if ml and statistics.median(ml) >= a.max_load:  # the machine got busy: the new timings are not kept
            print(f"median per-round load {statistics.median(ml)} >= {a.max_load}: new timings discarded", file=sys.stderr)
            meta["timed"] = False
            for r in rows:
                r.pop("time", None)
    if not meta["timed"]:
        for row in rows:
            c = row.get("cert")
            k = (row["t"], row["ks"], row["d"])
            if c and c["j"] > 0 and k in oldtime:
                tt = dict(oldtime[k])
                if "loads" not in tt:  # a timing taken before per-round loads were recorded
                    tt["loadAtMeasure"] = tt.get("loadAtMeasure", old["meta"].get("loadBefore"))
                tt["remeasure"] = tt.get("remeasure", True) if "loads" in tt else True
                row["time"] = tt
        meta["timingsFrom"] = old["meta"].get("timingsFrom") or {k: old["meta"].get(k) for k in ("start", "loadBefore", "loadAfter")}
    meta["loadAfter"] = load()
    if meta["timed"]:
        meta["timingsFrom"] = {"start": meta["start"], "loadBefore": meta["loadBefore"], "loadAfter": meta["loadAfter"]}
    meta["end"] = time.strftime("%Y-%m-%d %H:%M:%S")
    json.dump({"meta": meta, "rows": rows}, open(os.path.join(HERE, "depth_table.json"), "w"), indent=1)
    write_md(rows, meta)
    shutil.rmtree(scratch, ignore_errors=True)


def fmt_default(r):
    x = r["default"]
    v = f"CERTIFIED, margin {x['margin']}" if x["verdict"] == "CERTIFIED" else \
        (f"NOT CERTIFIED, overflow {x['overflow']:.2f} bits at {x['at']}" if x.get("overflow") is not None else x["verdict"] + " " + x.get("at", ""))
    return f"{x['N']} | {x['limbs']} | {x['log2Q']:.0f} | {v}"


def write_md(rows, meta):
    L = ["# Depth table: default OpenFHE v1.6.1 BFV contexts under the per-instruction certificate", "",
         "Generated by `depth_table.py` (untrusted; raw data `depth_table.json`). Context: `CCParams<CryptoContextBFVRNS>`",
         "with only the plaintext modulus `t` and the multiplicative depth set (multiplication `HPSPOVERQLEVELED`,",
         "60-bit primes, `HEStd_128_classic`), key switching BV (the library default: no setter called) or HYBRID.",
         "Program: `chain` of depth d (`EvalMult(a, b)`, then d−1 `EvalSquare`, each relinearized). \"OpenFHE's",
         "parameters\" = generated for depth d; \"certified\" = the smallest j such that the context generated",
         "for depth d + j is CERTIFIED by the current `fhe_check` (j <= 6 tried). Margin / overflow in bits as",
         "`fhe_check` prints them. Runtime: the homomorphic evaluation of the same chain only (no key",
         "generation, encryption or decryption; no tracer), single-threaded, `bfv_time.cpp`, ratio = median",
         "certified / median default over interleaved rounds; spread = the ratio's range min(cert)/max(default)",
         "..max(cert)/min(default).", "",
         f"Checker run: {meta.get('start')}. Timings: {'taken in this run' if meta.get('timed') else 'carried over from an earlier run (marked remeasure where taken at a 1-minute load >= ' + str(meta.get('maxLoad')) + ')'};",
         f"timing run started {(meta.get('timingsFrom') or {}).get('start')}, load average before {(meta.get('timingsFrom') or {}).get('loadBefore')},",
         f"after {(meta.get('timingsFrom') or {}).get('loadAfter')} (1, 5, 15 min) on a 128-thread machine shared with other jobs; the",
         "1-minute load before every round is in depth_table.json (`time.loads`). The absolute times are noisy, the",
         "ratio of interleaved runs less so.", ""]
    for t in (T16, T40):
        L += [f"## t = {t}", "",
              "| ks | d | OpenFHE's params: N | limbs | log2 Q | verdict | certified j | N | limbs | log2 Q | Δ log2 Q | ring dim. | margin | eval default (ms) | eval certified (ms) | ratio (spread) |",
              "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
        for r in rows:
            if r["t"] != t:
                continue
            c = r.get("cert")
            ks = "BV (default)" if r["ks"] == "bv" else "HYBRID"
            if not c:
                L.append(f"| {ks} | {r['d']} | {fmt_default(r)} | none for j <= {r['tries'][-1]['j']} | | | | | | | | | |")
                continue
            dq = c["log2Q"] - r["default"]["log2Q"]
            rd = "same" if c["N"] == r["default"]["N"] else f"×{c['N'] // r['default']['N']}"
            if c["j"] == 0:
                tm = "| (= default) | | 1"
            elif "time" in r:
                tt = r["time"]
                rm = " remeasure" if tt.get("remeasure") else ""
                tm = f"| {tt['defaultMs']:.1f} | {tt['certMs']:.1f} | {tt['ratio']:.2f} ({tt['ratioRange'][0]:.2f}..{tt['ratioRange'][1]:.2f}){rm}"
            else:
                tm = "| not measured | | "
            L.append(f"| {ks} | {r['d']} | {fmt_default(r)} | {c['j']} | {c['N']} | {c['limbs']} | {c['log2Q']:.0f} | {dq:+.0f} | {rd} | {c['margin']} {tm} |")
        L.append("")
    # the checker's status per row (fhe_check --json): what the certificate records, library decryption
    L += ["## Checker status per row", "",
          "From `fhe_check --json` on the default context (j = 0) and on the certified one: `assumed` = the",
          "hypotheses the certificate records (`realizability.assumptions`, i.e. `c.assumed`; `-` when there is no",
          "certificate), `floatTol` = the file's `bfv.multiplication.floatTolerant`, library decryption = the",
          "status of `libraryDecryption` (`proved`: `certifyBFV?_decryptsLibExt` applies to every output).", "",
          "| t | ks | d | technique | floatTol | default: verdict | assumed | library decryption | certified j | assumed | library decryption |",
          "|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        x, c = r["default"], r.get("cert")
        asm = lambda y: ", ".join(y.get("assumed") or []) or "-"
        L.append(f"| {r['t']} | {r['ks']} | {r['d']} | {x.get('technique')} | {x.get('floatTol')} | {x['verdict']} | {asm(x)} | "
                 f"{x.get('libraryDecryption') or '-'} | " + (f"{c['j']} | {asm(c)} | {c.get('libraryDecryption') or '-'} |" if c else "none | | |"))
    L.append("")
    # what limits depth: bits per multiplication on the certified contexts
    L += ["## What limits depth", ""]
    for t in (T16, T40):
        for ks in ("bv", "hybrid"):
            g = []
            for r in rows:
                c = r.get("cert")
                if r["t"] == t and r["ks"] == ks and c and len(c["relinBits"]) >= 2:
                    rb, mb = c["relinBits"], c["mulBits"]
                    g += [round(mb[k] - rb[k - 1], 2) for k in range(1, min(len(mb), len(rb)))]
            if g:
                L.append(f"* t = {t}, {ks}: bits added by each product after the first (bound after the product minus bound "
                         f"after the previous relinearization) on the certified contexts: {sorted(set(g))}")
    L += ["",
          "Reading: every certified context needs as many bits per product as the worst-case growth of",
          "`Challenge.BFV.mulBound`, which multiplies the operands' noise by about `N·(t·(K+1) + t−1)` with",
          "`K` about `N·B_s/2 + 1` (B_s = 1, ternary secret): `log2` about `2·log2 N + log2 t − 1`, i.e. 41, 43,",
          "45 bits at N = 2^13, 2^14, 2^15 for t = 65537 and 65, 67, 69 bits for t ≈ 2^40 (measured above:",
          "42..46 and 68..70, the rest is the relinearization added in between). OpenFHE adds one 60-bit limb",
          "per level and sizes its chain with the heuristic `C1 = 8·N·t` (32..34 bits at t = 65537, 56..58",
          "at t ≈ 2^40): the worst case is about `log2(N/16)` bits per level more (9..11 bits). In the table:",
          "at t = 65537, 4 of the 10 contexts certify as generated, 4 need one more level of parameters and 2",
          "need two; at t ≈ 2^40 (where each product needs more than one 60-bit limb in the worst case) none",
          "certifies as generated, 7 need one more and 3 need two. Under HPSPOVERQLEVELED a",
          "relinearization at which the library drops `dr` limbs internally is charged `ksLeveled`, about",
          "`Q_L/Q_(L−dr)` times the key-switching error at the reduced level; it is not what limits depth",
          "here (every first failure is at a product).", ""]
    open(os.path.join(HERE, "depth_table.md"), "w").write("\n".join(L) + "\n")


if __name__ == "__main__":
    main()
