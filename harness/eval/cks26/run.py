#!/usr/bin/env python3
"""UNTRUSTED orchestration of the CKS26 evaluation (harness/eval/cks26). See run.sh.

    run.py [--jobs J] [--stage A,B,...] [--force]

Runs the driver cks26 (OpenFHE v1.6.1 + tracer), extracts every trace with
harness/frontend/openfhe/extract_bfv.py, runs fhe_check, and writes for every case NAME
    out/NAME.summary.json    what was run, the extractor's answer on the trace as traced, whether
                             relabel cross-check (relabel.py), fhe_check's verdict line
                             verbatim, exit code, first failing instruction, bounds, per-step
                             bounds, and the driver's measurements (measure.json)
    cases/NAME.fhecheck.json.gz  the file fhe_check was run on (headline cases only)
Working files (traces, parameters) go to harness/build/cks26/runs/NAME (gitignored). A case whose
summary exists is not re-run unless --force. Stages:
    A  the attack circuits at the paper's K
    B  the same circuits at K' and K'+1 (K' = number of steps before the first failing instruction)
    C  repeated runs of the pt-ct circuit at N = 2^12, 2^13 (their outputs are not part of this release)
    D  cost of certified parameters
Nothing here is trusted; the verdicts are fhe_check's.
"""
import argparse
import concurrent.futures as cf
import gzip
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
BUILD = os.path.join(ROOT, "harness", "build", "cks26")
RUNS = os.path.join(BUILD, "runs")
OUT = os.path.join(HERE, "out")
CASES = os.path.join(HERE, "cases")
DRV = os.path.join(BUILD, "cks26")
FHE = os.environ.get("FHE_CHECK", os.path.join(ROOT, ".lake", "build", "bin", "fhe_check"))
EXTRACT = os.path.join(ROOT, "harness", "frontend", "openfhe", "extract_bfv.py")
RELABEL = os.path.join(HERE, "relabel.py")
ENV = dict(os.environ, OMP_NUM_THREADS="1")
# the probabilistic fresh-noise modes run on every checked file (fhe_check --kappa K; BFV since main 2515320)
KAPPAS = (128, 64, 40)
ONLY = None
# --reuse-traces: re-extract and re-check the runs in harness/build/cks26/runs instead of re-running OpenFHE
REUSE_TRACES = False

# Table 3 of the paper: (log N, t). Context and K, c as the attack code derives them (cks26.cpp).
PTCT_ROWS = [(12, 786433), (13, 4194305), (14, 67108865), (15, 33423361), (16, 1048577)]
# Paper Table 3, for comparison only: log N -> (d_leg, d_atk, log2 ||mu||, log2 |mu(omega)|)
PAPER_T3 = {12: (8, 8, 18.6, 28.9), 13: (7, 7, 21, 32.4), 14: (6, 6, 25, 37.4), 15: (6, 6, 24, 37.3), 16: (7, 7, 18.9, 33.2)}
# Attack 3 parameter sets: name -> (t, SetMultiplicativeDepth, K of phase 1, K of phases 2/3, rho, description)
CTCT_SETS = {
    "e3_t1153": (1153, 45, 45, 44, 8737706, "App. E.3, t = 1153: `indcpad_ctct 1153 45 8.15 262144 8737706` (bound of OpenFHE >= v1.4.2.4)"),
    "e3_t257": (257, 48, 48, 47, 189000000000, "App. E.3, t = 257: `indcpad_ctct 257 48 7.93 262144 189000000000`"),
    "s52_d34": (786433, 34, 35, 34, 24800, "Section 5.2 modulus (N = 2^16, 26 primes of 52 bits; `indcpad_ctct 786433 35 4.5 262144 24800` on OpenFHE v1.3.0), "
                                          "which v1.6.1 generates for depth 34; K as in the paper (35 and 34)"),
    "s52_d35": (786433, 35, 35, 34, 24800, "the Section 5.2 command on v1.6.1's own parameter generation (depth 35)"),
}


def dump(obj, path):
    """Compact JSON, one line: the committed summaries stay small."""
    with open(path, "w") as f:
        json.dump(obj, f, separators=(",", ":"))
        f.write("\n")


def case_gz(name):
    return os.path.join(CASES, name + ".fhecheck.json.gz")


def save_case(name, prog):
    """Commit the checked file gzip-compressed (deterministic: no name, mtime 0)."""
    with open(prog, "rb") as f, open(case_gz(name), "wb") as g:
        with gzip.GzipFile(filename="", mode="wb", fileobj=g, mtime=0) as z:
            z.write(f.read())


def case_file(name):
    """A plain copy of a committed case under harness/build/cks26/tmp (None if there is none)."""
    if not os.path.exists(case_gz(name)):
        return None
    d = os.path.join(BUILD, "tmp")
    os.makedirs(d, exist_ok=True)
    out = os.path.join(d, name + ".fhecheck.json")
    with gzip.open(case_gz(name), "rb") as z, open(out, "wb") as f:
        f.write(z.read())
    return out


def sh(cmd, **kw):
    return subprocess.run(cmd, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, **kw)


def log2int(s):
    n = int(s)
    return math.log2(n) if n > 0 else float("-inf")


def fhe_check(path):
    """Verdict line verbatim, exit code, JSON report, and the per-step bounds of the text report."""
    t0 = time.time()
    txt = sh([FHE, "--steps", "--no-suggest", path])
    js = sh([FHE, "--json", "--no-suggest", path])
    secs = (time.time() - t0) / 2
    rep = json.loads(js.stdout)
    line = txt.stdout.split("\n")[1] if txt.stdout.startswith("fhe_check:") else txt.stdout.split("\n")[0]
    steps = []
    for m in re.finditer(r"^\s+\[(\d+)\] (\S+) = (\w+)[^\n]*?B = 2\^([0-9.]+)(, margin ([0-9.]+) bits|, DECRYPTION CONDITION FAILS)?", txt.stdout, re.M):
        steps.append({"i": int(m.group(1)), "dst": m.group(2), "op": m.group(3), "log2B": float(m.group(4)),
                      "ok": m.group(5) is not None and "margin" in m.group(5)})
    res = {"verdictLine": line, "exit": txt.returncode, "verdict": rep.get("verdict"), "seconds": round(secs, 2),
           "realizability": rep.get("realizability"), "steps": steps,
           "params": {k: rep["params"].get(k) for k in ("N", "t", "log2Q")} if "params" in rep else None,
           "limbs": len(rep["params"]["limbs"]) if "params" in rep else None,
           "special": len(rep["params"]["special"]) if "params" in rep else None,
           "inputNoise": (rep.get("assumptions") or {}).get("inputNoise"),
           "budget": {k: (rep.get("budget") or {}).get(k) for k in ("keySwitch", "mulLift", "mulRound", "slacksProved", "roundSlackRho")}}
    if rep.get("failure"):
        ff = rep["failure"].get("firstFailing") or {}
        res["failure"] = {k: ff.get(k) for k in ("index", "instr", "op", "overflowBits", "boundLog2", "maxBoundLog2", "bound")}
        res["failure"]["reason"] = rep["failure"].get("reason")
    if rep.get("outputs"):
        res["outputs"] = [{k: o.get(k) for k in ("name", "boundLog2", "maxBoundLog2", "marginBits", "bound", "level")} for o in rep["outputs"]]
    if rep.get("summary"):
        res["summaryText"] = rep["summary"]
    res["certificateTheorem"] = rep.get("certificateTheorem")
    res["kappa"] = {}
    for k in KAPPAS:
        kt = sh([FHE, "--no-suggest", "--kappa", str(k), path])
        kj = json.loads(sh([FHE, "--json", "--no-suggest", "--kappa", str(k), path]).stdout)
        kl = [x for x in kt.stdout.splitlines() if x.startswith("VERDICT")]
        r = {"exit": kt.returncode, "verdictLine": kl[0] if kl else kt.stdout[:200], "certificateTheorem": kj.get("certificateTheorem")}
        if kj.get("failure"):
            ff = kj["failure"].get("firstFailing") or {}
            r["failure"] = {x: ff.get(x) for x in ("index", "op", "overflowBits", "boundLog2", "maxBoundLog2")}
        if kj.get("outputs"):
            r["outputs"] = [{x: o.get(x) for x in ("name", "boundLog2", "marginBits")} for o in kj["outputs"]]
        res["kappa"][str(k)] = r
    return res


def extract(params, trace, out):
    r = sh([sys.executable, "-I", EXTRACT, "--params", params, "--trace", trace])
    with open(out, "w") as f:
        f.write(r.stdout)
    try:
        doc = json.loads(r.stdout)
    except ValueError:
        return None, f"extractor crashed: {r.stderr[-300:]}"
    return doc, doc.get("error")


def run_case(name, args, force=False, keep_case=False, check=True):
    """One driver run + extraction + fhe_check. Returns the summary (also written to out/)."""
    spath = os.path.join(OUT, name + ".summary.json")
    if os.path.exists(spath) and not force:
        return json.load(open(spath))
    d = os.path.join(RUNS, name)
    old = os.path.join(OUT, name + ".summary.json.prev")
    if REUSE_TRACES and os.path.exists(os.path.join(d, "measure.json")) and os.path.exists(old):
        # re-extract and re-check the OpenFHE run already made for this case (same trace, same measurements);
        # used after a change of the extractor or of fhe_check only
        prev = json.load(open(old))
        assert prev["driverArgs"] == [str(a) for a in args], name
        r = subprocess.CompletedProcess([], 0, "", "")
        summ = {"name": name, "driverArgs": prev["driverArgs"], "driverSeconds": prev["driverSeconds"], "traceReused": True}
    else:
        shutil.rmtree(d, ignore_errors=True)
        os.makedirs(d)
        t0 = time.time()
        r = sh([DRV, args[0], d] + [str(a) for a in args[1:]])
        summ = {"name": name, "driverArgs": [str(a) for a in args], "driverSeconds": round(time.time() - t0, 1)}
    if r.returncode != 0:
        summ["driverError"] = (r.stderr or r.stdout)[-600:].replace(ROOT, "<repo>")
        dump(summ, spath)
        return summ
    summ["measure"] = json.load(open(os.path.join(d, "measure.json")))
    if summ["measure"]["mode"] == "ctct":
        # the exact noises of the squaring circuits are 400-digit integers per step and only their size is used
        for st in summ["measure"]["steps"]:
            st["log2Noise"] = round(log2int(st.pop("noise")), 4)
    if check:
        prog = os.path.join(d, "prog.fhecheck.json")
        doc, err = extract(os.path.join(d, "params.json"), os.path.join(d, "trace.jsonl"), prog)
        summ["extract"] = "ok" if not err else err
        if not err and summ["measure"]["enc"] == "coef":
            # cross-check only: the same trace with its CoefPacked plaintexts relabelled packed (relabel.py) must
            # extract to the same parameters and program (the native extraction adds a derivation note)
            n = sh([sys.executable, "-I", RELABEL, os.path.join(d, "trace.jsonl"), os.path.join(d, "trace.relabel.jsonl")])
            rel, rerr = extract(os.path.join(d, "params.json"), os.path.join(d, "trace.relabel.jsonl"), os.path.join(d, "prog.relabel.json"))
            nd = dict(doc["noiseDerivation"])
            cp = nd.pop("coefPackedPlaintexts", None)
            summ["coefPackedPlaintexts"] = len(cp["ids"]) if cp else 0
            summ["relabelCrossCheck"] = {"records": int(n.stdout.strip()),
                                         "identical": bool(not rerr and nd == rel["noiseDerivation"] and
                                                           all(doc[k] == rel[k] for k in doc if k != "noiseDerivation"))}
            os.unlink(os.path.join(d, "trace.relabel.jsonl"))
        if not err:
            summ["instructions"] = len(doc["program"]["body"])
            summ["ops"] = {}
            for i in doc["program"]["body"]:
                summ["ops"][i["op"]] = summ["ops"].get(i["op"], 0) + 1
            summ["freshInputs"] = sum(1 for i in doc["program"]["inputs"] if i["parts"] == 2)
            summ["limbBits"] = sorted({int(x["q"]).bit_length() for x in doc["params"]["limbs"]})
            summ["specialBits"] = [int(x["q"]).bit_length() for x in doc["params"]["special"]]
            summ["technique"] = doc["bfv"]["multiplication"]["technique"]
            summ["keySwitch"] = doc["source"]["keySwitchTechnique"]
            summ["fheCheck"] = fhe_check(prog)
            summ["programSha256"] = sh(["sha256sum", prog]).stdout.split()[0]
            if keep_case:
                save_case(name, prog)
    dump(summ, spath)
    return summ


def steps_before_index(summ, unit_op, idx):
    """Number of complete steps (instructions `unit_op`) before instruction `idx` of the checked program.
    Read from the program itself: the --steps diagnostic stops at the worst-case failure, and a --kappa
    failure can lie beyond it."""
    body = json.load(open(os.path.join(RUNS, summ["name"], "prog.fhecheck.json")))["program"]["body"]
    return sum(1 for i in body[:idx] if i["op"] == unit_op)


def steps_before_failure(summ, unit_op):
    """K' = number of completed steps (instructions `unit_op`) before the first failing instruction."""
    fc = summ["fheCheck"]
    if fc["exit"] == 0:
        return None
    idx = fc["failure"]["index"]
    return sum(1 for s in fc["steps"] if s["op"] == unit_op and s["i"] < idx)


def pmap(jobs, tasks):
    """tasks: list of (name, args, kwargs). Runs them with at most `jobs` drivers at once."""
    res = {}
    if ONLY:
        tasks = [x for x in tasks if re.search(ONLY, x[0])]
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(run_case, n, a, **kw): n for n, a, kw in tasks}
        for f in cf.as_completed(futs):
            n = futs[f]
            res[n] = f.result()
            s = res[n]
            v = s.get("fheCheck", {}).get("verdictLine", s.get("driverError", s.get("extract", "measured")))
            print(f"[{time.strftime('%H:%M:%S')}] {n}: {str(v)[:110]}", flush=True)
    return res


def ptct_args(logn, t, extra=()):
    return ["ptct", "--logn", logn, "--t", t] + list(extra)


def stage_a(jobs, force):
    tasks = []
    for logn, t in PTCT_ROWS:
        tasks.append((f"ptct_n{logn}_coef", ptct_args(logn, t, ["--enc", "coef"]), dict(force=force, keep_case=True)))
        if (t - 1) % (2 << logn) == 0 and all(t % p for p in range(2, int(t ** 0.5) + 1)):
            tasks.append((f"ptct_n{logn}_packed", ptct_args(logn, t, ["--enc", "packed"]), dict(force=force, keep_case=True)))
    for name, (t, depth, k1, k23, rho, _) in CTCT_SETS.items():
        enc = "packed" if t == 786433 else "coef"
        tasks.append((f"ctct_{name}_p1", ["ctct", "--t", t, "--depth", depth, "--K", k1, "--enc", enc], dict(force=force, keep_case=True)))
        # phases 2/3: the linear combination with C = rho * t over M = 64 encryptions, then K23 squarings
        tasks.append((f"ctct_{name}_p23_m64", ["ctct", "--t", t, "--depth", depth, "--K", k23, "--enc", enc,
                                              "--lincomb", 64, "--rho", rho, "--mu", "H"], dict(force=force, keep_case=True)))
    # the same linear combination with fewer encryptions (the bound of the sum depends on C, not on M)
    tasks.append(("ctct_e3_t1153_p23_m8", ["ctct", "--t", 1153, "--depth", 45, "--K", 44, "--enc", "coef",
                                          "--lincomb", 8, "--rho", 8737706, "--mu", "H"], dict(force=force)))
    # subset sums of a pool of fresh encryptions of 0 before every squaring
    tasks.append(("ctct_e3_t1153_p1_pool20", ["ctct", "--t", 1153, "--depth", 45, "--K", 45, "--enc", "coef", "--pool", 20], dict(force=force)))
    # the same context and circuit with OpenFHE's integer-only technique BEHZ (not what the attack code selects)
    tasks.append(("ctct_e3_t1153_p1_behz", ["ctct", "--t", 1153, "--depth", 45, "--K", 45, "--enc", "coef", "--mult", "BEHZ"], dict(force=force, keep_case=True)))
    # the CoefPacked variant where a packed one exists (relabelling must not change anything)
    tasks.append(("ctct_s52_d34_p1_coef", ["ctct", "--t", 786433, "--depth", 34, "--K", 35, "--enc", "coef"], dict(force=force)))
    return pmap(jobs, tasks)


def stage_b(jobs, force):
    tasks = []
    for f in sorted(os.listdir(OUT)):
        if not f.endswith(".summary.json") or "_K" in f or f.startswith(("gt_", "cost_")):
            continue
        s = json.load(open(os.path.join(OUT, f)))
        if "fheCheck" not in s or s["fheCheck"]["exit"] != 1:
            continue
        ptct = s["driverArgs"][0] == "ptct"
        kp = steps_before_failure(s, "mulPlain" if ptct else "relin")
        base = [a for a in s["driverArgs"]]
        if "--K" in base:
            i = base.index("--K")
            del base[i:i + 2]
        if ptct:  # keep the attack's constant: it is derived from the context, not from K, but be explicit
            base += ["--c", s["measure"]["c"]]
        for k, tag in ((kp, "Kp"), (kp + 1, "Kp1")):
            if k >= 1:
                tasks.append((f"{s['name']}_{tag}", base + ["--K", k], dict(force=force, keep_case=(tag == "Kp"))))
        # the largest K certified under --kappa, where it differs from the worst case: confirmed by real runs too
        unit = "mulPlain" if ptct else "relin"
        for kk, r in s["fheCheck"].get("kappa", {}).items():
            if r["exit"] == 1 and r.get("failure"):
                kpk = steps_before_index(s, unit, r["failure"]["index"])
                if kpk != kp:
                    for k, tag in ((kpk, f"Kpk{kk}"), (kpk + 1, f"Kpk{kk}p1")):
                        if k >= 1:
                            tasks.append((f"{s['name']}_{tag}", base + ["--K", k], dict(force=force)))
    res = pmap(jobs, tasks)
    # The first failing instruction bounds K' from above only: a prefix whose noise bound passes every
    # step can still be refused at its output (e.g. for OpenFHE's binary64 decryption of large t). Go
    # down one step at a time, in every mode, until a run is certified (runs named NAME_Kpm1, _Kpm2, ...).
    modes = ["worst"] + [str(k) for k in KAPPAS]
    for rnd in range(5):
        more = []
        for name, (base, kp) in confirm_bases().items():
            runs = confirm_runs(name)
            for mode in modes:
                ok = [k for k, r in runs.items() if mode_exit(r, mode) == 0]
                if ok or not runs:
                    continue
                # one step down at a time; after three rounds, straight to a single step (K = 1)
                k = min(runs) - 1 if rnd < 3 and len(runs) < 8 else 1
                if k >= 1 and k not in runs:
                    more.append((f"{name}_Kpm{kp - k}", base + ["--K", k], dict(force=force)))
        more = list({t[0]: t for t in more}.values())
        if not more:
            break
        res.update(pmap(jobs, more))
    return res


def mode_exit(summ, mode):
    fc = summ["fheCheck"]
    return fc["exit"] if mode == "worst" else fc["kappa"][mode]["exit"]


def confirm_bases():
    """name -> (driver arguments without --K, worst-case K' from the first failing instruction) for the
    attack-depth cases that stage B confirms."""
    out = {}
    for f in sorted(os.listdir(OUT)):
        if not f.endswith(".summary.json") or "_K" in f or f.startswith(("gt_", "cost_")):
            continue
        s = json.load(open(os.path.join(OUT, f)))
        if "fheCheck" not in s or s["fheCheck"]["exit"] != 1:
            continue
        ptct = s["driverArgs"][0] == "ptct"
        base = list(s["driverArgs"])
        if "--K" in base:
            i = base.index("--K")
            del base[i:i + 2]
        if ptct:
            base += ["--c", s["measure"]["c"]]
        out[s["name"]] = (base, steps_before_failure(s, "mulPlain" if ptct else "relin"))
    return out


def confirm_runs(name):
    """K -> summary of every confirmation run of case `name` (NAME_Kp, _Kp1, _Kpm*, _Kpk*)."""
    runs = {}
    for f in os.listdir(OUT):
        if f.startswith(name + "_K") and f.endswith(".summary.json"):
            s = json.load(open(os.path.join(OUT, f)))
            if "fheCheck" in s:
                runs[s["measure"]["K"]] = s
    return runs


def stage_c(jobs, force):
    tasks = []
    for logn, t in PTCT_ROWS[:2]:
        for k in (1, 2, 7, 100):
            for seed in range(10):
                tasks.append((f"gt_n{logn}_k{k}_r{seed}", ptct_args(logn, t, ["--enc", "coef", "--idx", k]), dict(force=force, check=False)))
    return pmap(jobs, tasks)


def transplant(base, small):
    """The program of `base` (a real extraction) on the parameters of `small` (a real extraction of a
    shorter run of the same circuit on another context): everything that depends on the context
    (params, keySwitching, bfv.multiplication, noise derivation) is `small`'s, the program is
    `base`'s with every level set to `small`'s number of limbs. Used ONLY to search for the depth to
    try; the depth found is then run in full and extracted for real."""
    doc = json.loads(json.dumps(small))
    l_old, l_new = len(base["params"]["limbs"]), len(small["params"]["limbs"])
    prog = json.loads(json.dumps(base["program"]))
    for i in prog["inputs"]:
        assert i["level"] == l_old
        i["level"] = l_new
    for ins in prog["body"]:
        if "expect" in ins:
            assert ins["expect"]["level"] == l_old
            ins["expect"]["level"] = l_new
    doc["program"] = prog
    doc["bfv"]["encryption"]["inputs"] = base["bfv"]["encryption"]["inputs"]
    if "freshEncryption" in base:  # which inputs are fresh encryptions: the base program's
        doc["freshEncryption"]["inputs"] = base["freshEncryption"]["inputs"]
    doc["provenance"] = [{"note": "synthetic: program of another run transplanted onto these parameters (harness/eval/cks26/run.py transplant)"}]
    return doc


def ctct_cost(name, force):
    """Smallest SetMultiplicativeDepth D' >= depth for which the phase-1 circuit with the attack's K
    squarings is CERTIFIED. Search: bisection over D' with a 2-squaring run per D' (real context,
    real extraction, timing) and the K-squaring program transplanted onto it; then the full circuit
    is run at the D' found."""
    t, depth, k1, _, _, _ = CTCT_SETS[name]
    enc = "packed" if t == 786433 else "coef"
    base = json.load(open(case_file(f"ctct_{name}_p1")))  # written by stage A (keep_case)
    log = []

    def probe(D):
        nm = f"cost_ctct_{name}_probe_d{D}"
        s = run_case(nm, ["ctct", "--t", t, "--depth", D, "--K", 2, "--enc", enc, "--time", 3], force=force)
        if "fheCheck" not in s:
            raise SystemExit(f"{nm}: {s.get('driverError') or s}")
        if "synthetic" not in s:
            small = json.load(open(os.path.join(RUNS, nm, "prog.fhecheck.json")))
            syn = os.path.join(RUNS, nm, "synthetic.fhecheck.json")
            json.dump(transplant(base, small), open(syn, "w"))
            s["synthetic"] = fhe_check(syn)
            s["synthetic"]["K"] = k1
            if D == depth:  # the transplant onto the base context must reproduce the real extraction
                synd = json.load(open(syn))
                s["transplantReproducesBase"] = all(base[k] == synd[k] for k in base if k not in ("provenance", "crossCheck"))
            dump(s, os.path.join(OUT, nm + ".summary.json"))
        if D == depth and not s.get("transplantReproducesBase"):
            raise SystemExit(f"{nm}: the transplanted program does not reproduce the real extraction on the base context")
        if s["synthetic"]["exit"] not in (0, 1) or (s["synthetic"]["exit"] == 1 and not s["synthetic"].get("failure", {}).get("index")):
            raise SystemExit(f"{nm}: the transplanted program is not analysed: {s['synthetic']['verdictLine'][:200]}")
        ok = s["synthetic"]["exit"] == 0
        log.append((D, s["measure"]["N"], s["measure"]["sizeQ"], ok))
        print(f"  {nm}: N={s['measure']['N']} limbs={s['measure']['sizeQ']} synthetic K={k1}: {s['synthetic']['verdictLine'][:60]}", flush=True)
        return ok

    lo, hi = depth, 2 * depth
    assert not probe(lo)
    while not probe(hi):
        hi += depth // 2
        if hi > 4 * depth:
            raise SystemExit(f"cost_ctct_{name}: no certified depth up to {hi}")
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if probe(mid):
            hi = mid
        else:
            lo = mid
    full = run_case(f"cost_ctct_{name}_full_d{hi}", ["ctct", "--t", t, "--depth", hi, "--K", k1, "--enc", enc], force=force, keep_case=True)
    res = {"name": name, "t": t, "baseDepth": depth, "K": k1, "smallestCertifiedDepthSynthetic": hi, "largestRefusedDepthSynthetic": lo,
           "probes": sorted(log), "fullRun": f"cost_ctct_{name}_full_d{hi}",
           "fullRunVerdict": full.get("fheCheck", {}).get("verdictLine", full.get("driverError"))}
    dump(res, os.path.join(OUT, f"cost_ctct_{name}.result.json"))
    print(f"[{time.strftime('%H:%M:%S')}] cost_ctct_{name}: D'={hi}: {res['fullRunVerdict']}", flush=True)
    return res


def stage_d(jobs, force):
    """Cost of certified parameters: the smallest SetMultiplicativeDepth (searched upward) for which the
    attack's K steps are CERTIFIED, at the row's N and with OpenFHE choosing N at 128 bits."""
    # pt-ct: the row's K and c, on parameters generated for a larger depth
    tasks = []
    for logn, t in PTCT_ROWS:
        base = json.load(open(os.path.join(OUT, f"ptct_n{logn}_coef.summary.json")))
        K, c = base["measure"]["K"], base["measure"]["c"]
        for D in range(4, 9):
            tasks.append((f"cost_ptct_n{logn}_sameN_d{D}", ptct_args(logn, t, ["--enc", "coef", "--depth", D, "--K", K, "--c", c, "--time", 101]), dict(force=force)))
            tasks.append((f"cost_ptct_n{logn}_sec128_d{D}", ["ptct", "--t", t, "--sec", "128", "--enc", "coef", "--depth", D, "--K", K, "--c", c, "--time", 101], dict(force=force)))
    pmap(min(jobs, 2), tasks)  # timed runs: keep the machine quiet
    # ct-ct
    names = [n for n in ("e3_t1153", "e3_t257", "s52_d34") if not ONLY or re.search(ONLY, "cost_ctct_" + n)]
    with cf.ThreadPoolExecutor(max_workers=1) as ex:  # one at a time: the probes are timed
        list(ex.map(lambda n: ctct_cost(n, force), names))


def lincomb_program(base, M, C, K):
    """SYNTHETIC fhe-check/v1 file: the phases-2/3 circuit with M fresh encryptions on the parameters
    of the real extraction `base` (ciphertexts are not computed). Same shape as cks26.cpp builds for
    --lincomb: the sum of the M encryptions, q*(sum) by double-and-add (q = C div M) plus the sum of
    the first C mod M, then K times (add a fresh encryption, mul, relin)."""
    doc = json.loads(json.dumps(base))
    L = len(base["params"]["limbs"])
    inputs, body, fresh = [], [], []
    n = [0]

    def new_input():
        n[0] += 1
        nm = f"in_{n[0]}"
        inputs.append({"name": nm, "parts": 2, "level": L, "key": 1})
        fresh.append(nm)
        return nm

    def emit(op, **kw):
        n[0] += 1
        dst = f"v_{n[0]}"
        body.append({"op": op, "dst": dst, **kw})
        return dst

    q, r = divmod(C, M)
    allsum, pre = None, None
    for i in range(M):
        ci = new_input()
        allsum = ci if allsum is None else emit("add", a=allsum, b=ci)
        if i + 1 == r:
            pre = allsum
    acc = None
    for b in range(q.bit_length() - 1, -1, -1):
        if acc is not None:
            acc = emit("add", a=acc, b=acc)
        if (q >> b) & 1:
            acc = allsum if acc is None else emit("add", a=acc, b=allsum)
    ct = acc if pre is None else emit("add", a=acc, b=pre)
    for _ in range(K):
        x = emit("add", a=ct, b=new_input())
        ct = emit("relin", a=emit("mul", a=x, b=x))
    doc["program"] = {"inputs": inputs, "body": body, "outputs": [ct]}
    doc["bfv"]["encryption"]["inputs"] = fresh
    if "freshEncryption" in doc:
        doc["freshEncryption"]["inputs"] = fresh
    doc["provenance"] = [{"note": "synthetic: no ciphertext was computed (harness/eval/cks26/run.py lincomb_program)"}]
    return doc


def stage_e(jobs, force):
    """Modes and limits: --kappa, recommend, the instruction limit at the paper's M = 2^18; provenance."""
    rows = []

    def row(what, label, cmd, timeout=None):
        t0 = time.time()
        try:
            r = sh(cmd, timeout=timeout)
        except subprocess.TimeoutExpired:
            rows.append({"what": what, "input": label, "line": f"no answer within {timeout} s (killed)", "exit": "-"})
            return
        lines = [x for x in r.stdout.splitlines() if x.startswith(("VERDICT", "RECOMMENDATION"))]
        rows.append({"what": what, "input": label, "line": (lines[0] if lines else r.stdout[:200]).replace(ROOT, "<repo>"), "exit": r.returncode,
                     "seconds": round(time.time() - t0, 1)})

    for case in ("ptct_n12_coef_Kp", "ptct_n12_coef", "ctct_e3_t1153_p1_Kp", "ctct_e3_t1153_p1"):
        f = case_file(case)
        if f:
            for k in (128, 40):
                row(f"`fhe_check --kappa {k}`", f"cases/{case}.fhecheck.json.gz", [FHE, "--kappa", str(k), "--no-suggest", f])
            row("`fhe_check recommend`", f"cases/{case}.fhecheck.json.gz", [FHE, "recommend", f])
    # the instruction limit: applied to a BGV file, not applied to a BFV file
    f = case_file("ptct_n12_coef_Kp")
    if f:
        row("`fhe_check --max-instructions 3` on a BFV file of 6 instructions", "cases/ptct_n12_coef_Kp.fhecheck.json.gz", [FHE, "--max-instructions", "3", "--no-suggest", f])
    g = os.path.join(ROOT, "harness", "frontend", "examples", "openfhe_depth2_fixedmanual.fhecheck.json")
    row("`fhe_check --max-instructions 3` on a BGV file of 6 instructions (for contrast)", "harness/frontend/examples/openfhe_depth2_fixedmanual.fhecheck.json",
        [FHE, "--max-instructions", "3", "--no-suggest", g])
    # the paper's M = 2^18 encryptions in phases 2/3 (synthetic program on the real E.3 parameters)
    basef = case_file("ctct_e3_t1153_p23_m64")  # written by stage A (keep_case)
    if basef:
        base = json.load(open(basef))
        t, _, _, k23, rho, _ = CTCT_SETS["e3_t1153"]
        # check the generator against the real extraction at M = 64 (same instruction and input counts, same verdict)
        syn64 = os.path.join(RUNS, "synthetic_lincomb_m64.fhecheck.json")
        json.dump(lincomb_program(base, 64, rho * t, k23), open(syn64, "w"))
        a, b = fhe_check(basef), fhe_check(syn64)
        d64 = json.load(open(syn64))
        same = (len(d64["program"]["body"]) == len(base["program"]["body"]) and len(d64["program"]["inputs"]) == len(base["program"]["inputs"])
                and a["verdictLine"] == b["verdictLine"] and a["failure"]["bound"] == b["failure"]["bound"])
        big = os.path.join(RUNS, "synthetic_lincomb_m262144.fhecheck.json")
        doc = lincomb_program(base, 262144, rho * t, k23)
        json.dump(doc, open(big, "w"))
        row(f"`fhe_check`, default limit; phases 2/3 with the paper's M = 2^18 (SYNTHETIC program, {len(doc['program']['body'])} instructions, "
            f"{len(doc['program']['inputs'])} inputs; generator reproduces the real M = 64 extraction's counts, verdict and failing bound: {same})",
            "synthetic (not committed: run.py lincomb_program)", [FHE, "--no-suggest", big], timeout=300)
        os.unlink(big)
    # time against the number of summed fresh inputs (synthetic programs: sum of M inputs with the paper's C, one squaring)
    scaling = []
    if basef:
        for M in (512, 1024, 2048, 4096, 8192):
            f = os.path.join(RUNS, f"synthetic_sum_m{M}.fhecheck.json")
            doc = lincomb_program(base, M, rho * t, 1)
            json.dump(doc, open(f, "w"))
            t0 = time.time()
            r = sh([FHE, "--no-suggest", f])
            line = [x for x in r.stdout.splitlines() if x.startswith("VERDICT")][0]
            scaling.append({"M": M, "instructions": len(doc["program"]["body"]), "seconds": round(time.time() - t0, 1), "exit": r.returncode,
                            "line": line.split(": every output")[0]})
            os.unlink(f)
    dump({"rows": rows, "scaling": scaling}, os.path.join(OUT, "misc.json"))
    for r in rows:
        print(f"{r['what'][:60]} | {r['input']} | {r['line'][:100]} | {r['exit']}")

    def git(*a):
        return sh(["git", "-C", ROOT] + list(a)).stdout.strip()
    prov = {
        "OpenFHE": "openfheorg/openfhe-development v1.6.1, commit b59e1f291965f14fbee5172cd83a20f5b856204f, with `harness/frontend/openfhe/openfhe-v1.6.1-tracer.patch` "
                   "(observation hooks only), built by `harness/frontend/openfhe/build_openfhe.sh` (Release, WITH_REDUCED_NOISE=OFF, NATIVEINT 64); patched checkout HEAD: "
                   + sh(["git", "-C", os.path.join(ROOT, "harness", "build", "frontend-openfhe", "src"), "rev-parse", "HEAD"]).stdout.strip(),
        "attack code (read, not built, not copied)": "github.com/hmchoe0528/NEW_INDCPAD_HE, commit 8d057909e0fe2d57e74c7facd0d99fd934f7d3ab (branch main as cloned on 2026-11-13); "
                                                      "its README states it was tested on OpenFHE v1.5.0 (df495ba) for pt-ct, v1.3 (2bf4524) for ct-ct (Sections 5.1-5.2) and v1.5.0 for App. E.3",
        "paper": "Choe, Kang, Stehlé, New IND-CPA-D Attacks on BFV and BGV, ACM CCS 2026; ePrint 2026/2546 (full version)",
        "fhe_check": "built with `lake build fhe_check` from this repository; last commit touching its sources (FheCheck.lean, FHE/, Spec/, Challenge/, Validation/, lakefile.toml): "
                     + git("log", "-1", "--format=%H", "--", "FheCheck.lean", "FHE", "Spec", "Challenge", "Validation", "lakefile.toml")
                     + "; sha256 of the binary used: " + sh(["sha256sum", FHE]).stdout.split()[0],
        "extractor": "harness/frontend/openfhe/extract_bfv.py, last commit touching harness/frontend/openfhe: " + git("log", "-1", "--format=%H", "--", "harness/frontend/openfhe"),
        "machine": "x86-64 Linux, gcc " + sh(["c++", "-dumpfullversion"]).stdout.strip() + ", single-threaded runs (OMP_NUM_THREADS=1) on a shared 128-core machine",
        "generated": time.strftime("%Y-%m-%d"),
    }
    dump(prov, os.path.join(OUT, "provenance.json"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=12)
    ap.add_argument("--stage", default="A,B,C,D,E")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--only", help="regular expression: run only the cases whose name matches")
    ap.add_argument("--reuse-traces", action="store_true",
                    help="for every case with a previous summary (out/NAME.summary.json.prev) and its run directory: "
                         "re-extract and re-check that run's trace instead of running OpenFHE again")
    a = ap.parse_args()
    global ONLY, REUSE_TRACES
    ONLY = a.only
    REUSE_TRACES = a.reuse_traces
    for p in (RUNS, OUT, CASES):
        os.makedirs(p, exist_ok=True)
    for st in a.stage.split(","):
        print(f"== stage {st}", flush=True)
        {"A": stage_a, "B": stage_b, "C": stage_c, "D": stage_d, "E": stage_e}[st](a.jobs, a.force)


if __name__ == "__main__":
    main()
