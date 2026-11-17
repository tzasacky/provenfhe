#!/usr/bin/env python3
"""UNTRUSTED: generate the real-OpenFHE inputs of the per-instruction BFV budget measurement.

    BFV_DEMO=.../bfv_demo python3 -I gen_inputs.py [--jobs J] [--scratch DIR]

Every row is one run of bfv_demo (traced OpenFHE v1.6.1) at OpenFHE's own parameters: only the
plaintext modulus and the multiplicative depth are set (128-bit security, 60-bit primes, default
multiplication technique = HPSPOVERQLEVELED), key switching BV (the default: no setter called) or
HYBRID; then extract_bfv.py and value_check_bfv.py. Kept: inputs/NAME.fhecheck.json and one line
of inputs/meta.tsv per run (the traces are deleted). Single-threaded runs (OMP_NUM_THREADS=1),
J of them in parallel.

Rows:
  chain  D = 1..5, parameters generated for depth D + j, j = 0..3, ks in {bv, hybrid},
         t in {65537, T40, T50}
  dot rot rotsum plain neg norelin compress  at --depth D --progdepth D, D in {2, 3},
         ks in {bv, hybrid}, t in {65537, T40}
"""
import argparse
import concurrent.futures as cf
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OPENFHE = os.path.join(HERE, "..", "openfhe")
T16 = 65537
T40 = 1099512938497          # smallest prime >= 2^40 that is 1 mod 2^18
T50 = 1125899915231233       # smallest prime >= 2^50 that is 1 mod 2^18
TAG = {T16: "t16", T40: "t40", T50: "t50"}
SHAPES = ["dot", "rot", "rotsum", "plain", "neg", "norelin", "compress"]


def jobs():
    out = []
    for t in (T16, T40, T50):
        for ks in ("bv", "hybrid"):
            for d in range(1, 6):
                for j in range(4):
                    out.append(dict(name=f"default_{ks}_{TAG[t]}_chain_d{d}_x{j}", t=t, ks=ks, prog="chain",
                                    depth=d + j, progdepth=d, extra=j))
    for t in (T16, T40):
        for ks in ("bv", "hybrid"):
            for prog in SHAPES:
                for d in (2, 3):
                    out.append(dict(name=f"default_{ks}_{TAG[t]}_{prog}_d{d}_x0", t=t, ks=ks, prog=prog,
                                    depth=d, progdepth=d, extra=0))
    return out


def run(job, demo, scratch, outdir):
    w = tempfile.mkdtemp(prefix=job["name"] + ".", dir=scratch)
    args = [demo, "run", w, "--t", str(job["t"]), "--prog", job["prog"], "--depth", str(job["depth"]),
            "--progdepth", str(job["progdepth"])]
    if job["ks"] == "hybrid":
        args += ["--ks", "HYBRID"]
    env = dict(os.environ, OMP_NUM_THREADS="1")
    r = subprocess.run(args, capture_output=True, text=True, env=env)
    meta = dict(job, demo_rc=r.returncode, demo_msg=(r.stdout + r.stderr).strip().replace("\n", " ")[:200])
    try:
        if r.returncode not in (0, 3):
            meta["status"] = "bfv_demo failed"
            return meta
        f = os.path.join(outdir, job["name"] + ".fhecheck.json")
        e = subprocess.run([sys.executable, "-I", os.path.join(OPENFHE, "extract_bfv.py"), "--params",
                            w + "/params.json", "--trace", w + "/trace.jsonl", "--artifact", "levelbfv_" + job["name"]],
                           capture_output=True, text=True)
        if e.returncode != 0:
            meta["status"] = "extraction error: " + e.stdout[:200].replace("\n", " ")
            return meta
        open(f, "w").write(e.stdout)
        v = subprocess.run([sys.executable, "-I", os.path.join(OPENFHE, "value_check_bfv.py"), f, w + "/values.json"],
                           capture_output=True, text=True)
        meta["value_check_rc"] = v.returncode
        meta["lib_decrypt"] = {0: "yes", 3: "NO"}.get(v.returncode, "value check FAILED")
        p = json.load(open(w + "/params.json"))
        vals = json.load(open(w + "/values.json"))
        Q = math.prod(int(x["q"]) for x in p["qs"])
        meta.update(N=p["N"], limbs=len(p["qs"]), special=len(p["special"]), log2Q=round(math.log2(Q), 2),
                    technique=p["multiplicationTechnique"], keySwitch=p["keySwitch"], dnum=p.get("dnum"),
                    stdLevel=p.get("stdLevel"),
                    observed_bits=round(math.log2(max(1, max(int(o["noise"]) for o in vals["outputs"].values()))), 2),
                    declimit_bits=round(math.log2(Q / (2 * p["t"])), 2),
                    cleartext_check=all(o.get("cleartextCheck") for o in vals["outputs"].values()),
                    status="ok")
        return meta
    finally:
        shutil.rmtree(w, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--scratch", default=None)
    ap.add_argument("--out", default=os.path.join(HERE, "inputs"))
    a = ap.parse_args()
    demo = os.environ.get("BFV_DEMO", os.path.join(ROOT, "harness/build/frontend-openfhe/bfv_demo"))
    os.makedirs(a.out, exist_ok=True)
    scratch = a.scratch or tempfile.mkdtemp(prefix="levelbfv.")
    os.makedirs(scratch, exist_ok=True)
    cols = ["name", "status", "prog", "progdepth", "depth", "extra", "ks", "t", "N", "limbs", "special", "log2Q",
            "technique", "keySwitch", "dnum", "stdLevel", "demo_rc", "cleartext_check", "value_check_rc",
            "lib_decrypt", "observed_bits", "declimit_bits", "demo_msg"]
    rows = []
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for m in ex.map(lambda j: run(j, demo, scratch, a.out), jobs()):
            rows.append(m)
            print(m["name"], m.get("status"), m.get("lib_decrypt"), file=sys.stderr, flush=True)
    with open(os.path.join(a.out, "meta.tsv"), "w") as f:
        f.write("\t".join(cols) + "\n")
        for m in rows:
            f.write("\t".join(str(m.get(c, "")) for c in cols) + "\n")


if __name__ == "__main__":
    main()
