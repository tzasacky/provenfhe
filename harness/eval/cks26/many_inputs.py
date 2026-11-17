#!/usr/bin/env python3
"""UNTRUSTED reproducer for a limitation found by the CKS26 evaluation: fhe_check's time on a BFV
program with many INPUTS (here: a sum of M fresh encryptions, the shape of phases 2/3 of attack 3),
measured before any analysis could matter.

    many_inputs.py BASE.fhecheck.json M [M ...]

BASE: any extracted BFV file with two-component fresh inputs (e.g. cases/ctct_e3_t1153_p23_m64.fhecheck.json).
For each M it writes a synthetic program (run.py lincomb_program with K = 1 squaring), runs
`fhe_check --no-suggest` (default instruction limit) and `fhe_check --no-suggest --max-instructions 0`
under a timeout (seconds, env TIMEOUT, default 600), and prints instructions, wall time, exit code
and the first line of the answer.
"""
import json
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
from run import BUILD, FHE, lincomb_program  # noqa: E402

base = json.load(open(sys.argv[1]))
t = base["params"]["t"]
limit = int(os.environ.get("TIMEOUT", "600"))
print("| M (inputs of the sum) | instructions | fhe_check option | wall time (s) | exit | answer |")
print("|---|---|---|---|---|---|")
for M in map(int, sys.argv[2:]):
    doc = lincomb_program(base, M, 8737706 * t, 1)
    os.makedirs(os.path.join(BUILD, "tmp"), exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".fhecheck.json", delete=False, dir=os.path.join(BUILD, "tmp")) as f:
        json.dump(doc, f)
    for opt in ([], ["--max-instructions", "0"]):
        t0 = time.time()
        try:
            r = subprocess.run([FHE, "--no-suggest"] + opt + [f.name], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=limit)
            line = [x for x in r.stdout.splitlines() if x.startswith("VERDICT")]
            ans, code = (line[0][:150] if line else r.stdout[:150]), r.returncode
        except subprocess.TimeoutExpired:
            ans, code = f"no answer within {limit} s (killed)", "-"
        print(f"| {M} | {len(doc['program']['body'])} | {' '.join(opt) or '(default)'} | {time.time() - t0:.1f} | {code} | {ans} |", flush=True)
    os.unlink(f.name)
