#!/usr/bin/env python3
"""UNTRUSTED: re-run fhe_check on the committed cases/*.fhecheck.json and compare with the
committed out/*.summary.json (verdict line, exit code, first failing instruction, output bounds).
No OpenFHE needed. Exit 1 on any difference."""
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
from run import CASES, OUT, case_file, fhe_check  # noqa: E402

bad = 0
files = sorted(glob.glob(os.path.join(CASES, "*.fhecheck.json.gz")))
for f in files:
    name = os.path.basename(f)[:-len(".fhecheck.json.gz")]
    want = json.load(open(os.path.join(OUT, name + ".summary.json")))["fheCheck"]
    got = fhe_check(case_file(name))
    same = all(got.get(k) == want.get(k) for k in ("verdictLine", "exit", "failure", "outputs", "steps"))
    print(f"{'ok  ' if same else 'DIFF'} {name}: {got['verdictLine'][:90]}")
    bad += not same
print(f"{len(files)} cases, {bad} differences")
sys.exit(1 if bad else 0)
