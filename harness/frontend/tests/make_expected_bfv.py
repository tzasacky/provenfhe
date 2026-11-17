#!/usr/bin/env python3
"""(Re)writes tests/expected-bfv.tsv from what fhe_check says NOW about the extracted OpenFHE BFV
examples and tests/negative-bfv/*. This RECORDS the current behaviour; it does not
judge it: review the diff of expected-bfv.tsv by hand after running it (each line: is this the
verdict the file should get?). Called by `tests/run.sh --update`.

    make_expected_bfv.py FHE_CHECK        (run from harness/frontend)
"""
import glob
import re
import subprocess
import sys

exe = sys.argv[1]
files = sorted(glob.glob("examples/openfhe_bfv_*.fhecheck.json")) + sorted(glob.glob("tests/negative-bfv/*.json"))
lines = ["# file (relative to harness/frontend)\texit code\tverdict\ttext that must appear in the human report",
         "# written by tests/make_expected_bfv.py (run.sh --update) from fhe_check's output: REVIEW every changed line"]
for f in files:
    r = subprocess.run(["timeout", "300", exe, "--no-suggest", f], capture_output=True, text=True)
    # a BFV CERTIFIED line may carry a qualification: "VERDICT: CERTIFIED (assuming ...): ..." or "(binary64 steps ... under the standard model ...)"
    m = re.search(r"^VERDICT: (CERTIFIED|NOT CERTIFIED FOR THE LIBRARY|NOT CERTIFIED|UNSUPPORTED|INVALID INPUT)(?: \([^:]*\))?: (.*)$", r.stdout, re.M)
    if not m:
        sys.exit(f"{f}: no verdict line (exit {r.returncode})")
    verdict, text = m.group(1), m.group(2)[:90].rstrip()
    if verdict == "CERTIFIED":
        mm = re.findall(r"^  (\S+: level \d+, noise <= \d+ \(2\^[0-9.]+\); largest accepted 2\^[0-9.]+; margin [0-9.]+ bits)", r.stdout, re.M)
        if mm:
            text = mm[-1]
    elif verdict == "NOT CERTIFIED":
        mm = re.search(r"overflow: .* by [0-9.]+ bits", r.stdout)
        if mm:
            text = mm.group(0)
    lines.append(f"{f}\t{r.returncode}\t{verdict}\t{text}")
open("tests/expected-bfv.tsv", "w").write("\n".join(lines) + "\n")
print(f"wrote tests/expected-bfv.tsv ({len(files)} files)")
