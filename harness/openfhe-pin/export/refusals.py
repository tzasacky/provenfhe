#!/usr/bin/env python3
"""UNTRUSTED. Tests the extractor's refusals (and its extractions) on recorded cases, without
OpenFHE: every case directory holds the `params.json` and `trace.jsonl` that upstream OpenFHE
v1.6.1 + the frontend's tracer wrote, and the `prog.fhecheck.json` the extractor produced at
export time.

  refusals.py [--jobs J] [--list FILE] CASEDIR...

For every case the UNMODIFIED extractor `harness/frontend/openfhe/extract.py` (BFV cases:
`extract_bfv.py`, with `--assume-fresh-inputs` for hand-built inputs) is run again, as
`export_case.sh` / `export_case_bfv.sh` run it (`python3 -I extract.py --params P --trace T --artifact NAME`), and

  * a case recorded as REFUSED (`prog.fhecheck.json` is `{"format": ..., "error": msg}`) must be
    refused again, exit status 1, with exactly the recorded message;
  * a case recorded with a program must be extracted again, and the parts of the file the Lean
    checker reads must be the recorded ones: `params`, `keySwitching`, `modSwitch`, `decryption`,
    `program` (other keys, e.g. `noiseDerivation` and `freshEncryption`, are descriptive and may
    gain fields).

Prints one line per disagreement and the counts; the last line is
`extractor: R refusals reproduced of R', P programs reproduced of P'`. Exit 0 iff no disagreement."""
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.abspath(os.path.join(HERE, "..", "..", "frontend", "openfhe", "extract.py"))
EXTRACT_BFV = os.path.abspath(os.path.join(HERE, "..", "..", "frontend", "openfhe", "extract_bfv.py"))
CHECKED = ("params", "keySwitching", "modSwitch", "decryption", "program")


def one(d):
    d = d.rstrip("/")
    name = os.path.basename(d)
    try:
        rec = json.load(open(os.path.join(d, "prog.fhecheck.json")))
    except Exception as e:
        return name, "?", f"prog.fhecheck.json unreadable: {e}"
    # BFV cases (pin.json "scheme": "BFV") go to extract_bfv.py, as export_case_bfv.sh runs it; a case
    # with hand-built inputs ("inputsArbitrary") was extracted with --assume-fresh-inputs
    try:
        pin = json.load(open(os.path.join(d, "pin.json")))
    except Exception:
        pin = {}
    bfv = pin.get("scheme") == "BFV"
    extra = ["--assume-fresh-inputs"] if bfv and pin.get("inputsArbitrary") else []
    r = subprocess.run([sys.executable, "-I", EXTRACT_BFV if bfv else EXTRACT, "--params", os.path.join(d, "params.json"),
                        "--trace", os.path.join(d, "trace.jsonl"), "--artifact", name] + extra,
                       capture_output=True, text=True)
    try:
        now = json.loads(r.stdout)
    except Exception:
        return name, "?", f"the extractor printed no JSON (exit {r.returncode}): {r.stderr.strip()[-200:]}"
    if "error" in rec:
        if r.returncode != 1 or "error" not in now:
            return name, "refusal", f"recorded as refused, but the extractor now exits {r.returncode} with a program"
        if now["error"] != rec["error"]:
            return name, "refusal", f"refusal message changed:\n    recorded: {rec['error']}\n    now:      {now['error']}"
        return name, "refusal", None
    if r.returncode != 0 or "error" in now:
        return name, "program", f"recorded with a program, but the extractor now refuses: {now.get('error')}"
    for k in CHECKED:
        if now.get(k) != rec.get(k):
            return name, "program", f"the extracted `{k}` differs from the recorded one"
    return name, "program", None


def main():
    args = sys.argv[1:]
    jobs = 16
    dirs = []
    i = 0
    while i < len(args):
        if args[i] == "--jobs":
            jobs = int(args[i + 1]); i += 2
        elif args[i] == "--list":
            dirs += [l.strip() for l in open(args[i + 1]) if l.strip()]; i += 2
        else:
            dirs.append(args[i]); i += 1
    with ThreadPoolExecutor(max(1, jobs)) as ex:
        rows = list(ex.map(one, dirs))
    n = {"refusal": [0, 0], "program": [0, 0], "?": [0, 0]}
    for name, kind, err in rows:
        n[kind][1] += 1
        if err is None:
            n[kind][0] += 1
        else:
            print(f"  EXTRACTOR {name}: {err}")
    print(f"extractor: {n['refusal'][0]} refusals reproduced of {n['refusal'][1]}, "
          f"{n['program'][0]} programs reproduced of {n['program'][1]}"
          + (f", {n['?'][1]} unreadable" if n["?"][1] else ""))
    sys.exit(0 if all(a == b for a, b in n.values()) and n["?"][1] == 0 else 1)


if __name__ == "__main__":
    main()
