#!/usr/bin/env python3
"""UNTRUSTED test driver (run from harness/frontend): key-provenance red-team rows of
tests/keyprov/expected.tsv (BGV, openfhe/extract.py) and tests/keyprov/expected-bfv.tsv (BFV,
openfhe/extract_bfv.py), and the refusal fixtures tests/refused/*/ and tests/refused-bfv/*/ (each
must be refused by the scheme's extractor with the message recorded in refusal.txt). Prints one
line per failure and exits 1 if any."""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FRONT = os.path.dirname(os.path.dirname(HERE))
EXTRACT = os.path.join(FRONT, "openfhe", "extract.py")
EXTRACT_BFV = os.path.join(FRONT, "openfhe", "extract_bfv.py")


sys.path.insert(0, os.path.join(FRONT, "openfhe"))
sys.dont_write_bytecode = True
from extract import stamp_tracer  # noqa: E402


def extract(params, trace, opts, script=EXTRACT):
    """The extractor on a (possibly mutated) committed trace. params.json is stamped with the current
    tracer version (stamp_tracer): a mutated trace is no committed one, so the extractor's tracer
    check would refuse it before the check under test."""
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as pf:
        json.dump(stamp_tracer(json.load(open(params))), pf)
    try:
        r = subprocess.run([sys.executable, "-I", script, "--params", pf.name, "--trace", trace] + opts,
                           capture_output=True, text=True)
    finally:
        os.unlink(pf.name)
    return r.returncode, r.stdout + r.stderr


def main():
    os.chdir(FRONT)
    fails, n = [], 0
    rows = [(r, EXTRACT) for r in open(os.path.join(HERE, "expected.tsv"))] + \
        [(r, EXTRACT_BFV) for r in open(os.path.join(HERE, "expected-bfv.tsv"))]
    for row, script in rows:
        if not row.strip() or row.startswith("#"):
            continue
        src, kind, opts, want, text = row.rstrip("\n").split("\t")
        if os.path.isdir(src):
            params, trace = os.path.join(src, "params.json"), os.path.join(src, "trace.jsonl")
        else:
            params, trace = src + ".params.json", src + ".trace.jsonl"
        opts = [] if opts == "-" else opts.split()
        ptmp = None
        if kind.startswith("params:"):
            # a params.json mutation: params:a.b=JSONVALUE
            key, val = kind[len("params:"):].split("=", 1)
            pj = json.load(open(params))
            d = pj
            *path, last = key.split(".")
            for k in path:
                d = d[k]
            d[last] = json.loads(val) if val[:1] in "0123456789tfn[{\"" else val
            with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as pt:
                json.dump(pj, pt)
            params, ptmp, kind = pt.name, pt.name, "-"
        with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as tmp:
            if kind == "-":
                tmp.write(open(trace).read())
            else:
                r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "mutate.py"), kind, trace],
                                   capture_output=True, text=True, check=True)
                tmp.write(r.stdout)
        rc, out = extract(params, tmp.name, opts, script)
        os.unlink(tmp.name)
        if ptmp:
            os.unlink(ptmp)
        n += 1
        ok_rc = (rc != 0 and '"error"' in out) if want == "REFUSE" else (rc == 0 and '"error"' not in out)
        if not ok_rc:
            fails.append(f"{src} {kind} {' '.join(opts)}: expected {want}, extractor exit {rc}: {out[:300]}")
        elif text not in out:
            fails.append(f"{src} {kind} {' '.join(opts)}: missing text {text!r}: {out[:300]}")
        elif want == "EXTRACT" and os.environ.get("FHE_CHECK"):
            # an extracted program must be well formed for the verified semantics
            with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
                f.write(out)
            r = subprocess.run([os.environ["FHE_CHECK"], "--no-suggest", f.name], capture_output=True, text=True)
            os.unlink(f.name)
            if "ill-formed" in r.stdout or r.returncode not in (0, 1, 2):
                fails.append(f"{src} {kind}: fhe_check: {r.stdout[:300]}")
    # --cse: an exact recomputation is merged, and fhe_check's answer is unchanged (same verdict,
    # same bound for every output) on the program with and without the duplicate.
    fhe = os.environ.get("FHE_CHECK")
    src = "examples/openfhe_dot_depth2"
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as tmp:
        tmp.write(subprocess.run([sys.executable, "-I", os.path.join(HERE, "mutate.py"), "dup_eval",
                                  src + ".trace.jsonl"], capture_output=True, text=True, check=True).stdout)
    files = {}
    for tag, opts in (("dup", []), ("cse", ["--cse"])):
        rc, out = extract(src + ".params.json", tmp.name, opts)
        files[tag] = out
    os.unlink(tmp.name)
    n += 1
    dup, cse = json.loads(files["dup"]), json.loads(files["cse"])
    orig = json.load(open(src + ".fhecheck.json"))
    if "error" in dup or "error" in cse or cse["crossCheck"]["cse"]["merged"] < 1 or \
            len(cse["program"]["body"]) != len(orig["program"]["body"]):
        fails.append(f"--cse did not merge the duplicated EvalMult: {files['cse'][:300]}")
    elif fhe:
        res = []
        for doc in (orig, dup, cse):
            with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
                json.dump(doc, f)
            r = json.loads(subprocess.run([fhe, "--json", "--no-suggest", f.name], capture_output=True, text=True).stdout)
            os.unlink(f.name)
            res.append((r["verdict"], sorted(str(o.get("bound")) for o in r.get("outputs", []))))
        # (without --cse the recomputation's first copy is an extra, unconsumed output)
        if not (res[0] == res[2] and res[0][0] == res[1][0] and set(res[0][1]) <= set(res[1][1])):
            fails.append(f"--cse changed fhe_check's answer: {res}")
    refused = [(os.path.join("tests/refused", d), EXTRACT) for d in sorted(os.listdir("tests/refused"))] + \
        [(os.path.join("tests/refused-bfv", d), EXTRACT_BFV) for d in sorted(os.listdir("tests/refused-bfv"))]
    for p, script in refused:
        rc, out = extract(os.path.join(p, "params.json"), os.path.join(p, "trace.jsonl"), [], script)
        n += 1
        want = open(os.path.join(p, "refusal.txt")).read().strip()
        if rc == 0 or json.loads(out).get("error") != want:
            fails.append(f"{p}: not refused with the recorded message: {out[:300]}")
    for f in fails:
        print("FAIL:", f)
    print(f"keyprov/refusal checks: {n - len(fails)}/{n} passed")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
