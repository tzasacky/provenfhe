#!/usr/bin/env python3
"""UNTRUSTED tests (tests/run.sh section 6c) of the frontend hardening against the referee-C findings:
what is certified must be what the program decrypts, computed by traced operations from traced
inputs, plaintexts and keys, under the dumped parameters. Run from harness/frontend; FHE_CHECK = the
fhe_check executable. Prints one line per failure and the count; exit 0 iff none.

1. tests/tamper/expected.tsv: real OpenFHE runs (openfhe/tamper_demo.cpp, openfhe/make_tamper.sh)
   that change a ciphertext / plaintext / key / parameter through the public API outside the
   traced calls must be refused; the honest run must be extracted with the decrypted ciphertext
   as an output.
2. Mutations of committed traces (the referee's reproducers, both extractors): a Decrypt of a
   ciphertext no traced operation produced (M1); --assume-fresh-inputs on a ciphertext that
   appears mid-program, or in a trace with a traced Encrypt (M2), and its positive case; a plaintext
   operand that no traced Make*Plaintext produced, and one recorded with another t (M3).
3. fhe_check: unknown or misspelt fields are INVALID INPUT (strict schema); an --idealised file
   is never headed CERTIFIED (it is NOT CERTIFIED FOR THE LIBRARY); extract_bfv.py refuses sigma != 3.19.
"""
import json
import os
import subprocess
import sys
import tempfile

FHE_CHECK = os.environ["FHE_CHECK"]
HERE = os.path.dirname(os.path.abspath(__file__))
bad = []
n = 0


sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "openfhe"))
sys.dont_write_bytecode = True
from extract import stamp_tracer  # noqa: E402


def extract(scheme, params, trace_text, *flags):
    """The extractor on a (possibly mutated) committed trace. params.json is stamped with the current
    tracer version (stamp_tracer): the mutated trace is no committed one, so the extractor's tracer
    check would refuse it before the check under test."""
    ex = "openfhe/extract_bfv.py" if scheme == "bfv" else "openfhe/extract.py"
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as f:
        f.write(trace_text)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as pf:
        json.dump(stamp_tracer(json.load(open(params))), pf)
    try:
        r = subprocess.run([sys.executable, "-I", ex, "--params", pf.name, "--trace", f.name, *flags],
                           capture_output=True, text=True)
    finally:
        os.unlink(f.name)
        os.unlink(pf.name)
    try:
        return r.returncode, json.loads(r.stdout)
    except Exception:
        return r.returncode, {"error": "NO JSON: " + r.stderr[-300:]}


def expect(name, rc, doc, want):
    global n
    n += 1
    if want.startswith("OK"):
        out = want.split(":", 1)[1] if ":" in want else None
        if rc != 0 or "error" in doc:
            bad.append(f"{name}: refused: {doc.get('error', '')[:200]}")
        elif out and out not in doc["program"]["outputs"]:
            bad.append(f"{name}: {out} is not an output ({doc['program']['outputs']})")
    elif rc != 1 or want not in doc.get("error", ""):
        bad.append(f"{name}: expected a refusal containing {want!r}, got exit {rc}: {str(doc.get('error'))[:200]}")


def fhe_check(doc, *flags):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump(doc, f)
    try:
        r = subprocess.run([FHE_CHECK, "--no-suggest", *flags, f.name], capture_output=True, text=True)
    finally:
        os.unlink(f.name)
    return next((l for l in r.stdout.splitlines() if l.startswith("VERDICT")), r.stdout[:200] + r.stderr[:200])


def lines(path):
    return open(path).read()


# 1. real runs
for row in open(os.path.join(HERE, "expected.tsv")):
    if row.startswith("#") or not row.strip():
        continue
    case, flags, want = row.rstrip("\n").split("\t")
    d = os.path.join(HERE, case)
    fl = [] if flags == "-" else flags.split(" ")
    rc, doc = extract(case.split("_")[0], os.path.join(d, "params.json"), lines(os.path.join(d, "trace.jsonl")), *fl)
    expect(f"tamper {case} {flags}", rc, doc, want)
    if want.startswith("OK") and rc == 0:
        n += 1
        if "decrypted" not in json.dumps(doc["crossCheck"].get("outputs", {})):
            bad.append(f"tamper {case}: crossCheck.outputs does not name the decrypted ciphertexts")

# 2. mutations of committed traces
DEC = ('{"ev":"begin","fn":"CryptoContext::Decrypt(PrivateKey,Ciphertext,Plaintext*)","d":0}\n'
       '{"ev":"in","d":0,"name":"ciphertext","kind":"ct","id":"%s","towers":%d,"parts":2,"nsd":%d,"sf":1}\n'
       '{"ev":"end","d":0}\n')
for scheme, ex in (("bfv", "examples/openfhe_bfv_hpspoverqleveled_hybrid_compress_d3"), ("bgv", "examples/openfhe_dot_depth2")):
    P, T = ex + ".params.json", lines(ex + ".trace.jsonl")
    rc, base = extract(scheme, P, T)
    out = base["program"]["outputs"][0]
    rec = [json.loads(l) for l in T.splitlines() if f'"id":"{out}"' in l][-1]
    # M1: Decrypt of a ciphertext no traced operation produced (an untraced change after the last op)
    rc, doc = extract(scheme, P, T + DEC % ("ct_999", rec["towers"], rec["nsd"]))
    expect(f"{ex}: Decrypt of an unknown ciphertext", rc, doc, "the decrypted ciphertext ct_999")
    rc, doc = extract(scheme, P, T + DEC % ("ct_999", rec["towers"], rec["nsd"]), "--assume-fresh-inputs")
    expect(f"{ex}: Decrypt of an unknown ciphertext, --assume-fresh-inputs", rc, doc, "the decrypted ciphertext ct_999")
    # ... and of the real output: extracted, and the output is certified
    rc, doc = extract(scheme, P, T + DEC % (out, rec["towers"], rec["nsd"]))
    expect(f"{ex}: Decrypt of the output", rc, doc, "OK:" + out)
    # m3: --outputs must include every decrypted ciphertext
    first = base["program"]["body"][0]["dst"]
    rc, doc = extract(scheme, P, T + DEC % (out, rec["towers"], rec["nsd"]), "--outputs", first)
    expect(f"{ex}: --outputs without the decrypted output", rc, doc, "which the program decrypts")
    # M2: an operand renamed mid-program (an untraced in-place change) and --assume-fresh-inputs
    ls = T.splitlines(True)
    top = max(i for i, l in enumerate(ls) if '"ev":"begin"' in l and '"d":0' in l)  # the last top-level call
    last_in = next(json.loads(l)["id"] for l in ls[top:] if '"ev":"in"' in l and '"kind":"ct"' in l)
    T2 = "".join(ls[:top]) + "".join(l.replace(f'"id":"{last_in}"', '"id":"ct_777"') for l in ls[top:])
    rc, doc = extract(scheme, P, T2)
    expect(f"{ex}: operand changed mid-program", rc, doc, "no traced operation produced it")
    rc, doc = extract(scheme, P, T2, "--assume-fresh-inputs")
    expect(f"{ex}: operand changed mid-program, --assume-fresh-inputs", rc, doc, "--assume-fresh-inputs does not apply")
    # M2: a trace with KeyGen but no Encrypt: the inputs are not assumed fresh
    stripped = subprocess.run([sys.executable, "-I", os.path.join(HERE, "strip.py"), ex + ".trace.jsonl"],
                              capture_output=True, text=True).stdout
    rc, doc = extract(scheme, P, stripped, "--assume-fresh-inputs")
    expect(f"{ex}: Encrypt stripped, an input first used mid-program, --assume-fresh-inputs", rc, doc,
           "--assume-fresh-inputs does not apply: it first appears after")
    # M2: an unknown ciphertext in a trace that contains traced Encrypt calls (it starts before encryption)
    ls = T.splitlines(True)
    first = next(i for i, l in enumerate(ls) if '"ev":"begin"' in l and '"d":0' in l and "Encrypt" not in l
                 and "KeyGen" not in l and "Make" not in l)
    cid = next(json.loads(l)["id"] for l in ls[first:] if '"ev":"in"' in l and '"kind":"ct"' in l)
    T5 = "".join(ls[:first]) + "".join(l.replace(f'"id":"{cid}"', '"id":"ct_778"') for l in ls[first:])
    rc, doc = extract(scheme, P, T5, "--assume-fresh-inputs")
    expect(f"{ex}: unknown input in a trace with traced Encrypt calls, --assume-fresh-inputs", rc, doc,
           "the trace contains a traced Encrypt")

# M2 positive: a trace that starts after key generation and encryption, inputs used by the first operation
for scheme, ex in (("bfv", "examples/openfhe_bfv_hps_bv_chain_d2"), ("bgv", "examples/openfhe_fixedauto_chain")):
    stripped = subprocess.run([sys.executable, "-I", os.path.join(HERE, "strip.py"), "--keys", ex + ".trace.jsonl"],
                              capture_output=True, text=True).stdout
    rc, doc = extract(scheme, ex + ".params.json", stripped, "--assume-fresh-inputs", "--assume-single-party-keys")
    expect(f"{ex}: starts after encryption, --assume-fresh-inputs", rc, doc, "OK")
    n += 1
    if rc == 0 and "assumed fresh encryption" not in json.dumps(doc["program"]["inputs"]):
        bad.append(f"{ex}: --assume-fresh-inputs did not declare the inputs")

# M3: plaintext operands
for scheme, ex in (("bfv", "examples/openfhe_bfv_default_plain_d2"), ("bgv", "examples/openfhe_fixedmanual_plain")):
    P, T = ex + ".params.json", lines(ex + ".trace.jsonl")
    ls = T.splitlines(True)
    made = [i for i, l in enumerate(ls) if '"kind":"pt"' in l and '"ev":"out"' in l]
    pid = json.loads(ls[made[-1]])["id"]
    first_use = next(i for i, l in enumerate(ls) if i > made[-1] and f'"id":"{pid}"' in l and '"ev":"in"' in l)
    T3 = "".join(ls[:first_use]) + "".join(l.replace(f'"id":"{pid}"', '"id":"pt_444"') for l in ls[first_use:])
    rc, doc = extract(scheme, P, T3)
    expect(f"{ex}: plaintext operand with no traced Make*", rc, doc, "pt_444 was not produced by a traced CryptoContext::Make*Plaintext")
    T4 = T.replace('"kind":"pt"', '"kind":"pt","t":786433')
    rc, doc = extract(scheme, P, T4)
    expect(f"{ex}: plaintext encoded for another t", rc, doc, "is encoded for plaintext modulus 786433")
    t = json.load(open(P))["t"]
    rc, doc = extract(scheme, P, T.replace('"kind":"pt"', f'"kind":"pt","t":{t}'))
    expect(f"{ex}: plaintexts recorded with the context's t", rc, doc, "OK")

# 3. fhe_check: strict schema, idealised label; extract_bfv: sigma
ex = "examples/openfhe_bfv_hps_hybrid_chain_d1"
good = json.load(open(ex + ".fhecheck.json"))
for path, key in ((["bfv", "multiplication"], "floatTolerent"), ([], "unknownTop"), (["params"], "secretKeyDist"),
                  (["freshEncryption"], "means"), (["program"], "output")):
    d = json.loads(json.dumps(good))
    o = d
    for k in path:
        o = o[k]
    o[key] = True
    v = fhe_check(d)
    n += 1
    if not v.startswith("VERDICT: INVALID INPUT") or "unknown field" not in v:
        bad.append(f"strict schema: {'.'.join(path + [key])} was accepted: {v[:160]}")
d = json.loads(json.dumps(good))
d["program"]["body"][0]["bb"] = "x"
v = fhe_check(d)
n += 1
if "unknown field" not in v:
    bad.append(f"strict schema: an unknown instruction field was accepted: {v[:160]}")
r = subprocess.run([sys.executable, "-I", "openfhe/extract_bfv.py", "--idealised", "--params", ex + ".params.json",
                    "--trace", ex + ".trace.jsonl"], capture_output=True, text=True)
v = fhe_check(json.loads(r.stdout))
n += 1
if not v.startswith("VERDICT: NOT CERTIFIED FOR THE LIBRARY (idealised algorithm certified)"):
    bad.append(f"--idealised: headline is not NOT CERTIFIED FOR THE LIBRARY: {v[:160]}")
p = json.load(open(ex + ".params.json"))
p["sigma"] = 3.2
with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
    json.dump(p, f)
rc, doc = extract("bfv", f.name, lines(ex + ".trace.jsonl"))
os.unlink(f.name)
expect("extract_bfv.py with sigma 3.2", rc, doc, "the declared sampler mean applies to sigma = 3.19 only")

# a FIXEDMANUAL/FIXEDAUTO context whose primes are not 1 mod t is refused, even for a program without a modulus switch
for ex in ("examples/openfhe_depth2_fixedmanual", "examples/openfhe_fixedauto_chain"):
    p = json.load(open(ex + ".params.json"))
    p["t"] = p["t"] + 2 ** 32
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump(p, f)
    rc, doc = extract("bgv", f.name, lines(ex + ".trace.jsonl"))
    os.unlink(f.name)
    expect(f"{ex} with primes not 1 mod t", rc, doc, "context whose primes are not 1 mod t")

for b in bad:
    print("  " + b)
print(f"tamper/hardening checks: {n - len(bad)}/{n} passed")
sys.exit(1 if bad else 0)
