#!/usr/bin/env python3
"""UNTRUSTED plaintext-value cross-check for the OpenFHE BFV frontend.

    value_check_bfv.py PROG.fhecheck.json VALUES.json

PROG is the extracted program (extract_bfv.py); VALUES is what `bfv_demo run` wrote: the
coefficients mod t of every plaintext it encoded under the trace, for the output the raw
polynomial OpenFHE's PKEBFVRNS::Decrypt returned (before Decode), and the OBSERVED noise
||[phase - floor(Q/t)*m]_Q||_inf of every fresh ciphertext and of the output.

This evaluates the extracted program at MESSAGE level, mirroring Spec.Source.step for BFV: a
message is a polynomial in Z_t[X]/(X^N + 1);
  add/sub/addPlain/subPlain   m + m', m - m'
  mul/square/mulPlain         m * m'  (negacyclic product)
  mulConst c                  c * m
  automorph g                 m(X^g)
  modSwitch/relin/keySwitch/copy/toEval/toCoeff   m   (a BFV modulus switch keeps the message)
Each ciphertext input's message is the encoded plaintext that CryptoContext::Encrypt received
(input.origin.openfhe); each plaintext input's message is that plaintext's encoding. The
prediction for every output must equal OpenFHE's raw decryption coefficient by coefficient
(unless the run records a mismatch with the cleartext, see below). A wrong operation mapping (wrong
operand, wrong rotation index, a missing or extra operation) changes the predicted polynomial.

Two further empirical checks (not proofs):
  * the observed noise of every fresh ciphertext is at most params.inputNoise (the frontend's
    derived worst-case bound) -- or the input's own `bound`;
  * if the library's output DISAGREES with the prediction, the script says so and exits 3
    ("differs from the cleartext prediction"): the extraction may still be right (bfv_demo's own
    cleartext check then failed as well: values.json cleartextCheck).

This script is NOT verified: it is an independent re-implementation used as a test oracle for
the (also untrusted) extractor. It is not part of what fhe_check certifies.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
from value_check import automorph, polymul  # noqa: E402


def main():
    prog_doc = json.load(open(sys.argv[1]))
    vals = json.load(open(sys.argv[2]))
    if "error" in prog_doc:
        print(f"value_check_bfv: extraction failed: {prog_doc['error']}")
        return 2
    P = prog_doc["params"]
    if P.get("scheme") != "BFV":
        print("value_check_bfv: not a BFV program")
        return 2
    t, N = int(P["t"]), int(P["N"])
    prog = prog_doc["program"]
    env = {}
    bad = 0
    for d in prog["inputs"]:
        src = d.get("origin", {}).get("openfhe")
        if src not in vals["plaintexts"]:
            print(f"value_check_bfv: no recorded plaintext for input {d['name']} (origin {src})")
            return 2
        m = [int(x) % t for x in vals["plaintexts"][src]]
        if len(m) != N:
            print(f"value_check_bfv: plaintext {src} has {len(m)} coefficients, N = {N}")
            return 2
        env[d["name"]] = m
        if d["parts"] == 1:
            if max(m) > int(d.get("bound", t - 1)):
                print(f"value_check_bfv: plaintext {d['name']} exceeds its declared bound")
                bad += 1
        else:
            obs = vals.get("fresh", {}).get(d["name"])
            decl = int(d.get("bound", P["inputNoise"]))
            if obs is not None and int(obs["noise"]) > decl:
                print(f"value_check_bfv: fresh ciphertext {d['name']}: observed noise {obs['noise']} > declared bound {decl}")
                bad += 1
    for i, ins in enumerate(prog["body"]):
        op, a, dst = ins["op"], ins["a"], ins["dst"]
        x = env[a]
        if op in ("add", "sub", "mul"):
            y = env[ins["b"]]
        elif op in ("addPlain", "subPlain", "mulPlain"):
            y = env[ins["p"]]
        if op in ("add", "addPlain"):
            r = [(u + v) % t for u, v in zip(x, y)]
        elif op in ("sub", "subPlain"):
            r = [(u - v) % t for u, v in zip(x, y)]
        elif op in ("mul", "mulPlain"):
            r = polymul(x, y, t, N)
        elif op == "square":
            r = polymul(x, x, t, N)
        elif op in ("mulConst", "negate"):
            c = int(ins.get("c", -1)) % t
            r = [(c * u) % t for u in x]
        elif op == "automorph":
            r = automorph(x, int(ins["g"]), t, N)
        elif op in ("modSwitch", "relin", "keySwitch", "copy", "toEval", "toCoeff"):
            r = x
        else:
            print(f"value_check_bfv: body[{i}]: operation {op} has no BFV message-level meaning here")
            return 2
        env[dst] = r
    checked, decfail = 0, 0
    for tid, o in vals["outputs"].items():
        # values.json names the output by its trace id; the extractor's SSA name of the latest value
        # with that content is the id itself or id#k (extract.py Extractor.define)
        oid = ([n for n in prog["outputs"] if n.split("#")[0] == tid] or [tid])[-1]
        if oid not in env or oid not in prog["outputs"]:
            print(f"value_check_bfv: OpenFHE output {oid} is not an output of the extracted program")
            bad += 1
            continue
        pred, raw = env[oid], [int(v) % t for v in o["raw"]]
        diff = [i for i in range(N) if pred[i] != raw[i]]
        if diff:
            if o.get("cleartextCheck") is False:
                print(f"value_check_bfv: {oid}: differs from the cleartext prediction: {len(diff)} of {N} coefficients differ from the "
                      f"predicted message, and bfv_demo's own cleartext check failed too")
                decfail += 1
            else:
                print(f"value_check_bfv: {oid}: {len(diff)} of {N} coefficients differ "
                      f"(first at X^{diff[0]}: predicted {pred[diff[0]]}, OpenFHE {raw[diff[0]]})")
                bad += 1
        checked += 1
    if bad:
        print(f"value_check_bfv: FAILED ({bad} problem(s))")
        return 1
    if decfail:
        print(f"value_check_bfv: the library run differs from the cleartext prediction ({decfail} output(s)); the translation could not be confirmed")
        return 3
    obs = max((int(v["noise"]) for v in vals.get("fresh", {}).values()), default=0)
    print(f"value_check_bfv: OK: {checked} output(s), all {N} coefficients of the predicted message equal "
          f"OpenFHE's raw decryption; observed fresh noise <= {obs} <= declared {P['inputNoise']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
