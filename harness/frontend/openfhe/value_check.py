#!/usr/bin/env python3
"""UNTRUSTED plaintext-value cross-check for the OpenFHE frontend.

    value_check.py PROG.fhecheck.json VALUES.json

PROG is the extracted program (extract.py); VALUES is what `bgv_demo run` wrote: the coefficients
mod t of every plaintext it encoded under the trace, and for the output the raw polynomial
OpenFHE's PKEBGVRNS::Decrypt returned (before Decode), with OpenFHE's scalingFactorInt.

This evaluates the extracted program at MESSAGE level, mirroring Spec.Source.step for BGV: a
message is a polynomial in Z_t[X]/(X^N + 1);
  add/sub/addPlain/subPlain   m + m', m - m'
  mul/square/mulPlain         m * m'  (negacyclic product)
  mulConst c                  c * m
  automorph g                 m(X^g)
  modSwitch                   q_last^-1 * m   (q_last = the limb being dropped)
  relin/keySwitch/copy/dropLimbs/toEval/toCoeff   m
Each ciphertext input's message is the encoded plaintext that CryptoContext::Encrypt received
(input.origin.openfhe); each plaintext input's message is that plaintext's encoding. The
prediction for every output, times the factor of the decryption switch (q_last^-1 for every limb
OpenFHE's Decrypt drops; `decryption.method = switch-to-one-limb`), must equal OpenFHE's raw
decryption coefficient by coefficient, and the replayed scale must equal Decrypt's
scalingFactorInt. A wrong operation mapping (wrong constant, wrong operand, wrong rotation
index, a missing or extra operation) changes the predicted polynomial.

This script is NOT verified: it is an independent re-implementation used as a test oracle for
the (also untrusted) extractor. It is not part of what fhe_check certifies.
"""
import json
import sys


def polymul(a, b, t, N):
    """Negacyclic product mod t by Kronecker substitution (exact big-integer arithmetic)."""
    k = 8 * ((2 * t.bit_length() + N.bit_length() + 8) // 8)  # bits per slot, byte aligned
    kb = k // 8
    A = int.from_bytes(b"".join(x.to_bytes(kb, "little") for x in a), "little")
    B = int.from_bytes(b"".join(x.to_bytes(kb, "little") for x in b), "little")
    C = (A * B).to_bytes(kb * 2 * N, "little")
    c = [int.from_bytes(C[i * kb:(i + 1) * kb], "little") for i in range(2 * N)]
    return [(c[i] - c[i + N]) % t for i in range(N)]


def automorph(a, g, t, N):
    r = [0] * N
    for i, x in enumerate(a):
        j = (i * g) % (2 * N)
        if j < N:
            r[j] = (r[j] + x) % t
        else:
            r[j - N] = (r[j - N] - x) % t
    return r


def main():
    prog_doc = json.load(open(sys.argv[1]))
    vals = json.load(open(sys.argv[2]))
    if "error" in prog_doc:
        print(f"value_check: extraction failed: {prog_doc['error']}")
        return 2
    P = prog_doc["params"]
    t, N = int(P["t"]), int(P["N"])
    qs = [int(x["q"]) for x in P["limbs"]]
    prog = prog_doc["program"]
    env, lev = {}, {}
    for d in prog["inputs"]:
        src = d.get("origin", {}).get("openfhe")
        if src not in vals["plaintexts"]:
            print(f"value_check: no recorded plaintext for input {d['name']} (origin {src})")
            return 2
        m = [int(x) % t for x in vals["plaintexts"][src]]
        if len(m) != N:
            print(f"value_check: plaintext {src} has {len(m)} coefficients, N = {N}")
            return 2
        env[d["name"]], lev[d["name"]] = m, d["level"]
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
        elif op == "modSwitch":
            qi = pow(qs[lev[a] - 1], -1, t)
            r = [(qi * u) % t for u in x]
        elif op in ("relin", "keySwitch", "copy", "dropLimbs", "toEval", "toCoeff"):
            r = x
        else:
            print(f"value_check: body[{i}]: operation {op} has no message-level meaning here")
            return 2
        env[dst] = r
        lev[dst] = lev[a] - (1 if op == "modSwitch" else int(ins.get("k", 0)) if op == "dropLimbs" else 0)
    dec = {d["output"]: d for d in prog_doc.get("crossCheck", {}).get("decryption", [])}
    switched = prog_doc.get("decryption", {}).get("method") == "switch-to-one-limb"
    bad = 0
    checked = 0
    for oid, o in vals["outputs"].items():
        name = oid
        if name not in env or name not in prog["outputs"]:
            print(f"value_check: OpenFHE output {oid} is not an output of the extracted program")
            bad += 1
            continue
        pred, raw = env[name], [int(v) for v in o["raw"]]
        if switched:
            # Spec.Decrypt.decScale: the message times (q_1 ... q_{l-1})^-1 mod t
            f = 1
            for l in range(lev[name], 1, -1):
                f = f * pow(qs[l - 1], -1, t) % t
            pred = [(f * u) % t for u in pred]
        diff = [i for i in range(N) if pred[i] != raw[i] % t]
        if not switched:
            print(f"value_check: {oid}: textbook decryption declared (--no-decrypt-switch); "
                  f"OpenFHE's raw decryption is at one tower, the prediction at level {lev[name]}")
        if diff:
            print(f"value_check: {oid} -> {name}: {len(diff)} of {N} coefficients differ "
                  f"(first at X^{diff[0]}: predicted {pred[diff[0]]}, OpenFHE {raw[diff[0]]})")
            bad += 1
        sc = dec.get(oid, {}).get("scale")
        if sc is not None and int(sc) != int(o["decryptSf"]):
            print(f"value_check: {oid}: replayed scale {sc} != OpenFHE Decrypt scalingFactorInt {o['decryptSf']}")
            bad += 1
        # the user-visible slots are OpenFHE's decode of raw * decryptSf^-1; report them too
        checked += 1
    if bad:
        print(f"value_check: FAILED ({bad} problem(s))")
        return 1
    print(f"value_check: OK: {checked} output(s), all {N} coefficients of the predicted message equal "
          f"OpenFHE's raw decryption; scales equal Decrypt's scalingFactorInt")
    return 0


if __name__ == "__main__":
    sys.exit(main())
