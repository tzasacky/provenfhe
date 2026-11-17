#!/usr/bin/env python3
"""UNTRUSTED quick sanity check of one openfhe-pin case directory (exporter-side; the real checks
are the Lean checker's). Independent of the C++ exporter: pure Python big integers.

  selftest.py <casedir> [--max-objects K] [--no-keys] [--json]

Checks
  shape    polys.txt lines: N coefficients, residues in [0, modulus), limbs consecutive from 0
  ids      every ct/pt id of trace.jsonl is in pin.json objects
  secret   every limb of s.rns is the centred vector s
  pk       pk.b == t*e - a*s on every limb (if pk.e was captured)
  enc      every encryption with captured randomness: ct == (b*u + t*e1 + m, a*u + t*e2)
  keys     every eval-key digit: (b + a*s_new - [limb in digit] * (P mod q) * s_old) / t is ONE small
           integer vector over all limbs (s_old = s^2 for relin, s for rot; s_new = s for relin,
           sigma_{index^-1}(s) for rot)
  decrypt  for every ciphertext with a decryption: phase = c0 + c1 s (+ c2 s^2 ...) mod Q_l (CRT,
           centred), reduced mod t, against decrypt.raw:  equal | factor f (raw == f * textbook mod t)
           | differs; f is compared with (q_1 ... q_{l-1})^-1 mod t. rawQ0 mod t (centred) == raw.
Exit status 0 if nothing is wrong (a 'differs' decryption is reported, and counted in the summary,
but is not an exporter error by itself: the phase may have wrapped)."""
import json
import sys
from math import prod


def load_polys(path):
    P = {}
    bad = []
    with open(path) as f:
        for ln, line in enumerate(f, 1):
            a = line.split(" ")
            name, limb, mod = a[0], int(a[1]), int(a[2])
            co = [int(x) for x in a[3:]]
            P.setdefault(name, [])
            if limb != len(P[name]):
                bad.append(f"line {ln}: {name} limb {limb} out of order")
            if mod > 0 and any(c < 0 or c >= mod for c in co):
                bad.append(f"line {ln}: {name} residue out of range")
            P[name].append((mod, co))
    return P, bad


def negmul(a, b, q):
    """a*b mod (X^n + 1, q) for residues in [0, q): Kronecker substitution on Python integers."""
    n = len(a)
    if n <= 32:
        r = [0] * (2 * n)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    r[i + j] += x * y
        return [(r[i] - r[i + n]) % q for i in range(n)]
    w = (2 * q.bit_length() + n.bit_length() + 8) // 8
    A = int.from_bytes(b"".join(x.to_bytes(w, "little") for x in a), "little")
    B = int.from_bytes(b"".join(x.to_bytes(w, "little") for x in b), "little")
    C = (A * B).to_bytes(2 * n * w, "little")
    r = [int.from_bytes(C[i * w:(i + 1) * w], "little") for i in range(2 * n)]
    return [(r[i] - r[i + n]) % q for i in range(n)]


def centre(x, q):
    return x - q if x > q // 2 else x


def crt_centred(limbs):
    """limbs: [(q, coeffs)] -> centred integers mod prod q"""
    Q = prod(q for q, _ in limbs)
    n = len(limbs[0][1])
    out = [0] * n
    for q, co in limbs:
        h = Q // q
        w = h * pow(h, -1, q)
        for i in range(n):
            out[i] += co[i] * w
    return [centre(x % Q, Q) for x in out], Q


def automorph(s, g, n):
    """sigma_g: X -> X^g on a signed vector (negacyclic)"""
    r = [0] * n
    for i, x in enumerate(s):
        k = (i * g) % (2 * n)
        if k < n:
            r[k] += x
        else:
            r[k - n] -= x
    return r


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    d = args[0]
    maxobj = 10 ** 9
    if "--max-objects" in sys.argv:
        maxobj = int(sys.argv[sys.argv.index("--max-objects") + 1])
    pin = json.load(open(d + "/pin.json"))
    P, bad = load_polys(d + "/polys.txt")
    N, t = pin["N"], int(pin["t"])
    qs = [int(x) for x in pin["qs"]]
    sp = [int(x) for x in pin["special"]]
    errs = list(bad)
    rep = {"case": pin["case"], "scaling": pin["scaling"], "N": N}
    for name, limbs in P.items():
        for mod, co in limbs:
            if len(co) != N:
                errs.append(f"{name}: {len(co)} coefficients, expected {N}")
    # ids
    ids = set()
    for line in open(d + "/trace.jsonl"):
        o = json.loads(line)
        if "id" in o and o.get("kind") in ("ct", "pt"):  # key ids (pk/sk/ek) have no object entry
            ids.add(o["id"])
    missing = sorted(ids - set(pin["objects"]))
    if missing:
        errs.append(f"trace ids missing from objects: {missing[:5]}")
    rep["traceIds"] = len(ids)
    # secret
    s = P[pin["secret"]][0][1]
    for q, co in P[pin["secretRns"]]:
        if [centre(x, q) for x in co] != s:
            errs.append("secretRns limb disagrees with s")
    smod = lambda q: [x % q for x in s]
    # pk
    pb, pa = P[pin["public"]["b"]], P[pin["public"]["a"]]
    if pin["public"]["e"]:
        e = P[pin["public"]["e"]][0][1]
        for (q, b), (_, a) in zip(pb, pa):
            as_ = negmul(a, smod(q), q)
            if [(t * e[i] - as_[i]) % q for i in range(N)] != b:
                errs.append("pk.b != t*e - a*s")
                break
    # encryptions
    nenc = 0
    for en in pin["encryptions"]:
        if en["randomness"] == "none":
            continue
        u, e1, e2 = (P[en[k]][0][1] for k in ("u", "e1", "e2"))
        ct = pin["objects"][en["ct"]]
        m = P[pin["objects"][en["pt"]]["poly"]]
        for l in range(ct["towers"]):
            q = qs[l]
            assert pb[l][0] == q
            um = [x % q for x in u]
            c0 = negmul(pb[l][1], um, q)
            c1 = negmul(pa[l][1], um, q)
            c0 = [(c0[i] + t * e1[i] + m[l][1][i]) % q for i in range(N)]
            c1 = [(c1[i] + t * e2[i]) % q for i in range(N)]
            if c0 != P[ct["polys"][0]][l][1] or c1 != P[ct["polys"][1]][l][1]:
                errs.append(f"encryption {en['ct']} not reproduced on limb {l}")
                break
        nenc += 1
    rep["encryptionsChecked"] = nenc
    # eval keys
    alpha = pin["ksInfo"]["numPerPartQ"]
    Pprod = prod(sp)
    s2 = None
    nkeys = 0
    if "--no-keys" not in sys.argv:
        for ek in pin["evalKeys"]:
            if ek.get("power", 2) != 2:
                continue
            if ek["kind"] == "relin":
                if s2 is None:
                    big = 1 << 62  # s^2 over the integers: |coefficient| <= N * max|s|^2, far below 2^61
                    s2 = [centre(x, big) for x in negmul([v % big for v in s], [v % big for v in s], big)]
                s_old, s_new = s2, s
            else:
                g = ek["index"]
                s_old, s_new = s, automorph(s, pow(g, -1, 2 * N), N)
            for j, dg in enumerate(ek["digits"]):
                ev = None
                for l, ((q, b), (_, a)) in enumerate(zip(P[dg["b"]], P[dg["a"]])):
                    x = negmul(a, [v % q for v in s_new], q)
                    indig = l < len(qs) and j * alpha <= l < (j + 1) * alpha
                    tinv = pow(t, -1, q)
                    el = [centre(((b[i] + x[i] - (Pprod * s_old[i] if indig else 0)) * tinv) % q, q) for i in range(N)]
                    if ev is None:
                        ev = el
                    elif ev != el:
                        errs.append(f"eval key {ek['kind']} {ek.get('index', '')} digit {j}: limb {l} gives a different error vector")
                        break
            nkeys += 1
    rep["evalKeysChecked"] = nkeys
    # decryptions
    dec = {"equal": 0, "factor-expected": 0, "factor-other": 0, "differs": 0, "error": 0, "none": 0}
    detail = []
    factors = {}
    k = 0
    for oid, o in pin["objects"].items():
        if o["kind"] != "ct":
            continue
        if o.get("decrypt") is None:
            dec["error" if "decryptError" in o else "none"] += 1
            continue
        k += 1
        if k > maxobj:
            continue
        L = o["towers"]
        raw = P[o["decrypt"]["raw"]][0]
        if raw[0] != t:
            errs.append(f"{oid}: decrypt.raw modulus is not t")
        if o["decrypt"]["rawQ0"]:
            q0, rq = P[o["decrypt"]["rawQ0"]][0]
            if [centre(x, q0) % t for x in rq] != raw[1]:
                errs.append(f"{oid}: rawQ0 mod t != raw")
        ph = []
        for l in range(L):
            q = qs[l]
            acc = list(P[o["polys"][0]][l][1])
            sp_ = smod(q)
            pw = sp_
            for part in o["polys"][1:]:
                x = negmul(P[part][l][1], pw, q)
                acc = [(acc[i] + x[i]) % q for i in range(N)]
                pw = negmul(pw, sp_, q)
            ph.append((q, acc))
        cz, Q = crt_centred(ph)
        text = [x % t for x in cz]
        expf = pow(prod(qs[1:L]) % t, -1, t) if L > 1 else 1
        norm = max(abs(x) for x in cz)
        if text == raw[1] and expf == 1:
            res = "equal"
        elif [x * expf % t for x in text] == raw[1]:
            res = "factor-expected"
            factors.setdefault(L, set()).add(expf)
        else:
            f = None
            for i in range(N):
                if text[i] % t:
                    f = raw[1][i] * pow(text[i], -1, t) % t
                    break
            if f is not None and [x * f % t for x in text] == raw[1]:
                res = "factor-other"
            else:
                res = "differs"
            detail.append({"id": oid, "towers": L, "parts": o["parts"], "result": res, "factor": f,
                           "expected": expf, "phaseBits": norm.bit_length(), "Qbits": Q.bit_length()})
        dec[res] += 1
    rep["decrypt"] = dec
    rep["decryptFactorByTowers"] = {str(L): sorted(v) for L, v in sorted(factors.items())}
    rep["decryptDetail"] = detail[:20]
    rep["errors"] = errs
    exc = [n for n in pin["notes"] if n.startswith("EXC ")]
    rep["exceptions"] = len(exc)
    if "--json" in sys.argv:
        print(json.dumps(rep))
    else:
        print(json.dumps(rep, indent=1))
    sys.exit(1 if errs else 0)


if __name__ == "__main__":
    main()
