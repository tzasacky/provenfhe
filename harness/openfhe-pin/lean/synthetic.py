#!/usr/bin/env python3
"""Write a small synthetic `openfhe-pin/v1` case (toy BGV in pure Python; no OpenFHE).

    synthetic.py OUTDIR [--n 8] [--seed 1] [--corrupt]

A loader / plumbing test for openfhe_pin: one public key, one fresh encryption `ct_1` of `pt_1`
over two limbs, its decryption computed here by the switch-to-one-limb procedure. There is no
program (`prog.fhecheck.json` holds an error object that is NOT an extractor refusal), so run it
with `openfhe_pin --only a,c`: checks a and c run; b, d, e, f do not, and the group `x`, which
requires a missing program to be an expected extractor refusal, is left out.
`--corrupt` flips one coefficient of the ciphertext: the checker must then FAIL.
"""
import json, os, random, sys


def negmul(a, b, n):
    out = [0] * n
    for i in range(n):
        for j in range(n):
            k = i + j
            if k < n:
                out[k] += a[i] * b[j]
            else:
                out[k - n] -= a[i] * b[j]
    return out


def centred(x, q):
    x %= q
    return x - q if 2 * x > q else x


def main():
    args = sys.argv[1:]
    out = args[0]
    n = int(args[args.index("--n") + 1]) if "--n" in args else 8
    rnd = random.Random(int(args[args.index("--seed") + 1]) if "--seed" in args else 1)
    t, qs = 257, [1073872897, 1074266113]
    Q = qs[0] * qs[1]
    tern = lambda: [rnd.choice([-1, 0, 1]) for _ in range(n)]
    err = lambda: [rnd.randint(-6, 6) for _ in range(n)]
    s, e, u, e1, e2 = tern(), err(), tern(), err(), err()
    a = [rnd.randrange(Q) for _ in range(n)]
    b = [(t * e[i] - x) % Q for i, x in enumerate(negmul(a, s, n))]
    m = [rnd.randrange(t) for _ in range(n)]
    c0 = [(x + t * e1[i] + m[i]) % Q for i, x in enumerate(negmul(b, u, n))]
    c1 = [(x + t * e2[i]) % Q for i, x in enumerate(negmul(a, u, n))]
    # decryption: centred phase, one t-corrected switch by q_1, centred mod q_0, mod t
    ph = [centred(c0[i] + x, Q) for i, x in enumerate(negmul(c1, s, n))]
    q1, q0 = qs[1], qs[0]
    sw = [(c + t * centred(-c * pow(t, -1, q1), q1)) // q1 for c in ph]
    decq = [x % q0 for x in sw]
    dec = [centred(x, q0) % t for x in sw]
    if "--corrupt" in args:
        c0[0] = (c0[0] + 1) % Q
    os.makedirs(out, exist_ok=True)
    name = os.path.basename(os.path.normpath(out))
    L = []
    rns = lambda nm, v: [L.append(f"{nm} {i} {q} " + " ".join(str(x % q) for x in v)) for i, q in enumerate(qs)]
    exact = lambda nm, v: L.append(f"{nm} 0 0 " + " ".join(str(x) for x in v))
    exact("s", s); rns("s.rns", s); rns("pk.b", b); rns("pk.a", a); exact("pk.e", e)
    exact("enc1.u", u); exact("enc1.e1", e1); exact("enc1.e2", e2)
    rns("pt_1.p", m); rns("ct_1.0", c0); rns("ct_1.1", c1)
    L.append(f"ct_1.dec 0 {t} " + " ".join(map(str, dec)))
    L.append(f"ct_1.decq 0 {q0} " + " ".join(map(str, decq)))
    open(os.path.join(out, "polys.txt"), "w").write("\n".join(L) + "\n")
    pin = {"format": "openfhe-pin/v1", "case": name, "seed": "0", "generator": "synthetic.py (toy BGV, not OpenFHE)",
           "N": n, "t": str(t), "qs": [str(q) for q in qs], "special": [], "scaling": "FIXEDMANUAL",
           "dnum": 1, "towersPerDigit": 2, "secret": "s", "secretRns": "s.rns",
           "public": {"b": "pk.b", "a": "pk.a", "e": "pk.e"}, "evalKeys": [],
           "encryptions": [{"ct": "ct_1", "pt": "pt_1", "u": "enc1.u", "e1": "enc1.e1", "e2": "enc1.e2", "randomness": "scripted"}],
           "objects": {"pt_1": {"kind": "pt", "towers": 2, "nsd": 1, "sf": "1", "level": 0, "poly": "pt_1.p"},
                       "ct_1": {"kind": "ct", "towers": 2, "parts": 2, "nsd": 1, "sf": "1", "level": 0,
                                "polys": ["ct_1.0", "ct_1.1"],
                                "decrypt": {"raw": "ct_1.dec", "rawQ0": "ct_1.decq", "sf": str(pow(q1, -1, t))}}},
           "final": ["ct_1"], "notes": ["synthetic toy case; error bound 6 instead of 39"]}
    json.dump(pin, open(os.path.join(out, "pin.json"), "w"), indent=1)
    json.dump({"format": "fhe-check/v1", "error": "synthetic case: no program"}, open(os.path.join(out, "prog.fhecheck.json"), "w"))
    open(os.path.join(out, "trace.jsonl"), "w").write("")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__); sys.exit(2)
    main()
