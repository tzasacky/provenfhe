#!/usr/bin/env python3
"""UNTRUSTED quick sanity check of one BFV openfhe-pin case directory (exporter-side; the real
checks are the Lean checker's). Independent of the C++ exporter: pure Python big integers
(negacyclic products by Kronecker substitution).

  selftest_bfv.py <casedir> [--json] [--max-n-keys N]

Checks
  shape    polys.txt lines: N coefficients, residues in [0, modulus), limbs consecutive from 0;
           every ciphertext / plaintext limb modulus is the matching prime of qs
  ids      every ct/pt id of trace.jsonl is in pin.json objects; final ids are objects
  secret   every limb of s.rns is the centred vector s (ternary)
  pk       pk.b == e - a*s on every limb (if pk.e was captured)
  enc      STANDARD entries with captured randomness: c0 == b*u + e1 + ceil(Q_k*p/t), c1 == a*u + e2 over
           the k limbs of the plaintext; the noise [c0 + c1 s - floor(Q_k/t) p]_{Q_k} of every fresh
           ciphertext is reported (max over the case: "freshNoise") and, for STANDARD, compared with
           39*(1 + 2N) + ceil((Q_k mod t)(t-1)/t)
           EXTENDED entries: the same relation modulo Q*r followed by the exact division
           (c - [c]_r)/r (centred [c]_r) of both components
  keys     HYBRID: for every digit j, b_j + a_j*s' - P*[Qhat_j^-1]_{Q_j}*Qhat_j*target is ONE small
           integer vector over all limbs of Q*P;  BV: b_j + a_j*s' - (target on limb j) (digit size 0),
           - 2^(w*k)*target on limb i (digit size w). relin: s' = s, target = s^2; rot g: s' =
           s(X^(g^-1 mod 2N)), target = s (KeySwitchGen(s, s'), base-leveledshe.cpp:419-427: the key
           switch runs BEFORE the automorphism, bfvrns-leveledshe.cpp:777-849).
           Skipped for N > --max-n-keys (default 4096) except the first key.
  decrypt  for every ciphertext with a decryption: round(t*[c0 + c1 s (+ c2 s^2)]_{Q_l}/Q_l) mod t
           (exact; a tie cannot occur for odd Q_l) against decrypt.raw; mismatches are
           listed with the distance of t*phase/Q_l from the nearest rounding boundary
  drops    largest traced levelsDropped (and how many are > 0), from trace.jsonl
Exit status 0 if nothing is wrong. A decrypt mismatch is a failure only if t*phase/Q_l is at least
1/4 away from a rounding boundary: PKEBFVRNS::Decrypt is a function of the phase, but the HPS-family
ScaleAndRound adds the binary64 sum of fractional parts to an integer sum of up to ~2^49 before
rounding (dcrtpoly-impl.h:1356-1480, t not a power of two), so it is exact rounding only up to an
error which the comments of the library bound by 1/4. Every mismatch is listed in decryptMismatch
with its distance from the boundary (maxBoundaryDistance)."""
import json
import sys
from fractions import Fraction
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


def kron_mul(a, b, n):
    """Negacyclic product of two integer vectors with NON-NEGATIVE entries (length n), exact."""
    k = ((max(a) * max(b) * n).bit_length() + 8) // 8  # bytes per packed coefficient
    A = int.from_bytes(b"".join(x.to_bytes(k, "little") for x in a), "little")
    B = int.from_bytes(b"".join(x.to_bytes(k, "little") for x in b), "little")
    raw = (A * B).to_bytes(2 * n * k, "little")
    c = [int.from_bytes(raw[i * k:(i + 1) * k], "little") for i in range(2 * n)]
    return [c[i] - c[i + n] for i in range(n)]


def nmul(a, b, n):
    """Negacyclic product of two integer vectors (any signs), exact."""
    ap, an = [max(x, 0) for x in a], [max(-x, 0) for x in a]
    bp, bn = [max(x, 0) for x in b], [max(-x, 0) for x in b]
    r = [0] * n
    for (x, sx) in ((ap, 1), (an, -1)):
        if not any(x):
            continue
        for (y, sy) in ((bp, 1), (bn, -1)):
            if not any(y):
                continue
            z = kron_mul(x, y, n)
            s = sx * sy
            for i in range(n):
                r[i] += s * z[i]
    return r


def crt(limbs):
    """[(q, coeffs)] -> (Q, coefficient list in [0, Q))."""
    qs = [q for q, _ in limbs]
    Q = prod(qs)
    n = len(limbs[0][1])
    r = [0] * n
    for q, co in limbs:
        h = Q // q
        f = h * pow(h, -1, q)
        for i in range(n):
            r[i] += f * co[i]
    return Q, [x % Q for x in r]


def centre(x, Q):
    return x - Q if 2 * x > Q else x


def auto(s, g, n):
    """s(X) -> s(X^g) in Z[X]/(X^n + 1)."""
    r = [0] * n
    for i, c in enumerate(s):
        e = i * g % (2 * n)
        if e < n:
            r[e] += c
        else:
            r[e - n] -= c
    return r


def main():
    d = sys.argv[1]
    as_json = "--json" in sys.argv
    max_n_keys = 4096
    if "--max-n-keys" in sys.argv:
        max_n_keys = int(sys.argv[sys.argv.index("--max-n-keys") + 1])
    pin = json.load(open(d + "/pin.json"))
    P, bad = load_polys(d + "/polys.txt")
    res = {"case": pin["case"], "fail": []}
    fail = res["fail"]
    fail += bad[:5]
    N, t = pin["N"], int(pin["t"])
    qs = [int(x) for x in pin["qs"]]
    sp = [int(x) for x in pin["special"]]
    L = len(qs)
    bfv = pin["bfv"]
    if pin.get("scheme") != "BFV":
        fail.append("not a BFV pin.json")
    for name, limbs in P.items():
        if any(len(co) != N for _, co in limbs):
            fail.append(f"{name}: not N coefficients")
    # ids
    ids = set()
    drops = []
    for line in open(d + "/trace.jsonl"):
        try:
            e = json.loads(line)
        except Exception:
            fail.append("trace.jsonl: unparsable line")
            break
        i = e.get("id")
        if isinstance(i, str) and (i.startswith("ct_") or i.startswith("pt_")):
            ids.add(i)
        for x in e.get("ids", []) if isinstance(e.get("ids"), list) else []:
            if isinstance(x, str) and (x.startswith("ct_") or x.startswith("pt_")):
                ids.add(x)
        if e.get("name") == "levelsDropped":
            drops.append(e.get("v"))
    missing = sorted(ids - set(pin["objects"]))
    if missing:
        fail.append(f"ids of the trace without an object: {missing[:5]}")
    for f_ in pin["final"]:
        if f_ not in pin["objects"]:
            fail.append(f"final {f_} is not an object")
    res["drops"] = {"n": len(drops), "positive": sum(1 for x in drops if x), "max": max(drops) if drops else 0}
    # secret
    s = P["s"][0][1]
    gauss = bfv.get("secretKeyDist") == "GAUSSIAN"
    if any(abs(x) > 1 for x in s) and not gauss:
        fail.append("secret is not ternary")
    for q, co in P["s.rns"]:
        if co != [x % q for x in s]:
            fail.append("s.rns is not s")
            break
    s2 = nmul(s, s, N)
    sq = [q for q, _ in P["s.rns"]]  # Q; EXTENDED encryption: Q then the extra prime r
    if sq != (qs + [int(bfv["extendedPrime"])] if bfv["enc"] == "EXTENDED" else qs):
        fail.append("s.rns limbs are not Q (EXTENDED: Q then r)")

    def mul_s(co, q, what=s):
        return [x % q for x in nmul(co, what, N)]

    # pk
    pkb, pka = P["pk.b"], P["pk.a"]
    if pin["public"]["e"]:
        e = P[pin["public"]["e"]][0][1]
        for (q, b), (_, a) in zip(pkb, pka):
            az = mul_s(a, q)
            if any((b[i] + az[i] - e[i]) % q for i in range(N)):
                fail.append("pk.b != e - a*s")
                break
    else:
        fail.append("pk.e not captured")
    # objects: shapes
    for i, o in pin["objects"].items():
        names = o["polys"] if o["kind"] == "ct" else [o["poly"]]
        for nm in names:
            if nm not in P:
                fail.append(f"{i}: {nm} not in polys.txt")
            elif [q for q, _ in P[nm]] != qs[:o["towers"]]:
                fail.append(f"{i}: limbs of {nm} are not the first {o['towers']} primes of qs")
    # encryptions
    Be = 39
    fresh_noise, n_enc_checked = 0, 0
    ext = bfv["enc"] == "EXTENDED"
    r_ext = int(bfv["extendedPrime"])
    for en in pin["encryptions"]:
        ct, pt = pin["objects"][en["ct"]], pin["objects"][en["pt"]]
        if pt["encoding"] != "packed":
            continue
        k = pt["towers"]
        Qk, p = crt(P[pt["poly"]])
        if any(x >= t for x in p):
            fail.append(f"{en['pt']}: stored packed plaintext has a coefficient >= t")
            continue
        c0, c1 = P[ct["polys"][0]], P[ct["polys"][1]]
        if en["u"] and not en.get("extended"):
            u, e1, e2 = (P[en[x]][0][1] for x in ("u", "e1", "e2"))
            enc = [-((-Qk * x) // t) for x in p]
            for l in range(k):
                q = qs[l]
                bu, au = nmul(pkb[l][1], u, N), nmul(pka[l][1], u, N)
                if any((bu[i] + e1[i] + enc[i] - c0[l][1][i]) % q or (au[i] + e2[i] - c1[l][1][i]) % q for i in range(N)):
                    fail.append(f"{en['ct']}: STANDARD encryption relation fails on limb {l}")
                    break
            n_enc_checked += 1
        elif en["u"] and en.get("extended"):
            u, e1, e2 = (P[en[x]][0][1] for x in ("u", "e1", "e2"))
            Qr = Qk * r_ext
            mods = qs[:k] + [r_ext]
            if len(pkb) != k + 1:
                fail.append("EXTENDED: public key is not over Q*r")
                continue
            _, B = crt(pkb)
            _, A = crt(pka)
            bu, au = nmul(B, u, N), nmul(A, u, N)
            x0 = [(bu[i] + e1[i] + (-((-Qr * p[i]) // t))) % Qr for i in range(N)]
            x1 = [(au[i] + e2[i]) % Qr for i in range(N)]

            def down(x):
                rr = centre(x % r_ext, r_ext)
                return ((x - rr) // r_ext) % Qk
            if en.get("extendedPre"):
                if crt(P[en["extendedPre"][0]])[1] != x0 or crt(P[en["extendedPre"][1]])[1] != x1:
                    fail.append(f"{en['ct']}: extendedPre is not (b*u + e1 + ceil(Q*r*p/t), a*u + e2) mod Q*r")
            _, C0 = crt(c0)
            _, C1 = crt(c1)
            if [down(x) for x in x0] != C0 or [down(x) for x in x1] != C1:
                fail.append(f"{en['ct']}: EXTENDED encryption relation fails")
            n_enc_checked += 1
            del mods
        # fresh noise
        _, C0 = crt(c0)
        _, C1 = crt(c1)
        c1s = nmul(C1, s, N)
        delta = Qk // t
        nz = max(abs(centre((C0[i] + c1s[i] - delta * p[i]) % Qk, Qk)) for i in range(N))
        fresh_noise = max(fresh_noise, nz)
        if not ext and not gauss and en["randomness"] != "none":
            bound = Be * (1 + 2 * N) + (-((-(Qk % t) * (t - 1)) // t))
            if nz > bound:
                fail.append(f"{en['ct']}: fresh noise {nz} > {bound}")
    res["encChecked"] = n_enc_checked
    res["freshNoise"] = fresh_noise
    # TimesQovert of every encryption: ceil(Q'*p/t) mod q_i over the limbs it is stored on (Q' = their product)
    ntq = 0
    for en in pin["encryptions"]:
        if not en.get("timesQovert"):
            continue
        tq = P[en["timesQovert"]]
        pt = pin["objects"][en["pt"]]
        _, pv = crt(P[pt["poly"]])
        Qx = 1
        for q, _ in tq:
            Qx *= q
        want = [-((-Qx * x) // t) for x in pv]
        if crt(tq)[1] != [w % Qx for w in want]:
            fail.append(f"{en['ct']}: timesQovert is not ceil(Q*p/t) over its limbs")
        ntq += 1
    res["timesQovertChecked"] = ntq
    # decryption tables: recomputed from qs and t (bfvrns-cryptoparameters.cpp:432-481) with Python binary64
    dt = pin.get("decryptTables")
    if dt is not None:
        import struct
        qq = [int(x) for x in dt["qs"]]
        Qd = 1
        for q in qq:
            Qd *= q
        qmsb = max(qq).bit_length()
        split = qmsb + len(qq).bit_length() >= 52
        hx = lambda d: struct.unpack("<Q", struct.pack("<d", d))[0]
        for i, q in enumerate(qq):
            th = pow(Qd // q, -1, q) * t
            if int(dt["intLo"][i]) != th // q % t or int(dt["fracLo"][i], 16) != hx(float(th % q) / float(q)):
                fail.append(f"decryptTables: entry {i} (lo) differs from the recomputation")
            if split:
                thB = th << (qmsb >> 1)
                if int(dt["intHi"][i]) != thB // q % t or int(dt["fracHi"][i], 16) != hx(float(thB % q) / float(q)):
                    fail.append(f"decryptTables: entry {i} (hi) differs from the recomputation")
        if not split and (dt["intHi"] or dt["fracHi"]):
            fail.append("decryptTables: B tables present on the non-split path")
        res["decryptTablesChecked"] = True
    # eval keys
    hybrid = bfv["ks"] == "HYBRID"
    w = bfv["digitSizeBV"]
    Pm = prod(sp) if sp else 1
    alpha = bfv["towersPerDigit"]
    nkeys = 0
    key_err = 0
    for ki, ek in enumerate(pin["evalKeys"]):
        if N > max_n_keys and ki > 0:
            continue
        if ek["kind"] == "relin":
            if ek.get("power", 2) != 2:
                continue
            target, snew = s2, s
        else:
            target, snew = s, auto(s, pow(ek["index"], -1, 2 * N), N)
        for j, dg in enumerate(ek["digits"]):
            b, a = P[dg["b"]], P[dg["a"]]
            mods = [q for q, _ in b]
            if mods != (qs + sp if hybrid else sq):
                fail.append(f"{dg['b']}: limbs are not {'Q then P' if hybrid else 'the limbs of the secret'}")
                break
            if hybrid:
                dq = qs[j * alpha:(j + 1) * alpha]
                Qj = prod(dq)
                Qhat = prod(qs) // Qj
                factor = Pm * Qhat * pow(Qhat, -1, Qj)
                fl = [factor % q for q in mods]
            elif w == 0:
                fl = [1 if l == j else 0 for l in range(len(sq))]
            else:
                fl = [pow(2, w * dg["power"], sq[l]) if l == dg["limb"] else 0 for l in range(len(sq))]
            ev = None
            for l, q in enumerate(mods):
                az = nmul(a[l][1], snew, N)
                e = [centre((b[l][1][i] + az[i] - fl[l] * target[i]) % q, q) for i in range(N)]
                if ev is None:
                    ev = e
                elif e != ev:
                    fail.append(f"{dg['b']}: key error is not one integer vector (limb {l})")
                    break
            if ev is not None:
                key_err = max(key_err, max(abs(x) for x in ev))
            nkeys += 1
    if key_err > Be:
        fail.append(f"eval-key error {key_err} > {Be}")
    res["keyDigitsChecked"] = nkeys
    res["keyError"] = key_err
    # decryptions
    exc = any(n.startswith("EXC ") for n in pin["notes"])
    ndec, mism, unsafe, final_margin = 0, [], [], {}
    nphase = 0
    min_margin = None
    for i, o in pin["objects"].items():
        if o["kind"] != "ct" or not o.get("decrypt"):
            continue
        cs = [crt(P[nm]) for nm in o["polys"]]
        Ql = cs[0][0]
        ph = list(cs[0][1])
        x = nmul(cs[1][1], s, N)
        for j in range(N):
            ph[j] += x[j]
        if len(cs) == 3:
            x = nmul(cs[2][1], s2, N)
            for j in range(N):
                ph[j] += x[j]
        if o["decrypt"].get("phase"):
            # the exporter's recomputed DecryptCore output is the phase mod Q_l
            if crt(P[o["decrypt"]["phase"]])[1] != [x % Ql for x in ph]:
                fail.append(f"{i}: decrypt.phase is not c0 + c1 s (+ c2 s^2) mod Q_l")
            nphase += 1
        raw = P[o["decrypt"]["raw"]]
        # modulus t (canonical), or an exact integer line (modulus 0) when the library returned t itself
        if raw[0][0] not in (t, 0) or any(v < 0 or v > t for v in raw[0][1]):
            fail.append(f"{i}: decrypt.raw is neither a mod-t line nor exact integers in [0, t]")
            continue
        rawv = [v % t for v in raw[0][1]]
        bad_here, worst, ct_margin = 0, None, None
        for j in range(N):
            c = centre(ph[j] % Ql, Ql)
            num = 2 * t * c + Ql
            m = (num // (2 * Ql)) % t  # floor(t*c/Ql + 1/2)
            fr = Fraction(t * c, Ql)
            dist = abs(abs(fr - (fr.numerator // fr.denominator)) - Fraction(1, 2))  # distance to a boundary
            if min_margin is None or dist < min_margin:
                min_margin = dist
            if ct_margin is None or dist < ct_margin:
                ct_margin = dist
            if m != rawv[j]:
                bad_here += 1
                if worst is None or dist > worst:
                    worst = dist
        ndec += 1
        if ct_margin < Fraction(1, 4):
            unsafe.append(i)
        if i in pin["final"]:
            final_margin[i] = float(ct_margin)
        if bad_here:
            mism.append({"id": i, "towers": o["towers"], "parts": o["parts"], "coefficients": bad_here,
                         "maxBoundaryDistance": float(worst)})
            if worst >= Fraction(1, 4):
                fail.append(f"decrypt: {i} ({o['towers']} limbs): {bad_here} coefficients differ from exact rounding, "
                            f"up to {float(worst):.3g} away from a rounding boundary")
    res["decrypted"] = ndec
    res["phaseChecked"] = nphase
    res["decryptMismatch"] = mism
    # ciphertexts whose t*phase/Q_l comes within 1/4 of a rounding boundary: the noise is at least
    # Q_l/(4t), or the phase is not an encryption under s at all (the traced intermediate of a
    # rotation is under the permuted key) -- informational
    res["phaseNearBoundary"] = unsafe
    res["finalBoundaryDistance"] = final_margin
    res["minBoundaryDistance"] = float(min_margin) if min_margin is not None else None
    res["ok"] = not fail
    if as_json:
        print(json.dumps(res))
    else:
        for k, v in res.items():
            print(f"{k}: {v}")
    sys.exit(0 if not fail else 1)


if __name__ == "__main__":
    main()
