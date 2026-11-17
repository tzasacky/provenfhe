#!/usr/bin/env python3
"""check.py -- UNTRUSTED cross-check of Challenge/BFVMul/Float.lean (standard library only).

The two binary64 sums of OpenFHE's HPS-family BFV multiplication, as transcribed in
`Challenge.BFVMul.Fl.nuSw` / `nuSr`, are evaluated here

  * in IEEE binary64, round to nearest (Python `float`: `float(int)`, `*`, `/`, `+` are
    correctly rounded), without contraction and with every `s += a*b` fused (the fused
    multiply-add is computed exactly in `Fraction` and rounded once), and
  * exactly, in `Fraction`,

and the measured error is compared with the proved bounds `doubleSw k / 2^53`,
`doubleSr ms / 2^53` (`Challenge.BFVMul.nuSw_tol`, `nuSr_tol`).

  check.py synth [--trials N]     parameter sets of the committed OpenFHE BFV examples
                                  (harness/frontend/examples/openfhe_bfv_*.params.json) and
                                  synthetic ones; random and extreme residues
  check.py real  FILE...          dumps of the real library functions written by dump.cpp:
                                  (a) the library's double tables equal the transcription's, bit
                                  for bit; (b) the outputs of DCRTPoly::SwitchCRTBasis and
                                  DCRTPoly::ScaleAndRound equal the transcription's `Fl.switch1`,
                                  `Fl.scale1` with the binary64 sums, coefficient by coefficient;
                                  (c) error of the sums against the proved bound

Exit status 1 if a bound is violated, a table differs, or an output differs.
"""
import glob, json, os, random, struct, sys
from fractions import Fraction as Fr

F = 2 ** 53


def double_sw(k):            # Spec.BudgetBFV.doubleSw
    return k * (k + 5)


def double_sr(ms):           # Spec.BudgetBFV.doubleSr
    return (len(ms) + 6) * (1 + sum(ms))


def fma(a, b, c):            # a*b + c rounded once
    return float(Fr(a) * Fr(b) + Fr(c))


def q_inv(q):                # Fl.qInv
    return 1.0 / float(q)


def frac(n, m):              # Fl.frac
    return float(n) / float(m)


def nu_sw(qs, y, fused=False):          # Fl.nuSw
    s = 0.5
    for q, yi in zip(qs, y):
        a, b = float(yi), q_inv(q)
        s = fma(a, b, s) if fused else s + a * b
    return s


def nu_sr(ms, ns, x, fused=False):      # Fl.nuSr
    s = 0.5
    for m, n, xi in zip(ms, ns, x):
        a, b = frac(n, m), float(xi)
        s = fma(a, b, s) if fused else s + a * b
    return s


def exact_sw(qs, y):
    return Fr(1, 2) + sum(Fr(yi, q) for q, yi in zip(qs, y))


def exact_sr(ms, ns, x):
    return Fr(1, 2) + sum(Fr(xi * n, m) for m, n, xi in zip(ms, ns, x))


def prod(l):
    r = 1
    for v in l:
        r *= v
    return r


def inv_mod(a, m):           # HPS.invMod
    return pow(a, -1, m) if m > 1 else 0


def digits(qs, x):           # HPS.digits
    Q = prod(qs)
    return [xi * inv_mod(Q // q, q) % q for q, xi in zip(qs, x)]


def switch1(qs, x, p, fused=False):     # Fl.switch1 with Fl.floatSums
    Q = prod(qs)
    y = digits(qs, x)
    v = int(nu_sw(qs, y, fused))        # truncation of a nonnegative double
    return (sum(yi * (Q // q % p) for q, yi in zip(qs, y)) - v * (Q % p)) % p


def theta(t, qs, ps):        # HPS.theta
    Q, P = prod(qs), prod(ps)
    return [t * P * inv_mod(Q * P // q, q) for q in qs]


def frac_nums(t, qs, ps):    # Fl.fracNums
    return [th % q for th, q in zip(theta(t, qs, ps), qs)]


def scale1(t, qs, ps, xq, p, xp, fused=False):   # Fl.scale1 with Fl.floatSums
    Q, P = prod(qs), prod(ps)
    th = theta(t, qs, ps)
    i = sum(xi * (thi // q % p) for thi, q, xi in zip(th, qs, xq))
    om = t * P * inv_mod(Q * P // p, p) // p % p
    return (i + xp * om + int(nu_sr(qs, frac_nums(t, qs, ps), xq, fused))) % p


class Stat:
    def __init__(self):
        self.rows = {}
        self.bad = 0

    def add(self, name, err, bound, flipped):
        r = self.rows.setdefault(name, [Fr(0), 0, 0, bound])
        if err > r[0]:
            r[0] = err
        r[1] += 1
        r[2] += flipped
        r[3] = max(r[3], bound)
        if err * F > bound:
            self.bad += 1
            print(f"VIOLATION {name}: error*2^53 = {float(err * F)} > bound {bound}")

    def report(self):
        print(f"{'sum':<44}{'samples':>9}{'max err*2^53':>16}{'proved bound':>16}{'ratio':>8}{'floor moved':>12}")
        for name, (err, n, fl, bound) in sorted(self.rows.items()):
            e = float(err * F)
            print(f"{name:<44}{n:>9}{e:>16.4g}{float(bound):>16.4g}{e / bound:>8.3f}{fl:>12}")


def measure_sw(st, name, qs, y):
    ex = exact_sw(qs, y)
    for fused in (False, True):
        s = nu_sw(qs, y, fused)
        st.add(f"{name} sw k={len(qs)}" + (" fma" if fused else ""), abs(Fr(s) - ex), double_sw(len(qs)),
               int(s) != ex.numerator // ex.denominator)


def measure_sr(st, name, ms, ns, x):
    ex = exact_sr(ms, ns, x)
    for fused in (False, True):
        s = nu_sr(ms, ns, x, fused)
        st.add(f"{name} sr k={len(ms)}" + (" fma" if fused else ""), abs(Fr(s) - ex), double_sr(ms),
               int(s) != ex.numerator // ex.denominator)


def extreme(rng, m):
    return rng.choice([0, 1, m - 1, m - 2, m // 2, m // 2 + 1, m // 3, min(m - 1, 2 ** 53 + 1), rng.randrange(m)])


def synth(trials):
    rng = random.Random(20261113)
    st = Stat()
    sets = {}
    here = os.path.dirname(os.path.abspath(__file__))
    for f in sorted(glob.glob(os.path.join(here, "..", "frontend", "examples", "openfhe_bfv_*.params.json"))):
        d = json.load(open(f))
        if d.get("multiplicationTechnique") not in ("HPS", "HPSPOVERQ", "HPSPOVERQLEVELED"):
            continue
        qs = tuple(e["q"] for e in d["qs"])
        rs = tuple(e["q"] for e in d["auxR"])
        sets.setdefault((d["t"], qs, rs), os.path.basename(f)[len("openfhe_bfv_"):-len(".params.json")])
    from math import gcd

    def coprimes(bits, n, avoid=()):
        """n pairwise coprime odd numbers just below 2^bits (also coprime to `avoid`)."""
        out, c = [], 2 ** bits - 1
        while len(out) < n:
            if all(gcd(c, o) == 1 for o in list(avoid) + out):
                out.append(c)
            c -= 2
        return out

    a60, a45, a30, a64 = coprimes(60, 7), coprimes(45, 6), coprimes(30, 5), coprimes(64, 4)  # 64-bit: beyond floatBasisOK, sums only meaningful
    small = [3, 5, 7]
    big = coprimes(60, 3, small)
    many = coprimes(60, 80)
    synth_sets = [
        (65537, tuple(a60[:3]), tuple(a60[3:]), "60bit-3x4"),
        (65537, tuple(a45[:3]), tuple(a45[3:]), "45bit-3x3"),
        (17, tuple(a30[:2]), tuple(a30[2:]), "30bit-2x3"),
        (65537, (small[0], big[0], small[1], big[1]), (small[2], big[2]), "mixed-sizes"),
        (2, tuple(a64[:2]), tuple(a64[2:]), "64bit-2x2"),
        (65537, tuple(many[:40]), tuple(many[40:]), "40-limbs(sums only)"),
    ]
    # one limb: the least room under doubleSw (6 at k = 1); worst observed with 54-bit moduli
    for bits in (52, 53, 54, 55, 57, 60):
        c = coprimes(bits, 2)
        synth_sets.append((65537, (c[0],), (c[1],), f"{bits}bit-1x1"))
    for t, qs, rs, name in synth_sets:
        sets.setdefault((t, qs, rs), name)
    print(f"{len(sets)} parameter sets, {trials} trials each")
    for (t, qs, rs), name in sets.items():
        tabs = []
        if "sums only" in name:
            tabs.append((qs, [rng.randrange(q) for q in qs]))
        else:
            tabs.append((qs, frac_nums(t, list(qs), list(rs))))          # scaling by t/Q into R
            tabs.append((rs, frac_nums(t, list(rs), list(qs))))          # scaling by t/R into Q
            if len(qs) >= 2:                                              # internal drop of one limb
                tabs.append((qs[-1:], frac_nums(1, list(qs[-1:]), list(qs[:-1]))))
        for _ in range(trials):
            mode = rng.randrange(3)
            for ms in (qs, rs):
                if mode == 0:
                    y = [rng.randrange(m) for m in ms]
                elif mode == 1:
                    y = [extreme(rng, m) for m in ms]
                else:   # a sum near a half-integer: all digits about m/len or m - 1
                    y = [min(m - 1, max(0, m * rng.randrange(1, 4) // (2 * len(ms)) + rng.randrange(-2, 3)))
                         for m in ms]
                measure_sw(st, name, ms, y)
            for ms, ns in tabs:
                x = [rng.randrange(m) if mode == 0 else extreme(rng, m) for m in ms]
                measure_sr(st, name, ms, ns, x)
        if len(qs) == 1:    # one limb: search near the top of the range, where the sum is near 3/2
            for ms in (qs, rs):
                for _ in range(40 * trials):
                    measure_sw(st, name, ms, [ms[0] - 1 - rng.randrange(2 ** rng.randrange(1, 50))])
    # one limb, moduli anywhere in the binade (the conversion and the reciprocal both round)
    for bits in (54, 57, 60):
        for _ in range(max(1, trials // 10)):
            q = rng.randrange(2 ** (bits - 1), 2 ** bits) | 1
            for _ in range(200):
                measure_sw(st, f"{bits}bit-1-limb-random-q", [q], [q - 1 - rng.randrange(2 ** rng.randrange(1, 50))])
    st.report()
    return st.bad


def unhex(h):
    return struct.unpack(">d", bytes.fromhex(h))[0]


def real(files):
    st = Stat()
    bad = 0

    def table(name, got, want):
        nonlocal bad
        got = [unhex(h) for h in got]
        ok = len(got) >= len(want) and all(g == w for g, w in zip(got, want))
        print(f"  table {name}: {len(want)} entries, {'identical' if ok else 'DIFFERENT'}")
        bad += 0 if ok else 1

    def outputs(name, n, f):
        """f(j, fused) -> (model limbs, library limbs) for coefficient j."""
        nonlocal bad
        plain = sum(1 for j in range(n) if f(j, False)[0] == f(j, False)[1])
        if plain == n:
            print(f"  {name}: {n} coefficients, model (no contraction) == library on all")
            return
        fused = sum(1 for j in range(n) if f(j, True)[0] == f(j, True)[1])
        print(f"  {name}: {n} coefficients; equal without contraction: {plain}; with every step fused: {fused}"
              + ("  (library built with contraction)" if fused == n else "  MISMATCH"))
        bad += 0 if fused == n else 1

    for fn in files:
        d = json.load(open(fn))
        t, Q, R, tech = d["t"], d["Q"], d["R"], d["tech"]
        print(f"{fn}: {tech}, |Q| = {len(Q)}, |R| = {len(R)}, {Q[0].bit_length()}-bit moduli")
        table("qInv", d["qInv"], [q_inv(q) for q in Q])
        table("rInv", d["rInv"], [q_inv(r) for r in R])
        n = len(d["sw_in"][0])
        col = lambda p, j: [limb[j] for limb in p]
        # SwitchCRTBasis Q -> R
        outputs("SwitchCRTBasis Q->R", n, lambda j, fu: (
            [switch1(Q, col(d["sw_in"], j), r, fu) for r in R], col(d["sw_out"], j)))
        for j in range(n):
            measure_sw(st, tech, Q, digits(Q, col(d["sw_in"], j)))
        if tech == "HPS":
            ns = frac_nums(t, Q, R)
            table("tRSHatInvModsDivsFrac", d["fracQ"], [frac(a, q) for a, q in zip(ns, Q)])
            k = len(Q)
            outputs("ScaleAndRound QR->R", n, lambda j, fu: (
                [scale1(t, Q, R, col(d["sr_in"], j)[:k], r, col(d["sr_in"], j)[k + i], fu)
                 for i, r in enumerate(R)], col(d["sr_out"], j)))
            for j in range(n):
                measure_sr(st, tech, Q, ns, col(d["sr_in"], j)[:k])
            outputs("SwitchCRTBasis R->Q", n, lambda j, fu: (
                [switch1(R, col(d["swb_in"], j), q, fu) for q in Q], col(d["swb_out"], j)))
            for j in range(n):
                measure_sw(st, tech + " back", R, digits(R, col(d["swb_in"], j)))
        else:
            ns = frac_nums(t, R, Q)
            table("tQlSlHatInvModsDivsFrac", d["fracR"], [frac(a, r) for a, r in zip(ns, R)])
            k = len(Q)
            outputs("ScaleAndRound QR->Q", n, lambda j, fu: (
                [scale1(t, R, Q, col(d["sr_in"], j)[k:], q, col(d["sr_in"], j)[i], fu)
                 for i, q in enumerate(Q)], col(d["sr_out"], j)))
            for j in range(n):
                measure_sr(st, tech, R, ns, col(d["sr_in"], j)[k:])
            if "drop_in" in d:
                l = k - 1
                ins, outs = Q[l:], Q[:l]
                ns1 = frac_nums(1, ins, outs)
                table("QlQHatInvModqDivqFrac", d["fracDrop"], [frac(a, q) for a, q in zip(ns1, ins)])
                outputs("ScaleAndRound Q->Q_l (drop 1)", n, lambda j, fu: (
                    [scale1(1, ins, outs, col(d["drop_in"], j)[l:], q, col(d["drop_in"], j)[i], fu)
                     for i, q in enumerate(outs)], col(d["drop_out"], j)))
                for j in range(n):
                    measure_sr(st, tech + " drop", ins, ns1, col(d["drop_in"], j)[l:])
    st.report()
    return bad + st.bad


def main():
    a = sys.argv[1:]
    if a and a[0] == "synth":
        trials = int(a[a.index("--trials") + 1]) if "--trials" in a else 2000
        bad = synth(trials)
    elif a and a[0] == "real" and len(a) > 1:
        bad = real(a[1:])
    else:
        print(__doc__)
        return 2
    print("FAILED" if bad else "OK: every measured error is within the proved bound")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
