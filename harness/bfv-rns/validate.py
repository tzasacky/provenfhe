#!/usr/bin/env python3
"""Numeric validation of the (U, rho) formulas of bounds.py against the limb-level models of
rnsbfv.py.  Usage:  python3 validate.py [--trials T] [--seed S] [--quick]

Sections (each prints a table; any violated bound makes the script exit 1):
  1. component level, tiny parameters: N in {2,4,8}, t in {3,17,257}, k in {2,3,4} limbs, every
     technique, idealised (Exact) and float-tolerant (Adversarial) models; random and adversarial
     operands (extreme coefficients, all-equal-sign, maximal base-conversion overshoot);
  2. IEEE binary64 on 60-bit and 45-bit limbs: the real float deviation of ScaleAndRound /
     SwitchCRTBasis against `double_e_sr` / `double_e_sw`, and (U, rho) with those tolerances;
  3. end to end: encrypt, multiply, check decryption, the contract quantities (k_a, k_b, D)
     against mulLift / mulRound of the general theorem, and the noise against Challenge.BFV.mulBound;
  4. leveled key switching (BV, internal drop to Q_l, multiply back by Q/Q_l) against
     `bounds.leveled_keyswitch`;
  5. necessity of the side conditions (informative: counts violations when a side condition is
     deliberately broken; not part of the pass/fail verdict).
"""
import argparse
import random
import sys
import time
from fractions import Fraction
from math import prod

import bounds
from rnsbfv import (Adversarial, Double, Exact, centred, crt, dec_ok, general_mul_lift,
                    general_mul_round, measure, mul_behz, mul_bound, mul_hps, mul_leveled,
                    mul_poverq, mul_textbook, norm_inf, padd, pmul, prev_primes, pscale, psub,
                    round_half_up)

FAILS = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("  FAIL:", msg)


# --------------------------------------------------------------------------------------------
# operands


def overshoot_values(src, mult):
    """Values x modulo S = prod(src) for which y_i = [x_i * mult * (S/s_i)^-1]_{s_i} is extreme:
    s_i - 1 for all i (maximal fast-conversion overshoot), and for every single i."""
    big = prod(src)
    consts = [mult * pow((big // s) % s, -1, s) % s for s in src]
    vals = []
    tops = [(s - 1) * pow(c, -1, s) % s for c, s in zip(consts, src)]
    vals.append(crt(tops, src))
    for i in range(len(src)):
        vals.append(crt([tops[j] if j == i else 0 for j in range(len(src))], src))
        vals.append(crt([tops[j] if j != i else 0 for j in range(len(src))], src))
    return vals


def pool_for(q, specials):
    h = (q - 1) // 2
    base = [0, 1, 2, q - 1, q - 2, h, h + 1, h - 1, h + 2, h - 2, h - 3, h + 3]
    return [v % q for v in base + list(specials)]


def gen_poly(rng, q, n, pool):
    kind = rng.randrange(6)
    if kind == 0:
        return [rng.randrange(q) for _ in range(n)]
    if kind == 1:                       # all coefficients equal, from the pool
        v = rng.choice(pool)
        return [v] * n
    if kind == 2:                       # every coefficient from the pool
        return [rng.choice(pool) for _ in range(n)]
    if kind == 3:                       # all positive / all negative, near the extremes
        h = (q - 1) // 2
        if rng.random() < 0.5:
            return [h - rng.randrange(4) for _ in range(n)]
        return [h + 1 + rng.randrange(4) for _ in range(n)]
    if kind == 4:                       # pool value plus a small perturbation
        return [(rng.choice(pool) + rng.randrange(-8, 9)) % q for _ in range(n)]
    return [rng.choice(pool) if rng.random() < 0.5 else rng.randrange(q) for _ in range(n)]


def gen_ct(rng, q, n, pool):
    """Two components; with probability 1/3 both components identical (worst case for the
    cross term)."""
    a = gen_poly(rng, q, n, pool)
    return [a, list(a)] if rng.random() < 1 / 3 else [a, gen_poly(rng, q, n, pool)]


# --------------------------------------------------------------------------------------------
# section 1 / 2: component level


class Row:
    def __init__(self, label):
        self.label = label
        self.trials = 0
        self.u = 0
        self.dev = Fraction(0)
        self.exc = None

    def add(self, m):
        self.trials += 1
        self.u = max(self.u, m["U"])
        self.dev = max(self.dev, max(m["dev"]))
        self.exc = m["excess"] if self.exc is None else max(self.exc, m["excess"])


def run_component(label, mulf, q, n, t, bnd, pool, trials, rng, fixed=()):
    """Runs `mulf(ca, cb)` on `fixed` operand pairs and `trials` generated ones; checks U, rho, eta
    of `bnd`.  Returns the Row."""
    row = Row(label)
    check(bnd["side"], f"{label}: side condition does not hold ({bnd['why']})")
    todo = list(fixed) + [None] * trials
    for item in todo:
        ca, cb = item if item is not None else (gen_ct(rng, q, n, pool), gen_ct(rng, q, n, pool))
        m = measure(mulf(ca, cb), ca, cb, t)
        row.add(m)
    check(row.u <= bnd["U"], f"{label}: observed |u| {row.u} > U {bnd['U']}")
    check(row.dev <= bnd["rho"], f"{label}: observed deviation {float(row.dev):.3f} > rho {bnd['rho']}")
    check(row.exc <= bnd["eta"], f"{label}: lift excess {float(row.exc):.3f} > eta {float(bnd['eta']):.3f}")
    return row, bnd


def fmt_row(row, bnd, q):
    exc = max(row.exc, Fraction(0))
    eta = bnd["eta"]
    tight = float(row.dev / bnd["rho"])
    return (f"{row.label:<46} {row.trials:>6} {row.u:>2}/{bnd['U']:<2} "
            f"{float(row.dev):>12.3f} {bnd['rho']:>10} {tight:>6.3f} "
            f"{float(exc / q):>9.2e} {float(Fraction(eta) / q):>9.2e}")


HEADER = (f"{'technique / parameters / model':<46} {'trials':>6} {'U':>5} "
          f"{'obs 2|QX-tT|/Q':>12} {'rho':>10} {'tight':>6} {'exc/Q':>9} {'eta/Q':>9}")


def hps_aux(qs, n, t, e_sw=0, e_sr=0):
    """k+1 auxiliary primes for HPS: OpenFHE takes the k+1 primes just below the smallest q
    (bfvrns-cryptoparameters.cpp:78, 129-141; upstream OpenFHE v1.6.1); at tiny sizes that product is below t N Q, so the
    primes are taken below the first power of two for which the side condition of `bounds.hps`
    holds (the smallest such choice, to exercise the condition)."""
    k = len(qs)
    bits = 3
    while True:
        try:
            rs = prev_primes(1 << bits, k + 1, avoid=qs)
        except ValueError:
            bits += 1
            continue
        if bounds.hps(n, t, qs, rs, e_sw=e_sw, e_sr=e_sr)["side"]:
            return rs
        bits += 1


def behz_aux(qs, n, t, mtilde):
    """B = the k primes below the smallest q; msk = the smallest prime above them for which the side
    condition of `bounds.behz` holds (OpenFHE: B*msk >= 2 n t Q, bfvrns-cryptoparameters.cpp:672-695)."""
    k = len(qs)
    bs = prev_primes(min(qs), k)
    cand = max(qs) + 2
    while True:
        while not (cand % 2 and all(cand % p for p in range(3, 200, 2) if p < cand) and
                   pow(2, cand - 1, cand) == 1 and cand not in qs and cand not in bs):
            cand += 1
        if bounds.behz(n, t, qs, bs + [cand], mtilde)["side"]:
            return bs + [cand]
        cand = cand * 2 + 1


def worst_poverq_pairs(q, n, src, p_mult):
    """ca with all coefficients +-(Q-1)/2, cb with maximal overshoot in every coefficient."""
    h = (q - 1) // 2
    xs = overshoot_values(src, (-p_mult) % prod(src))[0]
    out = []
    for av in (h, h + 1):
        out.append(([[av] * n, [av] * n], [[xs] * n, [xs] * n]))
    return out


def worst_leveled_pairs(q, n, qs, drop, rs):
    """Operand 1: A' = (Q_l - 1)/2 with rounding error alpha = floor(D/2) in every coefficient.
    Operand 2: a value with near-maximal overshoot delta whose lift B is positive and as large as
    possible (searched among y_i in [q_i - 8, q_i))."""
    from itertools import product as iproduct
    k, kl = len(qs), len(qs) - drop
    q_l, p_l = prod(qs[:kl]), prod(rs[:kl])
    d = q // q_l
    a = d * ((q_l - 1) // 2) - d // 2
    consts = [(-p_l) * pow((q // s) % s, -1, s) % s for s in qs]
    best = None
    for ys in iproduct(*[range(s - min(8, s), s) for s in qs]):
        x = crt([y * pow(c, -1, s) % s for y, c, s in zip(ys, consts, qs)], qs)
        if 2 * x < q - 2 * (k * q // p_l) - 2 and (best is None or x > best):
            best = x
    out = [([[a] * n, [a] * n], [[best] * n, [best] * n])] if best is not None else []
    return out + worst_poverq_pairs(q, n, qs, p_l)


def section1(trials, rng, quick):
    print("\n== 1. component level, tiny parameters (Exact = idealised, Adv = float-tolerant) ==")
    print(HEADER)
    worst = {}
    tol = Fraction(1, 64)       # adversarial SwitchCRTBasis tolerance (huge compared with 2^-45)
    ns = (2, 4, 8)
    ts = (3, 17, 257)
    ks = (2, 3) if quick else (2, 3, 4)
    for n in ns:
        for t in ts:
            for k in ks:
                qs = prev_primes(1 << (8 if k < 4 else 7), k)
                q = prod(qs)
                rs = prev_primes(min(qs), k)
                qsL = prev_primes(1 << 20, k)
                qL = prod(qsL)
                rsL = prev_primes(min(qsL), k)
                tag = f"N={n} t={t} k={k}"
                models = [("Exact", lambda: Exact(), dict(e_sw=0, e_sr=0, e_sr1=0)),
                          ("Adv F=1", lambda: Adversarial(tol, 1, rng.choice(("random", "max")), rng),
                           dict(e_sw=tol, e_sr=1, e_sr1=1))]
                for mname, mk, e in models:
                    rows = []
                    # HPS
                    rh = hps_aux(qs, n, t, e_sw=e["e_sw"], e_sr=e["e_sr"])
                    fl = mk()
                    b = bounds.hps(n, t, qs, rh, e_sw=e["e_sw"], e_sr=e["e_sr"])
                    rows.append(run_component(f"HPS {tag} {mname}", lambda a, c: mul_hps(a, c, qs, rh, t, fl),
                                              q, n, t, b, pool_for(q, []), trials, rng))
                    # HPSPOVERQ
                    fl = mk()
                    b = bounds.poverq(n, t, qs, rs, e_sw=e["e_sw"], e_sr=e["e_sr"])
                    sp = overshoot_values(qs, (-prod(rs)) % q)
                    rows.append(run_component(f"POVERQ {tag} {mname}",
                                              lambda a, c: mul_poverq(a, c, qs, rs, t, fl), q, n, t, b,
                                              pool_for(q, sp), trials, rng,
                                              fixed=worst_poverq_pairs(q, n, qs, prod(rs))))
                    # HPSPOVERQLEVELED with every possible internal drop
                    # (larger limbs: rho is about D t N (1 + 2k) and must stay below Q to mean anything)
                    for drop in range(1, k):
                        fl = mk()
                        b = bounds.leveled(n, t, qsL, rsL, drop, e_sw=e["e_sw"], e_sr1=e["e_sr1"], e_sr=e["e_sr"])
                        pl = rsL[:k - drop]
                        sp = overshoot_values(qsL, (-prod(pl)) % qL)
                        d = qL // prod(qsL[:k - drop])
                        sp += [(qL - 1) // 2 - d // 2, (qL - 1) // 2 - d // 2 + 1, d // 2, d // 2 + 1, d, 2 * d]
                        rows.append(run_component(
                            f"LEVELED drop={drop} {tag} {mname}",
                            lambda a, c: mul_leveled(a, c, qsL, rsL, drop, t, fl), qL, n, t, b,
                            pool_for(qL, sp), trials, rng, fixed=worst_leveled_pairs(qL, n, qsL, drop, rsL)))
                    # BEHZ (no floats: one model only)
                    if mname == "Exact":
                        for mt in (1 << 16, 16):
                            bsk = behz_aux(qs, n, t, mt)
                            b = bounds.behz(n, t, qs, bsk, mt)
                            sp = overshoot_values(qs, mt % q)
                            rows.append(run_component(
                                f"BEHZ mt={mt} {tag}", lambda a, c: mul_behz(a, c, qs, bsk, t, mt),
                                q, n, t, b, pool_for(q, sp), trials, rng))
                    for row, b in rows:
                        qq = qL if row.label.startswith("LEVELED") else q
                        check(2 * b["rho"] < qq, f"{row.label}: rho >= Q/2, the test is vacuous")
                        print(fmt_row(row, b, qq))
                        key = row.label.split(" N=")[0] + " " + mname
                        w = worst.get(key, (0, Fraction(0), 0, 0))
                        worst[key] = (w[0] + row.trials, max(w[1], row.dev / b["rho"]),
                                      max(w[2], row.u), max(w[3], b["U"]))
    print("\n   summary over all tiny parameter sets (technique, model): trials, max tightness "
          "obs/rho, max |u| / U")
    for key, (tr, tg, u, ub) in sorted(worst.items()):
        print(f"   {key:<34} {tr:>8} {float(tg):>7.3f} {u}/{ub}")


def section2(trials, rng):
    print("\n== 2. IEEE binary64 on realistic limbs (N=4): float deviation and (U, rho) ==")
    print(HEADER)
    n = 4
    for bits, t in ((60, 65537), (60, 257), (45, 65537), (30, 17)):
        for k in (2, 3):
            qs = prev_primes(1 << bits, k)
            q = prod(qs)
            rs = prev_primes(min(qs), k)
            tag = f"{bits}-bit k={k} t={t}"
            e_sw = bounds.double_e_sw(k + 1)
            # HPS
            rh = prev_primes(min(qs), k + 1)
            fl = Double()
            b = bounds.hps(n, t, qs, rh, e_sw=e_sw, e_sr=bounds.double_e_sr(qs))
            row, b = run_component(f"HPS {tag} double", lambda a, c: mul_hps(a, c, qs, rh, t, fl),
                                   q, n, t, b, pool_for(q, []), trials, rng)
            print(fmt_row(row, b, q))
            report_double("   ScaleAndRound t/Q", fl, bounds.double_e_sr(qs), e_sw)
            # POVERQ
            fl = Double()
            b = bounds.poverq(n, t, qs, rs, e_sw=e_sw, e_sr=bounds.double_e_sr(rs))
            row, b = run_component(f"POVERQ {tag} double", lambda a, c: mul_poverq(a, c, qs, rs, t, fl),
                                   q, n, t, b, pool_for(q, overshoot_values(qs, (-prod(rs)) % q)), trials, rng,
                                   fixed=worst_poverq_pairs(q, n, qs, prod(rs)))
            print(fmt_row(row, b, q))
            report_double("   ScaleAndRound t/P", fl, bounds.double_e_sr(rs), e_sw)
            # LEVELED, drop 1
            fl = Double()
            e1 = bounds.double_e_sr(qs[k - 1:])
            e2 = bounds.double_e_sr(rs[:k - 1])
            b = bounds.leveled(n, t, qs, rs, 1, e_sw=e_sw, e_sr1=e1, e_sr=e2)
            pl = rs[:k - 1]
            row, b = run_component(f"LEVELED drop=1 {tag} double",
                                   lambda a, c: mul_leveled(a, c, qs, rs, 1, t, fl), q, n, t, b,
                                   pool_for(q, overshoot_values(qs, (-prod(pl)) % q)), trials, rng,
                                   fixed=worst_poverq_pairs(q, n, qs, prod(pl)))
            print(fmt_row(row, b, q))
            report_double("   ScaleAndRound (both)", fl, max(e1, e2), e_sw)


def report_double(what, fl, e_sr, e_sw):
    print(f"{what}: max |nu_float - nu| = {float(fl.max_sr_err):.3e} (bound {float(e_sr):.3e}), "
          f"result off by up to {fl.max_sr_units} unit(s); SwitchCRTBasis max err "
          f"{float(fl.max_sw_err):.2e} (bound {float(e_sw):.2e}), flips {fl.sw_flips}")
    check(fl.max_sr_err <= e_sr, f"{what}: binary64 ScaleAndRound error above double_e_sr")
    check(fl.max_sw_err <= e_sw, f"{what}: binary64 SwitchCRTBasis error above double_e_sw")


# --------------------------------------------------------------------------------------------
# section 3: end to end


def ternary(rng, n):
    return [rng.choice((-1, 0, 1)) for _ in range(n)]


def encrypt(rng, m, s, q, t, be):
    n = len(m)
    a = [rng.randrange(q) for _ in range(n)]
    e = [rng.randint(-be, be) for _ in range(n)]
    b = psub(padd(pscale(q // t, m), e), pmul(a, s), q)
    return [b, a]


def phase(ct, s):
    acc, sp = [0] * len(s), [1] + [0] * (len(s) - 1)
    for c in ct:
        acc = padd(acc, pmul(c, sp))
        sp = pmul(sp, s)
    return acc


def e2e_one(rng, mulf, q, n, t, bnd, be, eta_lift=True):
    s = ternary(rng, n)
    m1 = [rng.randrange(t) for _ in range(n)]
    m2 = [rng.randrange(t) for _ in range(n)]
    ca, cb = encrypt(rng, m1, s, q, t, be), encrypt(rng, m2, s, q, t, be)
    res = mulf(ca, cb)
    msr = measure(res, ca, cb, t)
    m3 = pmul(m1, m2, t)
    # the contract of Spec.TraceBFV (mul): Q X = t (Phi_a + Q k_a)(Phi_b + Q k_b) + D, phase = X mod Q
    phi_a = [centred(x, q) for x in phase(ca, s)]
    phi_b = [centred(x, q) for x in phase(cb, s)]
    psi_a, psi_b = phase(res["A"], s), phase(res["B"], s)
    ka = [(x - y) // q for x, y in zip(psi_a, phi_a)]
    kb = [(x - y) // q for x, y in zip(psi_b, phi_b)]
    assert all((x - y) % q == 0 for x, y in zip(psi_a, phi_a))
    # X_j: the representative of out_j nearest to t T_j / Q
    tt = [pmul(res["A"][0], res["B"][0]),
          padd(pmul(res["A"][0], res["B"][1]), pmul(res["A"][1], res["B"][0])),
          pmul(res["A"][1], res["B"][1])]
    xs = [[o + q * round_half_up(t * tv - q * o, q * q) for o, tv in zip(res["out"][j], tt[j])] for j in range(3)]
    xph = phase(xs, s)
    d = psub(pscale(q, xph), pscale(t, pmul(psi_a, psi_b)))
    k_lift = general_mul_lift(n, 1, bnd["U"])
    k_eta = bounds.lift_from_eta(n, 1, q, bnd["eta"])
    r_round = general_mul_round(n, 1, bnd["rho"])
    out_phase = [x % q for x in phase(res["out"], s)]
    assert out_phase == [x % q for x in xph]
    noise = norm_inf([centred(x - (q // t) * mm, q) for x, mm in zip(out_phase, m3)])
    dec = [round_half_up(t * x, q) % t for x in out_phase]
    nb = mul_bound(n, t, q, k_lift, r_round, be, be)
    return dict(k=max(norm_inf(ka), norm_inf(kb)), k_lift=k_lift, k_eta=k_eta,
                d2=Fraction(2 * norm_inf(d), q), r_round=r_round, noise=noise, noise_bound=nb,
                dec_ok=dec_ok(t, q, nb), decrypts=dec == m3, msr=msr)


def section3(trials, rng, quick):
    print("\n== 3. end to end (ternary secret, fresh noise <= 3): contract quantities and decryption ==")
    print(f"{'technique / parameters / model':<44} {'trials':>6} {'max|k|':>6} {'mulLift':>7} {'(eta)':>6} "
          f"{'max 2|D|/Q':>12} {'mulRound':>12} {'noise':>12} {'mulBound':>12} {'decOK':>5} {'dec':>4}")
    be = 3
    tol = Fraction(1, 64)
    for n in (2, 4, 8):
        for t in (3, 17, 257):
            for k in ((3,) if quick else (3, 4)):
                qs = prev_primes(1 << 26, k)
                q = prod(qs)
                rs = prev_primes(min(qs), k)
                rh = prev_primes(min(qs), k + 1)
                mt = 1 << 16
                bsk = behz_aux(qs, n, t, mt)
                tag = f"N={n} t={t} k={k}"
                cases = []
                for mname, mk, e in (("Exact", lambda: Exact(), dict(e_sw=0, e_sr=0, e_sr1=0)),
                                     ("Adv", lambda: Adversarial(tol, 1, "random", rng),
                                      dict(e_sw=tol, e_sr=1, e_sr1=1))):
                    fl1, fl2, fl3 = mk(), mk(), mk()
                    cases.append((f"HPS {tag} {mname}", lambda a, c, fl=fl1: mul_hps(a, c, qs, rh, t, fl),
                                  bounds.hps(n, t, qs, rh, e_sw=e["e_sw"], e_sr=e["e_sr"])))
                    cases.append((f"POVERQ {tag} {mname}", lambda a, c, fl=fl2: mul_poverq(a, c, qs, rs, t, fl),
                                  bounds.poverq(n, t, qs, rs, e_sw=e["e_sw"], e_sr=e["e_sr"])))
                    cases.append((f"LEVELED drop=1 {tag} {mname}",
                                  lambda a, c, fl=fl3: mul_leveled(a, c, qs, rs, 1, t, fl),
                                  bounds.leveled(n, t, qs, rs, 1, e_sw=e["e_sw"], e_sr1=e["e_sr1"], e_sr=e["e_sr"])))
                cases.append((f"BEHZ {tag}", lambda a, c: mul_behz(a, c, qs, bsk, t, mt),
                              bounds.behz(n, t, qs, bsk, mt)))
                for label, mulf, bnd in cases:
                    check(bnd["side"], f"{label}: side condition")
                    agg = None
                    for _ in range(trials):
                        r = e2e_one(rng, mulf, q, n, t, bnd, be)
                        check(r["msr"]["U"] <= bnd["U"], f"{label}: U")
                        check(max(r["msr"]["dev"]) <= bnd["rho"], f"{label}: rho")
                        check(r["k"] <= r["k_lift"], f"{label}: |k| {r['k']} > mulLift {r['k_lift']}")
                        check(r["k"] <= r["k_eta"], f"{label}: |k| {r['k']} > eta-mulLift {r['k_eta']}")
                        check(r["d2"] <= r["r_round"], f"{label}: 2|D|/Q {float(r['d2'])} > mulRound {r['r_round']}")
                        if r["dec_ok"]:
                            check(r["noise"] <= r["noise_bound"], f"{label}: noise above mulBound")
                            check(r["decrypts"], f"{label}: decryption wrong although decOK")
                        if agg is None:
                            agg = dict(r, alldec=r["decrypts"])
                        else:
                            agg["k"] = max(agg["k"], r["k"])
                            agg["d2"] = max(agg["d2"], r["d2"])
                            agg["noise"] = max(agg["noise"], r["noise"])
                            agg["alldec"] = agg["alldec"] and r["decrypts"]
                    print(f"{label:<44} {trials:>6} {agg['k']:>6} {agg['k_lift']:>7} {agg['k_eta']:>6} "
                          f"{float(agg['d2']):>12.1f} {agg['r_round']:>12} {agg['noise']:>12} "
                          f"{agg['noise_bound']:>12} {str(agg['dec_ok']):>5} {'ok' if agg['alldec'] else 'BAD':>4}")


# --------------------------------------------------------------------------------------------
# section 4: leveled key switching


def bv_keygen(rng, s_tgt, s, qs, bk):
    """OpenFHE KeySwitchBV::KeySwitchGenInternal, digitSize 0 (keyswitch-bv.cpp:93-103, v1.6.1): key i
    is (b_i, a_i) with b_i = filtered_i - (a_i s + e_i), filtered_i = s_tgt in limb i and 0 in the
    others, i.e. g_i * s_tgt with g_i = (Q/q_i) [(Q/q_i)^-1]_{q_i} (Spec.Budget.gadgetFactor, P = 1)."""
    q = prod(qs)
    keys = []
    for qi in qs:
        hat = q // qi
        g = hat * pow(hat % qi, -1, qi)
        a = [rng.randrange(q) for _ in s]
        e = [rng.randint(-bk, bk) for _ in s]
        b = psub(pscale(g, s_tgt), padd(pmul(a, s), e), q)
        keys.append((b, a, e, g))
    return keys


def bv_keyswitch(c, keys, ql):
    """KeySwitchBV::KeySwitchCore at the level with limbs ql (keyswitch-bv.cpp:246-330, v1.6.1): digits =
    CRTDecompose(0) (dcrtpoly-impl.h:256-271): limb i of c, moved to the other limbs with
    the NativeVector(v, modulus) constructor (mubintvecnat.cpp:191-215, the same map as
    SwitchModulus, :217-237), which reads residues above q_i/2 as negative: the
    CENTRED residue.  Keys are the top-level keys with the dropped limbs removed."""
    q_l = prod(ql)
    ct0, ct1 = [0] * len(c), [0] * len(c)
    digs = []
    for i, qi in enumerate(ql):
        r = [x % qi for x in c]
        dig = [x - qi if x > qi // 2 else x for x in r]
        digs.append(dig)
        b, a, _, _ = keys[i]
        ct0 = padd(ct0, pmul(dig, [x % q_l for x in b]), q_l)
        ct1 = padd(ct1, pmul(dig, [x % q_l for x in a]), q_l)
    return ct0, ct1, digs


def section4(trials, rng):
    print("\n== 4. leveled key switching (BV digits, internal drop, multiply back by Q/Q_l) ==")
    print(f"{'case':<52} {'trials':>6} {'max |e|':>14} {'bound':>14} {'tight':>6}")
    bk = 3
    for n in (2, 4, 8):
        for k in (3, 4):
            qs = prev_primes(1 << 12, k)
            q = prod(qs)
            for drop in range(0, k):
                for target in ("relin s^2", "rotate s'"):
                    for mname, mk, e1 in (("Exact", lambda: Exact(), 0), ("Adv", lambda: Adversarial(0, 1, "max", rng), 1)):
                        kl = k - drop
                        ql, qd = qs[:kl], qs[kl:]
                        q_l = prod(ql)
                        d = q // q_l
                        worst = 0
                        b_tgt = 0
                        for _ in range(trials):
                            s = ternary(rng, n)
                            s_tgt = pmul(s, s) if target.startswith("relin") else ternary(rng, n)
                            b_tgt = max(b_tgt, n if target.startswith("relin") else 1)
                            keys = bv_keygen(rng, s_tgt, s, qs, bk)
                            # top-level key i restricted to Q_l is the level-l gadget key
                            for i, qi in enumerate(ql):
                                hat = q_l // qi
                                assert keys[i][3] % q_l == hat * pow(hat % qi, -1, qi) % q_l
                            c = [rng.randrange(q) for _ in range(n)] if rng.random() < 0.7 else \
                                [rng.choice((0, q - 1, (q - 1) // 2, (q + 1) // 2, d // 2, d // 2 + 1)) for _ in range(n)]
                            if _ == 0 and not target.startswith("relin"):
                                # engineered worst case: every digit (q_i - 1)/2, every key error
                                # -B_k, rounding error -floor(D/2) against s_tgt = -1 everywhere
                                s_tgt = [-1] * n
                                keys = [(psub(pscale(g, s_tgt), padd(pmul(a, s), [-bk] * n), q), a, [-bk] * n, g)
                                        for (_b, a, _e, g) in keys]
                                c = [d * crt([(qi - 1) // 2 for qi in ql], ql) + d // 2] * n
                            from rnsbfv import scale_and_round, to_rns, from_rns
                            x = to_rns(c, qs)
                            cl = from_rns(scale_and_round(x[kl:], x[:kl], qd, ql, 1, mk()), ql)
                            ct0, ct1, digs = bv_keyswitch(cl, keys, ql)
                            # phase added to the ciphertext, times D, against c * s_tgt
                            got = pscale(d, padd(ct0, pmul(ct1, s)))
                            err = [centred(g - w, q) for g, w in zip(got, pmul(c, s_tgt))]
                            worst = max(worst, norm_inf(err))
                        ks_l = bounds.bv_ks_bound(n, bk, ql)
                        bnd = bounds.leveled_keyswitch(n, d, ks_l, b_tgt, e_sr1=e1) if drop else ks_l
                        label = f"N={n} k={k} drop={drop} {target} {mname}"
                        check(worst <= bnd, f"key switch {label}: {worst} > {bnd}")
                        print(f"{label:<52} {trials:>6} {worst:>14} {bnd:>14} {worst / bnd:>6.3f}")


# --------------------------------------------------------------------------------------------
# section 5: side conditions are needed; POVERQ squaring uses two different lifts


def section5(trials, rng):
    print("\n== 5. informative: broken side conditions, and the two lifts of P-over-Q squaring ==")
    n, t, k = 4, 257, 3
    qs = prev_primes(1 << 8, k)
    q = prod(qs)
    pool = pool_for(q, [])
    # HPS with OpenFHE's rule for R (k+1 primes below the smallest q) at tiny size: R < t N Q
    rh = prev_primes(min(qs), k + 1)
    b = bounds.hps(n, t, qs, rh)
    bad = 0
    for _ in range(trials):
        ca, cb = gen_ct(rng, q, n, pool), gen_ct(rng, q, n, pool)
        m = measure(mul_hps(ca, cb, qs, rh, t, Exact()), ca, cb, t)
        bad += max(m["dev"]) > b["rho"]
    print(f"   HPS, R = {prod(rh)} < t N Q = {t * n * q} (side = {b['side']}): "
          f"{bad}/{trials} products violate rho = {b['rho']}")
    # BEHZ with msk too small
    bs = prev_primes(min(qs), k)
    msk = prev_primes(min(bs), 1)[0]
    b = bounds.behz(n, t, qs, bs + [msk], 1 << 16)
    bad = 0
    for _ in range(trials):
        ca, cb = gen_ct(rng, q, n, pool), gen_ct(rng, q, n, pool)
        m = measure(mul_behz(ca, cb, qs, bs + [msk], t), ca, cb, t)
        bad += max(m["dev"]) > b["rho"]
    print(f"   BEHZ, msk = {msk} (side = {b['side']}): {bad}/{trials} products violate rho = {b['rho']}")
    # squaring under P-over-Q: operand 1 and operand 2 of the same ciphertext get different lifts
    rs = prev_primes(min(qs), k)
    diff = 0
    for _ in range(trials):
        ca = gen_ct(rng, q, n, pool_for(q, overshoot_values(qs, (-prod(rs)) % q)))
        res = mul_poverq(ca, ca, qs, rs, t, Exact())
        diff += res["A"] != res["B"]
    h = (q - 1) // 2
    ca = [[h] * n, [0] * n]
    res = mul_poverq(ca, ca, qs, rs, t, Exact())
    print(f"   POVERQ EvalSquare (cv, cvPoverQ of the same ciphertext): lifts differ in {diff}/{trials} "
          f"adversarial squarings; e.g. component 0 = (Q-1)/2 everywhere: A_0[0] = {res['A'][0][0]}, "
          f"B_0[0] = {res['B'][0][0]} (differ by Q = {q})")
    same = 0
    for _ in range(trials):
        ca = [[rng.randrange(q) for _ in range(n)] for _ in range(2)]
        res = mul_poverq(ca, ca, qs, rs, t, Exact())
        same += res["A"] == res["B"]
    print(f"   ... on uniformly random ciphertexts the two lifts agree in {same}/{trials} squarings "
          f"(a coefficient must lie within k*Q/P of Q/2 for them to differ)")
    # HPS / BEHZ squaring: one lift
    res = mul_hps(ca, ca, qs, hps_aux(qs, n, t), t, Exact())
    assert res["A"] == res["B"]
    res = mul_behz(ca, ca, qs, behz_aux(qs, n, t, 1 << 16), t)
    assert res["A"] == res["B"]
    # agreement with the textbook algorithm when all lifts are centred (HPS idealised: identical)
    rh = hps_aux(qs, n, t)
    for _ in range(trials):
        ca, cb = gen_ct(rng, q, n, pool), gen_ct(rng, q, n, pool)
        assert mul_hps(ca, cb, qs, rh, t, Exact())["out"] == mul_textbook(ca, cb, q, t)
    print(f"   HPS idealised == textbook bfvMul (round half up) on {trials}/{trials} adversarial products")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--trials", type=int, default=200)
    ap.add_argument("--seed", type=int, default=20261113)
    ap.add_argument("--quick", action="store_true", help="fewer parameter sets")
    ap.add_argument("--sections", default="12345")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    t0 = time.time()
    if "1" in args.sections:
        section1(args.trials, rng, args.quick)
    if "2" in args.sections:
        section2(max(20, args.trials // 4), rng)
    if "3" in args.sections:
        section3(max(10, args.trials // 4), rng, args.quick)
    if "4" in args.sections:
        section4(max(10, args.trials // 4), rng)
    if "5" in args.sections:
        section5(args.trials, rng)
    print(f"\n{'ALL CHECKS PASSED' if not FAILS else str(len(FAILS)) + ' CHECK(S) FAILED'} "
          f"({time.time() - t0:.0f}s, seed {args.seed}, trials {args.trials})")
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
