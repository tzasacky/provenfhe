#!/usr/bin/env python3
"""Limb-by-limb Python models of OpenFHE's four BFVrns multiplication techniques.

Exact big-integer / Fraction arithmetic; no third-party packages.  Every routine mirrors one C++
routine of upstream OpenFHE v1.6.1 (b59e1f29), with the same representatives (line numbers are
those of v1.6.1; the arithmetic of every routine below is unchanged from v1.3.1):

  switch_crt_basis        DCRTPolyImpl::SwitchCRTBasis          dcrtpoly-impl.h:1058
  expand_crt_basis        DCRTPolyImpl::ExpandCRTBasis          dcrtpoly-impl.h:1112
  fast_expand_p_over_q    DCRTPolyImpl::FastExpandCRTBasisPloverQ (ApproxSwitchCRTBasis :938) :1181
  scale_and_round         DCRTPolyImpl::ScaleAndRound (DCRT -> DCRT overload)  dcrtpoly-impl.h:1536
  expand_ql_hat           DCRTPolyImpl::ExpandCRTBasisQlHat     dcrtpoly-impl.h:1197
  smmrq                   DCRTPolyImpl::FastBaseConvqToBskMontgomery  dcrtpoly-impl.h:1719
  fast_rns_floor_q        DCRTPolyImpl::FastRNSFloorq           dcrtpoly-impl.h:1815
  fast_base_conv_sk       DCRTPolyImpl::FastBaseConvSK          dcrtpoly-impl.h:1869
  mul_hps / mul_poverq / mul_leveled / mul_behz   LeveledSHEBFVRNS::EvalMult  bfvrns-leveledshe.cpp:200

The two float-assisted steps (the overflow count `nu` of SwitchCRTBasis and the fractional sum `nu`
of ScaleAndRound) go through a *float model*:

  Exact()          floats replaced by exact rational arithmetic (the idealised algorithm);
  Double()         IEEE-754 binary64, operation for operation as the C++ (Python floats are binary64;
                   int -> float is round-to-nearest-even like the C++ uint64 -> double conversion);
  Adversarial(..)  exact value perturbed adversarially within a declared tolerance: SwitchCRTBasis
                   may take the other representative when x/Q is within `tol` of the rounding
                   boundary, ScaleAndRound may return the exact rounding plus any s, |s| <= F.

A polynomial is a list of N Python ints; an RNS polynomial is a list of limbs (one polynomial per
modulus).  Multiplication is negacyclic schoolbook (no NTT: the moduli need not be NTT-friendly).
"""
from fractions import Fraction
from math import floor, prod
import random

# --------------------------------------------------------------------------------------------
# integers and polynomials


def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def prev_primes(start, count, avoid=()):
    """`count` distinct odd primes strictly below `start`, descending, none in `avoid`."""
    out, p = [], start - 1
    while len(out) < count:
        if p < 3:
            raise ValueError("ran out of primes")
        if is_prime(p) and p not in avoid and p not in out:
            out.append(p)
        p -= 1
    return out


def centred(x, m):
    """Representative of x mod m in (-m/2, m/2]  (Spec.NPoly `centered`)."""
    r = x % m
    return r - m if 2 * r > m else r


def cdiv(a, b):
    """ceil(a / b) for integers, b > 0."""
    return -((-a) // b)


def ceil_frac(x):
    x = Fraction(x)
    return cdiv(x.numerator, x.denominator)


def pmul(a, b, m=None):
    """a * b in Z[X]/(X^N+1), reduced modulo m if given."""
    n = len(a)
    r = [0] * n
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            k = i + j
            if k < n:
                r[k] += ai * bj
            else:
                r[k - n] -= ai * bj
    return [x % m for x in r] if m else r


def padd(a, b, m=None):
    r = [x + y for x, y in zip(a, b)]
    return [x % m for x in r] if m else r


def psub(a, b, m=None):
    r = [x - y for x, y in zip(a, b)]
    return [x % m for x in r] if m else r


def pscale(c, a, m=None):
    r = [c * x for x in a]
    return [x % m for x in r] if m else r


def norm_inf(a):
    return max(abs(x) for x in a)


def to_rns(a, moduli):
    return [[x % q for x in a] for q in moduli]


def crt(residues, moduli):
    """The integer in [0, prod moduli) with the given residues."""
    big = prod(moduli)
    x = 0
    for r, q in zip(residues, moduli):
        h = big // q
        x += r * h * pow(h % q, -1, q)
    return x % big


def from_rns(limbs, moduli):
    """Canonical [0, M) reconstruction, coefficient by coefficient."""
    return [crt([l[r] for l in limbs], moduli) for r in range(len(limbs[0]))]


def from_rns_centred(limbs, moduli):
    big = prod(moduli)
    out = []
    for x in from_rns(limbs, moduli):
        out.append(x - big if 2 * x >= big else x)  # [-M/2, M/2)
    return out


# --------------------------------------------------------------------------------------------
# float models


class Exact:
    """Idealised: both float sums evaluated exactly."""
    name = "exact"

    def sw_alpha(self, ys, src):
        return floor(Fraction(1, 2) + sum(Fraction(y, s) for y, s in zip(ys, src)))

    def sr_alpha(self, xs, nums, dens):
        return floor(Fraction(1, 2) + sum(Fraction(n * x, d) for x, n, d in zip(xs, nums, dens)))


class Double:
    """IEEE binary64, as the C++: SwitchCRTBasis `nu += y.ConvertToDouble() * qInv[i]` with
    `qInv[i] = 1. / double(q_i)` (dcrtpoly-impl.h:1080-1089, bfvrns-cryptoparameters.cpp:263-266);
    ScaleAndRound `nu += frac[i] * x.ConvertToDouble()` with `frac[i] = double(num) / double(q_i)`
    (dcrtpoly-impl.h:1566-1571, bfvrns-cryptoparameters.cpp:283-289).  Records the largest
    deviation from the exact value of each sum and of each resulting integer."""
    name = "double"

    def __init__(self):
        self.max_sw_err = Fraction(0)   # |nu_float - nu_exact| in SwitchCRTBasis
        self.max_sr_err = Fraction(0)   # |nu_float - nu_exact| in ScaleAndRound
        self.max_sr_units = 0           # |floor(nu_float) - floor(nu_exact)|
        self.sw_flips = 0               # floor(nu_float) != floor(nu_exact) in SwitchCRTBasis

    def sw_alpha(self, ys, src):
        nu = 0.5
        for y, s in zip(ys, src):
            nu += float(y) * (1.0 / float(s))
        ex = Fraction(1, 2) + sum(Fraction(y, s) for y, s in zip(ys, src))
        self.max_sw_err = max(self.max_sw_err, abs(Fraction(nu) - ex))
        if int(nu) != floor(ex):
            self.sw_flips += 1
        return int(nu)

    def sr_alpha(self, xs, nums, dens):
        nu = 0.5
        for x, n, d in zip(xs, nums, dens):
            nu += (float(n) / float(d)) * float(x)
        ex = Fraction(1, 2) + sum(Fraction(n * x, d) for x, n, d in zip(xs, nums, dens))
        self.max_sr_err = max(self.max_sr_err, abs(Fraction(nu) - ex))
        self.max_sr_units = max(self.max_sr_units, abs(int(nu) - floor(ex)))
        return int(nu)


class Adversarial:
    """Exact sums perturbed within a tolerance.  `tol`: SwitchCRTBasis may return the neighbouring
    overflow count whenever the fractional part of nu is within `tol` of an integer (i.e. x/S is
    within `tol` of the boundary 1/2).  `F`: ScaleAndRound returns exact + s with |s| <= F.
    `policy`: 'random' (each perturbation drawn at random, including none) or 'max' (always take
    the other representative; s = +F or -F at random)."""
    name = "adversarial"

    def __init__(self, tol=Fraction(0), F=1, policy="random", rng=None):
        self.tol, self.F, self.policy = Fraction(tol), F, policy
        self.rng = rng or random.Random(1)

    def sw_alpha(self, ys, src):
        nu = Fraction(1, 2) + sum(Fraction(y, s) for y, s in zip(ys, src))
        a = floor(nu)
        f = nu - a
        flip = self.policy == "max" or self.rng.random() < 0.5
        if f < self.tol and flip and a > 0:
            return a - 1
        if f > 1 - self.tol and flip and a < len(src):
            return a + 1
        return a

    def sr_alpha(self, xs, nums, dens):
        a = floor(Fraction(1, 2) + sum(Fraction(n * x, d) for x, n, d in zip(xs, nums, dens)))
        if not xs:                      # no input limb: nu is exactly 0.5 in the C++ too
            return a
        if self.policy == "max":
            return a + self.rng.choice((-self.F, self.F))
        return a + self.rng.randint(-self.F, self.F)


# --------------------------------------------------------------------------------------------
# HPS building blocks


def switch_crt_basis(x, src, dst, fl):
    """SwitchCRTBasis (dcrtpoly-impl.h:1058-1109).  y_i = [x_i (S/s_i)^-1]_{s_i} in [0, s_i);
    alpha = floor(0.5 + sum y_i / s_i) (float in the C++); out_j = sum y_i [S/s_i]_{p_j} -
    alpha S  (mod p_j).  Exactly: the representative of x in [-S/2, S/2), reduced modulo p_j."""
    big = prod(src)
    hats = [big // s for s in src]
    invs = [pow(h % s, -1, s) for h, s in zip(hats, src)]
    n = len(x[0])
    out = [[0] * n for _ in dst]
    for r in range(n):
        ys = [x[i][r] * invs[i] % src[i] for i in range(len(src))]
        alpha = fl.sw_alpha(ys, src)
        for j, p in enumerate(dst):
            out[j][r] = (sum(y * (h % p) for y, h in zip(ys, hats)) - alpha * (big % p)) % p
    return out


def expand_crt_basis(x, src, dst, fl):
    """ExpandCRTBasis (dcrtpoly-impl.h:1112-1143): limbs of x followed by SwitchCRTBasis(x)."""
    return x + switch_crt_basis(x, src, dst, fl)


def fast_expand_p_over_q(x, src, pl, ql, fl):
    """FastExpandCRTBasisPloverQ (dcrtpoly-impl.h:1181-1194) with the tables of
    bfvrns-cryptoparameters.cpp:485-527 (tables :497-498, :513-514, :525).  x is modulo Qs = prod(src).
      y_i = [x_i * (-P) * (Qs/q_i)^-1]_{q_i}            (m_negRlQHatInvModq / m_negRlQlHatInvModq)
      w_j = sum_i y_i * q_i^-1  (mod p_j)               (ApproxSwitchCRTBasis with m_qInvModr)
          = (P x + sum_i y_i Qs/q_i) / Qs  (mod p_j)    [an integer; = P x / Qs + delta]
      then SwitchCRTBasis(w: P -> Ql) and the result is [Ql limbs | P limbs].
    Returns (limbs over ql + pl, delta) with delta[r] = sum_i y_i / q_i  in [0, k)."""
    big, p_prod = prod(src), prod(pl)
    consts = [(-p_prod) * pow((big // q) % q, -1, q) % q for q in src]
    n = len(x[0])
    w = [[0] * n for _ in pl]
    delta = []
    for r in range(n):
        ys = [x[i][r] * consts[i] % src[i] for i in range(len(src))]
        delta.append(sum(Fraction(y, q) for y, q in zip(ys, src)))
        for j, p in enumerate(pl):
            w[j][r] = sum(y * pow(q % p, -1, p) for y, q in zip(ys, src)) % p
    return switch_crt_basis(w, pl, ql, fl) + w, delta


def scale_and_round(x_in, x_out, mod_in, mod_out, t, fl):
    """ScaleAndRound, DCRT -> DCRT overload (dcrtpoly-impl.h:1536-1649).  The input is modulo
    S = I * O (I = prod(mod_in), O = prod(mod_out)); the result is round(t * x / I) modulo O:
      nu      = 0.5 + sum_{i in I} x_i * frac_i,   frac_i = ((t O [(S/s_i)^-1]_{s_i}) mod s_i) / s_i
      out_j   = sum_{i in I} x_i * floor(t O [(S/s_i)^-1]_{s_i} / s_i)
                + x_{o_j} * (t O [(S/o_j)^-1]_{o_j} / o_j)  + floor(nu)        (mod o_j)
    Tables: HPS t/Q -> R  bfvrns-cryptoparameters.cpp:283-304; P-over-Q t/P -> Q_l :562-591;
    drop Q -> Q_l (t = 1) :597-618."""
    o_prod = prod(mod_out)
    big = prod(mod_in) * o_prod
    full = [t * o_prod * pow((big // s) % s, -1, s) for s in mod_in]
    ints = [f // s for f, s in zip(full, mod_in)]
    nums = [f % s for f, s in zip(full, mod_in)]
    outc = [(t * o_prod * pow((big // o) % o, -1, o)) // o for o in mod_out]
    n = len(x_out[0]) if x_out else len(x_in[0])
    out = [[0] * n for _ in mod_out]
    for r in range(n):
        xs = [x_in[i][r] for i in range(len(mod_in))]
        alpha = fl.sr_alpha(xs, nums, mod_in)
        for j, o in enumerate(mod_out):
            out[j][r] = (sum(x * c for x, c in zip(xs, ints)) + x_out[j][r] * outc[j] + alpha) % o
    return out


def expand_ql_hat(x, ql, q_all):
    """ExpandCRTBasisQlHat (dcrtpoly-impl.h:1197-1217): multiply by Q/Q_l in the kept limbs, zero in
    the others: the value D * x modulo Q, D = Q/Q_l."""
    d = prod(q_all) // prod(ql)
    n = len(x[0])
    return [[v * (d % q) % q for v in x[i]] for i, q in enumerate(ql)] + \
           [[0] * n for _ in q_all[len(ql):]]


def tensor_rns(a, b, moduli):
    """[a0 b0, a0 b1 + a1 b0, a1 b1], limb by limb (bfvrns-leveledshe.cpp:326-362)."""
    out = [[], [], []]
    for i, m in enumerate(moduli):
        out[0].append(pmul(a[0][i], b[0][i], m))
        out[1].append(padd(pmul(a[0][i], b[1][i], m), pmul(a[1][i], b[0][i], m), m))
        out[2].append(pmul(a[1][i], b[1][i], m))
    return out


def tensor_int(a, b):
    return [pmul(a[0], b[0]), padd(pmul(a[0], b[1]), pmul(a[1], b[0])), pmul(a[1], b[1])]


# --------------------------------------------------------------------------------------------
# the four techniques.  Operands ca, cb: two integer polynomials each (any representatives modulo
# the level modulus).  Result: dict with
#   out : three polynomials in [0, Q)   -- the ciphertext the library returns
#   A, B: the integer lifts actually multiplied (two polynomials each), A_i = ca_i (mod Q)
#   Q   : the modulus of the result


def mul_hps(ca, cb, qs, rs, t, fl):
    """HPS (bfvrns-leveledshe.cpp:224-237, 364-379): expand both operands Q -> Q u R exactly
    (centred), tensor modulo Q R, ScaleAndRound t/Q into R, SwitchCRTBasis R -> Q."""
    mods = qs + rs
    a = [expand_crt_basis(to_rns(c, qs), qs, rs, fl) for c in ca]
    b = [expand_crt_basis(to_rns(c, qs), qs, rs, fl) for c in cb]
    tt = tensor_rns(a, b, mods)
    out = []
    for comp in tt:
        in_r = scale_and_round(comp[:len(qs)], comp[len(qs):], qs, rs, t, fl)
        out.append(from_rns(switch_crt_basis(in_r, rs, qs, fl), qs))
    return dict(out=out, Q=prod(qs),
                A=[from_rns_centred(x, mods) for x in a], B=[from_rns_centred(x, mods) for x in b])


def _b_lift(w_limbs, delta, mods, q_src, p_prod):
    """The lift B behind a P-over-Q operand: W = (P/Q) B + delta exactly, B = x (mod Q)."""
    w = from_rns_centred(w_limbs, mods)
    out = []
    for wr, dr in zip(w, delta):
        b = (wr - dr) * q_src / p_prod
        assert b.denominator == 1, "P-over-Q operand is not (P/Q) B + delta"
        out.append(int(b))
    return out


def mul_poverq(ca, cb, ql, pl, t, fl):
    """HPSPOVERQ, and HPSPOVERQLEVELED on a ciphertext below the top level
    (bfvrns-leveledshe.cpp:238-262, 380-390): operand 1 expanded exactly Q_l -> Q_l u P_l; operand 2
    scaled by P_l/Q_l with a fast (approximate) conversion and expanded exactly P_l -> Q_l; tensor
    modulo Q_l P_l; ScaleAndRound t/P_l into Q_l."""
    mods = ql + pl
    a = [expand_crt_basis(to_rns(c, ql), ql, pl, fl) for c in ca]
    bw = [fast_expand_p_over_q(to_rns(c, ql), ql, pl, ql, fl) for c in cb]
    tt = tensor_rns(a, [w for w, _ in bw], mods)
    out = [from_rns(scale_and_round(comp[len(ql):], comp[:len(ql)], pl, ql, t, fl), ql) for comp in tt]
    q, p = prod(ql), prod(pl)
    return dict(out=out, Q=q, A=[from_rns_centred(x, mods) for x in a],
                B=[_b_lift(w, d, mods, q, p) for w, d in bw],
                delta=[d for _, d in bw], W=[from_rns_centred(w, mods) for w, _ in bw])


def mul_leveled(ca, cb, qs, rs, drop, t, fl):
    """HPSPOVERQLEVELED at the top level with `drop` >= 1 limbs dropped internally
    (bfvrns-leveledshe.cpp:263-301, 391-405): operand 1 ScaleAndRound Q -> Q_l then expanded exactly
    to P_l; operand 2 fast-converted Q -> P_l (scaling by P_l/Q) and expanded exactly to Q_l; tensor
    modulo Q_l P_l; ScaleAndRound t/P_l into Q_l; multiply by Q/Q_l (ExpandCRTBasisQlHat).
    `drop = 0` is `mul_poverq` (the C++ skips the first ScaleAndRound, :276)."""
    if drop == 0:
        return mul_poverq(ca, cb, qs, rs[:len(qs)], t, fl)
    kl = len(qs) - drop
    ql, pl, qd = qs[:kl], rs[:kl], qs[kl:]
    mods = ql + pl
    q, q_l, p = prod(qs), prod(ql), prod(pl)
    d = q // q_l
    a = []
    for c in ca:
        x = to_rns(c, qs)
        a.append(expand_crt_basis(scale_and_round(x[kl:], x[:kl], qd, ql, 1, fl), ql, pl, fl))
    bw = [fast_expand_p_over_q(to_rns(c, qs), qs, pl, ql, fl) for c in cb]
    tt = tensor_rns(a, [w for w, _ in bw], mods)
    out = []
    for comp in tt:
        x = scale_and_round(comp[kl:], comp[:kl], pl, ql, t, fl)
        out.append(from_rns(expand_ql_hat(x, ql, qs), qs))
    # lifts: A = D A' - alpha with alpha the centred residue of D A' - ca modulo Q
    a_small = [from_rns_centred(x, mods) for x in a]
    a_lift, alphas = [], []
    for c, asm in zip(ca, a_small):
        al = [centred(d * v - x, q) for v, x in zip(asm, c)]
        alphas.append(al)
        a_lift.append([d * v - e for v, e in zip(asm, al)])
    return dict(out=out, Q=q, A=a_lift, B=[_b_lift(w, dl, mods, q, p) for w, dl in bw],
                Asmall=a_small, alpha=alphas, delta=[dl for _, dl in bw])


def smmrq(x, qs, bsk, mtilde):
    """FastBaseConvqToBskMontgomery (dcrtpoly-impl.h:1719-1810), BEHZ "small Montgomery reduction".
      y_i = [x_i * mtilde * (Q/q_i)^-1]_{q_i};  c'' = sum_i y_i Q/q_i  (in Bsk and modulo mtilde);
      r = [-c'' / Q]_{mtilde} centred in [-mtilde/2, mtilde/2);  out_j = (c'' + Q r) / mtilde (mod b_j).
    Returns the limbs over qs + bsk (the q limbs are x unchanged)."""
    big = prod(qs)
    hats = [big // q for q in qs]
    consts = [mtilde * pow(h % q, -1, q) % q for h, q in zip(hats, qs)]
    neg_qinv = (-pow(big, -1, mtilde)) % mtilde
    n = len(x[0])
    out = [[0] * n for _ in bsk]
    for r in range(n):
        ys = [x[i][r] * consts[i] % qs[i] for i in range(len(qs))]
        rm = sum(y * (h % mtilde) for y, h in zip(ys, hats)) % mtilde * neg_qinv % mtilde
        if rm >= mtilde // 2:
            rm -= mtilde
        for j, b in enumerate(bsk):
            cpp = sum(y * (h % b) for y, h in zip(ys, hats)) % b
            out[j][r] = (cpp + rm * (big % b)) * pow(mtilde % b, -1, b) % b
    return x + out


def fast_rns_floor_q(xq, xbsk, qs, bsk, t):
    """FastRNSFloorq (dcrtpoly-impl.h:1815-1864).  y_i = [x_i * t * (Q/q_i)^-1]_{q_i};
    out_j = x_{b_j} * t / Q - sum_i y_i / q_i  (mod b_j)  = floor(t x / Q) - v,
    v = floor(sum_i y_i / q_i) in [0, k-1]."""
    big = prod(qs)
    consts = [t * pow((big // q) % q, -1, q) % q for q in qs]
    n = len(xq[0])
    out = [[0] * n for _ in bsk]
    for r in range(n):
        ys = [xq[i][r] * consts[i] % qs[i] for i in range(len(qs))]
        for j, b in enumerate(bsk):
            aq = sum(y * pow(q % b, -1, b) for y, q in zip(ys, qs)) % b
            out[j][r] = (xbsk[j][r] * (t * pow(big % b, -1, b) % b) - aq) % b
    return out


def fast_base_conv_sk(xbsk, qs, bsk):
    """FastBaseConvSK (dcrtpoly-impl.h:1869-1953), Shenoy-Kumaresan.  bsk = B u {msk}.
      z_i = [x_i (B/b_i)^-1]_{b_i};  alpha = [(sum_i z_i B/b_i - x_msk) / B]_{msk}, centred
      (alpha > floor(msk/2) is read as alpha - msk);  out_j = sum_i z_i B/b_i - alpha B  (mod q_j)."""
    bs, msk = bsk[:-1], bsk[-1]
    big = prod(bs)
    hats = [big // b for b in bs]
    invs = [pow(h % b, -1, b) for h, b in zip(hats, bs)]
    n = len(xbsk[0])
    out = [[0] * n for _ in qs]
    for r in range(n):
        zs = [xbsk[i][r] * invs[i] % bs[i] for i in range(len(bs))]
        alpha = (sum(z * (h % msk) for z, h in zip(zs, hats)) - xbsk[-1][r]) * pow(big % msk, -1, msk) % msk
        if alpha > msk // 2:
            alpha -= msk
        for j, q in enumerate(qs):
            out[j][r] = (sum(z * (h % q) for z, h in zip(zs, hats)) - alpha * big) % q
    return out


def mul_behz(ca, cb, qs, bsk, t, mtilde=1 << 16):
    """BEHZ (bfvrns-leveledshe.cpp:302-324, 407-428): SmMRq of both operands into Bsk, tensor in
    Q u Bsk, FastRNSFloorq into Bsk, Shenoy-Kumaresan back to Q.  Integer-only."""
    mods = qs + bsk
    a = [smmrq(to_rns(c, qs), qs, bsk, mtilde) for c in ca]
    b = [smmrq(to_rns(c, qs), qs, bsk, mtilde) for c in cb]
    tt = tensor_rns(a, b, mods)
    out, floor_bsk = [], []
    for comp in tt:
        f = fast_rns_floor_q(comp[:len(qs)], comp[len(qs):], qs, bsk, t)
        floor_bsk.append(from_rns_centred(f, bsk))
        out.append(from_rns(fast_base_conv_sk(f, qs, bsk), qs))
    return dict(out=out, Q=prod(qs), floor_bsk=floor_bsk,
                A=[from_rns_centred(x, mods) for x in a], B=[from_rns_centred(x, mods) for x in b])


# --------------------------------------------------------------------------------------------
# textbook reference and measurement


def round_half_up(num, den):
    return (2 * num + den) // (2 * den)


def mul_textbook(ca, cb, q, t):
    """Challenge.BFV.Defs.bfvMul: centred lifts, integer tensor, round(t T / Q), modulo Q."""
    a = [[centred(x, q) for x in c] for c in ca]
    b = [[centred(x, q) for x in c] for c in cb]
    return [[round_half_up(t * x, q) % q for x in comp] for comp in tensor_int(a, b)]


def measure(res, ca, cb, t):
    """What the general hypothesis asks of one run.  Returns
      U      max |u| over all coefficients, where lift = centred(operand) + Q u
      excess max(|lift|) - Q/2  (a Fraction; <= 0 for centred lifts)
      dev    per component j: max over coefficients of 2 |Q X_j - t T_j| / Q for the best integer
             X_j congruent to the output modulo Q  (must be <= rho)
    and asserts lift = operand (mod Q)."""
    q = res["Q"]
    umax, exc = 0, Fraction(-q, 2)
    for lifts, ops in ((res["A"], ca), (res["B"], cb)):
        for lift, op in zip(lifts, ops):
            for l, x in zip(lift, op):
                assert (l - x) % q == 0, "lift is not congruent to the operand"
                umax = max(umax, abs((l - centred(x, q)) // q))
                exc = max(exc, abs(l) - Fraction(q, 2))
    tt = tensor_int(res["A"], res["B"])
    dev = []
    for j in range(3):
        worst = Fraction(0)
        for o, tv in zip(res["out"][j], tt[j]):
            v = centred(q * o - t * tv, q * q)      # Q X - t T for the nearest X = o (mod Q)
            worst = max(worst, Fraction(2 * abs(v), q))
        dev.append(worst)
    return dict(U=umax, excess=exc, dev=dev)


# --------------------------------------------------------------------------------------------
# Lean-side formulas (Spec.BudgetBFV / Challenge.BFV.Defs), for the end-to-end check


def mul_bound(n, t, q, k, r_, b1, b2):
    """Challenge.BFV.mulBound N t Q K R B1 B2."""
    r, m, k1 = q % t, t - 1, k + 1
    return n * (b1 + b2) * (t * k1 + m) + r * n * m * (2 * k1 + 1) + \
        (q * r_ + 2 * n * (r * (q // t) * m * m + r * m * (b1 + b2) + t * b1 * b2)) // (2 * q)


def dec_ok(t, q, b):
    return 2 * (t * b + q % t * (t - 1)) < q


def general_mul_lift(n, bs, u):
    """mulLift of the general theorem: floor((2 + N B_s)/2) + U (1 + N B_s)."""
    return (2 + n * bs) // 2 + u * (1 + n * bs)


def general_mul_round(n, bs, rho):
    """mulRound of the general theorem: rho (1 + N B_s + (N B_s)^2)."""
    return rho * (1 + n * bs + (n * bs) ** 2)
