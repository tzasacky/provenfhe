#!/usr/bin/env python3
"""(U, rho) for the general "approximate multiplication" hypothesis, per OpenFHE BFVrns technique.

Hypothesis shape (two-component operands modulo Q):
  lifts   A_i = centred(a_i) + Q u_i,  B_i = centred(b_i) + Q v_i,   |u|, |v| <= U
  tensor  T = A (x) B over Z[X]/(X^N+1)
  output  X_j = out_j (mod Q)  with  2 |Q X_j - t T_j| <= Q rho  coefficientwise.

Every function returns a dict
  U, rho : natural numbers
  eta    : Fraction, a bound on  max|lift| - Q/2  (the lift is within Q/2 + eta; much finer than U)
  side   : bool, the side conditions under which (U, rho, eta) are claimed
  why    : the side conditions, as text
All moduli are assumed odd and pairwise coprime (products of distinct odd primes).

Float tolerance is described by three rationals (all 0 for the idealised algorithm):
  e_sw   SwitchCRTBasis: the float overflow sum `nu` is within e_sw of its exact value
  e_sr   final ScaleAndRound: `nu` within e_sr of its exact value  (so the result is within
         1/2 + e_sr of the exact quotient; "off by at most F units" is e_sr = F)
  e_sr1  (leveled only) the same for the internal ScaleAndRound Q -> Q_l
`double_e_sw` / `double_e_sr` give values valid for IEEE binary64 as the C++ computes them.
"""
from fractions import Fraction
from math import prod

from rnsbfv import ceil_frac


def double_e_sw(k):
    """|nu_float - nu| in SwitchCRTBasis over k source limbs, binary64 (u = 2^-53): each term
    fl(fl(y) * fl(1/fl(q))) carries 4 roundings (relative error <= 4u + O(u^2)) and is < 1; the k
    additions each add <= u (k + 1/2).  First order: k (k + 4.5) u.  Bound used: k (k + 5) / 2^53
    (an FMA contraction only removes roundings)."""
    return Fraction(k * (k + 5), 2 ** 53)


def double_e_sr(mod_in):
    """|nu_float - nu| in ScaleAndRound with input limbs `mod_in` (k of them), binary64: each term
    fl(fl(fl(num)/fl(s)) * fl(x)) carries 5 roundings (relative error <= 5u + O(u^2)) and is < s;
    the k additions each add <= u (1/2 + sum s).  First order: (k + 5) u (1/2 + sum s).  Bound
    used: (k + 6) (1 + sum s) / 2^53.  It exceeds 1/2 as soon as the limbs exceed about
    2^52 / (k (k + 6)): binary64 does NOT give an off-by-one ScaleAndRound for 60-bit limbs."""
    return Fraction((len(mod_in) + 6) * (1 + sum(mod_in)), 2 ** 53)


def hps(n, t, qs, rs, e_sw=0, e_sw_r=None, e_sr=0):
    """HPS.  Lifts: SwitchCRTBasis gives the representative in [-Q/2, Q/2), exactly when
    e_sw = 0; with float error it may give the other one when x/Q is within e_sw of 1/2.
    Output: X = round(t T / Q) + s, |s| <= e_sr, recovered from its residue modulo R, which needs
    |X| < R/2 (with margin R e_sw_r so that the final SwitchCRTBasis cannot flip).
      eta = Q e_sw;  U = 0 if e_sw = 0 else 1;  rho = ceil(1 + 2 e_sr)
      side:  t N Q (1 + 2 e_sw)^2 + 2 + 2 e_sr <= R (1 - 2 e_sw_r)."""
    q, r = prod(qs), prod(rs)
    e_sw = Fraction(e_sw)
    e_sw_r = e_sw if e_sw_r is None else Fraction(e_sw_r)
    e_sr = Fraction(e_sr)
    side = t * n * q * (1 + 2 * e_sw) ** 2 + 2 + 2 * e_sr <= r * (1 - 2 * e_sw_r) and e_sw < Fraction(1, 2)
    return dict(U=0 if e_sw == 0 else 1, rho=ceil_frac(1 + 2 * e_sr), eta=q * e_sw, side=side,
                why="t*N*Q*(1+2e_sw)^2 + 2 + 2e_sr <= R*(1-2e_sw_R)")


def poverq(n, t, ql, pl, e_sw=0, e_sr=0):
    """HPSPOVERQ (and HPSPOVERQLEVELED with no internal drop).  k = number of limbs of Q.
    Operand 1: exact centred lift A (|A| <= Q/2 + Q e_sw).  Operand 2: W = (P/Q) B + delta,
    delta in [0, k), W in [-P/2 - P e_sw, P/2 + P e_sw), so |B| <= Q/2 + Q e_sw + k Q / P.
    Output X = round(t A W / P) + s:  X - t A B / Q = t A delta / P + (rounding), per product
    |t A delta / P| <= t N (Q/2)(1 + 2 e_sw) k / P; component 1 has two products.
      U = 1;  eta = Q e_sw + k Q / P;  rho = ceil(1 + 2 e_sr + 2 t N k Q (1 + 2 e_sw) / P)
      side:  k / P + e_sw < 1/2.   No "no wrap-around" condition on the tensor: the output is only
      needed modulo Q and t*(Q P)/P = 0 (mod Q)."""
    q, p, k = prod(ql), prod(pl), len(ql)
    e_sw, e_sr = Fraction(e_sw), Fraction(e_sr)
    rho = ceil_frac(1 + 2 * e_sr + Fraction(2 * t * n * k * q, p) * (1 + 2 * e_sw))
    return dict(U=1, rho=rho, eta=q * e_sw + Fraction(k * q, p),
                side=Fraction(k, p) + e_sw < Fraction(1, 2), why="k/P + e_sw < 1/2")


def leveled(n, t, qs, rs, drop, e_sw=0, e_sr1=0, e_sr=0):
    """HPSPOVERQLEVELED at the top level with `drop` >= 1 limbs dropped.  k = limbs of Q,
    Q_l / P_l the first k - drop limbs, D = Q / Q_l.
    Operand 1: A' = round(Q_l a / Q) centred modulo Q_l;  D A' = A + alpha,  A = a (mod Q),
    |alpha| <= D (1/2 + e_sr1), |A'| <= Q_l/2 + Q_l e_sw.   Operand 2: W = (P_l/Q) B + delta,
    delta in [0, k), |B| <= Q/2 + Q e_sw + k Q / P_l.   Output X = D (round(t A' W / P_l) + s):
      X - t A B / Q = D (rounding + s) + t alpha B / Q + t D A' delta / P_l     (per product)
      rho = ceil( D (1 + 2 e_sr)
                  + t N D [ (1 + 2 e_sr1)(1 + 2 e_sw + 2 k / P_l) + 2 k Q_l (1 + 2 e_sw) / P_l ] )
      U = 1;  eta = max( D (1/2 + e_sr1) + Q e_sw ,  Q e_sw + k Q / P_l )
      side:  k / P_l + e_sw < 1/2  and  D (1/2 + e_sr1) + Q e_sw < Q/2."""
    if drop == 0:
        return poverq(n, t, qs, rs[:len(qs)], e_sw, e_sr)
    k, kl = len(qs), len(qs) - drop
    q, q_l, p_l = prod(qs), prod(qs[:kl]), prod(rs[:kl])
    d = q // q_l
    e_sw, e_sr1, e_sr = Fraction(e_sw), Fraction(e_sr1), Fraction(e_sr)
    rho = ceil_frac(d * (1 + 2 * e_sr) + t * n * d * (
        (1 + 2 * e_sr1) * (1 + 2 * e_sw + Fraction(2 * k, p_l)) + Fraction(2 * k * q_l, p_l) * (1 + 2 * e_sw)))
    eta_a = d * (Fraction(1, 2) + e_sr1) + q * e_sw
    eta_b = q * e_sw + Fraction(k * q, p_l)
    side = Fraction(k, p_l) + e_sw < Fraction(1, 2) and eta_a < Fraction(q, 2)
    return dict(U=1, rho=rho, eta=max(eta_a, eta_b), side=side,
                why="k/P_l + e_sw < 1/2 and D*(1/2+e_sr1) + Q*e_sw < Q/2")


def behz(n, t, qs, bsk, mtilde=1 << 16):
    """BEHZ (integer-only; nothing to idealise).  k = limbs of Q, Bsk = B u {msk}, k_B = limbs of B.
    Lifts (SmMRq): A = (c'' + Q r)/mtilde with c'' in [0, k Q - sum Q/q_i], r in [-mtilde/2, mtilde/2):
      A in [-Q/2, Q/2 + (k-1) Q / mtilde),  so  U = 1,  eta = (k-1) Q / mtilde.
    Output: X = floor(t T / Q) - v,  v in [0, k-1]  =>  t T / Q - X in [0, k):  rho = 2 k.
    Shenoy-Kumaresan is exact iff  |X| / B + k_B <= (msk - 1)/2;  with |T_1| <= 2 N (Q/2 + eta)^2:
      side:  t N Q (mtilde + 2(k-1))^2 + 2 k mtilde^2 <= mtilde^2 B (msk - 1 - 2 k_B),
             gcd(mtilde, Q) = 1,  2 (k-1) <= mtilde."""
    q, k = prod(qs), len(qs)
    b, msk, kb = prod(bsk[:-1]), bsk[-1], len(bsk) - 1
    side = (t * n * q * (mtilde + 2 * (k - 1)) ** 2 + 2 * k * mtilde ** 2 <= mtilde ** 2 * b * (msk - 1 - 2 * kb)
            and 2 * (k - 1) <= mtilde and q % 2 == 1)
    return dict(U=1, rho=2 * k, eta=Fraction((k - 1) * q, mtilde), side=side,
                why="t*N*Q*(mt+2(k-1))^2 + 2k*mt^2 <= mt^2*B*(msk-1-2k_B)")


def lift_from_eta(n, bs, q, eta):
    """A finer mulLift from a norm bound instead of U: if |A_i| <= Q/2 + eta for both components
    then the integer phase A_0 + A_1 s = Phi + Q k has |k| <= ((Q/2 + eta)(1 + N B_s) + Q/2) / Q:
      mulLift = floor( ((Q + 2 eta)(1 + N B_s) + Q) / (2 Q) ).
    (eta = 0 gives the textbook floor((2 + N B_s)/2).)"""
    eta = Fraction(eta)
    x = ((q + 2 * eta) * (1 + n * bs) + q) / (2 * q)
    return x.numerator // x.denominator


def leveled_keyswitch(n, d, ks_l, b_tgt, e_sr1=0):
    """Phase error of RelinearizeCore / EvalFastRotation in HPSPOVERQLEVELED with internal drop
    (bfvrns-leveledshe.cpp:856-900, 759-850; upstream OpenFHE v1.6.1): the switched component c is replaced by
    c' = round(Q_l c / Q) (+ float deviation), key-switched at level l with phase error e_l,
    |e_l| <= ks_l, and the result is multiplied by D = Q/Q_l.   D c' = c + D eps (mod Q),
    |eps| <= 1/2 + e_sr1, so the phase moves by  D (eps * s_tgt + e_l):
        |e| <= floor( D ((1 + 2 e_sr1) N b_tgt + 2 ks_l) / 2 )
    b_tgt = |s_tgt|_inf: N B_s^2 for relinearisation (target s^2), B_s for an automorphism or a
    key switch from another key of norm B_s."""
    x = d * ((1 + 2 * Fraction(e_sr1)) * n * b_tgt + 2 * ks_l) / 2
    return x.numerator // x.denominator


def bv_ks_bound(n, b_k, ql):
    """BV key switching, digitSize 0, at a level with limbs ql: digits are the centred residues
    (|d_i| <= (q_i - 1)/2), error sum_i d_i e_i:  N B_k sum_i (q_i - 1) / 2.  (<= Spec.Budget.ksBoundAt
    with no special primes, one limb per digit, canonical = false: floor(N B_k sum q_i / 2).)"""
    return n * b_k * sum(q - 1 for q in ql) // 2
