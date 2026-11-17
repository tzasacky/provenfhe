#!/usr/bin/env python3
"""Replica of OpenFHE's `FindLevelsToDrop` (src/pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:98-198 in
upstream OpenFHE v1.6.1 (b59e1f29)),
the function that decides how many RNS limbs HPSPOVERQLEVELED drops *inside* EvalMult, EvalSquare,
RelinearizeCore and EvalFastRotationPrecompute.  It is a deterministic function of the crypto
parameters and of the operand's `noiseScaleDeg`; an extractor can therefore declare the internal
drop of every operation without running the library.

The C++ computes in binary64 with libm `log2`, `sqrt`, `pow`, `floor` (v1.6.1 works in bits
throughout; v1.3.1 used natural logs and a cushion of 2 per level instead of 3); this file performs
the same operations in the same order with Python floats (binary64, same libm on the same
platform).  `GetDistributionParameter()` and `GetAssuranceMeasure()` return C `float`
(rlwe-cryptoparameters.h:154, 173), so sigma = 3.19f and alpha = 36.0f are first rounded to
binary32 here as well.  The result passes through `floor`, so a last-bit difference in libm (or an
FMA contraction in the C++ build) can only matter exactly on a limb boundary.

Call sites (all require multiplication technique HPSPOVERQLEVELED and a ciphertext with the full
number of limbs, sizeQ == sizeQM; otherwise nothing is dropped):

  EvalMult(ct1, ct2)            levels = max(deg1, deg2) - 1, keySwitch = False   (:264-272)
        l = sizeQ - 1 - drop  (index of the last kept limb; kept limbs = sizeQ - drop)
        result deg = max(deg1, deg2) + 1                                           (:431)
  EvalSquare(ct)                levels = deg - 1, keySwitch = False                (:486-492)
        result deg = deg + 1                                                       (:707)
  RelinearizeCore(ct, key)      levels = deg - 1,
                                keySwitch = (ct has 2 components)                  (:869-874)
        (after EvalMult the 3-component ciphertext already has deg = max + 1)
  EvalFastRotationPrecompute    levels = deg - 1, keySwitch = True                 (:776-779)
  EvalAutomorphism              -> RelinearizeCore on a 2-component ciphertext     (:752)

`dcrtBits` at every call site is `GetModulus().GetMSB()` of limb 0: its bit length.

noiseScaleDeg ("deg") bookkeeping in BFV: fresh encryption 1 (bfvrns-pke.cpp:162, 220); ct*ct
max + 1; square + 1; multiplication by an integer constant + 1 (bfvrns-leveledshe.cpp:741);
ct*plaintext unchanged (rns-leveledshe.cpp:265-266, NORESCALE branch); add/sub: the first operand's
(in-place on a clone).  An extractor that can read `GetNoiseScaleDeg()` should prefer it.
"""
import argparse
import struct
from math import floor, log2, sqrt


def f32(x):
    """Round to binary32 (the C++ getters return `float`)."""
    return struct.unpack("f", struct.pack("f", x))[0]


def find_levels_to_drop(multiplicative_depth, *, ring_dim, plaintext_modulus, dcrt_bits, size_q,
                        key_switch=False, digit_size=0, ks_technique="BV",
                        encryption_technique="STANDARD", secret_key_dist="UNIFORM_TERNARY",
                        sigma=3.19, assurance=36.0, threshold_parties=1,
                        num_per_part_q=0, num_part_q=0, reduced_noise=False):
    """`multiplicative_depth` is the `levels` argument of the call site (noiseScaleDeg - 1).
    Returns the number of limbs dropped, in [0, size_q - 1].

    ring_dim            n
    plaintext_modulus   t (called p in the C++)
    dcrt_bits           bit length of limb 0
    size_q              number of limbs of the context
    digit_size          GetDigitSize()  (0 = one digit per limb)
    ks_technique        "BV" | "HYBRID";  num_per_part_q / num_part_q only for HYBRID
                        (num_per_part_q = ceil(size_q / num_part_q), rns-cryptoparameters.cpp:90-98)
    encryption_technique "STANDARD" | "EXTENDED"
    secret_key_dist     "GAUSSIAN" | anything else (ternary: Bkey = threshold_parties)
    reduced_noise       the WITH_REDUCED_NOISE build option
    """
    sigma = f32(sigma)
    alpha = f32(assurance)
    p = float(plaintext_modulus)
    n = ring_dim
    relin_window = digit_size
    k = num_per_part_q
    dcrt_bits = int(dcrt_bits)

    berr = sigma * sqrt(alpha)
    bkey = sqrt(threshold_parties) * berr if secret_key_dist == "GAUSSIAN" else float(threshold_parties)
    w = pow(2, dcrt_bits if relin_window == 0 else relin_window)

    def delta(n_):
        return 2.0 * sqrt(n_)

    def delta_ms(n_):
        return 4.0 * sqrt(n_)

    def vnorm(n_):
        if encryption_technique == "EXTENDED":
            return (1.0 + delta_ms(n_) * bkey) / 2.0
        return berr * (1.0 + 2.0 * delta(n_) * bkey)

    def noise_ks(n_, logq_prev, w_):
        if ks_technique == "HYBRID":
            if reduced_noise:
                return k * (num_part_q * delta(n_) * berr + delta(n_) * bkey + 1.0) / 2.0
            return k * (num_part_q * delta(n_) * berr + delta_ms(n_) * bkey + 1.0)
        digits_per_tower = 1 if relin_window == 0 else (dcrt_bits // relin_window) + 1
        return delta(n_) * digits_per_tower * (floor(logq_prev / dcrt_bits) + 1) * w_ * berr / 2.0

    def c1(n_):
        return delta(n_) * delta_ms(n_) * p * bkey

    def c2(n_, logq_prev):
        return delta(n_) * delta_ms(n_) * bkey * bkey / 2.0 + noise_ks(n_, logq_prev, w)

    def logq_bfv(n_, logq_prev):
        if multiplicative_depth > 0:
            return (log2(4 * p) + (multiplicative_depth - 1) * log2(c1(n_)) +
                    log2(c1(n_) * vnorm(n_) + multiplicative_depth * c2(n_, logq_prev)))
        return log2(p * (4 * vnorm(n_)))

    logq_prev = 6.0 * log2(10)
    logq = logq_bfv(n, logq_prev)
    while abs(logq - logq_prev) > log2(1.001):
        logq_prev = logq
        logq = logq_bfv(n, logq_prev)

    loge = logq - 2 - log2(p)
    log_extra = log2(noise_ks(n, logq, w)) if key_switch else log2(delta_ms(n))
    levels = floor((loge - 3 * multiplicative_depth - 16 - log_extra) / dcrt_bits)
    return max(0, min(levels, size_q - 1))


def internal_drop(op, degs, **params):
    """Limbs dropped inside one operation of HPSPOVERQLEVELED on full-size ciphertexts.
    op: "mul" (degs = (deg1, deg2)), "square", "relin" (3-component input; pass the degree of that
    ciphertext, i.e. max + 1 after EvalMult), "keyswitch" / "rotate" (2-component input)."""
    if op == "mul":
        return find_levels_to_drop(max(degs) - 1, key_switch=False, **params)
    if op in ("square", "relin"):
        return find_levels_to_drop(degs[0] - 1, key_switch=False, **params)
    if op in ("keyswitch", "rotate"):
        return find_levels_to_drop(degs[0] - 1, key_switch=True, **params)
    raise ValueError(op)


def main():
    ap = argparse.ArgumentParser(description="FindLevelsToDrop replica (OpenFHE BFVrns, HPSPOVERQLEVELED)")
    ap.add_argument("--ring-dim", type=int, default=16384)
    ap.add_argument("--t", type=int, default=65537)
    ap.add_argument("--dcrt-bits", type=int, default=60)
    ap.add_argument("--size-q", type=int, default=3)
    ap.add_argument("--digit-size", type=int, default=0)
    ap.add_argument("--max-deg", type=int, default=6)
    args = ap.parse_args()
    params = dict(ring_dim=args.ring_dim, plaintext_modulus=args.t, dcrt_bits=args.dcrt_bits,
                  size_q=args.size_q, digit_size=args.digit_size)
    print(f"n={args.ring_dim} t={args.t} dcrtBits={args.dcrt_bits} sizeQ={args.size_q} digitSize={args.digit_size} (BV, STANDARD, ternary)")
    print("deg  drop in EvalMult/EvalSquare/relin(3 comp)   drop in key switch (2 comp)")
    for deg in range(1, args.max_deg + 1):
        print(f"{deg:>3}  {internal_drop('square', (deg,), **params):>10} "
              f"{internal_drop('rotate', (deg,), **params):>36}")


if __name__ == "__main__":
    main()
