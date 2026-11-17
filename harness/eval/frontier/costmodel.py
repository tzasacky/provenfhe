"""Time proxy for homomorphic evaluation (UNTRUSTED, a MODEL; fitted by timing_fit.py).

T ~ N log2 N * (a * A + b * B), with operation features summed over the program at each
operation's number of limbs l:
  A = sum over multiplications, automorphisms (rotations) and, BGV, modulus switches of l
  B = sum over key switches (relinearisations and rotations) of the key-switching work:
      HYBRID: d(l) * (l + K)   with d(l) = ceil(l / alpha) digits at level l, K special primes
      BV (BFV): l * l          (one digit per limb, each expanded to l limbs)
The coefficients (a, b) per (scheme, multiplication technique, key switching) are in
COEFFS (fitted on the pristine library; see timing_fit.py and RESULTS.md for the fit).
fhe_check recommend (FHE/Check/Recommend.lean, `costProxy`) uses the BGV HYBRID entry with the
same feature definitions, computed from the program's own levels.
"""
import math

# fitted by timing_fit.py (pristine OpenFHE v1.6.1, single thread, results/timing_fit.json);
# (a, b) in ms; max relative error on the fitted points in the comment
COEFFS = {
    "bgv/HYBRID": (5.0019e-06, 1.4675e-06),                    # FIXEDMANUAL, 28 points, 7.6%
    "bgv-auto/HYBRID": (3.3396e-06, 1.7574e-06),               # FLEXIBLEAUTOEXT, 3 points, 2.0%
    "bfv/BEHZ/BV": (2.5955e-05, 1.7250e-06),                   # 13 points, 12.6%
    "bfv/BEHZ/HYBRID": (3.2991e-05, 1.6866e-06),               # 15 points, 9.9%
    "bfv/HPSPOVERQ/BV": (2.3342e-05, 2.0983e-06),              # 13 points, 23.4%
    "bfv/HPSPOVERQ/HYBRID": (3.0732e-05, 2.3372e-06),          # 15 points, 24.1%
    "bfv/HPSPOVERQLEVELED/BV": (2.4342e-05, 1.0516e-06),       # 13 points, 19.0%
    "bfv/HPSPOVERQLEVELED/HYBRID": (3.5672e-05, 0.0),          # 15 points, 16.3%
}


def ceil_div(a, b):
    return -(-a // b)


def features(scheme, prog, d, L, K=0, alpha=1, ks="HYBRID"):
    """(A, B) for the programs of this directory (chain, poly) at depth d with L ciphertext limbs
    at the start, K special primes, alpha limbs per digit (HYBRID)."""
    def kswork(l):
        if ks == "BV":
            return l * l
        return ceil_div(l, alpha) * (l + K)
    A = B = 0
    if scheme == "bgv":
        # FIXEDMANUAL-style: every product followed by a modulus switch
        if prog == "chain":
            for j in range(d):
                l = L - j
                A += 2 * l
                B += kswork(l)
        elif prog == "poly":
            l = L
            A += 2 * l
            B += kswork(l)
            l -= 1
            A += 3 * l
            B += 3 * kswork(l)
            for _ in range(d - 1):
                A += 2 * l
                B += kswork(l)
                l -= 1
        return A, B
    # BFV: all operations at the full number of limbs
    if prog == "chain":
        return d * L, d * kswork(L)
    if prog == "poly":
        return (d + 3) * L, (d + 3) * kswork(L)
    raise ValueError(prog)


def proxy(group, N, A, B):
    a, b = COEFFS.get(group, (1.0, 1.0))
    return N * math.log2(N) * (a * A + b * B)
