# What certification costs: OpenFHE defaults vs the cheapest certified settings

This directory measures, for OpenFHE v1.6.1 BGV and BFV, how far the library's default parameters
are from parameters that `fhe_check` certifies (worst case, and with probabilistic fresh noise at
κ = 128), what the cheapest certified settings a user can actually configure are, and what they
cost in evaluation time. The final tables are in `RESULTS.md`; their data in `data/`.

Nothing here is trusted. Every verdict in the tables is a plain `fhe_check` run (the locked
decision `certify?` / `certifyBFV?` through the normal checker path) on a file extracted from the
library's OWN traced run of the program at those settings; the searches, the cost model and the
scripts only choose which settings to run.

## Programs

- `chain` (depth d): `y = (a·b)^(2^(d−1))`: `EvalMult` then `EvalSquare` d−1 times, each
  relinearised (BGV FIXEDMANUAL: `ModReduce` after each).
- `poly` (depth d), the realistic circuit: an inner product followed by a degree-d polynomial by
  Horner's rule. `u = a·b`; `u += rot(u,1)`; `u += rot(u,2)`; `u += rot(u,4)` (slot i holds
  Σ_{j<8} (a·b)[i+j]); `y = u + c_{d−1}`; then for j = d−2 … 0: `y = y·u + c_j`. So
  `y = p(⟨a,b⟩)` with `p(x) = x^d + c_{d−1}x^{d−1} + … + c_0` (packed plaintext coefficients): exactly
  d ciphertext×ciphertext multiplications, all on the critical path (depth d), 3 rotations, d
  plaintext additions. Under FIXEDMANUAL `u` is `LevelReduce`d to `y`'s level before each product.
  (Not included: a plaintext multiplication. In the worst case it multiplies the noise by
  N·(t−1), about 30-35 bits; the earlier study's `mixed` program had them, and under-counted its
  depth.)
- Inputs: packed plaintexts of 8 slots; every run's decryption is compared with the same function
  computed in the clear (slot model: rotation within rows of N/2 slots), and the extracted file is
  value-checked against OpenFHE's raw decryption (`value_check.py`, `value_check_bfv.py`).

## Families and what is searched

| family | settings searched (public API only) | how |
|---|---|---|
| BGV FIXEDMANUAL (HYBRID) | `SetFirstModSize`, `SetScalingModSize`, `SetNumLargeDigits`, `SetRingDim` | `fhe_check recommend` (time objective) on the default's extracted file; `--digits any`, `--digits keep`, and `--digits any --kappa 128`; then configured and run end to end |
| BGV FLEXIBLEAUTOEXT (OpenFHE's default) | `SetEvalAddCount` (0…10^6), `SetKeySwitchCount` (0…10^4), `SetMultiplicativeDepth` d, d+1, d+2 | library in the loop |
| BFV × {HPSPOVERQLEVELED (default), HPSPOVERQ, BEHZ} × {BV (default), HYBRID} | `SetMultiplicativeDepth` c = 1…d+10, `SetScalingModSize` s = 24…60, `SetNumLargeDigits` (HYBRID: default, 1-4) | library in the loop |

Depths 1-12, t = 65537 and t = 786433 (= 3·2^18 + 1, batching-friendly up to N = 2^17), both
programs: 384 cells.

**What OpenFHE's public API lets a BFV user set** (`bfvrns-parametergeneration.cpp` in v1.6.1):
every limb of Q has the same size `s = SetScalingModSize`, 14 ≤ s ≤ 60 (`:59`,
`rns-modulus-limits.h:43`; BFV has no first-modulus size); the number of limbs is
`k = ⌈⌈log q_est⌉ / s⌉` where `log q_est` is the library's noise heuristic for the requested
multiplicative depth c at ring dimension n (`:264-292`, `:320`), so k is steered by (c, s) and
cannot be set directly; N is the smallest secure one for `k·s` (+ the estimated P for HYBRID,
`:125-145`, `:297-303`) or `SetRingDim` (throws if insecure, `:314`); `SetEvalAddCount` or
`SetKeySwitchCount` together with a depth > 0 throws (`:304-311`), so they are not BFV levers; HYBRID
special primes are 60-bit (`auxBits`, `:84`) and `SetNumLargeDigits` sets their number; BV with a
digit size ≠ 0 (`SetDigitSize`) is refused by the extractor (`extract_bfv.py:588`), so it is outside
what can be certified here. So total log Q can be set to within one limb size of any target, but
never with limbs above 60 bits: the limb COUNT needed is ⌈needed log Q / 60⌉ at best.

**BGV automatic modes**: `SetScalingModSize`/`SetFirstModSize` are refused outside FIXEDMANUAL
(`gen-cryptocontext-params-validation.cpp:150-158`); the levers are the noise-estimate inputs
(`SetEvalAddCount`, `SetKeySwitchCount`) and a larger depth.

## The library-in-the-loop search (`frontier.py`, `lib_search`)

1. Every candidate setting is given to OpenFHE, which generates the context (a "params-only" run
   of the traced driver; ≈ 29,000 BFV contexts, cached). Contexts with N not allowed by packed
   encoding (t ≢ 1 mod 2N) are dropped.
2. Contexts are grouped into cost classes (N, limbs, special primes, limbs per digit) and the
   classes ordered by the time proxy (`costmodel.py`; a fitted MODEL, see below).
3. In that order, the largest-Q member of each class is run TRACED (single-threaded build),
   extracted, value-checked, cleartext-checked and checked by a plain `fhe_check` (worst case and
   `--kappa 128`); the first CERTIFIED class is the answer. Then the smallest Q of that class that
   still certifies is found by bisection ("least log Q in that class": how many bits the certificate
   actually needs, to within one limb-size step).

Not claimed: optimality. A class whose largest Q fails is not searched further (smaller limbs can
lower the BV relinearisation noise, so a smaller Q in the same class could in principle certify);
the class order is a model with up to 24% error on BFV (below).

## Time: measured, and the model

- MEASURED (`timing.py`): `frontier_time` on the PRISTINE OpenFHE v1.6.1 install, evaluation
  only (no key generation, encryption or decryption in the timed region), one thread
  (`OMP_NUM_THREADS=1`), one warm-up then 5 runs, two interleaved rounds of (default, certified,
  certified κ=128); the minimum is reported. The timed context's primes are asserted equal to the
  traced run's. The 1-minute load average is recorded before every process; rows above 20 are
  marked `*` (the machine is shared; ratios of interleaved runs are more robust than absolute times).
- MODELLED (`costmodel.py`, `timing_fit.py`): `T ≈ N·log₂N·(a·A + b·B)`, A = Σ limbs over
  multiplications, rotations and (BGV) modulus switches, B = Σ key-switching work (HYBRID:
  digits·(limbs + special primes); BV: limbs²). Fitted per family on 116 measured contexts
  (`data/timing_fit.json`): BGV FIXEDMANUAL (28 points, max error 7.6%), BFV 6 families (13-15 points
  each, max error 10-24%). `fhe_check recommend` uses the BGV FIXEDMANUAL fit.

## Files

- `build.sh OUT [TRACED] [PRISTINE]`: builds `frontier_bgv`, `frontier_bfv` (traced runs) and
  `frontier_time` (timing) from `src/`.
- `src/frontier_bgv.cpp`, `src/frontier_bfv.cpp`: the frontend's `bgv_demo.cpp`/`bfv_demo.cpp` with
  the `poly` program, `--progdepth`, a `params` (context-only) mode, BFV `--ringdim` (keeps the
  security level). `src/frontier_time.cpp`: the same contexts and programs, untraced, timed.
- `frontier.py OUT bgvfm|bgvauto|bfv`: the searches; `timing.py`; `timing_fit.py`; `tables.py`;
  `costmodel.py`; `frontier_lib.py` (shared glue).
- `run.sh OUT [TRACED] [PRISTINE]`: everything, in order.
- `data/`: `frontier.tsv` (one row per cell), `summary.json`, `timing.jsonl`, `timing_fit.json`.
  The compacted search rows `run.sh` also writes there (`rows/*.jsonl`: default, best classes,
  least-Q member, every class evaluated with its verdict) are intermediate and not part of the
  public release.

## Scope and limits

- One library version (OpenFHE v1.6.1), 128-bit classical security (OpenFHE's table), ternary
  secrets, two programs, two plaintext moduli; HYBRID BGV only; no CKKS.
- The searches are not claimed optimal (above). The cost model orders candidates; the reported
  ratios are measured.
- t = 65537 limits packed encoding to N ≤ 2^15: cells whose certified setting would need N = 2^16
  have NO certified setting at this t (a hard ceiling of the library's packed encoding, not of the
  checker).
- Timing: the committed `data/timing.jsonl` was taken on 2026-11-15 on an otherwise idle 128-core machine,
  one process at a time, `OMP_NUM_THREADS=1` (single-threaded evaluation on an OpenMP build); every row
  records the load average before each process (1.0 to 5.9; no row above the `*` limit of 20).
- The end-to-end validation is per row: the certified setting's own traced run is extracted,
  value-checked, cleartext-checked and CERTIFIED by a plain check; for BGV FIXEDMANUAL also the
  primes OpenFHE generated equal the ones `recommend` predicted.
