# Certified frontier: results (2026-11-15; every timing re-taken on a quiet machine)

Status: all 384 searches are complete and every certified row is end-to-end validated (the
certified setting's own traced run extracted, value-checked, cleartext-checked and CERTIFIED by a
plain fhe_check; BGV FIXEDMANUAL also: OpenFHE's primes = the predicted ones, 142/142). MEASURED
runtime ratios: every row that has a baseline was re-timed on 2026-11-15 on an otherwise idle
128-core machine (AMD EPYC 7742; the 1-minute load average read before each of the 2,378 timed
processes in the final rows was 1.0 to 5.9, median 1.4, which is the timing process's own
predecessor plus the desktop background; 51 started above 3), one timing process at a time
(`timing.py --workers 1`: the script does not pin cores, so concurrent workers were avoided),
on the pristine OpenFHE v1.6.1 build (built with OpenMP, Release, run with `OMP_NUM_THREADS=1`, so
single-threaded evaluation), evaluation only, minimum of 5 runs after one warm-up, two interleaved
rounds of (default, certified, certified kappa = 128). 381 of the 384 rows: BGV FIXEDMANUAL 48,
BGV FLEXIBLEAUTOEXT 45 (2 rows where the OpenFHE default itself throws have no baseline; 1 row has no certified setting),
BFV 288. No row in the tables below carries a `*` (the mark for a timing taken at high load): none
of the earlier loaded-machine timings (load 20 to 45) is left. `n/m` = not measurable (no baseline
or no certified setting). Ratios are certified / OpenFHE default evaluation time of the same circuit.

## Headline (supported by the data; scope: OpenFHE v1.6.1, 128-bit, t = 65537 and 786433, chain and inner-product+polynomial, depth 1-12)
- OpenFHE's defaults (column `default_worst` of `data/frontier.tsv`: the plain worst-case check of
  the default's own traced run): CERTIFIED in 61 of the 384 cells (BGV FIXEDMANUAL 4/48, BGV
  FLEXIBLEAUTOEXT 0/48, BFV HYBRID 24/144, BFV BV 33/144; at kappa = 128, 64: 3 more BGV FIXEDMANUAL
  d2 cells). Of the other 323: 313 overflow, 1 is NOT CERTIFIED without a reported overflow (BFV
  HPSPOVERQ BV, chain, t = 65537, d3), and 9 have no verdict: 2 where OpenFHE throws at the default
  (BGV FLEXIBLEAUTOEXT, t = 786433, d3) and 7 where the default run decrypts WRONGLY (cleartext
  mismatch; BFV HPSPOVERQLEVELED BV, t = 786433), so there is no file to check.
- BGV FIXEDMANUAL: certified parameters exist in all 48 cells at the default's ring dimension or a
  SMALLER one (38 same N, 10 smaller) with the same number of ciphertext primes; scaling primes
  45 -> 35-54 bits (t = 65537) / 48 -> 42-58 bits (t = 786433); measured 0.51-1.23x of the default's
  evaluation time over the 48 cells (at kappa = 128: 0.50-1.13x; digits kept: 0.99-1.08x in the
  43 cells where the certified setting has the default's shape).
- BGV FLEXIBLEAUTOEXT (default scaling): certified by raising SetEvalAddCount (and in a few cells
  one more level) in 47/48 cells; 10 cells need N doubled (measured 2.09-2.32x, all 10 timed), the other
  35 timed cells 0.99-1.31x (45 timed in all; 2 more certified cells have no baseline because the default throws);
  chain d12 at t = 65537 has no certified setting (would need N = 2^16, which packed encoding forbids).
- BFV: every cell certifiable; the default needs +0 to +3 limbs (HYBRID, never N doubled) or +0 to
  +8 limbs (BV; N doubles in 4-5 cells per BV family). Fine-grained limb sizes do NOT remove the
  BFV cost: the certificate needs about 44-46 bits of log Q per product, OpenFHE's heuristic gives
  about 37-40, and limbs cannot exceed 60 bits, so the limb count is ceil(need/60); smaller limbs
  only help when they avoid an N doubling, and BV key switching (quadratic in limbs) eats that gain.
  Measured, all 288 cells timed: HYBRID (3 families, 144 cells) 0.39-1.57x of the default's
  evaluation time; BV (3 families, 144 cells) 0.48-3.43x, of which the 14 cells that double N 2.97-3.18x
  and the other 130 cells 0.48-3.43x. The certified setting is cheaper than the default (ratio below
  1.00 as printed in the tables and `data/frontier.tsv`) in 28 HYBRID and 18 BV cells, every one of
  them below 0.95; another 1 HYBRID and 10 BV cells measure 0.995-0.9999 unrounded, which is 1.00 at
  the precision shown and within timing noise, so they are not counted. Per family (certified, worst
  case; kappa = 128 in the last column):

| BFV family | cells timed | ratio min to max | cells with ratio < 1.00 | cells with N doubled | kappa = 128: ratio min to max |
|---|---|---|---|---|---|
| BEHZ BV | 48 | 0.48 to 3.11 | 6 | 5 | 0.48 to 3.01 |
| BEHZ HYBRID | 48 | 0.39 to 1.51 | 10 | 0 | 0.39 to 1.51 |
| HPSPOVERQ BV | 48 | 0.48 to 3.09 | 6 | 5 | 0.48 to 3.01 |
| HPSPOVERQ HYBRID | 48 | 0.41 to 1.54 | 10 | 0 | 0.41 to 1.54 |
| HPSPOVERQLEVELED BV | 48 | 0.48 to 3.43 | 6 | 4 | 0.48 to 3.20 |
| HPSPOVERQLEVELED HYBRID | 48 | 0.41 to 1.57 | 8 | 0 | 0.41 to 1.57 |

See `../README.md` for method; `data/summary.json`, `data/frontier.tsv`, `data/timing.jsonl` for every number.

## Tightness: where the bound is loose, and which looseness is inherent

MEASURED: exact output noise `‖phase − Δm‖∞` (secret key, big-integer arithmetic) of real OpenFHE
v1.6.1 traced runs at N = 2^12 and 2^14 (`HEStd_NotSet`; measurement only, not certified
settings), 3 repetitions each, against `fhe_check`'s worst-case bound on the same extracted file.
Raw numbers: `data/tightness.tsv` (bound, observed maximum, gap, per program and N).

| operation (what the gap is measured on) | gap bound − observed (bits) | inherent or slack |
|---|---|---|
| BGV fresh encryption | 8.3-9.3 | slack: worst-case support model of the samplers (the κ and ℓ2 modes recover part of it) |
| BGV modulus switch (`msonly`; the chain's output after every `ModReduce`) | 5.0-6.3 | slack: ‖s‖₁ = N·B_s and the worst-case rounding terms |
| BGV one product, no switch (`mulonly`) | 24.6-27.5 at the output (≈ 8-9 bits on top of the operands' gaps) | slack: ring expansion N charged on ℓ∞ × ℓ∞ products |
| BGV rotation key switch (`rot`) | 8.7-9.9 (< 1 bit above the input's) | key switching itself is tight to < 1 bit |
| BFV fresh | 4-9 (fresh ≤ 15.7 observed vs bound) | slack (as BGV) |
| BFV first product (BV relinearisation dominated) | 10.8-12.0 | slack: N·B_s lift and ℓ∞ expansion |
| BFV each further product, BEHZ / HPSPOVERQ | +13-15 per product (24.0-27.1 at d2, 36.7-41.6 at d3) | slack, compounding: the per-product expansion (t·N·‖s‖₁ lift) |
| BFV HPSPOVERQLEVELED, same parameters | 10.8-11.7 at d2, 23.8-26.9 at d3 | the gap RESETS at each internal limb drop |
| BFV message magnitude (all coefficients at the extreme `advchain` vs typical messages) | identical within 0.3 | the message term is not binding |

Inherent, MEASURED: the leveled technique's internal limb drop. On the same parameters
(N = 2^14, d3 chain) the observed output noise is 2^156.97 under HPSPOVERQLEVELED and 2^126.81 under
BEHZ: the drop really adds ≈ 30 bits of noise (the bound adds 15.6). This is the library's choice
to trade noise for speed; a certificate must pay for it, and it is why LEVELED needs one more limb
than HPSPOVERQ/BEHZ at the same depth in several cells.

MODELLED (the per-prime figures are computed with a re-implementation of the bound formulas
that is not part of this release; recommend's choice is quoted for comparison): per-prime bits needed by the BGV chain at
d12, N = 2^15: 52.3 with the current worst-case bound (recommend chose 53); an ℓ1 key bound would
lower it to 48.3, an ℓ2 fresh lemma to 46.8; all κ refinements together to 44.5; OpenFHE's own
heuristic uses 38.3. So the BGV FIXEDMANUAL scaling primes move from OpenFHE's 45 bits to 49-53
for the worst case, and the refinements would bring them to ≈ 44-48.

## Two bound improvements, assessed (not implemented: they touch trusted definitions)

### (a) An ℓ1 bound on the secret key in the BFV multiplication lift and rounding

**Where N·B_s enters today** (all TRUSTED, hash-locked):
- `Spec/BudgetBFV.lean:50` `msBudget P = (1 + N·secretBound + 1)/2`; `:54` `mulLift P = (2 + N·secretBound)/2`;
  `:58-59` `mulRound P = 1 + N·B_s + (N·B_s)²`; `:65` `certified` (the budget the BFV decision uses).
- `Spec/BudgetBFVRns.lean:37-38` `mulLiftApprox P U = mulLift P + U·(1 + N·B_s)`; `:78-79` `mulLiftNormAt`
  (`(Q_ℓ + e)·(1 + N·B_s)`); the RNS budgets built on them (`:134-190`).
- `Spec/Budget.lean:221` the key-switching bound's `k·P·(1 + N·B_s)` term (shared with BFV through
  `Spec.BudgetBFV.ksBoundAt`, `Spec/BudgetBFV.lean:41-43`); `:229` BGV `msBudget`.
- `Spec/Params.lean:29` `secretBound` is an ℓ∞ bound (`1` for ternary).
- The analysis is parametric in the budget: `Challenge/BFV/Defs.lean:108` `mulBound N t Q K R B₁ B₂`
  with `K = E.mulLift`, `R = E.mulRound`; its leading term is `N·(B₁+B₂)·t·(K+1)`.
- Locked statements that pin today's numbers: `Challenge/BFV.lean:284` `stepOK_mul_textbook`, `:296`
  `stepOK_modSwitch_textbook`, `:310` `relin_realizable`; `Challenge/CertifyBFV.lean:99-234`
  (`certifyBFV?_spec`, `_budget`, `_sound`, `_decrypts`, `_textbook_mul`, `_textbook_square`), with the
  budget composed at `Challenge/CertifyBFV/Defs.lean:316`.

**Why the ℓ∞ form is loose.** The lift `k_a = (Ψ_a − Φ_a)/Q` of `Ψ_a = c₀ + c₁·s` (centred
`|c_i| ≤ Q/2`) is bounded by `(1 + ‖s‖₁)/2`, and `‖s‖₁ ≤ N·‖s‖∞` is what is charged. The ring
expansion `N` in `N·(B₁+B₂)` (ℓ∞ × ℓ∞ products of k and the noise) is separate and inherent to an
ℓ∞ analysis; only the `‖s‖₁` factor is at stake.

**Worst case gains nothing.** A uniform ternary secret can have `‖s‖₁ = N` (all ±1), so for the
worst-case certificate the ℓ1 bound is equal to today's. A gain needs one of:
1. a probabilistic hypothesis on key generation (the κ mode): `|s_i|` are i.i.d. Bernoulli(2/3), so by
   Hoeffding `Pr[‖s‖₁ ≥ 2N/3 + λ] ≤ exp(−2λ²/N)`; at failure probability 2^−κ,
   `S1 = 2N/3 + √(κ·ln2·N/2)`. COMPUTED: κ = 128 gives `log₂(N/S1)` = 0.434 (N = 2^13), 0.477 (2^14),
   0.507 (2^15), 0.530 (2^16); κ = 64: 0.48-0.55. The earlier study's 0.58 b was the MEAN (`log₂ 3/2`);
   the honest κ = 128 figure is 0.48-0.51 bit per product.
2. a recorded fact about the one key (`‖s‖₁` computed at key generation and declared, like
   `freshEncryption.l2.secretSq` today): worst case over everything else for that key. It
   reveals the key's Hamming weight (about log₂N bits of information about s) in the certificate
   file; that is a policy decision.

**Can it be additive?** Yes. Because the analyzer and the decision are parametric in the budget,
nothing existing has to change:
- new trusted definitions (a new `Spec` file, e.g. named `BudgetBFVL1`): `mulLiftL1 S1 = (2 + S1)/2`,
  `mulRoundL1 S1 = 1 + S1 + S1²`, `msBudgetL1 S1 = (S1 + 2)/2`, and `certifiedL1 P lay S1` (the BV/hybrid
  key-switching term `k·P·(1 + S1)`), plus the RNS variants (`mulLiftApproxL1`, `mulLiftNormAtL1`);
- new locked statements (a new `Challenge` file, e.g. named `BFVL1`): `stepOK_mul_textbook_l1`,
  `stepOK_square_textbook_l1`, `stepOK_modSwitch_textbook_l1`, `relin_realizable_l1`, each with the
  extra hypothesis `normL1 s ≤ S1`; a decision `certifyBFVL1? x S1` and `certifyBFVL1?_sound` /
  `_decrypts` whose hypothesis adds `normL1 s ≤ S1`; and, for route 1, a probability statement
  `Pr_{s ← ternary^N}[normL1 s > S1(κ)] ≤ 2^−κ` combined by a union bound with the existing κ
  fresh-noise statement (the certificate then fails with probability at most 2·2^−κ).
- proof obligations: (i) `|(c₀ + c₁·s)_j| ≤ (Q/2)(1 + ‖s‖₁)` in `ℤ[X]/(X^N+1)` (negacyclic convolution
  is ℓ∞×ℓ1-bounded: `‖a·b‖∞ ≤ ‖a‖∞·‖b‖₁`); (ii) the same for the three-term rounding error with
  `‖s²‖₁ ≤ ‖s‖₁²` (ℓ1 is submultiplicative in the negacyclic ring); (iii) the RNS slack lemmas of
  `Spec/BudgetBFVRns.lean` re-proved with `S1` in place of `N·B_s` (mechanical: the proofs only use
  the bound on the lift); (iv) Hoeffding for a sum of N bounded i.i.d. variables (Mathlib has
  sub-Gaussian/Hoeffding machinery; `Challenge/FreshNoiseL2.lean` already uses sub-Gaussian
  samplers), and the assumption that OpenFHE's ternary sampler is uniform i.i.d. (an assumption
  about the library, like the existing sampler bounds).

**Does it still matter after the fine-grained search?** MODELLED, not measured and not certified
(`analysis.py`, `data/summary.json`, fields `l1flips` and `l1possible`). For every BFV cell, a class
cheaper (by the time proxy) than the cheapest certified one would certify with an ℓ1 key bound if
its deficit (the reported overflow of the largest-Q member) were at most the ℓ1 credit
g(N)·d bits (g = log2 of the lift ratio at κ = 128 from the Hoeffding bound above, d the number of
products on the critical path). "Flips": the deficit is known exactly (the first failing
instruction is at or after the last product), so the cheaper class would be certified; "possible":
only an earlier failure is within the credit, so the cell might flip. Of the 288 BFV cells
(6 families × 48), 39 flip and 126 are possible (the possible count includes the flips):

| family | cells | flip | possible |
|---|---|---|---|
| BEHZ BV | 48 | 6 | 16 |
| BEHZ HYBRID | 48 | 9 | 26 |
| HPSPOVERQ BV | 48 | 6 | 20 |
| HPSPOVERQ HYBRID | 48 | 9 | 26 |
| HPSPOVERQLEVELED BV | 48 | 5 | 16 |
| HPSPOVERQLEVELED HYBRID | 48 | 4 | 22 |

So it still matters in 39 of 288 cells for certain and in at most 126 of 288; in the other 162 no
cheaper class that failed by an overflow is within the credit. These counts do not depend on the timings.

### (b) An ℓ2 fresh-noise lemma

**What exists.** `--kappa K --l2` (`Challenge/FreshNoiseL2.lean`, `Spec/Encrypt.lean:116`
`varProxyL2 E2 S2 Vu V1 V2 = Vu·E2 + V1 + V2·S2`, `:134` `epsFor`; `Challenge/Certify.lean:456`
`fresh_l2_certified`; `Challenge/FreshNoiseL2.lean:78` `varProxyL2_support`, `:95` `SubGaussSamplerOK`,
`:107` `subGaussSamplerOK_of_samplerOK`). Without supplied values it reproduces the support model
exactly (Hoeffding's lemma: proxy = squared support bound). With SUPPLIED values (ASSUMPTIONS:
‖e_pk‖₂² ≤ 11N, proxy 11 for the σ = 3.19 Gaussians, 1 for the ternary ephemeral) BGV FIXEDMANUAL
defaults certify at depth 1-5 (κ = 128; frontend README).

**The lemma that is missing** (additive, new statements only): (i) the truncated discrete Gaussian of
parameter σ (OpenFHE's sampler, truncated at 6σ… as declared) is sub-Gaussian with variance proxy
≤ 11 (σ² ≈ 10.18); (ii) uniform ternary has proxy ≤ 2/3 → use 1; (iii) `‖e_pk‖₂² ≤ 11·N` except with
probability 2^−κ (a tail bound on a sum of N bounded squares, Hoeffding/Bernstein), to be combined
by a union bound. With these, the extractor could emit the `l2` fields with a proof instead of an
assumption; `fresh_l2_certified`'s statement is unchanged (it already takes the proxies as
hypotheses through `SubGaussSamplerOK`).

**Does it matter after the search?** Fresh noise only enters at the start of a circuit. FILLED
FROM THE SWEEP: compare the cheapest worst-case and κ = 128 classes.

## Full tables

### BGV FIXEDMANUAL, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | certified, digits kept (e2e) | dbits | ratio | certified, least predicted time (e2e) | ratio | certified k128 (e2e) | ratio |
|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x45, P 1x60 | CERT 5.4 / CERT 11.7 | N=2^13, 36+1x49, dnum 2, P 1x60 | -5 | 1.01 | N=2^13, 36+1x49, dnum 1, P 2x60 | 0.95 | N=2^13, 46+1x34, dnum 1, P 2x60 | 0.94 |
| 2 | N=2^14, 3x45, P 2x60 | over 8.2 / CERT 6.5 | N=2^14, 36+2x51, dnum 2, P 2x60 | +3 | 1.01 | N=2^13, 33+2x50, dnum 3, P 1x60 | 0.51 | N=2^13, 34+2x45, dnum 3, P 1x60 | 0.52 |
| 3 | N=2^14, 4x45, P 2x60 | over 29.3 / over 0.1 | N=2^14, 34+3x51, dnum 2, P 2x60 | +7 | 1.01 | N=2^14, 34+3x51, dnum 2, P 2x60 | 1.01 | N=2^14, 34+3x47, dnum 1, P 3x60 | 0.95 |
| 4 | N=2^14, 5x45, P 2x60 | over 71.6 / over 13.2 | N=2^14, 34+4x51, dnum 3, P 2x60 | +13 | 1.00 | N=2^14, 34+4x51, dnum 3, P 2x60 | 1.01 | N=2^14, 34+4x47, dnum 3, P 2x60 | 1.00 |
| 5 | N=2^14, 6x45, P 2x60 | over 26.6 / over 39.3 | N=2^14, 34+5x51, dnum 3, P 2x60 | +19 | 1.01 | N=2^14, 34+5x51, dnum 3, P 2x60 | 1.01 | N=2^14, 34+5x47, dnum 3, P 2x60 | 1.01 |
| 6 | N=2^15, 7x45, P 3x60 | over 12.7 / over 41.3 | N=2^15, 37+6x53, dnum 3, P 3x60 | +40 | 1.00 | N=2^14, 34+6x51, dnum 7, P 1x60 | 0.62 | N=2^14, 34+6x47, dnum 4, P 2x60 | 0.50 |
| 7 | N=2^15, 8x45, P 3x60 | over 129.6 / over 142.0 | N=2^15, 37+7x53, dnum 3, P 3x60 | +48 | 1.01 | N=2^15, 37+7x53, dnum 1, P 7x60 | 1.04 | N=2^14, 34+7x47, dnum 8, P 1x60 | 0.65 |
| 8 | N=2^15, 9x45, P 3x60 | over 84.8 / over 97.3 | N=2^15, 37+8x53, dnum 3, P 3x60 | +56 | 1.01 | N=2^15, 37+8x53, dnum 3, P 3x60 | 1.01 | N=2^15, 37+8x49, dnum 2, P 4x60 | 0.94 |
| 9 | N=2^15, 10x45, P 4x60 | over 39.9 / over 52.6 | N=2^15, 37+9x53, dnum 3, P 4x60 | +64 | 1.00 | N=2^15, 37+9x53, dnum 3, P 4x60 | 1.00 | N=2^15, 37+9x49, dnum 3, P 4x60 | 1.00 |
| 10 | N=2^15, 11x45, P 4x60 | over 274.1 / over 7.8 | N=2^15, 37+10x53, dnum 3, P 4x60 | +72 | 1.00 | N=2^15, 37+10x53, dnum 3, P 4x60 | 1.02 | N=2^15, 37+10x49, dnum 3, P 4x60 | 1.01 |
| 11 | N=2^15, 12x45, P 4x60 | over 229.2 / over 209.8 | N=2^15, 37+11x53, dnum 3, P 4x60 | +80 | 1.01 | N=2^15, 37+11x53, dnum 3, P 4x60 | 1.00 | N=2^15, 37+11x49, dnum 2, P 5x60 | 0.94 |
| 12 | N=2^15, 13x45, P 4x60 | over 184.3 / over 165.1 | none | - | n/m | N=2^15, 37+12x53, dnum 5, P 3x60 | 1.13 | N=2^15, 37+12x49, dnum 4, P 4x60 | 1.08 |

### BGV FIXEDMANUAL, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | certified, digits kept (e2e) | dbits | ratio | certified, least predicted time (e2e) | ratio | certified k128 (e2e) | ratio |
|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x48, P 1x60 | CERT 4.2 / CERT 10.6 | N=2^13, 50+1x42, dnum 2, P 1x60 | -4 | 1.00 | N=2^13, 50+1x42, dnum 1, P 2x60 | 0.94 | N=2^13, 45+1x41, dnum 1, P 2x60 | 0.94 |
| 2 | N=2^14, 3x48, P 2x60 | over 10.5 / CERT 4.1 | N=2^14, 37+2x56, dnum 2, P 2x60 | +4 | 1.01 | N=2^13, 40+2x52, dnum 3, P 1x60 | 0.52 | N=2^13, 39+2x48, dnum 3, P 1x60 | 0.52 |
| 3 | N=2^14, 4x48, P 2x60 | over 34.1 / over 4.8 | N=2^14, 37+3x55, dnum 2, P 2x60 | +9 | 1.01 | N=2^14, 37+3x55, dnum 2, P 2x60 | 1.01 | N=2^14, 37+3x51, dnum 2, P 2x60 | 1.01 |
| 4 | N=2^14, 5x48, P 2x60 | over 81.2 / over 22.6 | N=2^14, 40+4x54, dnum 3, P 2x60 | +16 | 1.01 | N=2^14, 40+4x54, dnum 3, P 2x60 | 1.01 | N=2^14, 37+4x51, dnum 3, P 2x60 | 1.01 |
| 5 | N=2^14, 6x48, P 2x60 | over 33.2 / over 58.2 | N=2^14, 39+5x54, dnum 3, P 2x60 | +21 | 1.00 | N=2^14, 39+5x54, dnum 3, P 2x60 | 1.01 | N=2^14, 37+5x51, dnum 3, P 2x60 | 1.00 |
| 6 | N=2^15, 7x48, P 3x60 | over 16.4 / over 57.6 | N=2^15, 39+6x56, dnum 3, P 3x60 | +39 | 1.01 | N=2^14, 37+6x54, dnum 7, P 1x60 | 0.62 | N=2^14, 37+6x51, dnum 7, P 1x60 | 0.62 |
| 7 | N=2^15, 8x48, P 3x60 | over 143.0 / over 9.8 | N=2^15, 39+7x56, dnum 3, P 3x60 | +47 | 1.00 | N=2^15, 39+7x56, dnum 3, P 3x60 | 1.01 | N=2^15, 39+7x52, dnum 1, P 7x60 | 1.03 |
| 8 | N=2^15, 9x48, P 3x60 | over 95.1 / over 129.7 | N=2^15, 39+8x56, dnum 3, P 3x60 | +55 | 1.00 | N=2^15, 39+8x56, dnum 3, P 3x60 | 1.01 | N=2^15, 39+8x52, dnum 3, P 3x60 | 1.01 |
| 9 | N=2^15, 10x48, P 4x60 | over 47.3 / over 82.1 | N=2^15, 39+9x56, dnum 3, P 4x60 | +63 | 1.00 | N=2^15, 39+9x56, dnum 3, P 4x60 | 1.00 | N=2^15, 39+9x52, dnum 3, P 4x60 | 1.00 |
| 10 | N=2^15, 11x48, P 4x60 | over 300.8 / over 34.4 | N=2^15, 39+10x56, dnum 3, P 4x60 | +71 | 1.00 | N=2^15, 39+10x56, dnum 3, P 4x60 | 1.00 | N=2^15, 39+10x52, dnum 3, P 4x60 | 1.00 |
| 11 | N=2^15, 12x48, P 4x60 | over 253.1 / over 275.1 | N=2^16, 39+11x58, dnum 3, P 4x60 | +101 | 2.10 | N=2^15, 39+11x56, dnum 4, P 3x60 | 1.04 | N=2^15, 39+11x52, dnum 3, P 4x60 | 1.01 |
| 12 | N=2^16, 13x48, P 5x60 | over 334.4 / over 36.1 | N=2^16, 39+12x58, dnum 3, P 5x60 | +112 | 1.01 | N=2^15, 39+12x56, dnum 7, P 2x60 | 0.57 | N=2^15, 39+12x52, dnum 5, P 3x60 | 0.51 |

### BGV FIXEDMANUAL, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | certified, digits kept (e2e) | dbits | ratio | certified, least predicted time (e2e) | ratio | certified k128 (e2e) | ratio |
|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x45, P 1x60 | CERT 2.4 / CERT 8.6 | N=2^13, 54+1x35, dnum 2, P 1x60 | -2 | 1.01 | N=2^13, 54+1x35, dnum 2, P 1x60 | 1.00 | N=2^13, 49+1x34, dnum 2, P 1x60 | 1.00 |
| 2 | N=2^14, 3x45, P 2x60 | over 14.2 / CERT 0.2 | N=2^14, 34+2x54, dnum 2, P 2x60 | +7 | 1.00 | N=2^13, 33+2x52, dnum 3, P 1x60 | 0.52 | N=2^13, 36+2x47, dnum 3, P 1x60 | 0.52 |
| 3 | N=2^14, 4x45, P 2x60 | over 27.7 / over 6.2 | N=2^14, 34+3x53, dnum 2, P 2x60 | +13 | 1.00 | N=2^14, 36+3x53, dnum 1, P 4x60 | 1.02 | N=2^14, 41+3x48, dnum 1, P 4x60 | 1.03 |
| 4 | N=2^14, 5x45, P 2x60 | over 41.3 / over 12.6 | N=2^14, 34+4x53, dnum 3, P 2x60 | +21 | 1.01 | N=2^14, 34+4x53, dnum 3, P 2x60 | 1.00 | N=2^14, 36+4x49, dnum 3, P 2x60 | 1.02 |
| 5 | N=2^14, 6x45, P 2x60 | over 54.9 / over 19.0 | N=2^14, 38+5x52, dnum 3, P 2x60 | +28 | 1.00 | N=2^14, 38+5x52, dnum 3, P 2x60 | 1.00 | N=2^14, 36+5x49, dnum 3, P 2x60 | 1.00 |
| 6 | N=2^15, 7x45, P 3x60 | over 28.9 / over 42.2 | N=2^15, 39+6x54, dnum 3, P 3x60 | +48 | 1.00 | N=2^14, 38+6x52, dnum 7, P 1x60 | 0.66 | N=2^14, 34+6x49, dnum 7, P 1x60 | 0.66 |
| 7 | N=2^15, 8x45, P 3x60 | over 46.6 / over 51.6 | N=2^15, 39+7x54, dnum 3, P 3x60 | +57 | 1.02 | N=2^15, 39+7x54, dnum 2, P 4x60 | 0.95 | N=2^14, 34+7x49, dnum 8, P 1x60 | 0.66 |
| 8 | N=2^15, 9x45, P 3x60 | over 1.6 / over 6.7 | N=2^15, 39+8x54, dnum 3, P 3x60 | +66 | 1.00 | N=2^15, 39+8x54, dnum 3, P 3x60 | 0.99 | N=2^15, 37+8x51, dnum 3, P 3x60 | 0.99 |
| 9 | N=2^15, 10x45, P 4x60 | over 19.3 / over 16.3 | N=2^15, 39+9x54, dnum 3, P 4x60 | +75 | 1.01 | N=2^15, 39+9x54, dnum 3, P 4x60 | 1.00 | N=2^15, 40+9x51, dnum 3, P 4x60 | 1.01 |
| 10 | N=2^15, 11x45, P 4x60 | over 36.9 / over 25.8 | N=2^15, 39+10x54, dnum 3, P 4x60 | +84 | 1.00 | N=2^15, 39+10x54, dnum 3, P 4x60 | 1.00 | N=2^15, 40+10x51, dnum 3, P 4x60 | 1.00 |
| 11 | N=2^15, 12x45, P 4x60 | over 54.6 / over 35.2 | N=2^15, 39+11x54, dnum 3, P 4x60 | +93 | 1.00 | N=2^15, 39+11x54, dnum 3, P 4x60 | 1.00 | N=2^15, 40+11x51, dnum 3, P 4x60 | 0.99 |
| 12 | N=2^15, 13x45, P 4x60 | over 9.6 / over 44.7 | none | - | n/m | N=2^15, 39+12x54, dnum 5, P 3x60 | 1.12 | N=2^15, 37+12x51, dnum 5, P 3x60 | 1.13 |

### BGV FIXEDMANUAL, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | certified, digits kept (e2e) | dbits | ratio | certified, least predicted time (e2e) | ratio | certified k128 (e2e) | ratio |
|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x48, P 1x60 | CERT 1.2 / CERT 7.5 | N=2^13, 53+1x42, dnum 2, P 1x60 | -1 | 1.00 | N=2^13, 53+1x42, dnum 2, P 1x60 | 1.00 | N=2^13, 48+1x41, dnum 2, P 1x60 | 1.00 |
| 2 | N=2^14, 3x48, P 2x60 | over 16.5 / over 2.0 | N=2^14, 37+2x58, dnum 2, P 2x60 | +8 | 1.00 | N=2^13, 41+2x54, dnum 3, P 1x60 | 0.52 | N=2^13, 40+2x50, dnum 3, P 1x60 | 0.52 |
| 3 | N=2^14, 4x48, P 2x60 | over 31.3 / over 9.6 | N=2^14, 37+3x57, dnum 2, P 2x60 | +15 | 1.01 | N=2^14, 37+3x57, dnum 2, P 2x60 | 1.00 | N=2^14, 41+3x52, dnum 2, P 2x60 | 1.01 |
| 4 | N=2^14, 5x48, P 2x60 | over 46.1 / over 17.1 | N=2^14, 39+4x56, dnum 3, P 2x60 | +23 | 1.01 | N=2^14, 39+4x56, dnum 3, P 2x60 | 1.00 | N=2^14, 42+4x52, dnum 3, P 2x60 | 1.00 |
| 5 | N=2^14, 6x48, P 2x60 | over 60.9 / over 24.7 | N=2^15, 42+5x58, dnum 3, P 2x60 | +44 | 2.13 | N=2^14, 41+5x56, dnum 6, P 1x60 | 1.23 | N=2^14, 43+5x52, dnum 3, P 2x60 | 1.01 |
| 6 | N=2^15, 7x48, P 3x60 | over 32.0 / over 49.2 | N=2^15, 39+6x58, dnum 3, P 3x60 | +51 | 1.00 | N=2^14, 41+6x56, dnum 7, P 1x60 | 0.66 | N=2^14, 43+6x52, dnum 7, P 1x60 | 0.67 |
| 7 | N=2^15, 8x48, P 3x60 | over 50.8 / over 1.2 | N=2^15, 39+7x58, dnum 3, P 3x60 | +61 | 0.99 | N=2^15, 39+7x58, dnum 2, P 4x60 | 0.95 | N=2^15, 40+7x55, dnum 2, P 4x60 | 0.94 |
| 8 | N=2^15, 9x48, P 3x60 | over 2.9 / over 11.8 | N=2^15, 39+8x58, dnum 3, P 3x60 | +71 | 1.00 | N=2^15, 39+8x58, dnum 3, P 3x60 | 1.00 | N=2^15, 45+8x54, dnum 3, P 3x60 | 1.00 |
| 9 | N=2^15, 10x48, P 4x60 | over 21.8 / over 22.6 | N=2^15, 39+9x58, dnum 3, P 4x60 | +81 | 1.01 | N=2^15, 39+9x58, dnum 3, P 4x60 | 1.01 | N=2^15, 48+9x54, dnum 3, P 4x60 | 1.00 |
| 10 | N=2^15, 11x48, P 4x60 | over 40.6 / over 33.2 | N=2^15, 39+10x58, dnum 3, P 4x60 | +91 | 1.02 | N=2^15, 39+10x58, dnum 3, P 4x60 | 1.01 | N=2^15, 39+10x55, dnum 3, P 4x60 | 1.00 |
| 11 | N=2^15, 12x48, P 4x60 | over 59.5 / over 43.9 | N=2^16, 39+11x60, dnum 3, P 5x60 | +123 | 2.23 | N=2^15, 39+11x58, dnum 4, P 3x60 | 1.06 | N=2^15, 47+11x54, dnum 4, P 3x60 | 1.06 |
| 12 | N=2^16, 13x48, P 5x60 | over 47.1 / over 25.2 | N=2^16, 39+12x60, dnum 3, P 6x60 | +136 | 1.08 | N=2^15, 44+12x58, dnum 7, P 2x60 | 0.58 | N=2^15, 48+12x54, dnum 5, P 3x60 | 0.51 |

### BGV FLEXIBLEAUTOEXT, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 30+2x36, P 2x60 | over 4.0 / over 4.0 | N=2^13, 30+2x47, P 2x60 | depth 1, EvalAddCount 10000 | 7.0 | +13 | +0 | 1.00 | 88 (depth 1, EvalAddCount 200) | N=2^13, 30+2x47, P 2x60 | 1.01 |
| 2 | N=2^14, 31+3x37, P 2x60 | over 17.1 / over 17.0 | N=2^14, 31+3x54, P 2x60 | depth 2, EvalAddCount 1000000 | 11.8 | +43 | +0 | 1.00 | 136 (depth 2, EvalAddCount 1000) | N=2^14, 31+3x54, P 2x60 | 1.01 |
| 3 | N=2^14, 31+4x37, P 2x60 | over 41.1 / over 41.1 | N=2^14, 31+4x54, P 3x60 | depth 3, EvalAddCount 1000000 | 11.8 | +60 | +0 | 1.12 | 183 (depth 3, EvalAddCount 2000) | N=2^14, 31+4x54, P 3x60 | 1.12 |
| 4 | N=2^14, 31+5x37, P 2x60 | over 4.1 / over 4.1 | N=2^14, 31+5x54, P 2x60 | depth 4, EvalAddCount 1000000 | 11.8 | +77 | +0 | 1.00 | 228 (depth 4, EvalAddCount 2000) | N=2^14, 31+5x54, P 2x60 | 1.00 |
| 5 | N=2^14, 31+6x37, P 2x60 | over 52.2 / over 52.2 | N=2^15, 31+6x55, P 3x60 | depth 5, EvalAddCount 1000000 | 9.9 | +99 | +0 | 2.32 | 291 (depth 5, EvalAddCount 5000) | N=2^15, 31+6x55, P 3x60 | 2.33 |
| 6 | N=2^14, 31+7x37, P 2x60 | over 15.2 / over 15.2 | N=2^15, 31+7x55, P 3x60 | depth 6, EvalAddCount 1000000 | 9.9 | +117 | +0 | 2.29 | 339 (depth 6, EvalAddCount 5000) | N=2^15, 31+7x55, P 3x60 | 2.28 |
| 7 | N=2^14, 31+8x37, P 2x60 | over 111.4 / over 111.4 | N=2^15, 31+8x55, P 3x60 | depth 7, EvalAddCount 1000000 | 9.9 | +135 | +0 | 2.30 | 387 (depth 7, EvalAddCount 5000) | N=2^15, 31+8x55, P 3x60 | 2.29 |
| 8 | N=2^15, 31+9x38, P 3x60 | over 103.2 / over 103.2 | N=2^15, 31+9x55, P 4x60 | depth 8, EvalAddCount 1000000 | 9.9 | +142 | +0 | 1.10 | 435 (depth 8, EvalAddCount 5000) | N=2^15, 31+9x55, P 4x60 | 1.09 |
| 9 | N=2^15, 31+10x38, P 3x60 | over 65.2 / over 65.2 | N=2^15, 31+10x55, P 4x60 | depth 9, EvalAddCount 1000000 | 9.9 | +159 | +0 | 1.08 | 483 (depth 9, EvalAddCount 5000) | N=2^15, 31+10x55, P 4x60 | 1.07 |
| 10 | N=2^15, 31+11x38, P 3x60 | over 27.2 / over 27.2 | N=2^15, 31+11x55, P 4x60 | depth 10, EvalAddCount 1000000 | 9.9 | +176 | +0 | 1.07 | 531 (depth 10, EvalAddCount 5000) | N=2^15, 31+11x55, P 4x60 | 1.07 |
| 11 | N=2^15, 31+12x38, P 4x60 | over 251.4 / over 251.4 | N=2^15, 31+12x48, P 5x60 | depth 11, EvalAddCount 5000 | 2.5 | +110 | +0 | 1.05 | 579 (depth 11, EvalAddCount 5000) | N=2^15, 31+12x48, P 5x60 | 1.06 |
| 12 | N=2^15, 31+13x38, P 4x60 | over 213.4 / over 213.4 | none found | - |  |  |  | - | - | none found | - |

### BGV FLEXIBLEAUTOEXT, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 34+2x40, P 2x60 | over 3.2 / over 3.2 | N=2^13, 34+2x47, P 2x60 | depth 1, EvalAddCount 1000 | 3.8 | +7 | +0 | 1.00 | 94 (depth 1, EvalAddCount 100) | N=2^13, 34+2x47, P 2x60 | 1.00 |
| 2 | N=2^14, 34+3x41, P 2x60 | over 16.4 / over 16.4 | N=2^14, 34+3x58, P 2x60 | depth 2, EvalAddCount 1000000 | 11.6 | +44 | +0 | 0.99 | 146 (depth 2, EvalAddCount 1000) | N=2^14, 34+3x58, P 2x60 | 1.00 |
| 3 | - | - / - | N=2^14, 34+4x58, P 3x60 | depth 3, EvalAddCount 1000000 | 11.6 |  |  | n/m | 194 (depth 3, EvalAddCount 1000) | N=2^14, 34+4x58, P 3x60 | n/m |
| 4 | N=2^14, 34+5x41, P 2x60 | over 83.7 / over 83.6 | N=2^14, 34+5x56, P 2x60 | depth 4, EvalAddCount 300000 | 9.8 | +68 | +0 | 1.00 | 247 (depth 4, EvalAddCount 2000) | N=2^14, 34+5x56, P 2x60 | 1.00 |
| 5 | N=2^14, 34+6x41, P 3x60 | over 42.6 / over 42.6 | N=2^15, 35+6x57, P 3x60 | depth 5, EvalAddCount 300000 | 8.8 | +89 | +0 | 2.09 | 310 (depth 5, EvalAddCount 5000) | N=2^15, 35+6x57, P 3x60 | 2.12 |
| 6 | N=2^15, 35+7x42, P 3x60 | over 14.5 / over 14.5 | N=2^15, 35+7x57, P 3x60 | depth 6, EvalAddCount 300000 | 8.8 | +98 | +0 | 1.00 | 361 (depth 6, EvalAddCount 5000) | N=2^15, 35+7x57, P 3x60 | 1.00 |
| 7 | N=2^15, 35+8x42, P 3x60 | over 120.1 / over 120.0 | N=2^15, 35+8x57, P 3x60 | depth 7, EvalAddCount 300000 | 8.8 | +113 | +0 | 1.00 | 412 (depth 7, EvalAddCount 5000) | N=2^15, 35+8x57, P 3x60 | 1.00 |
| 8 | N=2^15, 35+9x42, P 3x60 | over 78.1 / over 78.0 | N=2^15, 35+9x57, P 4x60 | depth 8, EvalAddCount 300000 | 8.8 | +128 | +0 | 1.09 | 463 (depth 8, EvalAddCount 5000) | N=2^15, 35+9x57, P 4x60 | 1.09 |
| 9 | N=2^15, 35+10x42, P 3x60 | over 36.1 / over 36.0 | N=2^15, 35+10x57, P 4x60 | depth 9, EvalAddCount 300000 | 8.8 | +143 | +0 | 1.07 | 514 (depth 9, EvalAddCount 5000) | N=2^15, 35+10x57, P 4x60 | 1.06 |
| 10 | N=2^15, 35+11x42, P 3x60 | over 247.1 / over 246.9 | N=2^15, 35+11x57, P 4x60 | depth 10, EvalAddCount 300000 | 8.8 | +158 | +0 | 1.08 | 565 (depth 10, EvalAddCount 5000) | N=2^15, 35+11x57, P 4x60 | 1.08 |
| 11 | N=2^15, 35+12x42, P 4x60 | over 205.1 / over 204.9 | N=2^16, 35+12x58, P 5x60 | depth 11, EvalAddCount 300000 | 6.8 | +184 | +0 | 2.20 | 638 (depth 11, EvalAddCount 10000) | N=2^16, 35+12x58, P 5x60 | 2.20 |
| 12 | N=2^15, 35+13x42, P 4x60 | over 163.1 / over 162.9 | N=2^16, 35+13x58, P 5x60 | depth 12, EvalAddCount 300000 | 6.8 | +200 | +0 | 2.21 | 691 (depth 12, EvalAddCount 10000) | N=2^16, 35+13x58, P 5x60 | 2.21 |

### BGV FLEXIBLEAUTOEXT, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 30+2x36, P 2x60 | over 4.0 / over 4.0 | N=2^13, 30+2x47, P 2x60 | depth 1, EvalAddCount 10000 | 4.0 | +13 | +0 | 1.00 | 91 (depth 1, EvalAddCount 2000) | N=2^13, 30+2x47, P 2x60 | 1.00 |
| 2 | N=2^14, 31+3x37, P 2x60 | over 23.0 / over 23.0 | N=2^14, 31+3x54, P 2x60 | depth 2, EvalAddCount 1000000 | 11.8 | +43 | +0 | 1.01 | 144 (depth 2, EvalAddCount 5000) | N=2^14, 31+3x54, P 2x60 | 1.00 |
| 3 | N=2^14, 31+4x37, P 2x60 | over 29.0 / over 29.0 | N=2^14, 31+4x54, P 3x60 | depth 3, EvalAddCount 1000000 | 11.8 | +60 | +0 | 1.11 | 183 (depth 3, EvalAddCount 2000) | N=2^14, 31+4x54, P 3x60 | 1.11 |
| 4 | N=2^14, 31+5x37, P 2x60 | over 35.0 / over 35.0 | N=2^14, 31+5x54, P 2x60 | depth 4, EvalAddCount 1000000 | 11.8 | +77 | +0 | 1.00 | 228 (depth 4, EvalAddCount 2000) | N=2^14, 31+5x54, P 2x60 | 1.00 |
| 5 | N=2^14, 31+6x37, P 2x60 | over 41.0 / over 41.0 | N=2^14, 31+7x38, P 2x60 | depth 6, EvalAddCount 10 | 3.0 | +43 | +1 | 1.31 | 276 (depth 6, EvalAddCount 10) | N=2^14, 31+7x38, P 2x60 | 1.30 |
| 6 | N=2^14, 31+7x37, P 2x60 | over 4.0 / over 4.0 | N=2^15, 31+7x55, P 3x60 | depth 6, EvalAddCount 1000000 | 9.9 | +117 | +0 | 2.26 | 339 (depth 6, EvalAddCount 5000) | N=2^15, 31+7x55, P 3x60 | 2.25 |
| 7 | N=2^14, 31+8x37, P 2x60 | over 10.0 / over 10.0 | N=2^15, 31+8x55, P 3x60 | depth 7, EvalAddCount 1000000 | 9.9 | +135 | +0 | 2.22 | 387 (depth 7, EvalAddCount 5000) | N=2^15, 31+8x55, P 3x60 | 2.22 |
| 8 | N=2^15, 31+9x38, P 3x60 | over 24.0 / over 24.0 | N=2^15, 31+9x55, P 4x60 | depth 8, EvalAddCount 1000000 | 9.9 | +142 | +0 | 1.06 | 435 (depth 8, EvalAddCount 5000) | N=2^15, 31+9x55, P 4x60 | 1.05 |
| 9 | N=2^15, 31+10x38, P 3x60 | over 31.0 / over 31.0 | N=2^15, 31+10x55, P 4x60 | depth 9, EvalAddCount 1000000 | 9.9 | +159 | +0 | 1.05 | 483 (depth 9, EvalAddCount 5000) | N=2^15, 31+10x55, P 4x60 | 1.06 |
| 10 | N=2^15, 31+11x38, P 3x60 | over 38.0 / over 38.0 | N=2^15, 31+11x55, P 4x60 | depth 10, EvalAddCount 1000000 | 9.9 | +176 | +0 | 1.06 | 531 (depth 10, EvalAddCount 5000) | N=2^15, 31+11x55, P 4x60 | 1.05 |
| 11 | N=2^15, 31+12x38, P 4x60 | over 0.0 / over 0.0 | N=2^15, 31+12x48, P 5x60 | depth 11, EvalAddCount 5000 | 2.8 | +110 | +0 | 1.04 | 579 (depth 11, EvalAddCount 5000) | N=2^15, 31+12x48, P 5x60 | 1.05 |
| 12 | N=2^15, 31+13x38, P 4x60 | over 7.0 / over 7.0 | N=2^15, 31+14x45, P 4x60 | depth 13, EvalAddCount 1000 | 15.0 | +129 | +1 | 1.11 | 610 (depth 13, EvalAddCount 200) | N=2^15, 31+14x45, P 4x60 | 1.11 |

### BGV FLEXIBLEAUTOEXT, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 34+2x40, P 2x60 | over 3.2 / over 3.2 | N=2^13, 34+2x47, P 2x60 | depth 1, EvalAddCount 1000 | 0.8 | +7 | +0 | 1.00 | 97 (depth 1, EvalAddCount 1000) | N=2^13, 34+2x47, P 2x60 | 1.00 |
| 2 | N=2^14, 34+3x41, P 2x60 | over 22.4 / over 22.4 | N=2^14, 34+3x58, P 2x60 | depth 2, EvalAddCount 1000000 | 11.6 | +44 | +0 | 0.99 | 149 (depth 2, EvalAddCount 2000) | N=2^14, 34+3x58, P 2x60 | 0.99 |
| 3 | - | - / - | N=2^14, 34+4x58, P 3x60 | depth 3, EvalAddCount 1000000 | 11.6 |  |  | n/m | 198 (depth 3, EvalAddCount 2000) | N=2^14, 34+4x58, P 3x60 | n/m |
| 4 | N=2^14, 34+5x41, P 2x60 | over 33.5 / over 33.5 | N=2^14, 34+5x56, P 2x60 | depth 4, EvalAddCount 300000 | 9.8 | +68 | +0 | 1.00 | 247 (depth 4, EvalAddCount 2000) | N=2^14, 34+5x56, P 2x60 | 1.00 |
| 5 | N=2^14, 34+6x41, P 3x60 | over 39.1 / over 39.1 | N=2^15, 35+6x57, P 3x60 | depth 5, EvalAddCount 300000 | 8.8 | +89 | +0 | 2.10 | 305 (depth 5, EvalAddCount 2000) | N=2^15, 35+6x57, P 3x60 | 2.10 |
| 6 | N=2^15, 35+7x42, P 3x60 | over 3.1 / over 3.1 | N=2^15, 35+7x57, P 3x60 | depth 6, EvalAddCount 300000 | 8.8 | +98 | +0 | 1.00 | 355 (depth 6, EvalAddCount 2000) | N=2^15, 35+7x57, P 3x60 | 1.00 |
| 7 | N=2^15, 35+8x42, P 3x60 | over 9.7 / over 9.7 | N=2^15, 35+8x57, P 3x60 | depth 7, EvalAddCount 300000 | 8.8 | +113 | +0 | 1.00 | 405 (depth 7, EvalAddCount 2000) | N=2^15, 35+8x57, P 3x60 | 1.01 |
| 8 | N=2^15, 35+9x42, P 3x60 | over 16.3 / over 16.3 | N=2^15, 35+9x57, P 4x60 | depth 8, EvalAddCount 300000 | 8.8 | +128 | +0 | 1.07 | 455 (depth 8, EvalAddCount 2000) | N=2^15, 35+9x57, P 4x60 | 1.06 |
| 9 | N=2^15, 35+10x42, P 3x60 | over 22.9 / over 22.9 | N=2^15, 35+10x57, P 4x60 | depth 9, EvalAddCount 300000 | 8.8 | +143 | +0 | 1.05 | 505 (depth 9, EvalAddCount 2000) | N=2^15, 35+10x57, P 4x60 | 1.05 |
| 10 | N=2^15, 35+11x42, P 3x60 | over 29.4 / over 29.4 | N=2^15, 35+11x57, P 4x60 | depth 10, EvalAddCount 300000 | 8.8 | +158 | +0 | 1.06 | 555 (depth 10, EvalAddCount 2000) | N=2^15, 35+11x57, P 4x60 | 1.05 |
| 11 | N=2^15, 35+12x42, P 4x60 | over 36.0 / over 36.0 | N=2^15, 35+13x47, P 4x60 | depth 12, EvalAddCount 200 | 15.4 | +102 | +1 | 1.11 | 603 (depth 12, EvalAddCount 100) | N=2^15, 35+13x47, P 4x60 | 1.12 |
| 12 | N=2^15, 35+13x42, P 4x60 | over 42.6 / over 42.6 | N=2^16, 35+13x58, P 5x60 | depth 12, EvalAddCount 300000 | 6.8 | +200 | +0 | 2.16 | 679 (depth 12, EvalAddCount 5000) | N=2^16, 35+13x58, P 5x60 | 2.16 |

### BFV BEHZ BV, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 24.7 / CERT 24.7 | N=2^12, 2x54 | depth 1, qbits 54 | 19.7 | -12 | +0 | 0.48 | 76 (depth 1, qbits 38) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 42.1 / CERT 42.1 | N=2^13, 3x60 | depth 2, qbits 60 | 42.1 | +0 | +0 | 1.00 | 123 (depth 2, qbits 41) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | CERT 0.1 / CERT 0.1 | N=2^13, 3x60 | depth 2, qbits 60 | 0.1 | +0 | +0 | 1.00 | 180 (depth 2, qbits 60) | N=2^13, 3x60 | 1.00 |
| 4 | N=2^14, 4x60 | CERT 10.7 / CERT 10.7 | N=2^13, 5x43 | depth 5, qbits 43 | 8.9 | -25 | +1 | 0.63 | 210 (depth 4, qbits 42) | N=2^13, 5x43 | 0.63 |
| 5 | N=2^14, 4x60 | over 33.3 / over 33.3 | N=2^14, 5x60 | depth 6, qbits 60 | 26.4 | +60 | +1 | 1.31 | 270 (depth 6, qbits 54) | N=2^14, 5x60 | 1.32 |
| 6 | N=2^14, 5x60 | over 17.6 / over 17.6 | N=2^14, 6x60 | depth 8, qbits 60 | 42.1 | +60 | +1 | 1.26 | 312 (depth 7, qbits 52) | N=2^14, 6x60 | 1.26 |
| 7 | N=2^14, 5x60 | over 17.6 / over 17.6 | N=2^14, 7x60 | depth 10, qbits 60 | 57.9 | +120 | +2 | 1.56 | 357 (depth 8, qbits 51) | N=2^14, 7x60 | 1.57 |
| 8 | N=2^14, 6x60 | over 1.9 / over 1.9 | N=2^14, 7x60 | depth 10, qbits 60 | 13.9 | +60 | +1 | 1.23 | 406 (depth 9, qbits 58) | N=2^14, 7x60 | 1.23 |
| 9 | N=2^14, 6x60 | over 1.9 / over 1.9 | N=2^15, 8x60 | depth 11, qbits 60 | 12.7 | +120 | +2 | 3.11 | 472 (depth 11, qbits 59) | N=2^14, 12x36 | 2.78 |
| 10 | N=2^14, 7x60 | over 30.1 / over 30.1 | N=2^15, 9x60 | depth 13, qbits 60 | 26.5 | +120 | +2 | 3.00 | 513 (depth 12, qbits 57) | N=2^15, 9x60 | 2.99 |
| 11 | N=2^15, 8x60 | over 33.3 / over 33.3 | N=2^15, 10x60 | depth 15, qbits 60 | 40.4 | +120 | +2 | 1.39 | 560 (depth 14, qbits 56) | N=2^15, 10x60 | 1.39 |
| 12 | N=2^15, 8x60 | over 33.3 / over 33.3 | N=2^15, 11x60 | depth 16, qbits 60 | 54.2 | +180 | +3 | 1.61 | 605 (depth 15, qbits 55) | N=2^15, 11x60 | 1.61 |

### BFV BEHZ BV, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 21.1 / CERT 21.1 | N=2^12, 2x54 | depth 1, qbits 54 | 16.1 | -12 | +0 | 0.48 | 86 (depth 1, qbits 43) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 35.0 / CERT 35.0 | N=2^13, 3x60 | depth 2, qbits 60 | 35.0 | +0 | +0 | 1.00 | 132 (depth 2, qbits 44) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 10.6 / over 10.6 | N=2^13, 4x54 | depth 4, qbits 54 | 30.9 | +36 | +1 | 1.38 | 180 (depth 3, qbits 45) | N=2^13, 4x54 | 1.38 |
| 4 | N=2^14, 4x60 | over 3.6 / over 3.6 | N=2^14, 5x60 | depth 5, qbits 60 | 56.0 | +60 | +1 | 1.32 | 235 (depth 4, qbits 47) | N=2^14, 5x60 | 1.32 |
| 5 | N=2^14, 5x60 | CERT 8.5 / CERT 8.5 | N=2^14, 5x60 | depth 5, qbits 60 | 8.5 | +0 | +0 | 1.00 | 290 (depth 5, qbits 58) | N=2^14, 5x60 | 1.00 |
| 6 | N=2^14, 5x60 | over 39.1 / over 39.1 | N=2^14, 6x60 | depth 7, qbits 60 | 20.6 | +60 | +1 | 1.26 | 336 (depth 7, qbits 56) | N=2^14, 6x60 | 1.26 |
| 7 | N=2^14, 6x60 | over 27.0 / over 27.0 | N=2^14, 7x60 | depth 9, qbits 60 | 32.8 | +60 | +1 | 1.23 | 385 (depth 8, qbits 55) | N=2^14, 7x60 | 1.23 |
| 8 | N=2^14, 6x60 | over 27.0 / over 27.0 | N=2^14, 8x54 | depth 9, qbits 54 | 3.0 | +72 | +2 | 1.48 | 432 (depth 9, qbits 54) | N=2^14, 8x54 | 1.48 |
| 9 | N=2^14, 7x60 | over 14.8 / over 14.8 | N=2^15, 9x60 | depth 12, qbits 60 | 40.3 | +120 | +2 | 3.00 | 495 (depth 11, qbits 55) | N=2^15, 9x60 | 2.99 |
| 10 | N=2^15, 8x60 | over 19.6 / over 19.6 | N=2^15, 10x60 | depth 13, qbits 60 | 50.5 | +120 | +2 | 1.40 | 550 (depth 12, qbits 55) | N=2^15, 10x60 | 1.40 |
| 11 | N=2^15, 8x60 | over 19.6 / over 19.6 | N=2^15, 10x60 | depth 13, qbits 60 | 0.9 | +120 | +2 | 1.39 | 600 (depth 13, qbits 60) | N=2^15, 10x60 | 1.40 |
| 12 | N=2^15, 9x60 | over 9.3 / over 9.3 | N=2^15, 11x60 | depth 15, qbits 60 | 11.2 | +120 | +2 | 1.35 | 649 (depth 15, qbits 59) | N=2^15, 11x60 | 1.35 |

### BFV BEHZ BV, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 20.8 / CERT 20.8 | N=2^12, 2x54 | depth 1, qbits 54 | 15.8 | -12 | +0 | 0.48 | 80 (depth 1, qbits 40) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 38.2 / CERT 38.2 | N=2^13, 3x60 | depth 2, qbits 60 | 38.2 | +0 | +0 | 1.00 | 126 (depth 2, qbits 42) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 2.8 / over 2.8 | N=2^13, 4x54 | depth 4, qbits 54 | 38.8 | +36 | +1 | 1.42 | 168 (depth 3, qbits 42) | N=2^13, 4x54 | 1.41 |
| 4 | N=2^14, 4x60 | CERT 8.8 / CERT 8.8 | N=2^13, 5x43 | depth 5, qbits 43 | 7.2 | -25 | +1 | 0.63 | 210 (depth 4, qbits 42) | N=2^13, 5x43 | 0.63 |
| 5 | N=2^14, 4x60 | over 34.2 / over 34.2 | N=2^14, 5x60 | depth 6, qbits 60 | 25.5 | +60 | +1 | 1.33 | 270 (depth 6, qbits 54) | N=2^14, 5x60 | 1.33 |
| 6 | N=2^14, 5x60 | over 17.5 / over 17.5 | N=2^14, 6x60 | depth 8, qbits 60 | 42.2 | +60 | +1 | 1.26 | 312 (depth 7, qbits 52) | N=2^14, 6x60 | 1.27 |
| 7 | N=2^14, 5x60 | over 17.5 / over 17.5 | N=2^14, 7x60 | depth 10, qbits 60 | 59.0 | +120 | +2 | 1.56 | 357 (depth 8, qbits 51) | N=2^14, 7x60 | 1.56 |
| 8 | N=2^14, 6x60 | over 0.8 / over 0.8 | N=2^14, 7x60 | depth 10, qbits 60 | 16.0 | +60 | +1 | 1.23 | 406 (depth 9, qbits 58) | N=2^14, 7x60 | 1.23 |
| 9 | N=2^14, 6x60 | over 0.8 / over 0.8 | N=2^14, 12x36 | depth 11, qbits 36 | 2.7 | +72 | +6 | 2.78 | 432 (depth 11, qbits 36) | N=2^14, 11x39 | 2.42 |
| 10 | N=2^14, 7x60 | over 27.0 / over 27.0 | N=2^15, 9x60 | depth 13, qbits 60 | 30.6 | +120 | +2 | 2.99 | 513 (depth 12, qbits 57) | N=2^15, 9x60 | 3.00 |
| 11 | N=2^15, 8x60 | over 29.2 / over 29.2 | N=2^15, 10x60 | depth 15, qbits 60 | 45.5 | +120 | +2 | 1.39 | 550 (depth 13, qbits 55) | N=2^15, 10x60 | 1.39 |
| 12 | N=2^15, 8x60 | over 29.2 / over 29.2 | N=2^15, 10x60 | depth 15, qbits 60 | 0.5 | +120 | +2 | 1.40 | 600 (depth 15, qbits 60) | N=2^15, 10x60 | 1.40 |

### BFV BEHZ BV, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 17.2 / CERT 17.2 | N=2^12, 2x54 | depth 1, qbits 54 | 12.2 | -12 | +0 | 0.48 | 88 (depth 1, qbits 44) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 31.1 / CERT 31.1 | N=2^13, 3x60 | depth 2, qbits 60 | 31.1 | +0 | +0 | 1.00 | 138 (depth 2, qbits 46) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 13.5 / over 13.5 | N=2^13, 4x54 | depth 4, qbits 54 | 28.1 | +36 | +1 | 1.41 | 184 (depth 3, qbits 46) | N=2^13, 4x54 | 1.41 |
| 4 | N=2^14, 4x60 | over 5.5 / over 5.5 | N=2^14, 5x60 | depth 5, qbits 60 | 54.1 | +60 | +1 | 1.32 | 235 (depth 4, qbits 47) | N=2^14, 5x60 | 1.33 |
| 5 | N=2^14, 5x60 | CERT 7.6 / CERT 7.6 | N=2^14, 5x60 | depth 5, qbits 60 | 7.6 | +0 | +0 | 1.00 | 295 (depth 5, qbits 59) | N=2^14, 5x60 | 1.01 |
| 6 | N=2^14, 5x60 | over 39.0 / over 39.0 | N=2^14, 6x60 | depth 7, qbits 60 | 20.7 | +60 | +1 | 1.26 | 336 (depth 7, qbits 56) | N=2^14, 6x60 | 1.27 |
| 7 | N=2^14, 6x60 | over 25.9 / over 25.9 | N=2^14, 7x60 | depth 9, qbits 60 | 33.9 | +60 | +1 | 1.22 | 385 (depth 8, qbits 55) | N=2^14, 7x60 | 1.23 |
| 8 | N=2^14, 6x60 | over 25.9 / over 25.9 | N=2^14, 8x54 | depth 9, qbits 54 | 5.1 | +72 | +2 | 1.48 | 432 (depth 9, qbits 54) | N=2^14, 8x54 | 1.48 |
| 9 | N=2^14, 7x60 | over 12.7 / over 12.7 | N=2^15, 9x60 | depth 12, qbits 60 | 43.4 | +120 | +2 | 3.02 | 495 (depth 11, qbits 55) | N=2^15, 9x60 | 3.01 |
| 10 | N=2^15, 8x60 | over 16.5 / over 16.5 | N=2^15, 10x60 | depth 13, qbits 60 | 54.6 | +120 | +2 | 1.39 | 540 (depth 12, qbits 54) | N=2^15, 10x60 | 1.39 |
| 11 | N=2^15, 8x60 | over 16.5 / over 16.5 | N=2^15, 10x60 | depth 13, qbits 60 | 6.0 | +120 | +2 | 1.40 | 600 (depth 13, qbits 60) | N=2^15, 10x60 | 1.39 |
| 12 | N=2^15, 9x60 | over 5.2 / over 5.2 | N=2^15, 11x60 | depth 15, qbits 60 | 17.3 | +120 | +2 | 1.35 | 649 (depth 15, qbits 59) | N=2^15, 11x60 | 1.35 |

### BFV BEHZ HYBRID, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 38.6 / CERT 41.3 | N=2^13, 2x49, P 2x60 | depth 1, qbits 49, dnum 1 | 19.7 | -22 | +0 | 0.44 | 80 (depth 1, qbits 40, dnum 1) | N=2^13, 2x49, P 2x60 | 0.44 |
| 2 | N=2^14, 2x60, P 2x60 | over 5.4 / over 2.7 | N=2^13, 3x52, P 1x60 | depth 3, qbits 52, dnum 3 | 35.6 | +36 | +1 | 0.68 | 123 (depth 2, qbits 41, dnum 3) | N=2^13, 3x52, P 1x60 | 0.68 |
| 3 | N=2^14, 3x60, P 3x60 | CERT 10.6 / CERT 13.4 | N=2^14, 3x58, P 3x60 | depth 3, qbits 58, dnum 1 | 4.7 | -6 | +0 | 0.91 | 171 (depth 3, qbits 57, dnum 1) | N=2^14, 3x58, P 3x60 | 0.90 |
| 4 | N=2^14, 3x60, P 3x60 | over 33.4 / over 30.6 | N=2^14, 4x58, P 2x60 | depth 5, qbits 58 | 18.6 | +52 | +1 | 1.22 | 216 (depth 4, qbits 54) | N=2^14, 4x58, P 2x60 | 1.22 |
| 5 | N=2^14, 4x60, P 3x60 | over 17.3 / over 13.6 | N=2^14, 5x58, P 2x60 | depth 7, qbits 58 | 32.6 | +50 | +1 | 1.27 | 260 (depth 6, qbits 52) | N=2^14, 5x51, P 3x60 | 1.24 |
| 6 | N=2^14, 4x60, P 3x60 | over 17.3 / over 13.6 | N=2^14, 6x53, P 2x60 | depth 8, qbits 53 | 16.6 | +78 | +2 | 1.51 | 306 (depth 7, qbits 51) | N=2^14, 6x53, P 2x60 | 1.51 |
| 7 | N=2^15, 5x60, P 3x60 | over 14.3 / over 10.7 | N=2^15, 7x59, P 7x60 | depth 10, qbits 59, dnum 1 | 52.7 | +113 | +2 | 1.30 | 364 (depth 9, qbits 52, dnum 1) | N=2^15, 6x60, P 7x60 | 1.13 |
| 8 | N=2^15, 6x60, P 3x60 | over 0.3 / over 42.6 | N=2^15, 7x59, P 7x60 | depth 10, qbits 59, dnum 1 | 6.7 | +53 | +1 | 1.10 | 413 (depth 10, qbits 59, dnum 1) | N=2^15, 7x59, P 7x60 | 1.10 |
| 9 | N=2^15, 6x60, P 3x60 | over 0.3 / over 42.6 | N=2^15, 8x59, P 4x60 | depth 12, qbits 59, dnum 2 | 19.6 | +112 | +2 | 1.27 | 456 (depth 11, qbits 57, dnum 2) | N=2^15, 8x59, P 4x60 | 1.28 |
| 10 | N=2^15, 7x60, P 4x60 | over 32.3 / over 28.6 | N=2^15, 9x59, P 5x60 | depth 13, qbits 59, dnum 2 | 32.7 | +111 | +2 | 1.24 | 504 (depth 13, qbits 56, dnum 2) | N=2^15, 9x59, P 5x60 | 1.24 |
| 11 | N=2^15, 7x60, P 4x60 | over 32.3 / over 28.6 | N=2^15, 10x58, P 5x60 | depth 15, qbits 58, dnum 2 | 35.7 | +160 | +3 | 1.39 | 550 (depth 14, qbits 55, dnum 2) | N=2^15, 10x58, P 5x60 | 1.39 |
| 12 | N=2^15, 8x60, P 4x60 | over 18.3 / over 14.6 | N=2^15, 11x58, P 4x60 | depth 17, qbits 58 | 47.6 | +158 | +3 | 1.42 | 594 (depth 15, qbits 54) | N=2^15, 10x59, P 4x60 | 1.28 |

### BFV BEHZ HYBRID, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 30.6 / CERT 31.6 | N=2^13, 2x49, P 2x60 | depth 1, qbits 49, dnum 1 | 10.8 | -22 | +0 | 0.44 | 88 (depth 1, qbits 44, dnum 1) | N=2^13, 2x49, P 2x60 | 0.44 |
| 2 | N=2^14, 2x60, P 2x60 | over 17.0 / over 16.0 | N=2^13, 3x52, P 1x60 | depth 2, qbits 52, dnum 3 | 23.4 | +36 | +1 | 0.68 | 132 (depth 2, qbits 44, dnum 3) | N=2^13, 3x52, P 1x60 | 0.68 |
| 3 | N=2^14, 3x60, P 3x60 | over 3.9 / over 1.8 | N=2^14, 4x49, P 4x60 | depth 4, qbits 49, dnum 1 | 11.4 | +16 | +1 | 1.21 | 188 (depth 3, qbits 47, dnum 1) | N=2^14, 4x49, P 4x60 | 1.21 |
| 4 | N=2^14, 4x60, P 3x60 | CERT 8.0 / CERT 9.2 | N=2^14, 4x60, P 3x60 | depth 4, qbits 60 | 8.0 | +0 | +0 | 1.00 | 236 (depth 4, qbits 59) | N=2^14, 4x58, P 2x60 | 0.96 |
| 5 | N=2^14, 4x60, P 3x60 | over 39.6 / over 38.4 | N=2^14, 5x58, P 2x60 | depth 6, qbits 58 | 11.0 | +50 | +1 | 1.27 | 280 (depth 6, qbits 56) | N=2^14, 5x58, P 2x60 | 1.28 |
| 6 | N=2^15, 5x60, P 3x60 | over 39.9 / over 38.3 | N=2^15, 6x59, P 6x60 | depth 7, qbits 59, dnum 1 | 13.9 | +54 | +1 | 1.10 | 342 (depth 7, qbits 57, dnum 1) | N=2^15, 6x59, P 6x60 | 1.10 |
| 7 | N=2^15, 5x60, P 3x60 | over 39.9 / over 38.3 | N=2^15, 7x59, P 7x60 | depth 9, qbits 59, dnum 1 | 23.7 | +113 | +2 | 1.30 | 392 (depth 8, qbits 56, dnum 1) | N=2^15, 7x59, P 7x60 | 1.30 |
| 8 | N=2^15, 6x60, P 3x60 | over 29.5 / over 27.9 | N=2^15, 8x59, P 4x60 | depth 11, qbits 59, dnum 2 | 33.3 | +112 | +2 | 1.28 | 440 (depth 10, qbits 55, dnum 2) | N=2^15, 8x59, P 4x60 | 1.28 |
| 9 | N=2^15, 7x60, P 4x60 | over 18.8 / over 16.5 | N=2^15, 9x59, P 5x60 | depth 12, qbits 59, dnum 2 | 42.7 | +111 | +2 | 1.22 | 495 (depth 11, qbits 55, dnum 2) | N=2^15, 9x59, P 5x60 | 1.23 |
| 10 | N=2^15, 7x60, P 4x60 | over 18.8 / over 16.5 | N=2^15, 9x60, P 4x60 | depth 12, qbits 60 | 1.7 | +120 | +2 | 1.30 | 540 (depth 12, qbits 60) | N=2^15, 9x60, P 4x60 | 1.31 |
| 11 | N=2^15, 8x60, P 4x60 | over 8.2 / over 4.8 | N=2^15, 10x59, P 4x60 | depth 14, qbits 59 | 2.5 | +110 | +2 | 1.27 | 590 (depth 14, qbits 59) | N=2^15, 10x59, P 4x60 | 1.27 |
| 12 | N=2^15, 9x60, P 4x60 | over 47.9 / over 46.4 | N=2^15, 11x58, P 4x60 | depth 15, qbits 58 | 0.4 | +98 | +2 | 1.25 | 638 (depth 15, qbits 58) | N=2^15, 11x58, P 4x60 | 1.25 |

### BFV BEHZ HYBRID, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 35.6 / CERT 38.3 | N=2^13, 2x49, P 2x60 | depth 1, qbits 49, dnum 1 | 16.7 | -22 | +0 | 0.39 | 82 (depth 1, qbits 41, dnum 1) | N=2^13, 2x49, P 2x60 | 0.39 |
| 2 | N=2^14, 2x60, P 2x60 | over 8.4 / over 5.7 | N=2^13, 3x52, P 1x60 | depth 3, qbits 52, dnum 3 | 32.6 | +36 | +1 | 0.67 | 126 (depth 2, qbits 42, dnum 3) | N=2^13, 3x52, P 1x60 | 0.67 |
| 3 | N=2^14, 3x60, P 3x60 | CERT 8.6 / CERT 11.4 | N=2^14, 3x58, P 3x60 | depth 3, qbits 58, dnum 1 | 2.7 | -6 | +0 | 0.87 | 174 (depth 3, qbits 58, dnum 1) | N=2^14, 3x58, P 3x60 | 0.87 |
| 4 | N=2^14, 3x60, P 3x60 | over 34.4 / over 31.6 | N=2^14, 4x58, P 2x60 | depth 5, qbits 58 | 17.6 | +52 | +1 | 1.20 | 216 (depth 4, qbits 54) | N=2^14, 4x58, P 2x60 | 1.20 |
| 5 | N=2^14, 4x60, P 3x60 | over 17.3 / over 13.6 | N=2^14, 5x58, P 2x60 | depth 7, qbits 58 | 32.6 | +50 | +1 | 1.26 | 260 (depth 6, qbits 52) | N=2^14, 5x51, P 3x60 | 1.21 |
| 6 | N=2^14, 4x60, P 3x60 | over 17.3 / over 13.6 | N=2^14, 6x53, P 2x60 | depth 8, qbits 53 | 17.6 | +78 | +2 | 1.50 | 306 (depth 7, qbits 51) | N=2^14, 6x53, P 2x60 | 1.50 |
| 7 | N=2^15, 5x60, P 3x60 | over 13.3 / over 9.7 | N=2^15, 6x60, P 7x60 | depth 8, qbits 60, dnum 1 | 1.7 | +60 | +1 | 1.11 | 360 (depth 8, qbits 60, dnum 1) | N=2^15, 6x60, P 7x60 | 1.12 |
| 8 | N=2^15, 6x60, P 3x60 | over 43.3 / over 39.6 | N=2^15, 7x59, P 7x60 | depth 10, qbits 59, dnum 1 | 9.7 | +53 | +1 | 1.10 | 406 (depth 10, qbits 58, dnum 1) | N=2^15, 7x59, P 7x60 | 1.09 |
| 9 | N=2^15, 6x60, P 3x60 | over 43.3 / over 39.6 | N=2^15, 8x59, P 4x60 | depth 12, qbits 59, dnum 2 | 23.6 | +112 | +2 | 1.27 | 456 (depth 11, qbits 57, dnum 2) | N=2^15, 8x59, P 4x60 | 1.26 |
| 10 | N=2^15, 7x60, P 4x60 | over 28.3 / over 24.6 | N=2^15, 9x59, P 5x60 | depth 13, qbits 59, dnum 2 | 37.7 | +111 | +2 | 1.24 | 495 (depth 13, qbits 55, dnum 2) | N=2^15, 9x59, P 5x60 | 1.25 |
| 11 | N=2^15, 7x60, P 4x60 | over 28.3 / over 24.6 | N=2^15, 9x60, P 4x60 | depth 14, qbits 60 | 1.7 | +120 | +2 | 1.28 | 540 (depth 14, qbits 60) | N=2^15, 9x60, P 4x60 | 1.29 |
| 12 | N=2^15, 8x60, P 4x60 | over 13.3 / over 9.6 | N=2^15, 10x59, P 4x60 | depth 15, qbits 59 | 6.7 | +110 | +2 | 1.29 | 590 (depth 15, qbits 59) | N=2^15, 10x58, P 5x60 | 1.23 |

### BFV BEHZ HYBRID, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 27.6 / CERT 28.6 | N=2^13, 2x49, P 2x60 | depth 1, qbits 49, dnum 1 | 7.8 | -22 | +0 | 0.39 | 90 (depth 1, qbits 45, dnum 1) | N=2^13, 2x49, P 2x60 | 0.39 |
| 2 | N=2^14, 2x60, P 2x60 | over 20.0 / over 19.0 | N=2^13, 3x52, P 1x60 | depth 2, qbits 52, dnum 3 | 20.4 | +36 | +1 | 0.67 | 138 (depth 2, qbits 46, dnum 3) | N=2^13, 3x52, P 1x60 | 0.67 |
| 3 | N=2^14, 3x60, P 3x60 | over 5.9 / over 3.8 | N=2^14, 4x49, P 4x60 | depth 4, qbits 49, dnum 1 | 9.4 | +16 | +1 | 1.16 | 188 (depth 3, qbits 47, dnum 1) | N=2^14, 4x49, P 4x60 | 1.16 |
| 4 | N=2^14, 4x60, P 3x60 | CERT 7.0 / CERT 8.2 | N=2^14, 4x60, P 3x60 | depth 4, qbits 60 | 7.0 | +0 | +0 | 1.00 | 236 (depth 4, qbits 59) | N=2^14, 4x58, P 2x60 | 0.94 |
| 5 | N=2^14, 4x60, P 3x60 | over 39.6 / over 38.4 | N=2^14, 5x58, P 2x60 | depth 6, qbits 58 | 11.0 | +50 | +1 | 1.26 | 280 (depth 6, qbits 56) | N=2^14, 5x58, P 2x60 | 1.27 |
| 6 | N=2^15, 5x60, P 3x60 | over 38.9 / over 37.3 | N=2^15, 6x59, P 6x60 | depth 7, qbits 59, dnum 1 | 14.9 | +54 | +1 | 1.09 | 342 (depth 7, qbits 57, dnum 1) | N=2^15, 6x59, P 6x60 | 1.09 |
| 7 | N=2^15, 5x60, P 3x60 | over 38.9 / over 37.3 | N=2^15, 7x59, P 7x60 | depth 9, qbits 59, dnum 1 | 25.7 | +113 | +2 | 1.29 | 392 (depth 8, qbits 56, dnum 1) | N=2^15, 7x59, P 7x60 | 1.29 |
| 8 | N=2^15, 6x60, P 3x60 | over 27.5 / over 25.9 | N=2^15, 8x59, P 4x60 | depth 11, qbits 59, dnum 2 | 36.3 | +112 | +2 | 1.28 | 440 (depth 10, qbits 55, dnum 2) | N=2^15, 8x59, P 4x60 | 1.27 |
| 9 | N=2^15, 7x60, P 4x60 | over 15.8 / over 13.5 | N=2^15, 9x59, P 5x60 | depth 12, qbits 59, dnum 2 | 46.7 | +111 | +2 | 1.24 | 486 (depth 11, qbits 54, dnum 2) | N=2^15, 9x59, P 5x60 | 1.24 |
| 10 | N=2^15, 7x60, P 4x60 | over 15.8 / over 13.5 | N=2^15, 9x60, P 4x60 | depth 12, qbits 60 | 6.7 | +120 | +2 | 1.31 | 540 (depth 12, qbits 60) | N=2^15, 9x59, P 5x60 | 1.25 |
| 11 | N=2^15, 8x60, P 4x60 | over 4.2 / over 0.8 | N=2^15, 10x59, P 4x60 | depth 14, qbits 59 | 8.5 | +110 | +2 | 1.29 | 590 (depth 14, qbits 59) | N=2^15, 10x58, P 5x60 | 1.23 |
| 12 | N=2^15, 9x60, P 4x60 | over 41.9 / over 40.4 | N=2^15, 11x58, P 4x60 | depth 15, qbits 58 | 7.4 | +98 | +2 | 1.25 | 638 (depth 15, qbits 58) | N=2^15, 11x58, P 4x60 | 1.25 |

### BFV HPSPOVERQ BV, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 24.7 / CERT 24.7 | N=2^12, 2x54 | depth 1, qbits 54 | 19.7 | -12 | +0 | 0.48 | 76 (depth 1, qbits 38) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 42.1 / CERT 42.1 | N=2^13, 3x60 | depth 2, qbits 60 | 42.1 | +0 | +0 | 1.00 | 123 (depth 2, qbits 41) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | NOT CERTIFIE / NOT CERTIFIE | N=2^13, 4x54 | depth 4, qbits 54 | 41.7 | +36 | +1 | 1.39 | 164 (depth 3, qbits 41) | N=2^13, 4x54 | 1.39 |
| 4 | N=2^14, 4x60 | CERT 10.7 / CERT 10.7 | N=2^13, 5x43 | depth 5, qbits 43 | 8.8 | -25 | +1 | 0.63 | 210 (depth 4, qbits 42) | N=2^13, 5x43 | 0.64 |
| 5 | N=2^14, 4x60 | over 33.3 / over 33.3 | N=2^14, 5x60 | depth 6, qbits 60 | 26.4 | +60 | +1 | 1.34 | 270 (depth 6, qbits 54) | N=2^14, 5x60 | 1.34 |
| 6 | N=2^14, 5x60 | over 17.6 / over 17.6 | N=2^14, 6x60 | depth 8, qbits 60 | 42.1 | +60 | +1 | 1.27 | 312 (depth 7, qbits 52) | N=2^14, 6x60 | 1.27 |
| 7 | N=2^14, 5x60 | over 17.6 / over 17.6 | N=2^14, 7x60 | depth 10, qbits 60 | 57.9 | +120 | +2 | 1.55 | 357 (depth 8, qbits 51) | N=2^14, 7x60 | 1.56 |
| 8 | N=2^14, 6x60 | over 1.9 / over 1.9 | N=2^14, 7x60 | depth 10, qbits 60 | 13.9 | +60 | +1 | 1.22 | 406 (depth 9, qbits 58) | N=2^14, 7x60 | 1.22 |
| 9 | N=2^14, 6x60 | over 1.9 / over 1.9 | N=2^15, 8x60 | depth 11, qbits 60 | 12.7 | +120 | +2 | 3.09 | 472 (depth 11, qbits 59) | N=2^14, 12x36 | 2.68 |
| 10 | N=2^14, 7x60 | over 30.1 / over 30.1 | N=2^15, 9x60 | depth 13, qbits 60 | 26.5 | +120 | +2 | 2.99 | 513 (depth 12, qbits 57) | N=2^15, 9x60 | 2.97 |
| 11 | N=2^15, 8x60 | over 33.3 / over 33.3 | N=2^15, 10x60 | depth 15, qbits 60 | 40.4 | +120 | +2 | 1.39 | 560 (depth 14, qbits 56) | N=2^15, 10x60 | 1.40 |
| 12 | N=2^15, 8x60 | over 33.3 / over 33.3 | N=2^15, 11x60 | depth 16, qbits 60 | 54.2 | +180 | +3 | 1.60 | 605 (depth 15, qbits 55) | N=2^15, 11x60 | 1.61 |

### BFV HPSPOVERQ BV, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 21.1 / CERT 21.1 | N=2^12, 2x54 | depth 1, qbits 54 | 16.1 | -12 | +0 | 0.48 | 86 (depth 1, qbits 43) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 35.0 / CERT 35.0 | N=2^13, 3x60 | depth 2, qbits 60 | 35.0 | +0 | +0 | 1.00 | 132 (depth 2, qbits 44) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 10.6 / over 10.6 | N=2^13, 4x54 | depth 4, qbits 54 | 30.9 | +36 | +1 | 1.40 | 196 (depth 3, qbits 49) | N=2^13, 4x54 | 1.40 |
| 4 | N=2^14, 4x60 | over 3.6 / over 3.6 | N=2^14, 5x60 | depth 5, qbits 60 | 56.0 | +60 | +1 | 1.35 | 245 (depth 5, qbits 49) | N=2^14, 5x60 | 1.35 |
| 5 | N=2^14, 5x60 | CERT 8.5 / CERT 8.5 | N=2^14, 5x60 | depth 5, qbits 60 | 8.5 | +0 | +0 | 1.00 | 290 (depth 5, qbits 58) | N=2^14, 5x60 | 1.00 |
| 6 | N=2^14, 5x60 | over 39.1 / over 39.1 | N=2^14, 6x60 | depth 7, qbits 60 | 20.6 | +60 | +1 | 1.26 | 348 (depth 7, qbits 58) | N=2^14, 6x60 | 1.26 |
| 7 | N=2^14, 6x60 | over 27.0 / over 27.0 | N=2^14, 7x60 | depth 9, qbits 60 | 32.8 | +60 | +1 | 1.23 | 406 (depth 8, qbits 58) | N=2^14, 7x60 | 1.23 |
| 8 | N=2^14, 6x60 | over 27.0 / over 27.0 | N=2^14, 8x54 | depth 9, qbits 54 | 3.0 | +72 | +2 | 1.46 | 432 (depth 9, qbits 54) | N=2^14, 8x54 | 1.47 |
| 9 | N=2^14, 7x60 | over 14.8 / over 14.8 | N=2^15, 9x60 | depth 12, qbits 60 | 40.3 | +120 | +2 | 2.97 | 504 (depth 11, qbits 56) | N=2^15, 9x60 | 2.99 |
| 10 | N=2^15, 8x60 | over 19.6 / over 19.6 | N=2^15, 10x60 | depth 13, qbits 60 | 50.5 | +120 | +2 | 1.37 | 560 (depth 12, qbits 56) | N=2^15, 10x60 | 1.39 |
| 11 | N=2^15, 8x60 | over 19.6 / over 19.6 | N=2^15, 10x60 | depth 13, qbits 60 | 0.9 | +120 | +2 | 1.39 | 600 (depth 13, qbits 60) | N=2^15, 10x60 | 1.39 |
| 12 | N=2^15, 9x60 | over 9.3 / over 9.3 | N=2^15, 11x60 | depth 15, qbits 60 | 11.2 | +120 | +2 | 1.35 | 649 (depth 15, qbits 59) | N=2^15, 11x60 | 1.36 |

### BFV HPSPOVERQ BV, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 20.8 / CERT 20.8 | N=2^12, 2x54 | depth 1, qbits 54 | 15.8 | -12 | +0 | 0.48 | 80 (depth 1, qbits 40) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 38.2 / CERT 38.2 | N=2^13, 3x60 | depth 2, qbits 60 | 38.2 | +0 | +0 | 1.00 | 126 (depth 2, qbits 42) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 2.8 / over 2.8 | N=2^13, 4x54 | depth 4, qbits 54 | 38.8 | +36 | +1 | 1.44 | 168 (depth 3, qbits 42) | N=2^13, 4x54 | 1.44 |
| 4 | N=2^14, 4x60 | CERT 8.8 / CERT 8.8 | N=2^13, 5x43 | depth 5, qbits 43 | 7.2 | -25 | +1 | 0.64 | 210 (depth 4, qbits 42) | N=2^13, 5x43 | 0.64 |
| 5 | N=2^14, 4x60 | over 34.2 / over 34.2 | N=2^14, 5x60 | depth 6, qbits 60 | 25.5 | +60 | +1 | 1.36 | 270 (depth 6, qbits 54) | N=2^14, 5x60 | 1.36 |
| 6 | N=2^14, 5x60 | over 17.5 / over 17.5 | N=2^14, 6x60 | depth 8, qbits 60 | 42.2 | +60 | +1 | 1.29 | 312 (depth 7, qbits 52) | N=2^14, 6x60 | 1.28 |
| 7 | N=2^14, 5x60 | over 17.5 / over 17.5 | N=2^14, 7x60 | depth 10, qbits 60 | 59.0 | +120 | +2 | 1.58 | 357 (depth 8, qbits 51) | N=2^14, 7x60 | 1.58 |
| 8 | N=2^14, 6x60 | over 0.8 / over 0.8 | N=2^14, 7x60 | depth 10, qbits 60 | 16.0 | +60 | +1 | 1.22 | 406 (depth 9, qbits 58) | N=2^14, 7x60 | 1.22 |
| 9 | N=2^14, 6x60 | over 0.8 / over 0.8 | N=2^14, 12x36 | depth 11, qbits 36 | 2.5 | +72 | +6 | 2.73 | 432 (depth 11, qbits 36) | N=2^14, 11x39 | 2.39 |
| 10 | N=2^14, 7x60 | over 27.0 / over 27.0 | N=2^15, 9x60 | depth 13, qbits 60 | 30.6 | +120 | +2 | 3.01 | 513 (depth 12, qbits 57) | N=2^15, 9x60 | 3.01 |
| 11 | N=2^15, 8x60 | over 29.2 / over 29.2 | N=2^15, 10x60 | depth 15, qbits 60 | 45.5 | +120 | +2 | 1.39 | 550 (depth 13, qbits 55) | N=2^15, 10x60 | 1.40 |
| 12 | N=2^15, 8x60 | over 29.2 / over 29.2 | N=2^15, 11x60 | depth 16, qbits 60 | 60.4 | +180 | +3 | 1.61 | 594 (depth 15, qbits 54) | N=2^15, 11x60 | 1.61 |

### BFV HPSPOVERQ BV, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 17.2 / CERT 17.2 | N=2^12, 2x54 | depth 1, qbits 54 | 12.2 | -12 | +0 | 0.48 | 100 (depth 1, qbits 50) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 31.1 / CERT 31.1 | N=2^13, 3x60 | depth 2, qbits 60 | 31.1 | +0 | +0 | 1.00 | 150 (depth 2, qbits 50) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 13.5 / over 13.5 | N=2^13, 4x54 | depth 4, qbits 54 | 28.1 | +36 | +1 | 1.43 | 196 (depth 3, qbits 49) | N=2^13, 4x54 | 1.43 |
| 4 | N=2^14, 4x60 | over 5.5 / over 5.5 | N=2^14, 5x60 | depth 5, qbits 60 | 54.1 | +60 | +1 | 1.37 | 245 (depth 5, qbits 49) | N=2^14, 5x60 | 1.37 |
| 5 | N=2^14, 5x60 | CERT 7.6 / CERT 7.6 | N=2^14, 5x60 | depth 5, qbits 60 | 7.6 | +0 | +0 | 1.00 | 295 (depth 5, qbits 59) | N=2^14, 5x60 | 0.99 |
| 6 | N=2^14, 5x60 | over 39.0 / over 39.0 | N=2^14, 6x60 | depth 7, qbits 60 | 20.7 | +60 | +1 | 1.28 | 348 (depth 7, qbits 58) | N=2^14, 6x60 | 1.28 |
| 7 | N=2^14, 6x60 | over 25.9 / over 25.9 | N=2^14, 7x60 | depth 9, qbits 60 | 33.9 | +60 | +1 | 1.25 | 406 (depth 8, qbits 58) | N=2^14, 7x60 | 1.24 |
| 8 | N=2^14, 6x60 | over 25.9 / over 25.9 | N=2^14, 8x54 | depth 9, qbits 54 | 5.1 | +72 | +2 | 1.48 | 432 (depth 9, qbits 54) | N=2^14, 8x54 | 1.48 |
| 9 | N=2^14, 7x60 | over 12.7 / over 12.7 | N=2^15, 9x60 | depth 12, qbits 60 | 43.4 | +120 | +2 | 2.99 | 504 (depth 11, qbits 56) | N=2^15, 9x60 | 2.99 |
| 10 | N=2^15, 8x60 | over 16.5 / over 16.5 | N=2^15, 10x60 | depth 13, qbits 60 | 54.6 | +120 | +2 | 1.39 | 560 (depth 12, qbits 56) | N=2^15, 10x60 | 1.39 |
| 11 | N=2^15, 8x60 | over 16.5 / over 16.5 | N=2^15, 10x60 | depth 13, qbits 60 | 6.0 | +120 | +2 | 1.39 | 600 (depth 13, qbits 60) | N=2^15, 10x60 | 1.39 |
| 12 | N=2^15, 9x60 | over 5.2 / over 5.2 | N=2^15, 11x60 | depth 15, qbits 60 | 17.3 | +120 | +2 | 1.35 | 649 (depth 15, qbits 59) | N=2^15, 11x60 | 1.37 |

### BFV HPSPOVERQ HYBRID, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 38.6 / CERT 41.1 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 33.6 | -8 | +0 | 0.44 | 100 (depth 1, qbits 50) | N=2^13, 2x56, P 1x60 | 0.44 |
| 2 | N=2^14, 2x60, P 2x60 | over 5.4 / over 2.9 | N=2^13, 3x52, P 1x60 | depth 3, qbits 52, dnum 3 | 35.5 | +36 | +1 | 0.69 | 123 (depth 2, qbits 41, dnum 3) | N=2^13, 3x52, P 1x60 | 0.69 |
| 3 | N=2^14, 3x60, P 3x60 | CERT 10.6 / CERT 13.1 | N=2^14, 3x58, P 3x60 | depth 3, qbits 58, dnum 1 | 4.6 | -6 | +0 | 0.89 | 171 (depth 3, qbits 57, dnum 1) | N=2^14, 3x58, P 3x60 | 0.89 |
| 4 | N=2^14, 3x60, P 3x60 | over 33.5 / over 30.9 | N=2^14, 4x58, P 2x60 | depth 5, qbits 58 | 18.5 | +52 | +1 | 1.22 | 216 (depth 4, qbits 54) | N=2^14, 4x58, P 2x60 | 1.22 |
| 5 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 5x58, P 2x60 | depth 7, qbits 58 | 32.6 | +50 | +1 | 1.30 | 260 (depth 6, qbits 52) | N=2^14, 5x58, P 2x60 | 1.29 |
| 6 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 6x53, P 2x60 | depth 8, qbits 53 | 16.5 | +78 | +2 | 1.54 | 306 (depth 7, qbits 51) | N=2^14, 6x53, P 2x60 | 1.54 |
| 7 | N=2^15, 5x60, P 3x60 | over 14.4 / over 11.5 | N=2^15, 7x59, P 7x60 | depth 10, qbits 59, dnum 1 | 52.6 | +113 | +2 | 1.31 | 364 (depth 9, qbits 52, dnum 1) | N=2^15, 6x60, P 7x60 | 1.13 |
| 8 | N=2^15, 6x60, P 3x60 | over 0.4 / over 43.6 | N=2^15, 7x59, P 7x60 | depth 10, qbits 59, dnum 1 | 6.6 | +53 | +1 | 1.10 | 413 (depth 10, qbits 59, dnum 1) | N=2^15, 7x59, P 7x60 | 1.10 |
| 9 | N=2^15, 6x60, P 3x60 | over 0.4 / over 43.6 | N=2^15, 8x59, P 4x60 | depth 12, qbits 59, dnum 2 | 19.5 | +112 | +2 | 1.28 | 456 (depth 11, qbits 57, dnum 2) | N=2^15, 8x59, P 4x60 | 1.28 |
| 10 | N=2^15, 7x60, P 4x60 | over 32.4 / over 29.7 | N=2^15, 9x59, P 5x60 | depth 13, qbits 59, dnum 2 | 32.5 | +111 | +2 | 1.25 | 504 (depth 13, qbits 56, dnum 2) | N=2^15, 9x59, P 5x60 | 1.24 |
| 11 | N=2^15, 7x60, P 4x60 | over 32.4 / over 29.7 | N=2^15, 10x58, P 5x60 | depth 15, qbits 58, dnum 2 | 35.5 | +160 | +3 | 1.38 | 550 (depth 14, qbits 55, dnum 2) | N=2^15, 10x58, P 5x60 | 1.37 |
| 12 | N=2^15, 8x60, P 4x60 | over 18.5 / over 15.8 | N=2^15, 11x58, P 4x60 | depth 17, qbits 58 | 47.5 | +158 | +3 | 1.40 | 594 (depth 15, qbits 54) | N=2^15, 10x59, P 4x60 | 1.28 |

### BFV HPSPOVERQ HYBRID, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 30.6 / CERT 31.5 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 25.0 | -8 | +0 | 0.44 | 88 (depth 1, qbits 44) | N=2^13, 2x56, P 1x60 | 0.44 |
| 2 | N=2^14, 2x60, P 2x60 | over 17.0 / over 16.0 | N=2^13, 3x52, P 1x60 | depth 2, qbits 52, dnum 3 | 23.4 | +36 | +1 | 0.70 | 150 (depth 2, qbits 50, dnum 3) | N=2^13, 3x52, P 1x60 | 0.70 |
| 3 | N=2^14, 3x60, P 3x60 | over 3.9 / over 2.0 | N=2^14, 4x49, P 4x60 | depth 4, qbits 49, dnum 1 | 11.4 | +16 | +1 | 1.21 | 196 (depth 4, qbits 49, dnum 1) | N=2^14, 4x49, P 4x60 | 1.21 |
| 4 | N=2^14, 4x60, P 3x60 | CERT 8.0 / CERT 9.1 | N=2^14, 4x60, P 3x60 | depth 4, qbits 60 | 8.0 | +0 | +0 | 1.00 | 236 (depth 4, qbits 59) | N=2^14, 4x58, P 2x60 | 0.96 |
| 5 | N=2^14, 4x60, P 3x60 | over 39.6 / over 38.5 | N=2^14, 5x58, P 2x60 | depth 6, qbits 58 | 10.9 | +50 | +1 | 1.29 | 290 (depth 6, qbits 58) | N=2^14, 5x58, P 2x60 | 1.29 |
| 6 | N=2^15, 5x60, P 3x60 | over 40.0 / over 38.5 | N=2^15, 6x59, P 6x60 | depth 7, qbits 59, dnum 1 | 13.9 | +54 | +1 | 1.10 | 348 (depth 7, qbits 58, dnum 1) | N=2^15, 6x59, P 6x60 | 1.11 |
| 7 | N=2^15, 5x60, P 3x60 | over 40.0 / over 38.5 | N=2^15, 7x59, P 7x60 | depth 9, qbits 59, dnum 1 | 23.6 | +113 | +2 | 1.32 | 406 (depth 9, qbits 58, dnum 1) | N=2^15, 7x59, P 7x60 | 1.31 |
| 8 | N=2^15, 6x60, P 3x60 | over 29.6 / over 28.1 | N=2^15, 8x59, P 4x60 | depth 11, qbits 59, dnum 2 | 33.2 | +112 | +2 | 1.27 | 448 (depth 10, qbits 56, dnum 2) | N=2^15, 8x59, P 4x60 | 1.28 |
| 9 | N=2^15, 7x60, P 4x60 | over 18.9 / over 16.9 | N=2^15, 9x59, P 5x60 | depth 12, qbits 59, dnum 2 | 42.5 | +111 | +2 | 1.25 | 504 (depth 11, qbits 56, dnum 2) | N=2^15, 9x59, P 5x60 | 1.25 |
| 10 | N=2^15, 7x60, P 4x60 | over 18.9 / over 16.9 | N=2^15, 9x60, P 4x60 | depth 12, qbits 60 | 1.6 | +120 | +2 | 1.30 | 540 (depth 12, qbits 60) | N=2^15, 9x60, P 4x60 | 1.29 |
| 11 | N=2^15, 8x60, P 4x60 | over 8.3 / over 5.8 | N=2^15, 10x59, P 4x60 | depth 14, qbits 59 | 2.4 | +110 | +2 | 1.28 | 590 (depth 14, qbits 59) | N=2^15, 10x59, P 4x60 | 1.29 |
| 12 | N=2^15, 9x60, P 4x60 | over 48.0 / over 46.7 | N=2^15, 11x58, P 4x60 | depth 15, qbits 58 | 0.3 | +98 | +2 | 1.24 | 638 (depth 15, qbits 58) | N=2^15, 11x58, P 4x60 | 1.24 |

### BFV HPSPOVERQ HYBRID, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 35.6 / CERT 38.1 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 30.6 | -8 | +0 | 0.41 | 100 (depth 1, qbits 50) | N=2^13, 2x56, P 1x60 | 0.41 |
| 2 | N=2^14, 2x60, P 2x60 | over 8.4 / over 5.9 | N=2^13, 3x52, P 1x60 | depth 3, qbits 52, dnum 3 | 32.5 | +36 | +1 | 0.67 | 126 (depth 2, qbits 42, dnum 3) | N=2^13, 3x52, P 1x60 | 0.67 |
| 3 | N=2^14, 3x60, P 3x60 | CERT 8.6 / CERT 11.1 | N=2^14, 3x58, P 3x60 | depth 3, qbits 58, dnum 1 | 2.6 | -6 | +0 | 0.86 | 174 (depth 3, qbits 58, dnum 1) | N=2^14, 3x58, P 3x60 | 0.85 |
| 4 | N=2^14, 3x60, P 3x60 | over 34.5 / over 31.9 | N=2^14, 4x58, P 2x60 | depth 5, qbits 58 | 17.5 | +52 | +1 | 1.18 | 216 (depth 4, qbits 54) | N=2^14, 4x58, P 2x60 | 1.18 |
| 5 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 5x58, P 2x60 | depth 7, qbits 58 | 32.6 | +50 | +1 | 1.27 | 260 (depth 6, qbits 52) | N=2^14, 5x58, P 2x60 | 1.27 |
| 6 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 6x53, P 2x60 | depth 8, qbits 53 | 17.5 | +78 | +2 | 1.52 | 306 (depth 7, qbits 51) | N=2^14, 6x53, P 2x60 | 1.52 |
| 7 | N=2^15, 5x60, P 3x60 | over 13.4 / over 10.5 | N=2^15, 6x60, P 7x60 | depth 8, qbits 60, dnum 1 | 1.6 | +60 | +1 | 1.10 | 360 (depth 8, qbits 60, dnum 1) | N=2^15, 6x60, P 7x60 | 1.11 |
| 8 | N=2^15, 6x60, P 3x60 | over 43.4 / over 40.6 | N=2^15, 7x59, P 7x60 | depth 10, qbits 59, dnum 1 | 9.6 | +53 | +1 | 1.08 | 406 (depth 10, qbits 58, dnum 1) | N=2^15, 7x59, P 7x60 | 1.08 |
| 9 | N=2^15, 6x60, P 3x60 | over 43.4 / over 40.6 | N=2^15, 8x59, P 4x60 | depth 12, qbits 59, dnum 2 | 23.5 | +112 | +2 | 1.26 | 456 (depth 11, qbits 57, dnum 2) | N=2^15, 8x59, P 4x60 | 1.26 |
| 10 | N=2^15, 7x60, P 4x60 | over 28.4 / over 25.7 | N=2^15, 9x59, P 5x60 | depth 13, qbits 59, dnum 2 | 37.5 | +111 | +2 | 1.23 | 495 (depth 13, qbits 55, dnum 2) | N=2^15, 9x59, P 5x60 | 1.24 |
| 11 | N=2^15, 7x60, P 4x60 | over 28.4 / over 25.7 | N=2^15, 9x60, P 4x60 | depth 14, qbits 60 | 1.6 | +120 | +2 | 1.29 | 540 (depth 14, qbits 60) | N=2^15, 9x60, P 4x60 | 1.29 |
| 12 | N=2^15, 8x60, P 4x60 | over 13.5 / over 10.8 | N=2^15, 10x59, P 4x60 | depth 15, qbits 59 | 6.5 | +110 | +2 | 1.27 | 590 (depth 15, qbits 59) | N=2^15, 10x59, P 4x60 | 1.27 |

### BFV HPSPOVERQ HYBRID, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 27.6 / CERT 28.5 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 22.0 | -8 | +0 | 0.41 | 90 (depth 1, qbits 45) | N=2^13, 2x56, P 1x60 | 0.41 |
| 2 | N=2^14, 2x60, P 2x60 | over 20.0 / over 19.0 | N=2^13, 3x52, P 1x60 | depth 2, qbits 52, dnum 3 | 20.4 | +36 | +1 | 0.68 | 150 (depth 2, qbits 50, dnum 3) | N=2^13, 3x52, P 1x60 | 0.68 |
| 3 | N=2^14, 3x60, P 3x60 | over 5.9 / over 4.0 | N=2^14, 4x49, P 4x60 | depth 4, qbits 49, dnum 1 | 9.4 | +16 | +1 | 1.15 | 196 (depth 4, qbits 49, dnum 1) | N=2^14, 4x49, P 4x60 | 1.15 |
| 4 | N=2^14, 4x60, P 3x60 | CERT 7.0 / CERT 8.1 | N=2^14, 4x60, P 3x60 | depth 4, qbits 60 | 7.0 | +0 | +0 | 1.00 | 236 (depth 4, qbits 59) | N=2^14, 4x58, P 2x60 | 0.94 |
| 5 | N=2^14, 4x60, P 3x60 | over 39.6 / over 38.5 | N=2^14, 5x58, P 2x60 | depth 6, qbits 58 | 10.9 | +50 | +1 | 1.28 | 290 (depth 6, qbits 58) | N=2^14, 5x58, P 2x60 | 1.29 |
| 6 | N=2^15, 5x60, P 3x60 | over 39.0 / over 37.5 | N=2^15, 6x59, P 6x60 | depth 7, qbits 59, dnum 1 | 14.9 | +54 | +1 | 1.08 | 348 (depth 7, qbits 58, dnum 1) | N=2^15, 6x59, P 6x60 | 1.08 |
| 7 | N=2^15, 5x60, P 3x60 | over 39.0 / over 37.5 | N=2^15, 7x59, P 7x60 | depth 9, qbits 59, dnum 1 | 25.6 | +113 | +2 | 1.28 | 406 (depth 9, qbits 58, dnum 1) | N=2^15, 7x59, P 7x60 | 1.28 |
| 8 | N=2^15, 6x60, P 3x60 | over 27.6 / over 26.1 | N=2^15, 8x59, P 4x60 | depth 11, qbits 59, dnum 2 | 36.2 | +112 | +2 | 1.26 | 448 (depth 10, qbits 56, dnum 2) | N=2^15, 8x59, P 4x60 | 1.25 |
| 9 | N=2^15, 7x60, P 4x60 | over 15.9 / over 13.9 | N=2^15, 9x59, P 5x60 | depth 12, qbits 59, dnum 2 | 46.5 | +111 | +2 | 1.23 | 504 (depth 11, qbits 56, dnum 2) | N=2^15, 9x59, P 5x60 | 1.23 |
| 10 | N=2^15, 7x60, P 4x60 | over 15.9 / over 13.9 | N=2^15, 9x60, P 4x60 | depth 12, qbits 60 | 6.6 | +120 | +2 | 1.29 | 540 (depth 12, qbits 60) | N=2^15, 9x60, P 4x60 | 1.29 |
| 11 | N=2^15, 8x60, P 4x60 | over 4.3 / over 1.8 | N=2^15, 10x59, P 4x60 | depth 14, qbits 59 | 8.3 | +110 | +2 | 1.27 | 590 (depth 14, qbits 59) | N=2^15, 10x58, P 5x60 | 1.20 |
| 12 | N=2^15, 9x60, P 4x60 | over 42.0 / over 40.7 | N=2^15, 11x58, P 4x60 | depth 15, qbits 58 | 7.3 | +98 | +2 | 1.23 | 638 (depth 15, qbits 58) | N=2^15, 11x58, P 4x60 | 1.23 |

### BFV HPSPOVERQLEVELED BV, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 24.7 / CERT 24.7 | N=2^12, 2x54 | depth 1, qbits 54 | 19.7 | -12 | +0 | 0.48 | 76 (depth 1, qbits 38) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 24.7 / CERT 24.7 | N=2^13, 3x60 | depth 2, qbits 60 | 24.7 | +0 | +0 | 1.00 | 123 (depth 2, qbits 41) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 17.3 / over 17.3 | N=2^13, 4x54 | depth 4, qbits 54 | 30.1 | +36 | +1 | 1.42 | 164 (depth 3, qbits 41) | N=2^13, 4x54 | 1.42 |
| 4 | N=2^14, 4x60 | over 4.9 / over 4.9 | N=2^13, 5x43 | depth 5, qbits 43 | 6.9 | -25 | +1 | 0.61 | 210 (depth 4, qbits 42) | N=2^13, 5x43 | 0.61 |
| 5 | N=2^14, 4x60 | over 4.9 / over 4.9 | N=2^14, 5x60 | depth 6, qbits 60 | 10.7 | +60 | +1 | 1.39 | 285 (depth 6, qbits 57) | N=2^14, 5x60 | 1.39 |
| 6 | N=2^14, 5x60 | over 33.3 / over 33.3 | N=2^14, 6x60 | depth 8, qbits 60 | 26.4 | +60 | +1 | 1.30 | 324 (depth 7, qbits 54) | N=2^14, 6x60 | 1.31 |
| 7 | N=2^14, 5x60 | over 33.3 / over 33.3 | N=2^14, 7x60 | depth 10, qbits 60 | 42.1 | +120 | +2 | 1.68 | 364 (depth 8, qbits 52) | N=2^14, 7x60 | 1.68 |
| 8 | N=2^14, 6x60 | over 17.6 / over 17.6 | N=2^14, 8x54 | depth 10, qbits 54 | 21.9 | +72 | +2 | 1.52 | 408 (depth 10, qbits 51) | N=2^14, 8x54 | 1.53 |
| 9 | N=2^14, 6x60 | over 17.6 / over 17.6 | N=2^14, 14x31 | depth 12, qbits 31 | 0.3 | +74 | +8 | 3.43 | 434 (depth 12, qbits 31) | N=2^14, 12x36 | 2.70 |
| 10 | N=2^14, 7x60 | over 1.9 / over 1.9 | N=2^15, 9x60 | depth 13, qbits 60 | 12.7 | +120 | +2 | 3.17 | 531 (depth 13, qbits 59) | N=2^15, 9x60 | 3.18 |
| 11 | N=2^15, 8x60 | over 1.1 / over 1.1 | N=2^15, 10x60 | depth 15, qbits 60 | 26.5 | +120 | +2 | 1.47 | 570 (depth 14, qbits 57) | N=2^15, 10x60 | 1.47 |
| 12 | N=2^15, 8x60 | over 1.1 / over 1.1 | N=2^15, 11x60 | depth 16, qbits 60 | 40.4 | +180 | +3 | 1.74 | 616 (depth 15, qbits 56) | N=2^15, 11x60 | 1.74 |

### BFV HPSPOVERQLEVELED BV, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 21.1 / CERT 21.1 | N=2^12, 2x54 | depth 1, qbits 54 | 16.1 | -12 | +0 | 0.48 | 86 (depth 1, qbits 43) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 21.1 / CERT 21.1 | N=2^13, 3x60 | depth 2, qbits 60 | 21.1 | +0 | +0 | 1.00 | 132 (depth 2, qbits 44) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | - / - | N=2^13, 4x54 | depth 4, qbits 54 | 22.9 | +36 | +1 | 1.41 | 196 (depth 3, qbits 49) | N=2^13, 4x54 | 1.41 |
| 4 | N=2^14, 4x60 | over 15.6 / over 15.6 | N=2^14, 5x60 | depth 5, qbits 60 | 44.0 | +60 | +1 | 1.36 | 245 (depth 5, qbits 49) | N=2^14, 5x60 | 1.36 |
| 5 | N=2^14, 5x60 | over 3.6 / over 3.6 | N=2^14, 6x60 | depth 7, qbits 60 | 56.0 | +60 | +1 | 1.30 | 294 (depth 6, qbits 49) | N=2^14, 6x60 | 1.30 |
| 6 | N=2^14, 5x60 | - / - | N=2^14, 6x60 | depth 7, qbits 60 | 8.5 | +60 | +1 | 1.32 | 348 (depth 7, qbits 58) | N=2^14, 6x60 | 1.32 |
| 7 | N=2^14, 6x60 | over 39.1 / over 39.1 | N=2^14, 7x60 | depth 9, qbits 60 | 20.6 | +60 | +1 | 1.27 | 406 (depth 8, qbits 58) | N=2^14, 7x60 | 1.27 |
| 8 | N=2^14, 6x60 | - / - | N=2^14, 9x48 | depth 10, qbits 48 | 6.8 | +72 | +3 | 1.83 | 432 (depth 10, qbits 48) | N=2^14, 9x48 | 1.83 |
| 9 | N=2^14, 7x60 | over 27.0 / over 27.0 | N=2^15, 9x60 | depth 12, qbits 60 | 30.0 | +120 | +2 | 3.18 | 504 (depth 11, qbits 56) | N=2^15, 9x60 | 3.20 |
| 10 | N=2^15, 8x60 | over 29.8 / over 29.8 | N=2^15, 10x60 | depth 13, qbits 60 | 40.3 | +120 | +2 | 1.47 | 560 (depth 12, qbits 56) | N=2^15, 10x60 | 1.47 |
| 11 | N=2^15, 8x60 | - / - | N=2^15, 11x60 | depth 15, qbits 60 | 50.5 | +180 | +3 | 1.76 | 616 (depth 14, qbits 56) | N=2^15, 11x60 | 1.76 |
| 12 | N=2^15, 9x60 | over 19.6 / over 19.6 | N=2^15, 11x60 | depth 15, qbits 60 | 0.9 | +120 | +2 | 1.43 | 660 (depth 15, qbits 60) | N=2^15, 11x60 | 1.43 |

### BFV HPSPOVERQLEVELED BV, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 20.8 / CERT 20.8 | N=2^12, 2x54 | depth 1, qbits 54 | 15.8 | -12 | +0 | 0.48 | 80 (depth 1, qbits 40) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 24.7 / CERT 24.7 | N=2^13, 3x60 | depth 2, qbits 60 | 24.7 | +0 | +0 | 1.00 | 126 (depth 2, qbits 42) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 16.3 / over 16.3 | N=2^13, 4x54 | depth 4, qbits 54 | 31.1 | +36 | +1 | 1.45 | 168 (depth 3, qbits 42) | N=2^13, 4x54 | 1.45 |
| 4 | N=2^14, 4x60 | over 2.9 / over 2.9 | N=2^13, 5x43 | depth 5, qbits 43 | 6.7 | -25 | +1 | 0.62 | 210 (depth 4, qbits 42) | N=2^13, 5x43 | 0.62 |
| 5 | N=2^14, 4x60 | over 2.9 / over 2.9 | N=2^14, 5x60 | depth 6, qbits 60 | 13.7 | +60 | +1 | 1.37 | 280 (depth 6, qbits 56) | N=2^14, 5x60 | 1.37 |
| 6 | N=2^14, 5x60 | over 29.3 / over 29.3 | N=2^14, 6x60 | depth 8, qbits 60 | 30.4 | +60 | +1 | 1.31 | 318 (depth 7, qbits 53) | N=2^14, 6x60 | 1.31 |
| 7 | N=2^14, 5x60 | over 29.3 / over 29.3 | N=2^14, 7x60 | depth 10, qbits 60 | 47.1 | +120 | +2 | 1.67 | 357 (depth 8, qbits 51) | N=2^14, 7x60 | 1.67 |
| 8 | N=2^14, 6x60 | over 12.6 / over 12.6 | N=2^14, 7x60 | depth 10, qbits 60 | 4.1 | +60 | +1 | 1.27 | 420 (depth 10, qbits 60) | N=2^14, 7x60 | 1.27 |
| 9 | N=2^14, 6x60 | over 12.6 / over 12.6 | N=2^14, 12x36 | depth 11, qbits 36 | 2.5 | +72 | +6 | 2.71 | 432 (depth 11, qbits 36) | N=2^14, 11x39 | 2.39 |
| 10 | N=2^14, 7x60 | over 38.9 / over 38.9 | N=2^15, 9x60 | depth 13, qbits 60 | 20.7 | +120 | +2 | 3.15 | 522 (depth 12, qbits 58) | N=2^15, 9x60 | 3.16 |
| 11 | N=2^15, 8x60 | over 39.1 / over 39.1 | N=2^15, 10x60 | depth 15, qbits 60 | 35.5 | +120 | +2 | 1.44 | 560 (depth 14, qbits 56) | N=2^15, 10x60 | 1.44 |
| 12 | N=2^15, 8x60 | over 39.1 / over 39.1 | N=2^15, 11x60 | depth 16, qbits 60 | 50.4 | +180 | +3 | 1.70 | 605 (depth 15, qbits 55) | N=2^15, 11x60 | 1.70 |

### BFV HPSPOVERQLEVELED BV, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 2x60 | CERT 17.2 / CERT 17.2 | N=2^12, 2x54 | depth 1, qbits 54 | 12.2 | -12 | +0 | 0.48 | 100 (depth 1, qbits 50) | N=2^12, 2x54 | 0.48 |
| 2 | N=2^13, 3x60 | CERT 21.1 / CERT 21.1 | N=2^13, 3x60 | depth 2, qbits 60 | 21.1 | +0 | +0 | 1.00 | 150 (depth 2, qbits 50) | N=2^13, 3x60 | 1.00 |
| 3 | N=2^13, 3x60 | over 23.5 / over 23.5 | N=2^13, 4x54 | depth 4, qbits 54 | 23.9 | +36 | +1 | 1.45 | 196 (depth 3, qbits 49) | N=2^13, 4x54 | 1.44 |
| 4 | N=2^14, 4x60 | over 13.6 / over 13.6 | N=2^14, 5x60 | depth 5, qbits 60 | 46.0 | +60 | +1 | 1.38 | 245 (depth 5, qbits 49) | N=2^14, 5x60 | 1.37 |
| 5 | N=2^14, 5x60 | over 0.6 / over 0.6 | N=2^14, 6x60 | depth 7, qbits 60 | 59.0 | +60 | +1 | 1.29 | 294 (depth 6, qbits 49) | N=2^14, 6x60 | 1.29 |
| 6 | N=2^14, 5x60 | - / - | N=2^14, 6x60 | depth 7, qbits 60 | 12.5 | +60 | +1 | 1.31 | 348 (depth 7, qbits 58) | N=2^14, 6x60 | 1.30 |
| 7 | N=2^14, 6x60 | over 34.1 / over 34.1 | N=2^14, 7x60 | depth 9, qbits 60 | 25.6 | +60 | +1 | 1.27 | 406 (depth 8, qbits 58) | N=2^14, 7x60 | 1.28 |
| 8 | N=2^14, 6x60 | - / - | N=2^14, 9x48 | depth 10, qbits 48 | 10.2 | +72 | +3 | 1.82 | 432 (depth 10, qbits 48) | N=2^14, 9x48 | 1.83 |
| 9 | N=2^14, 7x60 | over 21.0 / over 21.0 | N=2^15, 9x60 | depth 12, qbits 60 | 37.0 | +120 | +2 | 3.17 | 504 (depth 11, qbits 56) | N=2^15, 9x60 | 3.17 |
| 10 | N=2^15, 8x60 | over 22.8 / over 22.8 | N=2^15, 10x60 | depth 13, qbits 60 | 48.3 | +120 | +2 | 1.45 | 560 (depth 12, qbits 56) | N=2^15, 10x60 | 1.45 |
| 11 | N=2^15, 8x60 | - / - | N=2^15, 11x60 | depth 15, qbits 60 | 59.5 | +180 | +3 | 1.72 | 616 (depth 14, qbits 56) | N=2^15, 11x60 | 1.71 |
| 12 | N=2^15, 9x60 | over 11.6 / over 11.6 | N=2^15, 11x60 | depth 15, qbits 60 | 10.9 | +120 | +2 | 1.43 | 649 (depth 15, qbits 59) | N=2^15, 11x60 | 1.42 |

### BFV HPSPOVERQLEVELED HYBRID, chain, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 38.6 / CERT 41.1 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 33.6 | -8 | +0 | 0.44 | 100 (depth 1, qbits 50) | N=2^13, 2x56, P 1x60 | 0.44 |
| 2 | N=2^14, 2x60, P 2x60 | over 5.4 / over 2.9 | N=2^13, 3x52, P 1x60 | depth 3, qbits 52, dnum 3 | 35.5 | +36 | +1 | 0.69 | 123 (depth 2, qbits 41, dnum 3) | N=2^13, 3x52, P 1x60 | 0.69 |
| 3 | N=2^14, 3x60, P 3x60 | CERT 10.6 / CERT 13.1 | N=2^14, 3x60, P 2x60 | depth 3, qbits 60, dnum 3 | 10.6 | +0 | +0 | 1.03 | 171 (depth 3, qbits 57, dnum 3) | N=2^14, 3x56, P 1x60 | 0.94 |
| 4 | N=2^14, 3x60, P 3x60 | over 33.5 / over 30.9 | N=2^14, 4x56, P 1x60 | depth 5, qbits 56, dnum 4 | 10.6 | +44 | +1 | 1.35 | 216 (depth 4, qbits 54, dnum 4) | N=2^14, 4x56, P 1x60 | 1.36 |
| 5 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 5x58, P 2x60 | depth 7, qbits 58 | 32.6 | +50 | +1 | 1.27 | 260 (depth 6, qbits 52) | N=2^14, 5x58, P 2x60 | 1.27 |
| 6 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 6x53, P 2x60 | depth 8, qbits 53 | 16.5 | +78 | +2 | 1.54 | 306 (depth 7, qbits 51) | N=2^14, 6x53, P 2x60 | 1.54 |
| 7 | N=2^15, 5x60, P 3x60 | over 14.4 / over 11.5 | N=2^15, 7x58, P 3x60 | depth 10, qbits 58 | 45.6 | +106 | +2 | 1.41 | 364 (depth 9, qbits 52) | N=2^15, 6x60, P 3x60 | 1.25 |
| 8 | N=2^15, 6x60, P 3x60 | over 0.4 / over 43.6 | N=2^15, 7x60, P 4x60 | depth 10, qbits 60 | 13.6 | +60 | +1 | 1.22 | 413 (depth 10, qbits 59) | N=2^15, 7x58, P 3x60 | 1.13 |
| 9 | N=2^15, 6x60, P 3x60 | over 0.4 / over 43.6 | N=2^15, 8x58, P 2x60 | depth 12, qbits 58, dnum 4 | 11.5 | +104 | +2 | 1.38 | 456 (depth 12, qbits 57, dnum 4) | N=2^15, 8x58, P 2x60 | 1.37 |
| 10 | N=2^15, 7x60, P 4x60 | over 32.4 / over 29.7 | N=2^15, 9x58, P 3x60 | depth 13, qbits 58 | 23.5 | +102 | +2 | 1.31 | 504 (depth 13, qbits 56) | N=2^15, 9x58, P 3x60 | 1.30 |
| 11 | N=2^15, 7x60, P 4x60 | over 32.4 / over 29.7 | N=2^15, 10x59, P 4x60 | depth 15, qbits 59 | 45.5 | +170 | +3 | 1.57 | 550 (depth 14, qbits 55) | N=2^15, 10x59, P 4x60 | 1.57 |
| 12 | N=2^15, 8x60, P 4x60 | over 18.5 / over 15.8 | N=2^15, 11x56, P 3x60 | depth 17, qbits 56, dnum 4 | 25.5 | +136 | +3 | 1.48 | 616 (depth 17, qbits 56, dnum 4) | N=2^15, 10x59, P 4x60 | 1.32 |

### BFV HPSPOVERQLEVELED HYBRID, chain, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 30.6 / CERT 31.5 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 25.0 | -8 | +0 | 0.44 | 88 (depth 1, qbits 44) | N=2^13, 2x56, P 1x60 | 0.44 |
| 2 | N=2^14, 2x60, P 2x60 | over 17.0 / over 16.0 | N=2^13, 3x52, P 1x60 | depth 2, qbits 52, dnum 3 | 23.4 | +36 | +1 | 0.65 | 150 (depth 2, qbits 50, dnum 3) | N=2^13, 3x52, P 1x60 | 0.65 |
| 3 | N=2^14, 3x60, P 3x60 | over 3.9 / over 2.0 | N=2^14, 4x56, P 1x60 | depth 4, qbits 56, dnum 4 | 39.2 | +44 | +1 | 1.34 | 196 (depth 4, qbits 49, dnum 4) | N=2^14, 4x56, P 1x60 | 1.34 |
| 4 | N=2^14, 4x60, P 3x60 | CERT 8.0 / CERT 9.1 | N=2^14, 4x60, P 2x60 | depth 4, qbits 60, dnum 4 | 8.0 | +0 | +0 | 1.07 | 236 (depth 4, qbits 59, dnum 4) | N=2^14, 4x60, P 2x60 | 1.07 |
| 5 | N=2^14, 4x60, P 3x60 | over 39.6 / over 38.5 | N=2^14, 5x58, P 2x60 | depth 6, qbits 58 | 10.9 | +50 | +1 | 1.30 | 290 (depth 6, qbits 58) | N=2^14, 5x58, P 2x60 | 1.30 |
| 6 | N=2^15, 5x60, P 3x60 | over 40.0 / over 38.5 | N=2^15, 6x58, P 2x60 | depth 7, qbits 58 | 8.3 | +48 | +1 | 1.20 | 348 (depth 7, qbits 58) | N=2^15, 6x58, P 2x60 | 1.20 |
| 7 | N=2^15, 5x60, P 3x60 | over 40.0 / over 38.5 | N=2^15, 7x58, P 3x60 | depth 9, qbits 58 | 16.4 | +106 | +2 | 1.50 | 406 (depth 9, qbits 58) | N=2^15, 7x58, P 3x60 | 1.48 |
| 8 | N=2^15, 6x60, P 3x60 | over 29.6 / over 28.1 | N=2^15, 8x58, P 2x60 | depth 10, qbits 58, dnum 4 | 25.3 | +104 | +2 | 1.44 | 448 (depth 10, qbits 56, dnum 4) | N=2^15, 8x58, P 2x60 | 1.44 |
| 9 | N=2^15, 7x60, P 4x60 | over 18.9 / over 16.9 | N=2^15, 9x58, P 3x60 | depth 12, qbits 58 | 33.2 | +102 | +2 | 1.34 | 504 (depth 11, qbits 56) | N=2^15, 9x58, P 3x60 | 1.34 |
| 10 | N=2^15, 7x60, P 4x60 | over 18.9 / over 16.9 | N=2^15, 9x60, P 4x60 | depth 12, qbits 60 | 1.6 | +120 | +2 | 1.43 | 540 (depth 12, qbits 60) | N=2^15, 9x60, P 4x60 | 1.43 |
| 11 | N=2^15, 8x60, P 4x60 | over 8.3 / over 5.8 | N=2^15, 10x59, P 4x60 | depth 14, qbits 59 | 2.4 | +110 | +2 | 1.33 | 590 (depth 14, qbits 59) | N=2^15, 10x59, P 4x60 | 1.33 |
| 12 | N=2^15, 9x60, P 4x60 | over 48.0 / over 46.7 | N=2^15, 11x58, P 3x60 | depth 16, qbits 58, dnum 4 | 0.3 | +98 | +2 | 1.31 | 638 (depth 16, qbits 58, dnum 4) | N=2^15, 11x58, P 3x60 | 1.30 |

### BFV HPSPOVERQLEVELED HYBRID, poly, t = 65537

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 35.6 / CERT 38.1 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 30.6 | -8 | +0 | 0.41 | 100 (depth 1, qbits 50) | N=2^13, 2x56, P 1x60 | 0.42 |
| 2 | N=2^14, 2x60, P 2x60 | over 8.4 / over 5.9 | N=2^13, 3x52, P 1x60 | depth 3, qbits 52, dnum 3 | 32.5 | +36 | +1 | 0.67 | 126 (depth 2, qbits 42, dnum 3) | N=2^13, 3x52, P 1x60 | 0.68 |
| 3 | N=2^14, 3x60, P 3x60 | CERT 8.6 / CERT 11.1 | N=2^14, 3x60, P 2x60 | depth 3, qbits 60, dnum 3 | 8.6 | +0 | +0 | 1.04 | 174 (depth 3, qbits 58, dnum 3) | N=2^14, 3x60, P 2x60 | 1.04 |
| 4 | N=2^14, 3x60, P 3x60 | over 34.5 / over 31.9 | N=2^14, 4x56, P 1x60 | depth 5, qbits 56, dnum 4 | 9.6 | +44 | +1 | 1.35 | 216 (depth 4, qbits 54, dnum 4) | N=2^14, 4x56, P 1x60 | 1.34 |
| 5 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 5x58, P 2x60 | depth 7, qbits 58 | 32.6 | +50 | +1 | 1.27 | 260 (depth 6, qbits 52) | N=2^14, 5x58, P 2x60 | 1.26 |
| 6 | N=2^14, 4x60, P 3x60 | over 17.4 / over 14.3 | N=2^14, 6x53, P 2x60 | depth 8, qbits 53 | 17.5 | +78 | +2 | 1.52 | 306 (depth 7, qbits 51) | N=2^14, 6x53, P 2x60 | 1.52 |
| 7 | N=2^15, 5x60, P 3x60 | over 13.4 / over 10.5 | N=2^15, 6x60, P 3x60 | depth 8, qbits 60 | 1.6 | +60 | +1 | 1.25 | 360 (depth 8, qbits 60) | N=2^15, 6x60, P 3x60 | 1.25 |
| 8 | N=2^15, 6x60, P 3x60 | over 43.4 / over 40.6 | N=2^15, 7x58, P 3x60 | depth 10, qbits 58 | 2.6 | +46 | +1 | 1.12 | 406 (depth 10, qbits 58) | N=2^15, 7x58, P 3x60 | 1.13 |
| 9 | N=2^15, 6x60, P 3x60 | over 43.4 / over 40.6 | N=2^15, 8x58, P 2x60 | depth 12, qbits 58, dnum 4 | 15.5 | +104 | +2 | 1.36 | 456 (depth 12, qbits 57, dnum 4) | N=2^15, 8x58, P 2x60 | 1.37 |
| 10 | N=2^15, 7x60, P 4x60 | over 28.4 / over 25.7 | N=2^15, 9x58, P 3x60 | depth 13, qbits 58 | 28.5 | +102 | +2 | 1.29 | 495 (depth 13, qbits 55) | N=2^15, 9x58, P 3x60 | 1.29 |
| 11 | N=2^15, 7x60, P 4x60 | over 28.4 / over 25.7 | N=2^15, 9x60, P 4x60 | depth 14, qbits 60 | 1.6 | +120 | +2 | 1.39 | 540 (depth 14, qbits 60) | N=2^15, 9x60, P 4x60 | 1.39 |
| 12 | N=2^15, 8x60, P 4x60 | over 13.5 / over 10.8 | N=2^15, 10x59, P 4x60 | depth 15, qbits 59 | 6.5 | +110 | +2 | 1.30 | 590 (depth 15, qbits 59) | N=2^15, 10x59, P 4x60 | 1.30 |

### BFV HPSPOVERQLEVELED HYBRID, poly, t = 786433

| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | N=2^14, 2x60, P 2x60 | CERT 27.6 / CERT 28.5 | N=2^13, 2x56, P 1x60 | depth 1, qbits 56 | 22.0 | -8 | +0 | 0.41 | 90 (depth 1, qbits 45) | N=2^13, 2x56, P 1x60 | 0.41 |
| 2 | N=2^14, 2x60, P 2x60 | over 20.0 / over 19.0 | N=2^13, 3x52, P 1x60 | depth 2, qbits 52, dnum 3 | 20.4 | +36 | +1 | 0.65 | 150 (depth 2, qbits 50, dnum 3) | N=2^13, 3x52, P 1x60 | 0.66 |
| 3 | N=2^14, 3x60, P 3x60 | over 5.9 / over 4.0 | N=2^14, 4x56, P 1x60 | depth 4, qbits 56, dnum 4 | 37.2 | +44 | +1 | 1.35 | 196 (depth 4, qbits 49, dnum 4) | N=2^14, 4x56, P 1x60 | 1.34 |
| 4 | N=2^14, 4x60, P 3x60 | CERT 7.0 / CERT 8.1 | N=2^14, 4x60, P 2x60 | depth 4, qbits 60, dnum 4 | 7.0 | +0 | +0 | 1.11 | 236 (depth 4, qbits 59, dnum 4) | N=2^14, 4x60, P 2x60 | 1.12 |
| 5 | N=2^14, 4x60, P 3x60 | over 39.6 / over 38.5 | N=2^14, 5x58, P 2x60 | depth 6, qbits 58 | 10.9 | +50 | +1 | 1.29 | 290 (depth 6, qbits 58) | N=2^14, 5x58, P 2x60 | 1.28 |
| 6 | N=2^15, 5x60, P 3x60 | over 39.0 / over 37.5 | N=2^15, 6x58, P 2x60 | depth 7, qbits 58 | 9.3 | +48 | +1 | 1.17 | 348 (depth 7, qbits 58) | N=2^15, 6x58, P 2x60 | 1.16 |
| 7 | N=2^15, 5x60, P 3x60 | over 39.0 / over 37.5 | N=2^15, 7x58, P 3x60 | depth 9, qbits 58 | 18.4 | +106 | +2 | 1.45 | 406 (depth 9, qbits 58) | N=2^15, 7x58, P 3x60 | 1.44 |
| 8 | N=2^15, 6x60, P 3x60 | over 27.6 / over 26.1 | N=2^15, 8x58, P 2x60 | depth 10, qbits 58, dnum 4 | 28.3 | +104 | +2 | 1.40 | 448 (depth 10, qbits 56, dnum 4) | N=2^15, 8x58, P 2x60 | 1.40 |
| 9 | N=2^15, 7x60, P 4x60 | over 15.9 / over 13.9 | N=2^15, 9x58, P 3x60 | depth 12, qbits 58 | 37.2 | +102 | +2 | 1.31 | 504 (depth 11, qbits 56) | N=2^15, 9x58, P 3x60 | 1.32 |
| 10 | N=2^15, 7x60, P 4x60 | over 15.9 / over 13.9 | N=2^15, 9x60, P 4x60 | depth 12, qbits 60 | 6.6 | +120 | +2 | 1.39 | 540 (depth 12, qbits 60) | N=2^15, 9x60, P 4x60 | 1.39 |
| 11 | N=2^15, 8x60, P 4x60 | over 4.3 / over 1.8 | N=2^15, 10x59, P 4x60 | depth 14, qbits 59 | 8.3 | +110 | +2 | 1.30 | 590 (depth 14, qbits 59) | N=2^15, 10x59, P 4x60 | 1.30 |
| 12 | N=2^15, 9x60, P 4x60 | over 42.0 / over 40.7 | N=2^15, 11x58, P 3x60 | depth 16, qbits 58, dnum 4 | 7.3 | +98 | +2 | 1.30 | 638 (depth 16, qbits 58, dnum 4) | N=2^15, 11x58, P 3x60 | 1.29 |
