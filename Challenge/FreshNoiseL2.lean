import Challenge.FreshNoise

/-!
# Challenge.FreshNoiseL2 — the tail of a fresh encryption from `ℓ₂` norms and sub-Gaussian samplers   (LOCKED statements; proofs in `Validation/FreshNoise/L2.lean`)

`Challenge.FreshNoise.freshError_tail` charges every one of the `2N + 1` terms of a coefficient of
`e_pk·u + e₁ + e₂·s` at the square of the product of two *support bounds* (for OpenFHE `39²` per
term). That is sound and far from tight: the public-key error is treated as if every one of its
coefficients sat at its support bound, and each sampler as if it were a fair coin on `±` that bound.
This file adds a second tail theorem, alongside the first (which is unchanged):

* the fixed key enters through the squared `ℓ₂` norms `‖e_pk‖₂² ≤ E2`, `‖s‖₂² ≤ S2`
  (`Spec.Encrypt.normSq`), and
* the samplers through sub-Gaussian variance proxies `V_u`, `V_1`, `V_2` (`SubGaussSamplerOK`),

and the variance proxy of a coefficient is `V = V_u·E2 + V_1 + V_2·S2`
(`Spec.Encrypt.varProxyL2`).

**Derivation.** Coefficient `k` of `e_pk·u` in `ℤ[X]/(X^N + 1)` is `∑_i ±e_pk,(k−i mod N)·u_i`:
every coefficient of `u` appears once, and so does every coefficient of `e_pk`, with a sign.
For independent `u_i` of proxy `V_u` this weighted sum has proxy `V_u·∑_j e_pk,j² = V_u·‖e_pk‖₂²`.
The same for `e₂·s` with `‖s‖₂²`; and `e₁,k` contributes `V_1`. The `2N + 1` coordinates involved
are distinct and independent, so the proxies add. The union bound over the `N` coefficients and
the two signs gives `2N·exp(−ε²/(2V))` for the deviation of each coefficient from its mean.

**The means.** The proxies are those of the coordinates *about their means*, and the means are
assumed at most `μ = mn/md` in absolute value, not zero. The mean of coefficient `k` is then at
most `μ·(‖e_pk‖₁ + 1 + ‖s‖₁)` in absolute value, and `‖a‖₁ ≤ ‖a‖₂²` for an integer polynomial
(`|x| ≤ x²` for every integer `x`), so at most `μ·(E2 + 1 + S2)`: the tail bound holds for the
threshold `ε + μ·(E2 + 1 + S2)`. (Cauchy–Schwarz would give the smaller `μ·(√(N·E2) + 1 +
√(N·S2))`; with means as small as `3431/2⁶⁴`, either is far below 1, and
the computed `Spec.Encrypt.meanDrift` rounds up to 1.) With `mn = 0` the threshold is `ε`.

**The hypotheses on the key are hypotheses.** `normSq e ≤ E2` and `normSq s ≤ S2` are assumptions
of every theorem here about the one fixed key; nothing here says a generated key meets them. A
frontend can discharge them (i) by computing both sums from an exported key, or (ii) by a stated
high-probability event over key generation (e.g. for `N` independent errors of variance `σ²`,
`‖e_pk‖₂² ≤ N·σ²·(1 + margin)` except with a probability that has to be bounded separately and
added to the failure probability), or (iii) deterministically from support bounds,
`normSq a ≤ N·‖a‖∞²` (`normSq_le`): for a ternary secret `S2 = N` always holds. With (iii) for
both and the squared support bounds as proxies the new bound is the old one
(`varProxyL2_support`, `subGaussSamplerOK_of_samplerOK`).

**The hypothesis on the samplers is a hypothesis.** `SubGaussSamplerOK` asks that each of the `3N`
coefficients, minus its mean, has Mathlib's `ProbabilityTheory.HasSubgaussianMGF` with the stated
proxy, i.e. `E[exp(t·(X − E X))] ≤ exp(V·t²/2)` for every real `t`; that its mean is at most
`mn/md` in absolute value; and that the `3N` coefficients are independent. Proved here: bounded
coefficients satisfy it with the square of the bound and the same mean bound (Hoeffding's lemma,
`subGaussSamplerOK_of_samplerOK`), so every sampler of the support-bound model is an instance.
NOT proved here, and assumed by anyone who instantiates the proxies below the squared support
bound: that a centred discrete Gaussian of parameter `σ`, truncated symmetrically, has proxy
`σ²` (a known fact: Micciancio–Peikert 2012, Lemma 2.8, for the untruncated one; symmetric
truncation only lowers `E[cosh(t·X)]`), that the same proxy is valid about its mean for the
sampler a library implements, and that the uniform ternary distribution has proxy `2/3`. The proxies are natural numbers: an integer upper bound of the
real proxy is what is meant (ternary: use 1), and
`subGaussSamplerOK_mono` says a larger number is always allowed.

The composition pins are the analogues of `Challenge.FreshNoise.fresh_certified`,
`fresh_certified_kappa` and `fresh_kappa_decrypts`. `Spec.Encrypt.epsFor` is generic in the
variance proxy, so it and its pin `Challenge.FreshNoise.epsFor_spec` are reused as they are; the
only new trusted definitions are `Spec.Encrypt.normSq` and `Spec.Encrypt.varProxyL2`.
-/

namespace Challenge.FreshNoiseL2
open Spec NPoly Scheme Source Correct Spec.Encrypt Challenge.Headline MeasureTheory ProbabilityTheory
open Challenge.FreshNoise

variable {N : ℕ}

/-! ## 1. The `ℓ₂` norm and the variance proxy -/

/-- The squared `ℓ₂` norm is at most `N` times the square of the `ℓ∞` norm. (So a support bound
discharges the `ℓ₂` hypotheses deterministically: `‖s‖₂² ≤ N` for every ternary secret.) -/
theorem normSq_le (a : IntPoly N) : normSq a ≤ N * normInf a ^ 2 := sorry

/-- With the `ℓ₂` bounds `N·B_k²`, `N·B_s²` implied by the support bounds, and the squared support
bounds as variance proxies, the `ℓ₂` variance proxy is the support-bound one. -/
theorem varProxyL2_support (N Bs Bk Bu B1 B2 : ℕ) :
    varProxyL2 (N * Bk ^ 2) (N * Bs ^ 2) (Bu ^ 2) (B1 ^ 2) (B2 ^ 2) = varProxy N Bs Bk Bu B1 B2 :=
  sorry

/-! ## 2. Sub-Gaussian samplers -/

/-- The variance proxy of each coordinate: `Vu` for `u`, `V1` for `e₁`, `V2` for `e₂`. -/
def coordProxy (N Vu V1 V2 : ℕ) : Fin N ⊕ Fin N ⊕ Fin N → ℕ :=
  Sum.elim (fun _ => Vu) (Sum.elim (fun _ => V1) (fun _ => V2))

/-- What is assumed of one encryption's randomness, on an arbitrary probability space: its `3N`
coefficients are (jointly) independent random variables; each, minus its mean, is sub-Gaussian
with its variance proxy in Mathlib's sense, `ProbabilityTheory.HasSubgaussianMGF Y c μ` with
`c : ℝ≥0`: `exp(t·Y)` is integrable and `E[exp(t·Y)] ≤ exp(c·t²/2)`, for every real `t`, here for
`Y = X − E[X]` (so `X` has variance at most `c`); and each has mean at most `mn/md` in absolute
value (`mn = 0`: mean zero, and then `X` itself is sub-Gaussian). The proxies are natural numbers
`Vu`, `V1`, `V2`, upper bounds of the samplers' real proxies. No distribution is named. -/
structure SubGaussSamplerOK {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Vu V1 V2 mn md : ℕ)
    (u e₁ e₂ : Ω → IntPoly N) : Prop where
  indep : iIndepFun (fun j ω => (coords u e₁ e₂ j ω : ℝ)) μ
  subG : ∀ j, HasSubgaussianMGF
    (fun ω => (coords u e₁ e₂ j ω : ℝ) - ∫ ω', (coords u e₁ e₂ j ω' : ℝ) ∂μ)
    ((coordProxy N Vu V1 V2 j : ℕ) : NNReal) μ
  mean : ∀ j, |∫ ω, (coords u e₁ e₂ j ω : ℝ) ∂μ| ≤ (mn : ℝ) / md

/-- **Bounded samplers are sub-Gaussian about their means** (Hoeffding's lemma): a coefficient
with values in `[−B, B]`, minus its mean, has variance proxy `B²` (half the range, squared). So
every randomness meeting the support-bound assumption `SamplerOK` meets `SubGaussSamplerOK` with
the squared bounds and the same mean bound. -/
theorem subGaussSamplerOK_of_samplerOK {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Bu B1 B2 mn md : ℕ) (u e₁ e₂ : Ω → IntPoly N)
    (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂) :
    SubGaussSamplerOK μ (Bu ^ 2) (B1 ^ 2) (B2 ^ 2) mn md u e₁ e₂ := sorry

/-- The proxies are upper bounds: larger ones are always allowed. -/
theorem subGaussSamplerOK_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Vu V1 V2 Vu' V1' V2' mn md : ℕ) (hu : Vu ≤ Vu') (h1 : V1 ≤ V1') (h2 : V2 ≤ V2')
    (u e₁ e₂ : Ω → IntPoly N) (h : SubGaussSamplerOK μ Vu V1 V2 mn md u e₁ e₂) :
    SubGaussSamplerOK μ Vu' V1' V2' mn md u e₁ e₂ := sorry

/-- **`SubGaussSamplerOK` is satisfiable** by the explicit product measure of
`Challenge.FreshNoise.samplerOK_rademacher`: `3N` independent fair coins, each coefficient `±` a
scale `Bu`, `B1`, `B2`, with variance proxies the squared scales (for a fair sign on `±B` the
proxy `B²` is also its variance, so no smaller proxy is possible), for every declared mean bound
(the coins have mean zero). -/
theorem subGaussSamplerOK_rademacher (N Bu B1 B2 mn md : ℕ) :
    SubGaussSamplerOK (N := N)
      (Measure.pi fun _ : Fin N ⊕ Fin N ⊕ Fin N =>
        ((2⁻¹ : NNReal) • (Measure.dirac true + Measure.dirac false) : Measure Bool))
      (Bu ^ 2) (B1 ^ 2) (B2 ^ 2) mn md
      (fun ω => ⟨fun i => coin Bu (ω (.inl i))⟩)
      (fun ω => ⟨fun i => coin B1 (ω (.inr (.inl i)))⟩)
      (fun ω => ⟨fun i => coin B2 (ω (.inr (.inr i)))⟩) := sorry

/-! ## 3. The tail bound -/

/-- **Tail bound from `ℓ₂` norms.** For any fixed secret and public-key error with
`‖s‖₂² ≤ S2`, `‖e_pk‖₂² ≤ E2`, and any randomness meeting `SubGaussSamplerOK` with proxies
`V_u`, `V_1`, `V_2` and mean bound `μ = mn/md`:
`P[‖e_pk·u + e₁ + e₂·s‖∞ ≥ ε + μ·(E2 + 1 + S2)] ≤ 2N·exp(−ε² / (2·V))` for every `ε ≥ 0`, with
`V = V_u·E2 + V_1 + V_2·S2`. With `mn = 0` the threshold is `ε`. -/
theorem freshError_tail_l2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hN : 0 < N) (s e : IntPoly N) (E2 S2 Vu V1 V2 mn md : ℕ)
    (hs : normSq s ≤ S2) (he : normSq e ≤ E2) (u e₁ e₂ : Ω → IntPoly N)
    (h : SubGaussSamplerOK μ Vu V1 V2 mn md u e₁ e₂) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε + (mn : ℝ) / md * (E2 + 1 + S2 : ℕ) ≤
        (normInf (freshError s e (u ω) (e₁ ω) (e₂ ω)) : ℝ)} ≤
      2 * N * Real.exp (-ε ^ 2 / (2 * (varProxyL2 E2 S2 Vu V1 V2 : ℝ))) := sorry

/-! ## 4. The noise headline and the certificates -/

/-- **The noise headline with probabilistic fresh noise, `ℓ₂` version.** As
`Challenge.FreshNoise.fresh_certified`, with the key bounded in `ℓ₂` (`normSq s ≤ S2`,
`normSq e ≤ E2`: hypotheses on the fixed key) and the randomness of each fresh input meeting
`SubGaussSamplerOK` with mean bound `mn/md`; the analysis at input noise at least
`Bp + t·(ε + D)` with `D` at least the drift `(mn/md)·(E2 + 1 + S2)`: the probability that there
exist stored plaintext polynomials within `Bp` and messages for which some output of some run is
wrong is at most `n · 2N · exp(−ε² / (2·V))`, `V = varProxyL2`. -/
theorem fresh_certified_l2 (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp ε D : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hnoise : freshNoise P.src.t Bp (ε + D) ≤ P.inputNoise)
    (fresh : List Var) (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (E2 S2 Vu V1 V2 mn md : ℕ) (hD : (mn : ℝ) / md * (E2 + 1 + S2 : ℕ) ≤ D)
    (s e b a : IntPoly P.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤
      fresh.length * (2 * P.src.N *
        Real.exp (-(ε : ℝ) ^ 2 / (2 * (varProxyL2 E2 S2 Vu V1 V2 : ℝ)))) := sorry

/-- With `ε = epsFor V (n·2N) κ + meanDrift (E2 + 1 + S2) mn md`, `V = varProxyL2` (positive)
and a positive denominator `md`, the failure probability of `fresh_certified_l2` is at most
`2^(−κ)`. (`epsFor` and `epsFor_spec` are those of the support-bound version: they are generic in
`V`.) -/
theorem fresh_certified_kappa_l2 (P : FullParams) (E : Trace.Budget) (prog : Program)
    (B Bp κ : ℕ) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (E2 S2 Vu V1 V2 mn md : ℕ)
    (hV : 0 < varProxyL2 E2 S2 Vu V1 V2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxyL2 E2 S2 Vu V1 V2)
      (fresh.length * (2 * P.src.N)) κ + meanDrift (E2 + 1 + S2) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (s e b a : IntPoly P.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-- **The probabilistic certificate with decryption, `ℓ₂` version**, as one statement: the
analogue of `Challenge.FreshNoise.fresh_kappa_decrypts`. For a fixed key with `normSq s ≤ S2`,
`normSq e ≤ E2` (hypotheses), under `freshOK?`, `certOK?` and the reference analysis at the input
noise `freshNoise t Bp (epsFor (varProxyL2 …) (n·2N) κ + meanDrift (E2 + 1 + S2) mn md)`, the
probability over the encryption randomness that there exist stored plaintext polynomials within
`Bp` and messages for which some output of some run fails to decrypt with `s` is at most
`2^(−κ)`. -/
theorem fresh_kappa_decrypts_l2 (P : FullParams) (E : Trace.Budget) (prog : Program)
    (B Bp κ : ℕ) (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (E2 S2 Vu V1 V2 mn md : ℕ)
    (hV : 0 < varProxyL2 E2 S2 Vu V1 V2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxyL2 E2 S2 Vu V1 V2)
      (fresh.length * (2 * P.src.N)) κ + meanDrift (E2 + 1 + S2) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s e b a : IntPoly P.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | DecryptFails P E prog switched fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-! ## 5. Guards -/

#guard normSq (⟨![3, -4, 0, 1]⟩ : IntPoly 4) == 26
#guard normInf (⟨![3, -4, 0, 1]⟩ : IntPoly 4) == 4
#guard varProxyL2 (16384 * 39 ^ 2) (16384 * 1 ^ 2) (1 ^ 2) (39 ^ 2) (39 ^ 2) ==
  varProxy 16384 1 39 1 39 39

-- Samplers at `N = 2¹⁴`, two fresh inputs: ternary `u` (proxy 1), errors with proxy 11.
-- ASSUMED of the key, not proved: `‖e_pk‖₂² ≤ 11·N = 180224`, and `‖s‖₂² ≤ N` (true of every
-- ternary secret, `normSq_le`).
-- Then `V = 360459` against the support-bound `49841649`, and the error bound `ε` drops from
-- 62204 (`2^15.92`) to 5290 (`2^12.37`) at `κ = 40`, from 74348 to 6323 at `κ = 64` and from
-- 99749 (`2^16.61`) to 8483 (`2^13.05`) at `κ = 128`: about 3.56 bits in each case.
#guard varProxyL2 (11 * 16384) 16384 1 11 11 == 360459
#guard epsFor (varProxyL2 (11 * 16384) 16384 1 11 11) (2 * (2 * 16384)) 40 == 5290
#guard epsFor (varProxyL2 (11 * 16384) 16384 1 11 11) (2 * (2 * 16384)) 64 == 6323
#guard epsFor (varProxyL2 (11 * 16384) 16384 1 11 11) (2 * (2 * 16384)) 128 == 8483
#guard freshNoise 65537 65536 8483 == 556015907
-- The drift for a mean bound of `3431/2⁶⁴` at these `ℓ₂` figures is 1.
#guard meanDrift (11 * 16384 + 1 + 16384) 3431 (2 ^ 64) == 1
#guard meanDrift (11 * 16384 + 1 + 16384) 0 1 == 0
#guard 11 * epsFor (varProxyL2 (11 * 16384) 16384 1 11 11) (2 * (2 * 16384)) 128 <
  epsFor (varProxy 16384 1 39 1 39 39) (2 * (2 * 16384)) 128
-- A secret of Hamming weight `2N/3` (`S2 = 10923`) gains a little more.
#guard epsFor (varProxyL2 (11 * 16384) 10923 1 11 11) (2 * (2 * 16384)) 128 == 7744
-- The gain is the key's and the samplers', separately: with the `ℓ₂` bound of the public-key
-- error left at its support value `N·39²` and only the samplers' proxies lowered, `ε` is 70787.
#guard epsFor (varProxyL2 (16384 * 39 ^ 2) 16384 1 11 11) (2 * (2 * 16384)) 128 == 70787
-- The bound is monotone in every argument of `varProxyL2`: a larger assumed norm or proxy never
-- gives a smaller `ε`.
#guard epsFor (varProxyL2 (11 * 16384) 16384 1 11 11) (2 * (2 * 16384)) 128 <
  epsFor (varProxyL2 (12 * 16384) 16384 1 11 11) (2 * (2 * 16384)) 128

end Challenge.FreshNoiseL2
