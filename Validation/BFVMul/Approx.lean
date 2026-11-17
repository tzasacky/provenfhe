import Challenge.BFVMul
import Validation.BFV.Textbook

/-!
# Validation.BFVMul.Approx — every approximate BFV multiplication meets the `mul` contract

Proofs of the pins `stepOK_mul_approx` and `stepOK_square_approx` of `Challenge.BFVMul`.

The argument, for operands `[a₀, a₁]`, `[b₀, b₁]` at modulus `Q` under the secret `sk`
(`sk = σ_key(s)`, whose `ℓ₁` norm is at most `N·B_s`):

* `lift_approx`. The lifts `Aᵢ = [aᵢ]_Q + Q·uᵢ` have integer phase
  `A₀ + sk·A₁ = Φ_a + Q·k_a` with `k_a = k₀ + u₀ + sk·u₁`, where `k₀` is the lift defect of the
  centred representatives (`Validation.BFV.lift_core`, `2‖k₀‖∞ ≤ 2 + N·B_s`) and
  `‖u₀ + sk·u₁‖∞ ≤ U·(1 + N·B_s)`.
* `mul_core_gen`. If `2·|Q·Xⱼ − t·Tⱼ| ≤ M` for the three components `Tⱼ` of the tensor product,
  then `Q·(X₀ + sk·X₁ + sk²·X₂) = t·Ψ_a·Ψ_b + D` with `2‖D‖∞ ≤ M·(1 + S + S²)`
  (`Validation.BFV.mul_core` is the case `M = Q`).
* `phaseAt_eq_of_map_eq`. The stored result has the phase of `X`, being congruent to it modulo
  `Q` component by component.

The helper lemmas are in the namespace `Validation.BFVMul.Approx`; the pins in
`Validation.BFVMul`.
-/

namespace Validation.BFVMul.Approx
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV

variable {N : ℕ}

/-! ### Integer cores -/

/-- The integer phase of the lifts `[aᵢ]_Q + Q·uᵢ` (`‖uᵢ‖∞ ≤ U`) is the centred phase plus `Q·k`
with `‖k‖∞ ≤ ⌊(2 + S)/2⌋ + U·(1 + S)`, `S ≥ ‖sk‖₁`. -/
theorem lift_approx [NeZero N] (Q : ℕ) (hQ : 0 < Q) (sk a0 a1 u0 u1 : IntPoly N) (S U : ℕ)
    (hS : ∑ j, |sk.coeff j| ≤ (S : ℤ))
    (h0 : ∀ i, |u0.coeff i| ≤ (U : ℤ)) (h1 : ∀ i, |u1.coeff i| ≤ (U : ℤ)) :
    ∃ k : IntPoly N, (∀ i, |k.coeff i| ≤ (((2 + S) / 2 + U * (1 + S) : ℕ) : ℤ)) ∧
      (centered (ofInt Q a0) + ((Q : ℤ) : IntPoly N) * u0) +
          sk * (centered (ofInt Q a1) + ((Q : ℤ) : IntPoly N) * u1) =
        centered (phase (ofInt Q sk) ([a0, a1].map (ofInt Q))) + ((Q : ℤ) : IntPoly N) * k := by
  obtain ⟨k0, hk0, e⟩ := lift_core Q hQ sk (centered (ofInt Q a0)) (centered (ofInt Q a1))
    (centered (phase (ofInt Q sk) ([a0, a1].map (ofInt Q)))) (S : ℤ) hS
    (fun i => two_abs_valMinAbs_le hQ _) (fun i => two_abs_valMinAbs_le hQ _)
    (fun i => two_abs_valMinAbs_le hQ _)
    (by simp only [ofInt_add, ofInt_mul, ofInt_centered, phase_map_ofInt_two])
  refine ⟨k0 + u0 + sk * u1, ?_, ?_⟩
  · intro i
    have hk0' : |k0.coeff i| ≤ (((2 + S) / 2 : ℕ) : ℤ) := by
      have := hk0 i
      generalize |k0.coeff i| = z at this
      omega
    have hb := h0 i
    have hc := abs_coeff_mul_le sk u1 (U : ℤ) h1 i
    have hd : (∑ j, |sk.coeff j|) * (U : ℤ) ≤ (S : ℤ) * (U : ℤ) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    have tri := abs_add_three (k0.coeff i) (u0.coeff i) ((sk * u1).coeff i)
    rw [coeff_add', coeff_add', Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    linarith
  · calc (centered (ofInt Q a0) + ((Q : ℤ) : IntPoly N) * u0) +
          sk * (centered (ofInt Q a1) + ((Q : ℤ) : IntPoly N) * u1)
        = (centered (ofInt Q a0) + sk * centered (ofInt Q a1)) +
            ((Q : ℤ) : IntPoly N) * (u0 + sk * u1) := by ring
      _ = centered (phase (ofInt Q sk) ([a0, a1].map (ofInt Q))) +
            ((Q : ℤ) : IntPoly N) * (k0 + u0 + sk * u1) := by rw [e]; ring

theorem abs_le_half' {x : ℤ} {M : ℕ} (h : 2 * |x| ≤ M) : |x| ≤ ((M / 2 : ℕ) : ℤ) := by
  generalize |x| = z at h
  omega

/-- The scaling error of a product whose three components are each within `M/2` of `t·Tⱼ/Q`
(after multiplication by `Q`): `Q·(X₀ + sk·X₁ + sk²·X₂) = t·Ψ_a·Ψ_b + D` with
`2‖D‖∞ ≤ M·(1 + S + S²)`. -/
theorem mul_core_gen [NeZero N] (t Q M : ℕ) (sk Ψa Ψb X0 X1 X2 T0 T1 T2 : IntPoly N) (S : ℤ)
    (hS : ∑ j, |sk.coeff j| ≤ S)
    (hT : Ψa * Ψb = T0 + sk * T1 + (sk * sk) * T2)
    (h0 : ∀ i, 2 * |(Q : ℤ) * X0.coeff i - (t : ℤ) * T0.coeff i| ≤ M)
    (h1 : ∀ i, 2 * |(Q : ℤ) * X1.coeff i - (t : ℤ) * T1.coeff i| ≤ M)
    (h2 : ∀ i, 2 * |(Q : ℤ) * X2.coeff i - (t : ℤ) * T2.coeff i| ≤ M) :
    ∃ D : IntPoly N, (∀ i, 2 * |D.coeff i| ≤ (M : ℤ) * (1 + S + S * S)) ∧
      ((Q : ℤ) : IntPoly N) * (X0 + sk * X1 + (sk * sk) * X2) =
        (((t : ℤ)) : IntPoly N) * (Ψa * Ψb) + D := by
  obtain ⟨D0, hD0⟩ : ∃ D0, D0 = ((Q : ℤ) : IntPoly N) * X0 - ((t : ℤ) : IntPoly N) * T0 := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D1, D1 = ((Q : ℤ) : IntPoly N) * X1 - ((t : ℤ) : IntPoly N) * T1 := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ D2, D2 = ((Q : ℤ) : IntPoly N) * X2 - ((t : ℤ) : IntPoly N) * T2 := ⟨_, rfl⟩
  have hc0 : ∀ i, |D0.coeff i| ≤ ((M / 2 : ℕ) : ℤ) := by
    intro i; rw [hD0, coeff_sub', coeff_intCast_mul, coeff_intCast_mul]; exact abs_le_half' (h0 i)
  have hc1 : ∀ i, |D1.coeff i| ≤ ((M / 2 : ℕ) : ℤ) := by
    intro i; rw [hD1, coeff_sub', coeff_intCast_mul, coeff_intCast_mul]; exact abs_le_half' (h1 i)
  have hc2 : ∀ i, |D2.coeff i| ≤ ((M / 2 : ℕ) : ℤ) := by
    intro i; rw [hD2, coeff_sub', coeff_intCast_mul, coeff_intCast_mul]; exact abs_le_half' (h2 i)
  refine ⟨D0 + sk * D1 + sk * (sk * D2), ?_, ?_⟩
  · intro i
    have hS0 : (0 : ℤ) ≤ ∑ j, |sk.coeff j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hS0' : (0 : ℤ) ≤ S := hS0.trans hS
    have hh : 2 * ((M / 2 : ℕ) : ℤ) ≤ M := two_mul_half_le M
    have hh0 : (0 : ℤ) ≤ ((M / 2 : ℕ) : ℤ) := by positivity
    have b0 := hc0 i
    have b1 := abs_coeff_mul_le sk D1 _ hc1 i
    have b2' : ∀ j, |(sk * D2).coeff j| ≤ (∑ j, |sk.coeff j|) * ((M / 2 : ℕ) : ℤ) :=
      abs_coeff_mul_le sk D2 _ hc2
    have b2 := abs_coeff_mul_le sk (sk * D2) _ b2' i
    have A : (∑ j, |sk.coeff j|) * ((M / 2 : ℕ) : ℤ) ≤ S * ((M / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right hS hh0
    have B : (∑ j, |sk.coeff j|) * ((∑ j, |sk.coeff j|) * ((M / 2 : ℕ) : ℤ)) ≤
        S * (S * ((M / 2 : ℕ) : ℤ)) :=
      mul_le_mul hS A (mul_nonneg hS0 hh0) hS0'
    have C : 2 * ((M / 2 : ℕ) : ℤ) * (1 + S + S * S) ≤ (M : ℤ) * (1 + S + S * S) :=
      mul_le_mul_of_nonneg_right hh (by nlinarith)
    rw [coeff_add', coeff_add']
    have tri : |D0.coeff i + (sk * D1).coeff i + (sk * (sk * D2)).coeff i| ≤
        |D0.coeff i| + |(sk * D1).coeff i| + |(sk * (sk * D2)).coeff i| := abs_add_three _ _ _
    nlinarith
  · subst hD0 hD1 hD2
    rw [hT]
    ring

/-- `mul_core_gen` for the tensor product of two two-component lifts, with the rounding
hypothesis in the form of the pins (`List.getD` on the three components). -/
theorem mul_core_tensor [NeZero N] (t Q M : ℕ) (sk A0 A1 B0 B1 X0 X1 X2 : IntPoly N) (S : ℤ)
    (hS : ∑ j, |sk.coeff j| ≤ S)
    (h : ∀ (j : ℕ) (i : Fin N), 2 * |(Q : ℤ) * ([X0, X1, X2].getD j 0).coeff i -
      (t : ℤ) * ((Challenge.Source.tensor [A0, A1] [B0, B1]).getD j 0).coeff i| ≤ M) :
    ∃ D : IntPoly N, (∀ i, 2 * |D.coeff i| ≤ (M : ℤ) * (1 + S + S * S)) ∧
      ((Q : ℤ) : IntPoly N) * (X0 + sk * X1 + (sk * sk) * X2) =
        (((t : ℤ)) : IntPoly N) * ((A0 + sk * A1) * (B0 + sk * B1)) + D :=
  mul_core_gen t Q M sk _ _ X0 X1 X2 (A0 * B0) (A0 * B1 + A1 * B0) (A1 * B1) S hS (by ring)
    (h 0) (h 1) (h 2)

/-! ### Reading the lifts and the stored result -/

/-- `approxLift` of two-component lists, with the constant-polynomial form of `Q·u`. -/
theorem approxLift_two [NeZero N] (Q : ℕ) (a0 a1 u0 u1 : IntPoly N) :
    approxLift Q [a0, a1] [u0, u1] =
      [centered (ofInt Q a0) + ((Q : ℤ) : IntPoly N) * u0,
       centered (ofInt Q a1) + ((Q : ℤ) : IntPoly N) * u1] := by
  rw [← specSMul_eq_intCast_mul, ← specSMul_eq_intCast_mul]
  rfl

variable (P : FullParams)

/-- **Congruent components, same phase.** Ciphertexts that agree modulo `Q` component by
component have the same phase modulo `Q` under every key. -/
theorem phaseAt_eq_of_map_eq (Q key : ℕ) (s : IntPoly P.src.N) (c c' : List (IntPoly P.src.N))
    (h : c.map (ofInt Q) = c'.map (ofInt Q)) :
    Trace.phaseAt P Q key s c = Trace.phaseAt P Q key s c' := by
  unfold Trace.phaseAt
  rw [h]

/-- The `ℓ₁` norm of `σ_key(s)` for a secret within the bound. -/
theorem sum_abs_secret_le (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (key : ℕ) :
    (∑ j, |(automorph key s).coeff j|) ≤ ((P.src.N * P.secretBound : ℕ) : ℤ) := by
  push_cast
  exact (sum_abs_automorph_le _ _).trans (sum_abs_le s _ ((normInf_le_iff _ _).mp hs))

/-- From the integer bound of `lift_approx` to the `mulLift` clause of the contract. -/
theorem normInf_le_mulLift (U : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift) (k : IntPoly P.src.N)
    (hk : ∀ i, |k.coeff i| ≤ (((2 + P.src.N * P.secretBound) / 2 +
      U * (1 + P.src.N * P.secretBound) : ℕ) : ℤ)) : normInf k ≤ E.mulLift := by
  rw [normInf_le_iff]
  intro i
  exact (hk i).trans (Nat.cast_le.mpr hL)

/-- From the integer bound of `mul_core_gen` to the `mulRound` clause of the contract. -/
theorem two_normInf_le_mulRound (Q r : ℕ) (E : TraceBFV.Budget)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound) (D : IntPoly P.src.N)
    (hD : ∀ i, 2 * |D.coeff i| ≤ ((Q * r : ℕ) : ℤ) *
      (1 + ((P.src.N * P.secretBound : ℕ) : ℤ) +
        ((P.src.N * P.secretBound : ℕ) : ℤ) * ((P.src.N * P.secretBound : ℕ) : ℤ))) :
    2 * normInf D ≤ Q * E.mulRound := by
  have hle : normInf D ≤ Q * E.mulRound / 2 := by
    rw [normInf_le_iff]
    intro i
    have h' : 2 * |D.coeff i| ≤ ((Q * BudgetBFV.mulRoundApprox P r : ℕ) : ℤ) := by
      refine (hD i).trans (le_of_eq ?_)
      unfold BudgetBFV.mulRoundApprox BudgetBFV.mulRound
      push_cast
      ring
    have h'' : Q * BudgetBFV.mulRoundApprox P r ≤ Q * E.mulRound := Nat.mul_le_mul_left _ hR
    generalize Q * BudgetBFV.mulRoundApprox P r = u at h' h''
    generalize Q * E.mulRound = w at h'' ⊢
    generalize |D.coeff i| = z at h'
    omega
  omega

end Validation.BFVMul.Approx

/-! ### The pins -/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV
open Validation.BFVMul.Approx

variable (P : FullParams)

/-- **Every approximate multiplication meets the `mul` contract.** -/
theorem stepOK_mul_approx (hP : SchemeParamsOK P) (U r : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua ub X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hub : ub.length = 2) (hX : X.length = 3)
    (hUa : ∀ u ∈ ua, normInf u ≤ U) (hUb : ∀ u ∈ ub, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) cb ub)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := by
  have _ := hℓ
  have _ := hℓL
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hla
  obtain ⟨b0, b1, rfl⟩ := List.length_eq_two.mp hlb
  obtain ⟨u0, u1, rfl⟩ := List.length_eq_two.mp hua
  obtain ⟨w0, w1, rfl⟩ := List.length_eq_two.mp hub
  obtain ⟨X0, X1, X2, rfl⟩ := List.length_eq_three.mp hX
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  have hlen : out.length = 3 := by simpa using congrArg List.length hout
  refine ⟨_, out, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x, h2y, hlen]
  refine ⟨x, y, [a0, a1], [b0, b1], ?_⟩
  dsimp only
  rw [← hkey, phaseAt_eq_of_map_eq P _ _ s out _ hout]
  unfold Trace.phaseAt
  have hS := sum_abs_secret_le P s hs x.key
  have hu0 := (normInf_le_iff _ _).mp (hUa u0 (by simp))
  have hu1 := (normInf_le_iff _ _).mp (hUa u1 (by simp))
  have hw0 := (normInf_le_iff _ _).mp (hUb w0 (by simp))
  have hw1 := (normInf_le_iff _ _).mp (hUb w1 (by simp))
  simp only [approxLift_two] at hround
  generalize automorph x.key s = sk at hS ⊢
  generalize P.src.modulus x.level = Q at hQ hround ⊢
  obtain ⟨ka, hka, hΨa⟩ := lift_approx Q hQ sk a0 a1 u0 u1 _ U hS hu0 hu1
  obtain ⟨kb, hkb, hΨb⟩ := lift_approx Q hQ sk b0 b1 w0 w1 _ U hS hw0 hw1
  obtain ⟨D, hD, hXD⟩ := mul_core_tensor P.src.t Q (Q * r) sk _ _ _ _ X0 X1 X2 _ hS
    (fun j i => by push_cast; exact hround j i)
  refine ⟨ka, kb, X0 + sk * X1 + (sk * sk) * X2, D, hx, hy, ha, hb,
    normInf_le_mulLift P U E hL ka hka, normInf_le_mulLift P U E hL kb hkb,
    two_normInf_le_mulRound P Q r E hR D hD, ?_, ?_⟩
  · rw [specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, specSMul_eq_intCast_mul,
      specSMul_eq_intCast_mul, ← hΨa, ← hΨb]
    exact hXD
  · simp only [List.map_cons, List.map_nil, phase_three', ofInt_add, ofInt_mul]

/-- **Every approximate squaring meets the `square` contract.** -/
theorem stepOK_square_approx (hP : SchemeParamsOK P) (U r : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hX : X.length = 3) (hUa : ∀ u ∈ ua, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) ca ua)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := by
  have _ := hℓ
  have _ := hℓL
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hla
  obtain ⟨u0, u1, rfl⟩ := List.length_eq_two.mp hua
  obtain ⟨X0, X1, X2, rfl⟩ := List.length_eq_three.mp hX
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  have hlen : out.length = 3 := by simpa using congrArg List.length hout
  refine ⟨_, out, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x, hlen]
  refine ⟨x, [a0, a1], ?_⟩
  dsimp only
  rw [phaseAt_eq_of_map_eq P _ _ s out _ hout]
  unfold Trace.phaseAt
  have hS := sum_abs_secret_le P s hs x.key
  have hu0 := (normInf_le_iff _ _).mp (hUa u0 (by simp))
  have hu1 := (normInf_le_iff _ _).mp (hUa u1 (by simp))
  simp only [approxLift_two] at hround
  generalize automorph x.key s = sk at hS ⊢
  generalize P.src.modulus x.level = Q at hQ hround ⊢
  obtain ⟨ka, hka, hΨa⟩ := lift_approx Q hQ sk a0 a1 u0 u1 _ U hS hu0 hu1
  obtain ⟨D, hD, hXD⟩ := mul_core_tensor P.src.t Q (Q * r) sk _ _ _ _ X0 X1 X2 _ hS
    (fun j i => by push_cast; exact hround j i)
  refine ⟨ka, X0 + sk * X1 + (sk * sk) * X2, D, hx, ha,
    normInf_le_mulLift P U E hL ka hka, two_normInf_le_mulRound P Q r E hR D hD, ?_, ?_⟩
  · rw [specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, ← hΨa]
    exact hXD
  · simp only [List.map_cons, List.map_nil, phase_three', ofInt_add, ofInt_mul]

end Validation.BFVMul
