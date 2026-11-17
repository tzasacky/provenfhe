import Challenge.BFVMul
import Validation.BFVMul.Approx

/-!
# Validation.BFVMul.Lifted — multiplication of representatives of bounded size meets the `mul` contract

Proof of the pin `stepOK_mul_lifted` of `Challenge.BFVMul`.

For integer representatives `A₀, A₁` of an operand's components modulo `Q` with
`2·‖Aᵢ‖∞ ≤ M` (`M = Q + e`), the integer phase `Ψ = A₀ + sk·A₁` is congruent modulo `Q` to the
centred phase `Φ` (`2·‖Φ‖∞ ≤ Q`) and `2·‖Ψ‖∞ ≤ M·(1 + S)`, `S ≥ ‖sk‖₁`; so `Ψ = Φ + Q·k` with
`‖k‖∞ ≤ ⌊(M·(1 + S) + Q)/(2Q)⌋` (`lift_norm`). The rounding part is
`Validation.BFVMul.Approx.mul_core_tensor`, as for `stepOK_mul_approx`.

The helper lemmas are in the namespace `Validation.BFVMul.Lifted`; the pin in
`Validation.BFVMul`.
-/

namespace Validation.BFVMul.Lifted
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV Validation.BFVMul.Approx

variable {N : ℕ}

/-- The integer phase `A₀ + sk·A₁` of representatives with `2·‖Aᵢ‖∞ ≤ M` is the centred phase
plus `Q·k` with `‖k‖∞ ≤ ⌊(M·(1 + S) + Q)/(2Q)⌋`, `S ≥ ‖sk‖₁`. -/
theorem lift_norm [NeZero N] (Q M : ℕ) (hQ : 0 < Q) (sk A0 A1 : IntPoly N) (S : ℕ)
    (hS : ∑ j, |sk.coeff j| ≤ (S : ℤ))
    (h0 : ∀ i, 2 * |A0.coeff i| ≤ (M : ℤ)) (h1 : ∀ i, 2 * |A1.coeff i| ≤ (M : ℤ)) :
    ∃ k : IntPoly N, (∀ i, |k.coeff i| ≤ (((M * (1 + S) + Q) / (2 * Q) : ℕ) : ℤ)) ∧
      A0 + sk * A1 =
        centered (phase (ofInt Q sk) ([A0, A1].map (ofInt Q))) + ((Q : ℤ) : IntPoly N) * k := by
  set Φ := centered (phase (ofInt Q sk) ([A0, A1].map (ofInt Q))) with hΦdef
  have hE : ofInt Q (A0 + sk * A1) = ofInt Q Φ := by
    rw [hΦdef, ofInt_centered, phase_map_ofInt_two]
  have hΦ : ∀ i, 2 * |Φ.coeff i| ≤ (Q : ℤ) := fun i => two_abs_valMinAbs_le hQ _
  have hK : ∀ i, ∃ j : ℤ, (A0 + sk * A1).coeff i = Φ.coeff i + (Q : ℤ) * j := by
    intro i
    have := congrArg (fun p => p.coeff i) hE
    simp only [coeff_ofInt] at this
    exact exists_eq_add_mul_of_cast_eq this
  choose K hK using hK
  refine ⟨⟨K⟩, ?_, ?_⟩
  · intro i
    show |K i| ≤ _
    have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
    have hS0 : (0 : ℤ) ≤ ∑ j, |sk.coeff j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hh : 2 * ((M / 2 : ℕ) : ℤ) ≤ M := two_mul_half_le M
    have hh0 : (0 : ℤ) ≤ ((M / 2 : ℕ) : ℤ) := by positivity
    have hm := abs_coeff_mul_le sk A1 _ (fun j => abs_le_half' (h1 j)) i
    have hSh : (∑ j, |sk.coeff j|) * ((M / 2 : ℕ) : ℤ) ≤ (S : ℤ) * ((M / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right hS hh0
    have hSM : 2 * ((S : ℤ) * ((M / 2 : ℕ) : ℤ)) ≤ (S : ℤ) * M := by
      have := mul_le_mul_of_nonneg_left hh (hS0.trans hS)
      linarith
    have e := hK i
    rw [coeff_add'] at e
    have e' : (Q : ℤ) * K i = A0.coeff i + (sk * A1).coeff i + (-Φ.coeff i) := by linarith
    have hab : (Q : ℤ) * |K i| ≤ |A0.coeff i| + |(sk * A1).coeff i| + |Φ.coeff i| := by
      rw [← abs_of_pos hQ', ← abs_mul, e']
      refine (abs_add_three _ _ _).trans ?_
      rw [abs_neg]
    have h0i := h0 i
    have hΦi := hΦ i
    have hcast : (((M * (1 + S) + Q) / (2 * Q) : ℕ) : ℤ) =
        ((M : ℤ) * (1 + S) + Q) / (2 * Q) := by push_cast; rfl
    rw [hcast, Int.le_ediv_iff_mul_le (by positivity)]
    nlinarith
  · ext i
    rw [hK i, coeff_add', coeff_intCast_mul]

/-- `2·‖p‖∞ ≤ M` coefficient by coefficient. -/
theorem two_abs_coeff_le (p : IntPoly N) (M : ℕ) (h : 2 * normInf p ≤ M) (i : Fin N) :
    2 * |p.coeff i| ≤ (M : ℤ) := by
  have h' : normInf p ≤ M / 2 := by omega
  have := (normInf_le_iff _ _).mp h' i
  generalize |p.coeff i| = z at this
  omega

end Validation.BFVMul.Lifted

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV
open Validation.BFVMul.Approx Validation.BFVMul.Lifted

variable (P : FullParams)

/-- **Every multiplication of representatives of bounded size meets the `mul` contract.** -/
theorem stepOK_mul_lifted (hP : SchemeParamsOK P) (e r : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (A B X out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hB : B.map (ofInt (P.src.modulus x.level)) = cb.map (ofInt (P.src.modulus x.level)))
    (hX : X.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hBn : ∀ p ∈ B, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := by
  have _ := hℓ
  have _ := hℓL
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  have hlA : A.length = 2 := by simpa [hla] using congrArg List.length hA
  have hlB : B.length = 2 := by simpa [hlb] using congrArg List.length hB
  obtain ⟨A0, A1, rfl⟩ := List.length_eq_two.mp hlA
  obtain ⟨B0, B1, rfl⟩ := List.length_eq_two.mp hlB
  obtain ⟨X0, X1, X2, rfl⟩ := List.length_eq_three.mp hX
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  have hlen : out.length = 3 := by simpa using congrArg List.length hout
  refine ⟨_, out, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x, h2y, hlen]
  refine ⟨x, y, ca, cb, ?_⟩
  dsimp only
  rw [← hkey, phaseAt_eq_of_map_eq P _ _ s out _ hout,
    phaseAt_eq_of_map_eq P _ _ s ca _ hA.symm, phaseAt_eq_of_map_eq P _ _ s cb _ hB.symm]
  unfold Trace.phaseAt
  have hS := sum_abs_secret_le P s hs x.key
  have hA0 := two_abs_coeff_le A0 _ (hAn A0 (by simp))
  have hA1 := two_abs_coeff_le A1 _ (hAn A1 (by simp))
  have hB0 := two_abs_coeff_le B0 _ (hBn B0 (by simp))
  have hB1 := two_abs_coeff_le B1 _ (hBn B1 (by simp))
  have hL' : ((P.src.modulus x.level + e) * (1 + P.src.N * P.secretBound) +
      P.src.modulus x.level) / (2 * P.src.modulus x.level) ≤ E.mulLift := hL
  generalize automorph x.key s = sk at hS ⊢
  generalize P.src.modulus x.level = Q at hQ hround hA0 hA1 hB0 hB1 hL' ⊢
  obtain ⟨ka, hka, hΨa⟩ := lift_norm Q (Q + e) hQ sk A0 A1 _ hS hA0 hA1
  obtain ⟨kb, hkb, hΨb⟩ := lift_norm Q (Q + e) hQ sk B0 B1 _ hS hB0 hB1
  obtain ⟨D, hD, hXD⟩ := mul_core_tensor P.src.t Q (Q * r) sk A0 A1 B0 B1 X0 X1 X2 _ hS
    (fun j i => by push_cast; exact hround j i)
  refine ⟨ka, kb, X0 + sk * X1 + (sk * sk) * X2, D, hx, hy, ha, hb, ?_, ?_,
    two_normInf_le_mulRound P Q r E hR D hD, ?_, ?_⟩
  · rw [normInf_le_iff]
    exact fun i => (hka i).trans (Nat.cast_le.mpr hL')
  · rw [normInf_le_iff]
    exact fun i => (hkb i).trans (Nat.cast_le.mpr hL')
  · rw [specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, specSMul_eq_intCast_mul,
      specSMul_eq_intCast_mul, ← hΨa, ← hΨb]
    exact hXD
  · simp only [List.map_cons, List.map_nil, phase_three', ofInt_add, ofInt_mul]

end Validation.BFVMul
