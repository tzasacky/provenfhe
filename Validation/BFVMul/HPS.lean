import Challenge.BFVMul.HPS
import FHE.BFV.MulHPS
import Validation.BFV.Textbook
import Validation.BFVMul.Congr

/-!
# Validation.BFVMul.HPS — idealised HPS multiplication meets the BFV `mul` contract

`stepOK_mul_hps`, `stepOK_square_hps`: the limb-level `Challenge.BFVMul.hpsMul` (exact base
extension, limb-wise tensor, RNS scale-and-round, exact switch back; floating-point sums of the
library replaced by exact rounding) meets the `mul`/`square` contract of `Spec.TraceBFV` within
the *textbook* budget (`Spec.BudgetBFV.mulLift`, `mulRound`), for every auxiliary basis accepted
by `hpsAuxOK?`.

Derivation: `FHE.BFV.MulHPS.hpsMul_congr_bfvMul` (the result is congruent to the textbook
`bfvMul` modulo `Q`, component by component), `Validation.BFV.stepOK_mul_textbook`, and
`stepOK_mul_congr` (a contract reads the stored ciphertext modulo `Q` only). For `square` the
textbook step is `stepOK_square_bfvMul` below (`bfvMul` of the operand with itself).
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV

variable (P : FullParams)

/-- Textbook squaring (`bfvMul` of the operand with itself) meets the `square` contract within
the textbook budget. -/
theorem stepOK_square_bfvMul (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)) (.square d a) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hla
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  have ht : bfvMul P.src.t (P.src.modulus x.level) [a0, a1] [a0, a1] =
      [scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a0) *
            centered (ofInt (P.src.modulus x.level) a0)),
       scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a0) *
              centered (ofInt (P.src.modulus x.level) a1) +
            centered (ofInt (P.src.modulus x.level) a1) *
              centered (ofInt (P.src.modulus x.level) a0)),
       scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a1) *
            centered (ofInt (P.src.modulus x.level) a1))] := rfl
  rw [ht]
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x]
  refine ⟨x, [a0, a1], ?_⟩
  dsimp only
  unfold Trace.phaseAt
  have hS : (∑ j, |(automorph x.key s).coeff j|) ≤ (P.src.N : ℤ) * (P.secretBound : ℤ) :=
    (sum_abs_automorph_le _ _).trans (sum_abs_le s _ ((normInf_le_iff _ _).mp hs))
  generalize automorph x.key s = sk at hS ⊢
  generalize P.src.modulus x.level = Q at hQ ⊢
  obtain ⟨ka, hka, hΨa⟩ := lift_core Q hQ sk (centered (ofInt Q a0)) (centered (ofInt Q a1))
    (centered (phase (ofInt Q sk) ([a0, a1].map (ofInt Q)))) _ hS
    (fun i => two_abs_valMinAbs_le hQ _) (fun i => two_abs_valMinAbs_le hQ _)
    (fun i => two_abs_valMinAbs_le hQ _)
    (by simp only [ofInt_add, ofInt_mul, ofInt_centered, phase_map_ofInt_two])
  obtain ⟨D, hD, hXD⟩ := mul_core P.src.t Q sk
    (centered (ofInt Q a0) + sk * centered (ofInt Q a1))
    (centered (ofInt Q a0) + sk * centered (ofInt Q a1))
    (scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a0)))
    (scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a1) +
      centered (ofInt Q a1) * centered (ofInt Q a0)))
    (scaleRound P.src.t Q (centered (ofInt Q a1) * centered (ofInt Q a1)))
    _ _ _ _ hS (by ring)
    (fun i => two_abs_roundDiv_sub_le _ _ hQ) (fun i => two_abs_roundDiv_sub_le _ _ hQ)
    (fun i => two_abs_roundDiv_sub_le _ _ hQ)
  refine ⟨ka,
    scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a0)) +
      sk * scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a1) +
        centered (ofInt Q a1) * centered (ofInt Q a0)) +
      (sk * sk) * scaleRound P.src.t Q (centered (ofInt Q a1) * centered (ofInt Q a1)),
    D, hx, ha, ?_, ?_, ?_, ?_⟩
  · rw [normInf_le_iff]
    intro i
    have h' : 2 * |ka.coeff i| ≤ 2 + ((P.src.N * P.secretBound : ℕ) : ℤ) := by
      push_cast; exact hka i
    unfold BudgetBFV.mulLift at hL
    generalize P.src.N * P.secretBound = m at h' hL
    generalize |ka.coeff i| = z at h'
    omega
  · have hle : normInf D ≤ Q * E.mulRound / 2 := by
      rw [normInf_le_iff]
      intro i
      have h' : 2 * |D.coeff i| ≤ ((Q * BudgetBFV.mulRound P : ℕ) : ℤ) := by
        unfold BudgetBFV.mulRound; push_cast; exact hD i
      have h'' : Q * BudgetBFV.mulRound P ≤ Q * E.mulRound := Nat.mul_le_mul_left _ hR
      generalize Q * BudgetBFV.mulRound P = u at h' h''
      generalize Q * E.mulRound = w at h'' ⊢
      generalize |D.coeff i| = z at h'
      omega
    omega
  · rw [specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, ← hΨa]
    exact hXD
  · simp only [List.map_cons, List.map_nil, phase_three', ofInt_add, ofInt_mul]

/-- **Idealised HPS multiplication meets the `mul` contract** within the textbook budget
(`mulLift = ⌊(2 + N·B_s)/2⌋`, `mulRound = 1 + N·B_s + (N·B_s)²`), for two-component operands at
level `ℓ` with ciphertext basis the first `ℓ` moduli and any auxiliary basis `ps` accepted by
`hpsAuxOK?`. -/
theorem stepOK_mul_hps (P : FullParams) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : hpsAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (hpsMul P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := by
  have H := Validation.BFV.stepOK_mul_textbook P hP E hL hR s hs ρ ρ' σ d a b x y ca cb hstep hx hy
    ha hb hla hlb h2x h2y
  refine stepOK_mul_congr E s ρ ρ' σ d a b _ _ ?_ H
  intro v hv
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  rw [set_self] at hv
  cases hv
  exact (FHE.BFV.MulHPS.hpsMul_congr_bfvMul P.src.t (P.src.qs.take x.level) ps haux ca cb
    hla hlb).symm

/-- **Idealised HPS squaring meets the `square` contract** within the textbook budget: the same
algorithm with both operands equal. -/
theorem stepOK_square_hps (P : FullParams) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : hpsAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (hpsMul P.src.t (P.src.qs.take x.level) ps ca ca)) (.square d a) := by
  have _ := hℓ
  have _ := hℓL
  have H := stepOK_square_bfvMul P hP E hL hR s hs ρ ρ' σ d a x ca hstep hx ha hla h2x
  refine stepOK_square_congr E s ρ ρ' σ d a _ _ ?_ H
  intro v hv
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  rw [set_self] at hv
  cases hv
  exact (FHE.BFV.MulHPS.hpsMul_congr_bfvMul P.src.t (P.src.qs.take x.level) ps haux ca ca
    hla hla).symm

/-- The idealised HPS product is the textbook product modulo `Q` (pin
`Challenge.BFVMul.hpsMul_congr_bfvMul`; proof in `FHE/BFV/MulHPS.lean`). -/
theorem hpsMul_congr_bfvMul {N : ℕ} (t : ℕ) (qs ps : List ℕ)
    (haux : hpsAuxOK? t N qs ps = true) (c d : List (IntPoly N))
    (hc : c.length = 2) (hd : d.length = 2) :
    (hpsMul t qs ps c d).map (ofInt qs.prod) = (bfvMul t qs.prod c d).map (ofInt qs.prod) :=
  FHE.BFV.MulHPS.hpsMul_congr_bfvMul t qs ps haux c d hc hd

end Validation.BFVMul
