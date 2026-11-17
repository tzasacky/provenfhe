import Challenge.BFVMul.BEHZ
import FHE.BFV.MulBEHZ
import Validation.BFVMul.Lifted

/-!
# Validation.BFVMul.BEHZ — BEHZ multiplication meets the BFV `mul` and `square` contracts

`stepOK_mul_behz`, `stepOK_square_behz`: the limb-level `Challenge.BFVMul.behzMul` (small
Montgomery extension, limb-wise tensor, fast RNS floor, Shenoy–Kumaresan conversion; integers
only) meets the `mul`/`square` contract of `Spec.TraceBFV` for every budget with

  `mulLift ≥ Spec.BudgetBFV.mulLiftNormAt P ℓ e`,  `e = ⌈2(k−1)·Q/m̃⌉`
  `mulRound ≥ Spec.BudgetBFV.mulRoundApprox P (2k)`,

the slacks of `Spec.BudgetBFV.behzSlack`, at every level `ℓ` (with `k = ℓ` limbs) whose basis
with the auxiliary moduli passes `behzAuxOK?`.

Derivation: `FHE.BFV.MulBEHZ.behzMul_lifted` (the component-level facts: the lifts `A`, `B` are
representatives modulo `Q` with `2·‖·‖∞ ≤ Q + e`, the result is congruent modulo `Q` to `X` with
`2·|Q·Xⱼ − t·(A ⊗ B)ⱼ| ≤ Q·2k`) and `stepOK_mul_lifted` (every such multiplication meets the
contract). For `square`, BEHZ lifts the operand once, so both factors of the tensor product are
the same lift and the `square` contract (one `k_a`) holds: `stepOK_square_lifted` (a pin of
`Challenge.BFVMul`) is the `square` analogue of `stepOK_mul_lifted`, proved here from the same
two integer cores
(`Lifted.lift_norm`, `Approx.mul_core_tensor`).
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV
open Validation.BFVMul.Approx Validation.BFVMul.Lifted

variable (P : FullParams)

/-- **Every squaring of representatives of bounded size meets the `square` contract.** As
`stepOK_mul_lifted`, with the same integer representatives `A` of the operand's components
(`2·‖Aᵢ‖∞ ≤ Q + e`) on both sides of the tensor product. -/
theorem stepOK_square_lifted (hP : SchemeParamsOK P) (e r : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (A X out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hX : X.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor A A).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  have hlA : A.length = 2 := by simpa [hla] using congrArg List.length hA
  obtain ⟨A0, A1, rfl⟩ := List.length_eq_two.mp hlA
  obtain ⟨X0, X1, X2, rfl⟩ := List.length_eq_three.mp hX
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  have hlen : out.length = 3 := by simpa using congrArg List.length hout
  refine ⟨_, out, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x, hlen]
  refine ⟨x, ca, ?_⟩
  dsimp only
  rw [phaseAt_eq_of_map_eq P _ _ s out _ hout, phaseAt_eq_of_map_eq P _ _ s ca _ hA.symm]
  unfold Trace.phaseAt
  have hS := sum_abs_secret_le P s hs x.key
  have hA0 := two_abs_coeff_le A0 _ (hAn A0 (by simp))
  have hA1 := two_abs_coeff_le A1 _ (hAn A1 (by simp))
  have hL' : ((P.src.modulus x.level + e) * (1 + P.src.N * P.secretBound) +
      P.src.modulus x.level) / (2 * P.src.modulus x.level) ≤ E.mulLift := hL
  generalize automorph x.key s = sk at hS ⊢
  generalize P.src.modulus x.level = Q at hQ hround hA0 hA1 hL' ⊢
  obtain ⟨ka, hka, hΨa⟩ := lift_norm Q (Q + e) hQ sk A0 A1 _ hS hA0 hA1
  obtain ⟨D, hD, hXD⟩ := mul_core_tensor P.src.t Q (Q * r) sk A0 A1 A0 A1 X0 X1 X2 _ hS
    (fun j i => by push_cast; exact hround j i)
  refine ⟨ka, X0 + sk * X1 + (sk * sk) * X2, D, hx, ha, ?_,
    two_normInf_le_mulRound P Q r E hR D hD, ?_, ?_⟩
  · rw [normInf_le_iff]
    exact fun i => (hka i).trans (Nat.cast_le.mpr hL')
  · rw [specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, ← hΨa]
    exact hXD
  · simp only [List.map_cons, List.map_nil, phase_three', ofInt_add, ofInt_mul]

/-! ### BEHZ -/

/-- **BEHZ multiplication meets the `mul` contract** with the slacks of
`Spec.BudgetBFV.behzSlack`: lift excess `e = ⌈2(k−1)·Q/m̃⌉` (`mulLiftNormAt P ℓ e`) and rounding
slack `2k` (`mulRoundApprox P (2k)`), for two-component operands at level `ℓ` (`k = ℓ` limbs,
ciphertext basis the first `ℓ` moduli) and any auxiliary basis `bs`, `msk`, `mt` accepted by
`behzAuxOK?`. -/
theorem stepOK_mul_behz (P : FullParams) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length mt).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca cb)) (.mul d a b) := by
  obtain ⟨A, B, X, -, -, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FHE.BFV.MulBEHZ.behzMul_lifted P.src.t (P.src.qs.take x.level) bs msk mt haux ca cb hla hlb
  have hk : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  rw [hk] at hAn hBn hround
  exact stepOK_mul_lifted P hP _ (2 * x.level) E s hs ρ ρ' σ d a b x y ca cb hL hR hstep hx hy
    ha hb hla hlb h2x h2y hℓ hℓL A B X _ hA hB hX hAn hBn hround hout

/-- **BEHZ squaring meets the `square` contract** with the same slacks: the same algorithm with
both operands equal (the operand is lifted once). -/
theorem stepOK_square_behz (P : FullParams) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length mt).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca ca)) (.square d a) := by
  have _ := hℓ
  obtain ⟨hpos, hcop, -, -, -, -, hgcd, hmt, heven⟩ :=
    (FHE.BFV.MulBEHZ.behzAuxOK_iff _ _ _ bs msk mt).mp haux
  rw [List.append_assoc] at hpos hcop
  have hposq : ∀ q ∈ P.src.qs.take x.level, 0 < q := fun q hq =>
    hpos q (List.mem_append_left _ hq)
  have hcopq : (P.src.qs.take x.level).Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hQmt : Nat.Coprime (P.src.qs.take x.level).prod mt := Nat.Coprime.symm hgcd
  have hk : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  have hAn : ∀ p ∈ FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca,
      2 * normInf p ≤ P.src.modulus x.level +
        (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
          bs.length mt).e := by
    intro p hp
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
    have := FHE.BFV.MulBEHZ.smmrPoly_norm (P.src.qs.take x.level) hposq mt hmt heven hQmt c
    rw [hk] at this
    exact this
  have hround := FHE.BFV.MulBEHZ.behzFloor_round P.src.t (P.src.qs.take x.level) hposq hcopq
    (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)
    (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)
  rw [hk] at hround
  have hX : (FHE.BFV.MulBEHZ.behzFloor P.src.t (P.src.qs.take x.level)
      (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)
      (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)).length = 3 := by
    obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hla
    rfl
  exact stepOK_square_lifted P hP _ (2 * x.level) E s hs ρ ρ' σ d a x ca hL hR hstep hx ha
    hla h2x _ _ _
    (FHE.BFV.MulBEHZ.behzLift_congr (P.src.qs.take x.level) hposq hcopq mt hmt hQmt ca)
    hX hAn hround
    (FHE.BFV.MulBEHZ.behzMul_congr P.src.t (P.src.qs.take x.level) bs msk mt haux ca ca hla hla)

end Validation.BFVMul
