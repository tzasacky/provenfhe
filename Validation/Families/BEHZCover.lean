import Challenge.Families.BEHZCover
import Validation.Families.BEHZ
import Validation.Families.Coverage
import Validation.Profile

/-!
# Validation.Families.BEHZCover — proofs of the pins of `Challenge.Families.BEHZCover`

`approxLift_of_lifted`: componentwise, `u = (A − [c]_Q)/Q`; `Q ∣ A − [c]_Q` because both are
representatives of `c` modulo `Q` (`ZMod.coe_valMinAbs`), and `2·Q·|u| ≤ 2|A| + 2|[c]_Q| ≤ 2Q + e
< 4Q`, so `|u| ≤ 1`. `behzSlack_e_le`: `⌈2(k−1)·Q/m̃⌉ ≤ Q` from `2(k−1) ≤ m̃`, read off
`FHE.BFV.MulBEHZ.behzAuxOK_iff`. The coverage statements are
`FHE.BFV.MulBEHZ.behzMul_lifted` (resp. the integer facts used by
`Validation.BFVMul.stepOK_square_behz`) rewritten through the bridge into the hypotheses of
`Validation.Profile.coversBFV?_mul` (resp. `_square`). The SEAL instance combines
`Validation.Families.sealBFV_covers` and `Validation.Families.sealBFV_behzAuxOK`. No locked
definition is unfolded by name (`approxLift` is read through local `rfl` equations).
-/

namespace Validation.Families
open Spec NPoly Scheme Source Challenge.BFV Challenge.BFVMul Challenge.Profile Challenge.Families
open Validation.Ring Validation.Scheme Validation.Source

/-- `approxLift` of the empty lists. -/
private theorem approxLift_nil {N : ℕ} (Q : ℕ) :
    approxLift Q ([] : List (IntPoly N)) [] = [] := rfl

/-- `approxLift` of two non-empty lists, with `Q • u` written coefficientwise. -/
private theorem approxLift_cons {N : ℕ} (Q : ℕ) (c0 u0 : IntPoly N) (c u : List (IntPoly N)) :
    approxLift Q (c0 :: c) (u0 :: u) =
      (centered (ofInt Q c0) + ⟨fun i => (Q : ℤ) * u0.coeff i⟩) :: approxLift Q c u := rfl

/-- One component of the bridge. -/
private theorem lift_one {N : ℕ} (Q e : ℕ) (hQ : 0 < Q) (he : e < 2 * Q) (c a : IntPoly N)
    (hA : ofInt Q a = ofInt Q c) (hAn : 2 * normInf a ≤ Q + e) :
    ∃ u : IntPoly N, normInf u ≤ 1 ∧
      centered (ofInt Q c) + ⟨fun i => (Q : ℤ) * u.coeff i⟩ = a := by
  haveI : NeZero Q := ⟨hQ.ne'⟩
  have hdvd : ∀ i, (Q : ℤ) ∣ a.coeff i - (centered (ofInt Q c)).coeff i := fun i => by
    have h1 := congrArg (fun p => p.coeff i) hA
    simp only [coeff_ofInt] at h1
    have h2 : (centered (ofInt Q c)).coeff i = ((c.coeff i : ZMod Q)).valMinAbs := rfl
    rw [h2, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, ZMod.coe_valMinAbs, h1, sub_self]
  refine ⟨⟨fun i => (a.coeff i - (centered (ofInt Q c)).coeff i) / Q⟩, ?_, ?_⟩
  · rw [normInf_le_iff]
    intro i
    have ha := Validation.BFVMul.Lifted.two_abs_coeff_le a _ hAn i
    have hv : 2 * |(centered (ofInt Q c)).coeff i| ≤ (Q : ℤ) :=
      Validation.BFV.two_abs_valMinAbs_le hQ _
    have hq := Int.mul_ediv_cancel' (hdvd i)
    show |(a.coeff i - (centered (ofInt Q c)).coeff i) / Q| ≤ ((1 : ℕ) : ℤ)
    generalize (a.coeff i - (centered (ofInt Q c)).coeff i) / Q = u at hq ⊢
    have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
    have he' : (e : ℤ) < 2 * Q := by exact_mod_cast he
    have h3 : |(Q : ℤ) * u| ≤ |a.coeff i| + |(centered (ofInt Q c)).coeff i| := by
      rw [hq]; exact abs_sub _ _
    rw [abs_mul, abs_of_pos hQz] at h3
    push_cast at ha ⊢
    by_contra hc
    have h4 : (2 : ℤ) ≤ |u| := by omega
    nlinarith
  · ext i
    show (centered (ofInt Q c)).coeff i +
        (Q : ℤ) * ((a.coeff i - (centered (ofInt Q c)).coeff i) / Q) = a.coeff i
    rw [Int.mul_ediv_cancel' (hdvd i)]
    ring

theorem approxLift_of_lifted {N : ℕ} (Q e : ℕ) (hQ : 0 < Q) (he : e < 2 * Q)
    (c A : List (IntPoly N)) (hA : A.map (ofInt Q) = c.map (ofInt Q))
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ Q + e) :
    ∃ u : List (IntPoly N), u.length = c.length ∧ (∀ v ∈ u, normInf v ≤ 1) ∧
      approxLift Q c u = A := by
  induction A generalizing c with
  | nil =>
    cases c with
    | nil => exact ⟨[], rfl, by simp, approxLift_nil Q⟩
    | cons _ _ => simp at hA
  | cons a A ih =>
    cases c with
    | nil => simp at hA
    | cons c0 c =>
      simp only [List.map_cons, List.cons.injEq] at hA
      obtain ⟨u0, hu0, e0⟩ := lift_one Q e hQ he c0 a hA.1 (hAn a (by simp))
      obtain ⟨u, hu, hU, eu⟩ := ih c hA.2 fun p hp => hAn p (by simp [hp])
      refine ⟨u0 :: u, by simp [hu], ?_, ?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hu0
        · exact hU v hv
      · rw [approxLift_cons, e0, eu]

theorem behzSlack_e_le (t N : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true) :
    (BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).e ≤ qs.prod := by
  obtain ⟨-, -, -, -, -, hk, -, hmt, -⟩ :=
    (FHE.BFV.MulBEHZ.behzAuxOK_iff t N qs bs msk mt).mp haux
  show (2 * (qs.length - 1) * qs.prod + mt - 1) / mt ≤ qs.prod
  have h1 := Nat.mul_le_mul_right qs.prod hk
  have h2 : 2 * (qs.length - 1) * qs.prod + mt - 1 < qs.prod * mt + mt := by
    rw [Nat.mul_comm mt] at h1; omega
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hmt).mpr (by rw [Nat.succ_mul qs.prod mt]; exact h2))

/-- The facts every coverage statement below needs about BEHZ at the operand's level. -/
private theorem behz_level_facts (P : FullParams) (ℓ : ℕ) (hℓL : ℓ ≤ P.src.qs.length)
    (bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take ℓ) bs msk mt = true) :
    (P.src.qs.take ℓ).length = ℓ ∧ 0 < (P.src.qs.take ℓ).prod ∧
      (BudgetBFV.behzSlack P.src.t P.src.N (P.src.qs.take ℓ).prod bs.prod msk
        (P.src.qs.take ℓ).length bs.length mt).e < 2 * (P.src.qs.take ℓ).prod := by
  have hk : (P.src.qs.take ℓ).length = ℓ := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  obtain ⟨hpos, -⟩ := (FHE.BFV.MulBEHZ.behzAuxOK_iff _ _ _ bs msk mt).mp haux
  have hQ : 0 < (P.src.qs.take ℓ).prod :=
    List.prod_pos fun q hq => hpos q (List.mem_append_left _ (List.mem_append_left _ hq))
  exact ⟨hk, hQ, by have := behzSlack_e_le _ _ _ bs msk mt haux; omega⟩

theorem stepOK_mul_behz_covered (P : FullParams) (lay : Budget.KSLayout) (r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay 1 r body E = true)
    (k : ℕ) (d a b : Var) (hk : body[k]? = some (.mul d a b))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (hr : 2 * x.level ≤ r)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca cb)) (.mul d a b) := by
  obtain ⟨hlen, hQ, he⟩ := behz_level_facts P x.level hℓL bs msk mt haux
  obtain ⟨A, B, X, -, -, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FHE.BFV.MulBEHZ.behzMul_lifted P.src.t (P.src.qs.take x.level) bs msk mt haux ca cb hla hlb
  obtain ⟨ua, hua, hUa, hEa⟩ := approxLift_of_lifted _ _ hQ he ca A hA hAn
  obtain ⟨ub, hub, hUb, hEb⟩ := approxLift_of_lifted _ _ hQ he cb B hB hBn
  have hrho : (BudgetBFV.behzSlack P.src.t P.src.N (P.src.qs.take x.level).prod bs.prod msk
      (P.src.qs.take x.level).length bs.length mt).rho = 2 * x.level := by
    show 2 * (P.src.qs.take x.level).length = 2 * x.level
    rw [hlen]
  rw [hrho] at hround
  have hQz : (0 : ℤ) ≤ ((P.src.qs.take x.level).prod : ℤ) := by positivity
  have hr' : ((2 * x.level : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  refine Validation.Profile.coversBFV?_mul P lay 1 r body E hc k d a b hk s hs ρ ρ' σ x y ca cb
    hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL ua ub X _ (hua.trans hla) (hub.trans hlb) hX hUa hUb
    (fun j i => ?_) hout
  have hEa' : approxLift (P.src.modulus x.level) ca ua = A := hEa
  have hEb' : approxLift (P.src.modulus x.level) cb ub = B := hEb
  rw [hEa', hEb']
  exact (hround j i).trans (mul_le_mul_of_nonneg_left hr' hQz)

theorem stepOK_square_behz_covered (P : FullParams) (lay : Budget.KSLayout) (r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay 1 r body E = true)
    (k : ℕ) (d a : Var) (hk : body[k]? = some (.square d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (hr : 2 * x.level ≤ r)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca ca)) (.square d a) := by
  obtain ⟨hlen, hQ, he⟩ := behz_level_facts P x.level hℓL bs msk mt haux
  obtain ⟨hpos, hcop, -, -, -, -, hgcd, hmt, heven⟩ :=
    (FHE.BFV.MulBEHZ.behzAuxOK_iff _ _ _ bs msk mt).mp haux
  rw [List.append_assoc] at hpos hcop
  have hposq : ∀ q ∈ P.src.qs.take x.level, 0 < q := fun q hq =>
    hpos q (List.mem_append_left _ hq)
  have hcopq : (P.src.qs.take x.level).Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hQmt : Nat.Coprime (P.src.qs.take x.level).prod mt := Nat.Coprime.symm hgcd
  have hAn : ∀ p ∈ FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca,
      2 * normInf p ≤ (P.src.qs.take x.level).prod +
        (BudgetBFV.behzSlack P.src.t P.src.N (P.src.qs.take x.level).prod bs.prod msk
          (P.src.qs.take x.level).length bs.length mt).e := by
    intro p hp
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
    exact FHE.BFV.MulBEHZ.smmrPoly_norm (P.src.qs.take x.level) hposq mt hmt heven hQmt c
  have hA := FHE.BFV.MulBEHZ.behzLift_congr (P.src.qs.take x.level) hposq hcopq mt hmt hQmt ca
  have hround := FHE.BFV.MulBEHZ.behzFloor_round P.src.t (P.src.qs.take x.level) hposq hcopq
    (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)
    (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)
  rw [hlen] at hround
  have hX : (FHE.BFV.MulBEHZ.behzFloor P.src.t (P.src.qs.take x.level)
      (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)
      (FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca)).length = 3 := by
    obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hla
    rfl
  obtain ⟨ua, hua, hUa, hEa⟩ := approxLift_of_lifted _ _ hQ he ca _ hA hAn
  have hQz : (0 : ℤ) ≤ ((P.src.qs.take x.level).prod : ℤ) := by positivity
  have hr' : ((2 * x.level : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  refine Validation.Profile.coversBFV?_square P lay 1 r body E hc k d a hk s hs ρ ρ' σ x ca
    hstep hx ha hla h2x hℓ hℓL ua _ _ (hua.trans hla) hX hUa (fun j i => ?_)
    (FHE.BFV.MulBEHZ.behzMul_congr P.src.t (P.src.qs.take x.level) bs msk mt haux ca ca hla hla)
  have hEa' : approxLift (P.src.modulus x.level) ca ua =
      FHE.BFV.MulBEHZ.behzLift (P.src.qs.take x.level) mt ca := hEa
  rw [hEa']
  exact (hround j i).trans (mul_le_mul_of_nonneg_left hr' hQz)

theorem stepOK_mul_behz_sealBFV_covered (k : ℕ) (d a b : Var)
    (hk : sealProg.body[k]? = some (.mul d a b))
    (s : IntPoly sealBFV.src.N) (hs : SecretOK sealBFV.secretBound s) (ρ ρ' : Env sealBFV.src)
    (σ : Trace.CtEnv sealBFV) (x y : Val sealBFV.src) (ca cb : List (IntPoly sealBFV.src.N))
    (hstep : step sealBFV.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ sealBFV.src.qs.length) :
    TraceBFV.StepOK sealBFV (BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0) s ρ ρ' σ
      (σ.set d (behzMul sealBFV.src.t (sealBFV.src.qs.take x.level) (sealAuxB x.level) sealMsk
        (2 ^ 32) ca cb)) (.mul d a b) := by
  have hL4 : sealBFV.src.qs.length = 4 := by decide
  have hmem : x.level ∈ [1, 2, 3, 4] := by
    rcases (by omega : x.level = 1 ∨ x.level = 2 ∨ x.level = 3 ∨ x.level = 4) with h | h | h | h <;>
      simp [h]
  exact stepOK_mul_behz_covered sealBFV sealLayout 8 sealProg.body
    (fun _ => BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0)
    Validation.Families.sealBFV_covers k d a b hk s hs ρ ρ' σ x y ca cb (sealAuxB x.level) sealMsk
    (2 ^ 32) hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL (by omega)
    (Validation.Families.sealBFV_behzAuxOK x.level hmem)

end Validation.Families
