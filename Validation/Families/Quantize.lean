import Challenge.Families.Quantize
import Validation.BFVMul.Approx
import Validation.BFVMul.BEHZ
import FHE.BFV.MulHPS

/-!
# Validation.Families.Quantize — proofs of the pins of `Challenge.Families.Quantize`

Rounding before scaling is an approximate multiplication with rounding slack `t·ρ₀`:
`2·|Q·(t·D) − t·T| = t·2·|Q·D − T| ≤ t·Q·ρ₀`, so `Validation.BFVMul.stepOK_mul_approx`
(`stepOK_square_approx`) applies with `X = t·D`. The exact quotient:
`FHE.BFV.MulHPS.roundDiv_bounds`.
The closed fact about Lattigo's example set is a kernel computation.
-/

namespace Validation.Families
open Spec NPoly Scheme Source Challenge.BFV Challenge.BFVMul Challenge.Families

variable (P : FullParams)

/-- The rounding inequality of `stepOK_mul_approx` for `X = t·D`. -/
theorem quantize_round_scaled {N : ℕ} (Q t ρ₀ : ℕ) (D T : List (IntPoly N))
    (h : ∀ (j : ℕ) (i : Fin N), 2 * |(Q : ℤ) * (D.getD j 0).coeff i - (T.getD j 0).coeff i|
      ≤ (Q : ℤ) * ρ₀) (j : ℕ) (i : Fin N) :
    2 * |(Q : ℤ) *
          ((D.map fun p => (⟨fun i => (t : ℤ) * p.coeff i⟩ : IntPoly N)).getD j 0).coeff i -
        (t : ℤ) * (T.getD j 0).coeff i| ≤ (Q : ℤ) * ((t * ρ₀ : ℕ) : ℤ) := by
  have hg : ((D.map fun p => (⟨fun i => (t : ℤ) * p.coeff i⟩ : IntPoly N)).getD j 0).coeff i =
      (t : ℤ) * (D.getD j 0).coeff i := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases D[j]? <;> rfl
  rw [hg]
  have hj := h j i
  have ht : (0 : ℤ) ≤ t := by positivity
  have e2 : (Q : ℤ) * ((t : ℤ) * (D.getD j 0).coeff i) - (t : ℤ) * (T.getD j 0).coeff i =
      (t : ℤ) * ((Q : ℤ) * (D.getD j 0).coeff i - (T.getD j 0).coeff i) := by ring
  rw [e2, abs_mul, abs_of_nonneg ht]
  push_cast
  nlinarith [abs_nonneg ((Q : ℤ) * (D.getD j 0).coeff i - (T.getD j 0).coeff i)]

theorem stepOK_mul_quantize (hP : SchemeParamsOK P) (U ρ₀ : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua ub D out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hub : ub.length = 2) (hD : D.length = 3)
    (hUa : ∀ u ∈ ua, normInf u ≤ U) (hUb : ∀ u ∈ ub, normInf u ≤ U)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) cb ub)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := by
  have hr := quantize_round_scaled (P.src.modulus x.level) P.src.t ρ₀ D _ hquant
  have hX :
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).length = 3 := by
    rw [List.length_map]; exact hD
  exact Validation.BFVMul.stepOK_mul_approx P hP U (P.src.t * ρ₀) E hL hR s hs ρ ρ' σ d a b x y
    ca cb hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL ua ub _ out hua hub hX hUa hUb hr hout

theorem stepOK_square_quantize (hP : SchemeParamsOK P) (U ρ₀ : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua D out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hD : D.length = 3) (hUa : ∀ u ∈ ua, normInf u ≤ U)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) ca ua)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := by
  have hr := quantize_round_scaled (P.src.modulus x.level) P.src.t ρ₀ D _ hquant
  have hX :
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).length = 3 := by
    rw [List.length_map]; exact hD
  exact Validation.BFVMul.stepOK_square_approx P hP U (P.src.t * ρ₀) E hL hR s hs ρ ρ' σ d a x ca
    hstep hx ha hla h2x hℓ hℓL ua _ out hua hX hUa hr hout

theorem stepOK_mul_quantize_lifted (hP : SchemeParamsOK P) (e ρ₀ : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (A B D out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hB : B.map (ofInt (P.src.modulus x.level)) = cb.map (ofInt (P.src.modulus x.level)))
    (hD : D.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hBn : ∀ p ∈ B, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor A B).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := by
  have hr := quantize_round_scaled (P.src.modulus x.level) P.src.t ρ₀ D _ hquant
  have hX :
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).length = 3 := by
    rw [List.length_map]; exact hD
  exact Validation.BFVMul.stepOK_mul_lifted P hP e (P.src.t * ρ₀) E s hs ρ ρ' σ d a b x y ca cb
    hL hR hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL A B _ out hA hB hX hAn hBn hr hout

theorem stepOK_square_quantize_lifted (hP : SchemeParamsOK P) (e ρ₀ : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (A D out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hD : D.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor A A).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := by
  have hr := quantize_round_scaled (P.src.modulus x.level) P.src.t ρ₀ D _ hquant
  have hX :
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).length = 3 := by
    rw [List.length_map]; exact hD
  exact Validation.BFVMul.stepOK_square_lifted P hP e (P.src.t * ρ₀) E s hs ρ ρ' σ d a x ca hL hR
    hstep hx ha hla h2x A _ out hA hX hAn hr hout

theorem quantize_round_ok (T : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    2 * |(Q : ℤ) * roundDiv T Q - T| ≤ (Q : ℤ) * 1 := by
  obtain ⟨h1, h2⟩ := FHE.BFV.MulHPS.roundDiv_bounds T Q hQ
  have e : 2 * |(Q : ℤ) * roundDiv T Q - T| = |2 * ((Q : ℤ) * roundDiv T Q - T)| := by
    rw [abs_mul]; norm_num
  rw [mul_one, e, abs_le]
  constructor <;> nlinarith

theorem lattigo_quantizeAuxOK : ∀ ℓ ∈ List.range' 1 12,
    quantizeAuxOK? 16384 (lattigoQs.take ℓ) (lattigoQMulAt 16384 lattigoQs lattigoQMul ℓ) 0 1 &&
      quantizeAuxOK? 16384 (lattigoQs.take ℓ) (lattigoQMulAt 16384 lattigoQs lattigoQMul ℓ) 1 3
    = true := by
  decide +kernel

end Validation.Families
