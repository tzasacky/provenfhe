import Challenge.BFVMul.Float
import FHE.BFV.FloatHPS
import Validation.BFVMul.BEHZ

/-!
# Validation.BFVMul.FloatHPS — HPS multiplication with sums within the tolerances meets the BFV `mul` contract

Proofs of the pins `stepOK_mul_hps_tol` and `stepOK_square_hps_tol` of `Challenge.BFVMul.Float`:
for every `S : Fl.Sums` within the tolerances (`Fl.SumsOK S`), `Fl.hpsMul S` meets the `mul`
(resp. `square`) contract of `Spec.TraceBFV` for every budget with

  `mulLift ≥ mulLiftNormAt P ℓ e`,   `mulRound ≥ mulRoundApprox P rho`,

`⟨e, rho, ok⟩ = Spec.BudgetBFV.hpsSlack t N Q_ℓ R (doubleSw ℓ) (doubleSw |R|) (doubleSr qs)` with
`ok = true`, for every auxiliary basis accepted by `floatAuxOK?`.

Derivation: `FHE.BFV.FloatHPS.hpsMul_lifted'` (the representatives multiplied and the distance of
the result from `t·(A ⊗ B)/Q`, on integers) and `stepOK_mul_lifted` / `stepOK_square_lifted`
(every multiplication of representatives of bounded size meets the contract). Both operands are
lifted by the same map, so squaring uses one lift and is an instance of the `square` contract.
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul

/-- **HPS multiplication with sums within the tolerances meets the `mul` contract** at the slack
`hpsSlack t N Q R (doubleSw k) (doubleSw |R|) (doubleSr qs)`. -/
theorem stepOK_mul_hps_tol (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := by
  have hlen : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  have hok' : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.qs.take x.level).prod ps.prod
      (BudgetBFV.doubleSw (P.src.qs.take x.level).length) (BudgetBFV.doubleSw ps.length)
      (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true := by
    rw [hlen]; exact hok
  obtain ⟨X, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FHE.BFV.FloatHPS.hpsMul_lifted' S hS P.src.t (P.src.qs.take x.level) ps haux hok' ca cb
      hla hlb
  rw [hlen] at hAn hBn hround
  exact stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep hx hy ha hb hla hlb
    h2x h2y hℓ hℓL _ _ X _ hA hB hX hAn hBn hround hout

/-- **HPS squaring with sums within the tolerances meets the `square` contract** at the same
slack. -/
theorem stepOK_square_hps_tol (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca ca)) (.square d a) := by
  have _ := hℓ
  have hlen : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  have hok' : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.qs.take x.level).prod ps.prod
      (BudgetBFV.doubleSw (P.src.qs.take x.level).length) (BudgetBFV.doubleSw ps.length)
      (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true := by
    rw [hlen]; exact hok
  obtain ⟨X, hX, hA, -, hAn, -, hround, hout⟩ :=
    FHE.BFV.FloatHPS.hpsMul_lifted' S hS P.src.t (P.src.qs.take x.level) ps haux hok' ca ca
      hla hla
  rw [hlen] at hAn hround
  exact stepOK_square_lifted P hP _ _ E s hs ρ ρ' σ d a x ca hL hR hstep hx ha hla h2x _ X _
    hA hX hAn hround hout

example : type_of% @Validation.BFVMul.stepOK_mul_hps_tol =
    type_of% @Challenge.BFVMul.stepOK_mul_hps_tol := rfl

example : type_of% @Validation.BFVMul.stepOK_square_hps_tol =
    type_of% @Challenge.BFVMul.stepOK_square_hps_tol := rfl

end Validation.BFVMul
