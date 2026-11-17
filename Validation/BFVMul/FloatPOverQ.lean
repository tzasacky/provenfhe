import Challenge.BFVMul.Float
import FHE.BFV.FloatLeveled
import Validation.BFVMul.Lifted

/-!
# Validation.BFVMul.FloatPOverQ — P-over-Q multiplication with sums within the tolerances meets the BFV `mul` contract

`stepOK_mul_poverq_tol`: the limb-level `Challenge.BFVMul.Fl.poverqMul S` (OpenFHE `HPSPOVERQ`
with the two truncated sums taken from `S`), for every `S` with `Fl.SumsOK S`, meets the `mul`
contract of `Spec.TraceBFV` within the budget of the slack
`Spec.BudgetBFV.poverqSlack t N Q_ℓ P ℓ (doubleSw ℓ) (doubleSr ps)`, for every auxiliary basis of
at most `ℓ` moduli accepted by `floatAuxOK?`.

`stepOK_mul_leveled_tol`: the same for `Fl.leveledMul S` (OpenFHE `HPSPOVERQLEVELED` with `drop`
limbs dropped internally) and
`Spec.BudgetBFV.leveledSlack t N Q_ℓ Q_{ℓ−drop} P_l ℓ (doubleSw ℓ) (doubleSr (dropped limbs)) (doubleSr P_l)`.

Derivation: `FHE.BFV.FloatPOverQ.poverqMul_lifted`, `FHE.BFV.FloatLeveled.leveledMul_lifted` (the
representatives multiplied and the distance of the result from `t·(A ⊗ B)/Q`, on integers) and
`Validation.BFVMul.stepOK_mul_lifted`. Neither needs the flag `ok` of the slack.
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul

/-- **P-over-Q multiplication with sums within the tolerances meets the `mul` contract** at the
slack `poverqSlack t N Q P k (doubleSw k) (doubleSr ps)`, for an auxiliary basis of at most `k`
moduli. -/
theorem stepOK_mul_poverq_tol (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSr ps)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSr ps)).rho ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (hps : ps.length ≤ x.level)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.poverqMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := by
  have hlen : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  obtain ⟨A, B, X, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FHE.BFV.FloatPOverQ.poverqMul_lifted S hS P.src.t (P.src.qs.take x.level) ps haux
      (by rw [hlen]; exact hps) ca cb hla hlb
  rw [hlen] at hAn hBn hround
  exact stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep hx hy ha hb hla hlb
    h2x h2y hℓ hℓL A B X _ hA hB hX hAn hBn hround hout

/-- **Leveled P-over-Q multiplication with sums within the tolerances meets the `mul` contract**
at the slack `leveledSlack t N Q Q_l P_l k (doubleSw k) (doubleSr (dropped limbs)) (doubleSr P_l)`,
for every number `1 ≤ drop < k` of limbs dropped internally. -/
theorem stepOK_mul_leveled_tol (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ) (drop : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (BudgetBFV.doubleSw x.level)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))
              (BudgetBFV.doubleSr (ps.take (x.level - drop)))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (BudgetBFV.doubleSw x.level)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))
              (BudgetBFV.doubleSr (ps.take (x.level - drop)))).rho ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) (ps.take (x.level - drop)) = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.leveledMul S P.src.t (P.src.qs.take x.level) ps drop ca cb)) (.mul d a b) := by
  have hlen : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  obtain ⟨A, B, X, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FHE.BFV.FloatLeveled.leveledMul_lifted S hS P.src.t (P.src.qs.take x.level) ps drop
      (by rw [hlen]; exact haux) ca cb hla hlb
  have htake : (P.src.qs.take x.level).take (x.level - drop) = P.src.qs.take (x.level - drop) := by
    rw [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)]
  rw [hlen, htake] at hAn hBn hround
  exact stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep hx hy ha hb hla hlb
    h2x h2y hℓ hℓL A B X _ hA hB hX hAn hBn hround hout

end Validation.BFVMul
