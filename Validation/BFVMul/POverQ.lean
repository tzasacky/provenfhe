import Challenge.BFVMul.POverQ
import FHE.BFV.MulPOverQLeveled
import Validation.BFVMul.Lifted

/-!
# Validation.BFVMul.POverQ — idealised P-over-Q multiplication meets the BFV `mul` contract

`stepOK_mul_poverq`: the limb-level `Challenge.BFVMul.poverqMul` (OpenFHE `HPSPOVERQ`: exact
extension of operand 1, fast scaling by `P/Q` of operand 2, limb-wise tensor, RNS scale-and-round
by `t/P`; the floating-point sums of the library replaced by exact rounding) meets the `mul`
contract of `Spec.TraceBFV` for every budget with

  `mulLift ≥ mulLiftNormAt P ℓ e`,   `mulRound ≥ mulRoundApprox P rho`,

`⟨e, rho, _⟩ = Spec.BudgetBFV.poverqSlack t N Q_ℓ P ℓ 0 0` (`e = ⌈2ℓQ/P⌉`,
`rho = 1 + ⌈2tNℓQ/P⌉`), for every auxiliary basis `ps` accepted by `poverqAuxOK?` (positive,
pairwise coprime moduli).

Derivation: `FHE.BFV.MulPOverQ.poverqMul_lifted` (the representatives multiplied and the distance
of the result from `t·(A ⊗ B)/Q`, on integers) and `Validation.BFVMul.stepOK_mul_lifted` (every
multiplication of representatives of bounded size meets the contract).

`stepOK_mul_leveled`: the same for `Challenge.BFVMul.leveledMul` (OpenFHE `HPSPOVERQLEVELED`
with `drop` limbs dropped internally) and `Spec.BudgetBFV.leveledSlack t N Q_ℓ Q_{ℓ−drop} P_l ℓ 0 0 0`,
from `FHE.BFV.MulPOverQ.leveledMul_lifted` (`FHE/BFV/MulPOverQLeveled.lean`).

There is no `square` theorem: the library's squaring is this multiplication with both operands
equal, which lifts the operand in two different ways, so it is a `mul a a` (the theorem allows
`a = b`), not an instance of the `square` contract's hypothesis of one lift.
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul

/-- **Idealised P-over-Q multiplication meets the `mul` contract** within the budget of the
slack `Spec.BudgetBFV.poverqSlack` at zero floating-point tolerances, for two-component operands
at level `ℓ` with ciphertext basis the first `ℓ` moduli and any auxiliary basis `ps` accepted by
`poverqAuxOK?`. The two operands may be the same variable. -/
theorem stepOK_mul_poverq (P : FullParams) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level 0 0).e
          ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level 0 0).rho
          ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : poverqAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (poverqMul P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := by
  obtain ⟨A, B, X, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FHE.BFV.MulPOverQ.poverqMul_lifted P.src.t (P.src.qs.take x.level) ps haux ca cb hla hlb
  have hlen : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  rw [hlen] at hAn hBn hround
  exact stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep hx hy ha hb hla hlb
    h2x h2y hℓ hℓL A B X _ hA hB hX hAn hBn hround hout

/-- **Idealised leveled P-over-Q multiplication meets the `mul` contract** (OpenFHE
`HPSPOVERQLEVELED` with `drop` limbs dropped internally; `Challenge.BFVMul.leveledMul`) within the
budget of the slack `Spec.BudgetBFV.leveledSlack` at zero floating-point tolerances: operands at
level `ℓ`, the product computed at the first `ℓ − drop` limbs of the ciphertext basis and of the
auxiliary basis `ps`, for every `ps` and `drop` accepted by `leveledAuxOK?`. -/
theorem stepOK_mul_leveled (P : FullParams) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ) (drop : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level 0 0 0).e
          ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level 0 0 0).rho
          ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : leveledAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps drop = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (leveledMul P.src.t (P.src.qs.take x.level) ps drop ca cb)) (.mul d a b) := by
  obtain ⟨A, B, X, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FHE.BFV.MulPOverQ.leveledMul_lifted P.src.t (P.src.qs.take x.level) ps drop haux ca cb hla hlb
  have hlen : (P.src.qs.take x.level).length = x.level := by
    rw [List.length_take]; exact Nat.min_eq_left hℓL
  have htake : (P.src.qs.take x.level).take (x.level - drop) = P.src.qs.take (x.level - drop) := by
    rw [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)]
  rw [hlen, htake] at hAn hBn hround
  exact stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep hx hy ha hb hla hlb
    h2x h2y hℓ hℓL A B X _ hA hB hX hAn hBn hround hout

end Validation.BFVMul
