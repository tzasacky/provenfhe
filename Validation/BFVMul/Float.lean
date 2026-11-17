import Challenge.BFVMul.Float
import Validation.BFVMul.FloatSums
import Validation.BFVMul.FloatHPS
import Validation.BFVMul.FloatPOverQ

/-!
# Validation.BFVMul.Float — OpenFHE's HPS-family multiplications in any conforming binary64 arithmetic

Proofs of `Challenge.BFVMul.stepOK_mul_hps_float`, `stepOK_square_hps_float`,
`stepOK_mul_poverq_float`, `stepOK_mul_leveled_float`: the statements for sums within the
tolerances (`Validation/BFVMul/FloatHPS.lean`, `FloatPOverQ.lean`) at `S = Fl.floatSums A`, which
is within the tolerances for every conforming `A` (`floatSums_ok`, `Validation/BFVMul/FloatSums.lean`).
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul Spec.Float

theorem stepOK_mul_hps_float (P : FullParams) (A : Arith) (hA : Conforms A)
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
      (σ.set d (Fl.hpsMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps ca cb))
      (.mul d a b) :=
  stepOK_mul_hps_tol P (Fl.floatSums A) (floatSums_ok A hA) hP E s hs ρ ρ' σ d a b x y ca cb ps hL hR hok hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL haux

example : type_of% @Validation.BFVMul.stepOK_mul_hps_float =
    type_of% @Challenge.BFVMul.stepOK_mul_hps_float := rfl

example : type_of% @Validation.BFVMul.stepOK_mul_hps_tol =
    type_of% @Challenge.BFVMul.stepOK_mul_hps_tol := rfl

theorem stepOK_square_hps_float (P : FullParams) (A : Arith) (hA : Conforms A)
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
      (σ.set d (Fl.hpsMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps ca ca))
      (.square d a) :=
  stepOK_square_hps_tol P (Fl.floatSums A) (floatSums_ok A hA) hP E s hs ρ ρ' σ d a x ca ps hL hR hok hstep hx ha hla h2x hℓ hℓL haux

example : type_of% @Validation.BFVMul.stepOK_square_hps_float =
    type_of% @Challenge.BFVMul.stepOK_square_hps_float := rfl

example : type_of% @Validation.BFVMul.stepOK_square_hps_tol =
    type_of% @Challenge.BFVMul.stepOK_square_hps_tol := rfl

theorem stepOK_mul_poverq_float (P : FullParams) (A : Arith) (hA : Conforms A)
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
      (σ.set d (Fl.poverqMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps ca cb))
      (.mul d a b) :=
  stepOK_mul_poverq_tol P (Fl.floatSums A) (floatSums_ok A hA) hP E s hs ρ ρ' σ d a b x y ca cb ps hL hR hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL hps haux

example : type_of% @Validation.BFVMul.stepOK_mul_poverq_float =
    type_of% @Challenge.BFVMul.stepOK_mul_poverq_float := rfl

example : type_of% @Validation.BFVMul.stepOK_mul_poverq_tol =
    type_of% @Challenge.BFVMul.stepOK_mul_poverq_tol := rfl

theorem stepOK_mul_leveled_float (P : FullParams) (A : Arith) (hA : Conforms A)
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
      (σ.set d (Fl.leveledMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps drop ca cb))
      (.mul d a b) :=
  stepOK_mul_leveled_tol P (Fl.floatSums A) (floatSums_ok A hA) hP E s hs ρ ρ' σ d a b x y ca cb ps drop hL hR hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL haux

example : type_of% @Validation.BFVMul.stepOK_mul_leveled_float =
    type_of% @Challenge.BFVMul.stepOK_mul_leveled_float := rfl

example : type_of% @Validation.BFVMul.stepOK_mul_leveled_tol =
    type_of% @Challenge.BFVMul.stepOK_mul_leveled_tol := rfl

end Validation.BFVMul
