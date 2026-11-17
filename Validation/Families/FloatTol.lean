import Challenge.Families.FloatTol
import Validation.Families.FloatTolCore
import Validation.BFVMul.FloatHPS
import Validation.BFVMul.FloatPOverQ

/-!
# Validation.Families.FloatTol — proofs of the pins of `Challenge.Families.FloatTol`

The general statements: `Validation.Families.FloatTol.hpsMul_liftedT`, `poverqMul_liftedT`,
`leveledMul_liftedT` (the integer facts at any tolerance, `Validation/Families/FloatTolCore.lean`)
and `Validation.BFVMul.stepOK_mul_lifted` / `stepOK_square_lifted`, as in
`Validation/BFVMul/Float{HPS,POverQ}.lean`. The OpenFHE instances are the general statements at
`w = doubleSw`, `r = doubleSr` (`Fl.SumsOK S` is `SumsOK' doubleSw doubleSr S` by definition; the
monotonicity hypothesis of the P-over-Q statements is `FHE.BFV.FloatPOverQ.doubleSw_mono`); they
do not use the proofs of `Validation.BFVMul.stepOK_mul_hps_tol` etc. The `example`s at the end
check that each instance has the type of the corresponding locked theorem of
`Challenge.BFVMul.Float`.
-/

namespace Validation.Families
open Spec NPoly Scheme Source Correct Challenge.BFV Spec.Float Challenge.BFVMul Challenge.Families

theorem sumsOK'_openfhe (S : Fl.Sums) :
    SumsOK' BudgetBFV.doubleSw BudgetBFV.doubleSr S ↔ Fl.SumsOK S := by
  exact Iff.rfl

theorem stepOK_mul_hps_anyTol (P : FullParams) (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' w r S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (w x.level) (w ps.length) (r (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (w x.level) (w ps.length) (r (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (w x.level) (w ps.length) (r (P.src.qs.take x.level))).ok = true)
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
      (w (P.src.qs.take x.level).length) (w ps.length)
      (r (P.src.qs.take x.level))).ok = true := by
    rw [hlen]; exact hok
  obtain ⟨X, hX, hA, hB, hAn, hBn, hround, hout⟩ :=
    FloatTol.hpsMul_liftedT w r S hS P.src.t (P.src.qs.take x.level) ps haux hok' ca cb hla hlb
  rw [hlen] at hAn hBn hround
  exact Validation.BFVMul.stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep
    hx hy ha hb hla hlb h2x h2y hℓ hℓL _ _ X _ hA hB hX hAn hBn hround hout

theorem stepOK_square_hps_anyTol (P : FullParams) (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums)
    (hS : SumsOK' w r S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (w x.level) (w ps.length) (r (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (w x.level) (w ps.length) (r (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (w x.level) (w ps.length) (r (P.src.qs.take x.level))).ok = true)
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
      (w (P.src.qs.take x.level).length) (w ps.length)
      (r (P.src.qs.take x.level))).ok = true := by
    rw [hlen]; exact hok
  obtain ⟨X, hX, hA, -, hAn, -, hround, hout⟩ :=
    FloatTol.hpsMul_liftedT w r S hS P.src.t (P.src.qs.take x.level) ps haux hok' ca ca hla hla
  rw [hlen] at hAn hround
  exact Validation.BFVMul.stepOK_square_lifted P hP _ _ E s hs ρ ρ' σ d a x ca hL hR hstep hx ha
    hla h2x _ X _ hA hX hAn hround hout

theorem stepOK_mul_poverq_anyTol (P : FullParams) (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums)
    (hS : SumsOK' w r S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hw : ∀ m ≤ x.level, w m ≤ w x.level)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (w x.level) (r ps)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (w x.level) (r ps)).rho ≤ E.mulRound)
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
    FloatTol.poverqMul_liftedT w r S hS P.src.t (P.src.qs.take x.level) ps haux
      (by rw [hlen]; exact hps) (by rw [hlen]; exact hw) ca cb hla hlb
  rw [hlen] at hAn hBn hround
  exact Validation.BFVMul.stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep
    hx hy ha hb hla hlb h2x h2y hℓ hℓL A B X _ hA hB hX hAn hBn hround hout

theorem stepOK_mul_leveled_anyTol (P : FullParams) (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums)
    (hS : SumsOK' w r S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ) (drop : ℕ)
    (hw : ∀ m ≤ x.level, w m ≤ w x.level)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (w x.level)
              (r ((P.src.qs.take x.level).drop (x.level - drop)))
              (r (ps.take (x.level - drop)))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (w x.level)
              (r ((P.src.qs.take x.level).drop (x.level - drop)))
              (r (ps.take (x.level - drop)))).rho ≤ E.mulRound)
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
    FloatTol.leveledMul_liftedT w r S hS P.src.t (P.src.qs.take x.level) ps drop
      (by rw [hlen]; exact haux) (by rw [hlen]; exact hw) ca cb hla hlb
  have htake : (P.src.qs.take x.level).take (x.level - drop) =
      P.src.qs.take (x.level - drop) := by
    rw [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)]
  rw [hlen, htake] at hAn hBn hround
  exact Validation.BFVMul.stepOK_mul_lifted P hP _ _ E s hs ρ ρ' σ d a b x y ca cb hL hR hstep
    hx hy ha hb hla hlb h2x h2y hℓ hℓL A B X _ hA hB hX hAn hBn hround hout

theorem stepOK_mul_hps_tol_openfhe (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
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
  exact stepOK_mul_hps_anyTol P BudgetBFV.doubleSw BudgetBFV.doubleSr S hS hP E s hs ρ ρ' σ d a b
    x y ca cb ps hL hR hok hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL haux

theorem stepOK_square_hps_tol_openfhe (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
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
  exact stepOK_square_hps_anyTol P BudgetBFV.doubleSw BudgetBFV.doubleSr S hS hP E s hs ρ ρ' σ d a
    x ca ps hL hR hok hstep hx ha hla h2x hℓ hℓL haux

theorem stepOK_mul_poverq_tol_openfhe (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
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
  exact stepOK_mul_poverq_anyTol P BudgetBFV.doubleSw BudgetBFV.doubleSr S hS hP E s hs ρ ρ' σ d a
    b x y ca cb ps (fun _ hm => FHE.BFV.FloatPOverQ.doubleSw_mono hm) hL hR hstep hx hy ha hb hla
    hlb h2x h2y hℓ hℓL hps haux

theorem stepOK_mul_leveled_tol_openfhe (P : FullParams) (S : Fl.Sums) (hS : Fl.SumsOK S)
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
  exact stepOK_mul_leveled_anyTol P BudgetBFV.doubleSw BudgetBFV.doubleSr S hS hP E s hs ρ ρ' σ d
    a b x y ca cb ps drop (fun _ hm => FHE.BFV.FloatPOverQ.doubleSw_mono hm) hL hR hstep hx hy ha
    hb hla hlb h2x h2y hℓ hℓL haux

example : type_of% @Validation.Families.stepOK_mul_hps_tol_openfhe =
    type_of% @Challenge.BFVMul.stepOK_mul_hps_tol := rfl

example : type_of% @Validation.Families.stepOK_square_hps_tol_openfhe =
    type_of% @Challenge.BFVMul.stepOK_square_hps_tol := rfl

example : type_of% @Validation.Families.stepOK_mul_poverq_tol_openfhe =
    type_of% @Challenge.BFVMul.stepOK_mul_poverq_tol := rfl

example : type_of% @Validation.Families.stepOK_mul_leveled_tol_openfhe =
    type_of% @Challenge.BFVMul.stepOK_mul_leveled_tol := rfl

end Validation.Families
