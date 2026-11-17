import Challenge.BFVMul.Float

/-!
# Challenge.Families.FloatTol — the HPS-family multiplications at any summation tolerance   (LOCKED definitions and statements; proofs in `Validation/Families/FloatTol.lean`)

`Challenge.BFVMul.Fl.SumsOK` fixes the tolerances of the two floating-point sums of the HPS
family to OpenFHE's: `Spec.BudgetBFV.doubleSw k` (the overflow sum of a base switch over `k`
moduli) and `Spec.BudgetBFV.doubleSr ms` (the fractional sum of a scaling over the moduli `ms`),
the bounds proved for OpenFHE's binary64 summation order (`Challenge.BFVMul.nuSw_tol`,
`nuSr_tol`). Here the tolerances are parameters: `SumsOK' w r S` says each truncated sum of `S`
is the floor of a number within `w k / 2⁵³` (base switch over `k` moduli), resp. `r ms / 2⁵³`
(scaling over `ms`), of its exact value, for ARBITRARY functions `w : ℕ → ℕ`,
`r : List ℕ → ℕ`. A library that sums in another order, in another precision, or exactly, is
covered once its own tolerance functions are proved; the slacks are then those of
`Spec.BudgetBFV.hpsSlack`, `poverqSlack`, `leveledSlack` evaluated at `w`, `r`.

* `stepOK_mul_hps_anyTol`, `stepOK_square_hps_anyTol`: HPS at
  `hpsSlack t N Q R (w k) (w |R|) (r qs)` (with its flag `ok`). No condition on `w`.
* `stepOK_mul_poverq_anyTol`, `stepOK_mul_leveled_anyTol`: the P-over-Q variants, with ONE
  extra hypothesis that OpenFHE's statements do not need: `w m ≤ w k` for every `m ≤ k`. The
  slack charges every base switch at `w k`, but the switches from the auxiliary base `P` (P-over-Q)
  and from `Q_l` and `P_l` (leveled) are over at most `k` moduli; OpenFHE's `doubleSw` is
  monotone (`doubleSw_mono` in the proofs), an arbitrary `w` need not be. Without the hypothesis
  the statements are not proved here (charging the slack at `max (w k) (w |P|)` instead is argued,
  not proved, and not stated).
* `sumsOK'_openfhe`, and `stepOK_mul_hps_tol_openfhe`, `stepOK_square_hps_tol_openfhe`,
  `stepOK_mul_poverq_tol_openfhe`, `stepOK_mul_leveled_tol_openfhe`: the instance
  `w = doubleSw`, `r = doubleSr`. `SumsOK' doubleSw doubleSr` IS `Fl.SumsOK` (by `Iff.rfl`), and
  each `*_openfhe` theorem has, verbatim, the statement of the corresponding locked theorem of
  `Challenge.BFVMul.Float` (`stepOK_mul_hps_tol`, …); the Validation proofs derive them from the
  general statements here, not from the existing proofs, and check the type equality with
  `type_of%`.

**What stays tied to OpenFHE's decomposition.** Only the arithmetic of the two sums and its
error are generalised. Fixed, because they are in the definitions of `Fl.hpsMul`, `Fl.poverqMul`,
`Fl.leveledMul` and `Fl.SumsOK` that this file reuses:

* WHICH quantities are computed approximately. The base switch computes the overflow count as the
  truncation of `1/2 + Σᵢ yᵢ/qᵢ` and subtracts `count·[Q]_p` (OpenFHE's `SwitchCRTBasis`, the
  table `alphaQModp[⌊nu⌋]` modelled as a multiplication); the scaling splits each
  `θᵢ = t·P·[(Q·P/qᵢ)⁻¹]_{qᵢ}` into an integer part `⌊θᵢ/qᵢ⌋ mod p` (exact) and a fractional part
  `(θᵢ mod qᵢ)/qᵢ` (the `…Frac` tables), and only `1/2 + Σᵢ xᵢ·(θᵢ mod qᵢ)/qᵢ` is approximate
  (`Fl.switch1`, `Fl.scale1`). A library that rounds the whole of `t·x/Q` in floating point, or
  splits `θ` differently, is not this algorithm.
* The start value `1/2` and the truncation (`⌊s⌋`, the cast of a nonnegative value).
* The digits and residues the sums read are reduced, in `[0, q)` (`Fl.Reduced`; OpenFHE built
  with `WITH_REDUCED_NOISE=OFF`); centred digits are not covered.
* `floatBasisOK` (at most 128 moduli, each below `2⁶⁰`) is a premise inside `SumsOK'` and a side
  condition of every statement (`floatAuxOK?`), as for OpenFHE.
* The tolerances are numerators over `2⁵³` (`Spec.BudgetBFV.floatDen`), as in the slack formulas.
  Any precision is expressible (a coarser one by a larger numerator), but the denominator is fixed.
* For the leveled variant: the number of dropped limbs is a parameter, and the structure of the
  internal drop (scale `Q → Q_l` with `t = 1`, `POverQ.expandQlHat` back to `Q`) is OpenFHE's.
-/

namespace Challenge.Families
open Spec NPoly Scheme Source Correct Challenge.BFV Spec.Float Challenge.BFVMul

/-- **The sums within the tolerances `w`, `r`.** On reduced arguments over a basis passing
`floatBasisOK`, each truncated sum of `S` is the floor of a number within `w k / 2⁵³` (base
switch, `k` moduli), resp. `r ms / 2⁵³` (scaling over the moduli `ms`), of the exact sum.
`Fl.SumsOK` is `SumsOK' doubleSw doubleSr`. -/
def SumsOK' (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums) : Prop :=
  (∀ (qs : List ℕ) (y : List ℤ), floatBasisOK qs = true → Fl.Reduced qs y →
    ∃ s : ℚ, S.sw qs y = ⌊s⌋ ∧
      |s - Fl.exactSw qs y| ≤ (w qs.length : ℚ) / BudgetBFV.floatDen) ∧
  (∀ (ms : List ℕ) (ns x : List ℤ), floatBasisOK ms = true → Fl.Reduced ms ns → Fl.Reduced ms x →
    ∃ s : ℚ, S.sr ms ns x = ⌊s⌋ ∧
      |s - Fl.exactSr ms ns x| ≤ (r ms : ℚ) / BudgetBFV.floatDen)

/-- **OpenFHE's tolerances are an instance**: `Fl.SumsOK` is `SumsOK'` at `doubleSw`, `doubleSr`. -/
theorem sumsOK'_openfhe (S : Fl.Sums) :
    SumsOK' BudgetBFV.doubleSw BudgetBFV.doubleSr S ↔ Fl.SumsOK S := sorry

variable (P : FullParams)

/-! ## The multiplications at any tolerance -/

/-- **HPS multiplication with sums within any tolerances `w`, `r` meets the `mul` contract** at
the slack `hpsSlack t N Q R (w k) (w |R|) (r qs)`. -/
theorem stepOK_mul_hps_anyTol (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' w r S)
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
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- **HPS squaring with sums within any tolerances meets the `square` contract** at the same
slack. -/
theorem stepOK_square_hps_anyTol (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums)
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
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca ca)) (.square d a) := sorry

/-- **P-over-Q multiplication with sums within any tolerances meets the `mul` contract** at the
slack `poverqSlack t N Q P k (w k) (r ps)`, for an auxiliary basis of at most `k` moduli and a
base-switch tolerance that does not decrease up to `k` moduli (module docstring). -/
theorem stepOK_mul_poverq_anyTol (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums)
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
      (σ.set d (Fl.poverqMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- **Leveled P-over-Q multiplication with sums within any tolerances meets the `mul` contract**
at the slack `leveledSlack t N Q Q_l P_l k (w k) (r (dropped limbs)) (r P_l)`, for every number
`drop` of limbs dropped internally and a base-switch tolerance that does not decrease up to `k`
moduli (module docstring). -/
theorem stepOK_mul_leveled_anyTol (w : ℕ → ℕ) (r : List ℕ → ℕ) (S : Fl.Sums)
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
      (σ.set d (Fl.leveledMul S P.src.t (P.src.qs.take x.level) ps drop ca cb)) (.mul d a b) :=
  sorry

/-! ## OpenFHE's tolerances as an instance

The four statements below are, verbatim, `Challenge.BFVMul.stepOK_mul_hps_tol`,
`stepOK_square_hps_tol`, `stepOK_mul_poverq_tol`, `stepOK_mul_leveled_tol`; they are proved in
`Validation/Families/FloatTol.lean` as the instance `w = doubleSw`, `r = doubleSr` of the
statements above. -/

/-- `Challenge.BFVMul.stepOK_mul_hps_tol`, as an instance of `stepOK_mul_hps_anyTol`. -/
theorem stepOK_mul_hps_tol_openfhe (S : Fl.Sums) (hS : Fl.SumsOK S)
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
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- `Challenge.BFVMul.stepOK_square_hps_tol`, as an instance of `stepOK_square_hps_anyTol`. -/
theorem stepOK_square_hps_tol_openfhe (S : Fl.Sums) (hS : Fl.SumsOK S)
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
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca ca)) (.square d a) := sorry

/-- `Challenge.BFVMul.stepOK_mul_poverq_tol`, as an instance of `stepOK_mul_poverq_anyTol`. -/
theorem stepOK_mul_poverq_tol_openfhe (S : Fl.Sums) (hS : Fl.SumsOK S)
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
      (σ.set d (Fl.poverqMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- `Challenge.BFVMul.stepOK_mul_leveled_tol`, as an instance of `stepOK_mul_leveled_anyTol`. -/
theorem stepOK_mul_leveled_tol_openfhe (S : Fl.Sums) (hS : Fl.SumsOK S)
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
      (σ.set d (Fl.leveledMul S P.src.t (P.src.qs.take x.level) ps drop ca cb)) (.mul d a b) :=
  sorry

-- At zero tolerance the HPS slack is the idealised one (no lift excess, one unit of rounding),
-- while OpenFHE's scaling tolerance over three limbs just below `2⁶⁰` costs a rounding slack of
-- `1 + ⌈2·doubleSr/2⁵³⌉ = 6913` units: a summation order with a smaller proved tolerance
-- lowers it accordingly.
#guard (BudgetBFV.hpsSlack 65537 16384 (2 ^ 180) (2 ^ 240) 0 0 0).e == 0 &&
  (BudgetBFV.hpsSlack 65537 16384 (2 ^ 180) (2 ^ 240) 0 0 0).rho == 1
#guard BudgetBFV.doubleSw 3 == 24 && BudgetBFV.doubleSw 1 ≤ BudgetBFV.doubleSw 3
#guard (BudgetBFV.hpsSlack 65537 16384 (2 ^ 180) (2 ^ 240) (BudgetBFV.doubleSw 3)
    (BudgetBFV.doubleSw 4) (BudgetBFV.doubleSr [2 ^ 60 - 1, 2 ^ 60 - 1, 2 ^ 60 - 1])).rho == 6913

end Challenge.Families
