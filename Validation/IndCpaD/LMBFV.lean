import Challenge.IndCpaD.LMBFV
import Validation.IndCpaD.LMInstance
import Validation.IndCpaD.Profile
import Validation.BFV.Domain
import Validation.RealizeBFV
import Validation.BFVEncrypt

/-!
# Validation.IndCpaD.LMBFV — proofs of the pins of `Challenge.IndCpaD.LMBFV`

As `Validation.IndCpaD.ProfileBGVKS` for BFV: the evaluator's run is an induction over the body
with the shapes, the levels and "the evaluator's environment is the zero-message replay"
(`Validation.BFV.SoundAux.step_zenv`); each step is the textbook BFV pin of `Validation.BFV` or
the key-switch pin of `Validation.RealizeBFV` with the keys the public key carries for the
operand's level; the profile is constant, so the per-instruction budget of `RunAt` is `E` at
every position. Locality is by the shapes of `Validation.IndCpaD.LMInstance`. The locked
definitions are read through `show`/`change`.
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.Encrypt Spec.EncryptBFV Spec.IndCpaD Spec.IndCpaDProfile
  Spec.IndCpaDLM Challenge.IndCpaDLM Challenge.IndCpaDProfile Challenge.Source Challenge.BFV
  Challenge.RealizeBFV MeasureTheory
open Validation.Budget.RunAux (Shape Levels levels_step)
open Validation.BFV.SoundAux (zenv zv)
open Validation.Ring Validation.Scheme

/-! ## Locality -/

section Shapes
variable {P : FullParams} {Pr : Params} {σ σ₂ σ' : Trace.CtEnv P} {ρ ρ₂ : Env Pr} {d a c : Var}

theorem shapeR2 (F : Val Pr → List (IntPoly P.src.N) → List (IntPoly P.src.N) →
      List (IntPoly P.src.N))
    (h : (ρ a).bind (fun x => (σ a).bind fun ca => (σ c).map fun cb => σ.set d (F x ca cb)) =
      some σ')
    (hr : Ext ρ ρ₂) (hs : Ext σ σ₂) :
    ∃ ct, σ' = σ.set d ct ∧
      (ρ₂ a).bind (fun x => (σ₂ a).bind fun ca => (σ₂ c).map fun cb => σ₂.set d (F x ca cb)) =
        some (σ₂.set d ct) := by
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ca, hca, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F x ca cb, rfl, by rw [hr a x hx, hs a ca hca]; simp [hs c cb hcb]⟩

theorem progR2 (F : Val Pr → List (IntPoly P.src.N) → List (IntPoly P.src.N) →
      List (IntPoly P.src.N))
    (h0 : (ρ a).isSome) (h : (σ a).isSome) (h' : (σ c).isSome) :
    ((ρ a).bind fun x => (σ a).bind fun ca => (σ c).map fun cb => σ.set d (F x ca cb)).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h'
  rw [hx]; simp [hca, hcb]

end Shapes

theorem bfvStep_interpOK (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    InterpOK D (bfvStepFn D lay rk gk) := by
  refine ⟨fun pk ρ ρ₂ σ σ₂ i σ' hr hs h => ?_, fun pk ρ σ i ρ' h hd => ?_⟩
  · cases i with
    | add d a c => exact shape2 (fun ca cb => padZip (· + ·) ca cb) h hs
    | sub d a c => exact shape2 (fun ca cb => padZip (· - ·) ca cb) h hs
    | mul d a c =>
      exact shapeR2 (fun x ca cb => bfvMul D.Pe.src.t (D.Pe.src.modulus x.level) ca cb) h hr hs
    | square d a =>
      exact shapeR (fun x ca => bfvMul D.Pe.src.t (D.Pe.src.modulus x.level) ca ca) h hr hs
    | mulConst d a k => exact shape1 (fun ca => ca.map (bfvMulConst k)) h hs
    | copy d a => exact shape1 (fun ca => ca) h hs
    | toEval d a => exact shape1 (fun ca => ca) h hs
    | toCoeff d a => exact shape1 (fun ca => ca) h hs
    | dropLimbs d a k => exact shape1 (fun ca => ca) h hs
    | automorph d a g => exact shape1 (fun ca => ca.map (automorph g)) h hs
    | addPlain d a c =>
      exact shapeR2 (fun x ca cp => bfvAddPlain D.Pe.src.t (D.Pe.src.modulus x.level) ca
        (cp.headD 0)) h hr hs
    | subPlain d a c =>
      exact shapeR2 (fun x ca cp => bfvSubPlain D.Pe.src.t (D.Pe.src.modulus x.level) ca
        (cp.headD 0)) h hr hs
    | mulPlain d a c => exact shape2 (fun ca cp => ca.map (cp.headD 0 * ·)) h hs
    | relin d a =>
      exact shapeR (fun x ca => relinBFV D.Pe lay x.level ca (rk pk x.level)) h hr hs
    | keySwitch d a =>
      exact shapeR (fun x ca => keySwitchBFV D.Pe lay x.level ca (gk pk x.key x.level)) h hr hs
    | modSwitch d a =>
      exact shapeR (fun x ca => ca.map (bfvModSwitchComp D.Pe.src.qs[x.level - 1]!)) h hr hs
  · have hone : ∀ a, (∃ x, ρ a = some x) → (σ a).isSome := fun a ⟨x, hx⟩ =>
      hd a (by rw [hx]; rfl)
    cases i with
    | add d a c | sub d a c | mulPlain d a c =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      rcases hy : ρ c with _ | y
      · simp [step, hx, hy] at h
      have h1 := hone a ⟨x, hx⟩
      have h2 := hone c ⟨y, hy⟩
      first
      | exact prog2 (fun ca cb => padZip (· + ·) ca cb) h1 h2
      | exact prog2 (fun ca cb => padZip (· - ·) ca cb) h1 h2
      | exact prog2 (fun ca cp => ca.map (cp.headD 0 * ·)) h1 h2
    | mul d a c | addPlain d a c | subPlain d a c =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      rcases hy : ρ c with _ | y
      · simp [step, hx, hy] at h
      have h1 := hone a ⟨x, hx⟩
      have h2 := hone c ⟨y, hy⟩
      have h0 : (ρ a).isSome := by rw [hx]; rfl
      first
      | exact progR2 (fun x ca cb => bfvMul D.Pe.src.t (D.Pe.src.modulus x.level) ca cb) h0 h1 h2
      | exact progR2 (fun x ca cp => bfvAddPlain D.Pe.src.t (D.Pe.src.modulus x.level) ca
          (cp.headD 0)) h0 h1 h2
      | exact progR2 (fun x ca cp => bfvSubPlain D.Pe.src.t (D.Pe.src.modulus x.level) ca
          (cp.headD 0)) h0 h1 h2
    | mulConst d a _ | copy d a | toEval d a | toCoeff d a | dropLimbs d a _ | automorph d a _ =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      have h1 := hone a ⟨x, hx⟩
      first
      | exact prog1 (fun ca => ca.map (bfvMulConst _)) h1
      | exact prog1 (fun ca => ca) h1
      | exact prog1 (fun ca => ca.map (automorph _)) h1
    | square d a | relin d a | keySwitch d a | modSwitch d a =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      have h1 := hone a ⟨x, hx⟩
      have h0 : (ρ a).isSome := by rw [hx]; rfl
      first
      | exact progR (fun x ca => bfvMul D.Pe.src.t (D.Pe.src.modulus x.level) ca ca) h0 h1
      | exact progR (fun x ca => relinBFV D.Pe lay x.level ca (rk pk x.level)) h0 h1
      | exact progR (fun x ca => keySwitchBFV D.Pe lay x.level ca (gk pk x.key x.level)) h0 h1
      | exact progR (fun x ca => ca.map (bfvModSwitchComp D.Pe.src.qs[x.level - 1]!)) h0 h1

/-! ## The run -/

theorem shape_step_bfv {P : FullParams} {E : TraceBFV.Budget} {s : IntPoly P.src.N}
    {ρ ρ' : Env P.src} {σ σ' : Trace.CtEnv P} {i : Instr} (h : Shape P ρ σ)
    (hstep : step P.src ρ i = some ρ') (hok : TraceBFV.StepOK P E s ρ ρ' σ σ' i) :
    Shape P ρ' σ' := by
  obtain ⟨w, hw⟩ := Validation.Headline.NoiseAux.step_set hstep
  obtain ⟨v, ct, hv, hlen, hσ', -⟩ := hok
  intro y vy hy
  by_cases hyd : y = Trace.dst i
  · subst hyd
    rw [hv] at hy; cases hy
    exact ⟨ct, by rw [hσ']; simp [Trace.CtEnv.set], hlen⟩
  · rw [hw] at hy
    simp only [Env.set, hyd, ite_false] at hy
    obtain ⟨ct', h1, h2⟩ := h y vy hy
    exact ⟨ct', by rw [hσ']; simp [Trace.CtEnv.set, hyd, h1], h2⟩

section Run
variable {P : FullParams} {lay : Budget.KSLayout} {rots : List ℕ} {E : TraceBFV.Budget}
  {s : IntPoly P.src.N} {rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N)}
  {gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N)}

theorem bfvSide_facts (h : bfvSide P lay = true) :
    Budget.SpecialOK P ∧ ksDeclOK? P lay = true ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := by
  change (Budget.specialOK? P && ksDeclOK? P lay &&
    (List.range P.src.qs.length).all fun j => lay.okAt (j + 1)) = true at h
  simp only [Bool.and_eq_true] at h
  refine ⟨Validation.Budget.specialOK?_sound P h.1.1, h.1.2, fun ℓ h1 hℓ => ?_⟩
  have := List.all_eq_true.mp h.2 (ℓ - 1) (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h1] at this

variable (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P) (hside : bfvSide P lay = true)
  (hs : SecretOK P.secretBound s)
  (hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
    Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
    ∀ g ∈ rots, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ))
include hk hP hside hs hkeys

theorem bfv_step {ρ ρ' : Env P.src} {σ : Trace.CtEnv P} (i : Instr) (hsh : Shape P ρ σ)
    (hlv : Levels P ρ) (hneed : bfvNeedAt P lay rots E (zenv ρ) i = true)
    (hstep : step P.src ρ i = some ρ') :
    ∃ σ', bfvStep P lay rk gk (zenv ρ) σ i = some σ' ∧ TraceBFV.StepOK P E s ρ ρ' σ σ' i := by
  obtain ⟨hS, hdecl, hok⟩ := bfvSide_facts hside
  have plain : ∀ {p : Var} {y : Val P.src} {cb : List (IntPoly P.src.N)}, y.parts = 1 →
      cb.length = y.parts → ∃ c, cb = [c] := fun hy1 hlb =>
    List.length_eq_one_iff.mp (hlb.trans hy1)
  cases i with
  | add d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    refine ⟨_, ?_, Validation.BFV.stepOK_add_padded P E s ρ ρ' σ d a b x y ca cb hstep hx hy
      ha hb hla hlb⟩
    show (σ a).bind (fun ca => (σ b).map fun cb => σ.set d (padZip (· + ·) ca cb)) = _
    rw [ha, hb]; rfl
  | sub d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    refine ⟨_, ?_, Validation.BFV.stepOK_sub_padded P E s ρ ρ' σ d a b x y ca cb hstep hx hy
      ha hb hla hlb⟩
    show (σ a).bind (fun ca => (σ b).map fun cb => σ.set d (padZip (· - ·) ca cb)) = _
    rw [ha, hb]; rfl
  | mul d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hzy : zenv ρ b = some (zv y) := by simp [zenv, hy]
    have hn : ((zenv ρ a).elim true fun x => (zenv ρ b).elim true fun y =>
        decide (BudgetBFV.mulLift P ≤ E.mulLift) && decide (BudgetBFV.mulRound P ≤ E.mulRound) &&
          decide (x.parts = 2) && decide (y.parts = 2)) = true := hneed
    rw [hzx, hzy] at hn
    have hn' : (decide (BudgetBFV.mulLift P ≤ E.mulLift) &&
        decide (BudgetBFV.mulRound P ≤ E.mulRound) && decide (x.parts = 2) &&
        decide (y.parts = 2)) = true := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn'
    obtain ⟨⟨⟨hL, hR⟩, h2x⟩, h2y⟩ := hn'
    refine ⟨_, ?_, Validation.BFV.stepOK_mul_textbook P hP E hL hR s hs ρ ρ' σ d a b x y ca cb
      hstep hx hy ha hb (hla.trans h2x) (hlb.trans h2y) h2x h2y⟩
    show (zenv ρ a).bind (fun x => (σ a).bind fun ca => (σ b).map fun cb =>
      σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca cb)) = _
    rw [hzx, ha, hb]; rfl
  | square d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hn : ((zenv ρ a).elim true fun x =>
        decide (BudgetBFV.mulLift P ≤ E.mulLift) && decide (BudgetBFV.mulRound P ≤ E.mulRound) &&
          decide (x.parts = 2)) = true := hneed
    rw [hzx] at hn
    have hn' : (decide (BudgetBFV.mulLift P ≤ E.mulLift) &&
        decide (BudgetBFV.mulRound P ≤ E.mulRound) && decide (x.parts = 2)) = true := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn'
    obtain ⟨⟨hL, hR⟩, h2x⟩ := hn'
    refine ⟨_, ?_, Validation.BFV.stepOK_square_textbook P hP E hL hR s hs ρ ρ' σ d a x ca
      hstep hx ha (hla.trans h2x) h2x⟩
    show (zenv ρ a).bind (fun x => (σ a).map fun ca =>
      σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)) = _
    rw [hzx, ha]; rfl
  | mulConst d a k =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.BFV.stepOK_mulConst_textbook P E s ρ ρ' σ d a k x ca hstep hx ha
      hla⟩
    show (σ a).map (fun ca => σ.set d (ca.map (bfvMulConst k))) = _
    rw [ha]; rfl
  | copy d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.BFV.stepOK_copy_textbook P E s ρ ρ' σ _ d a x ca (Or.inl rfl)
      hstep hx ha hla⟩
    show (σ a).map (fun ca => σ.set d ca) = _
    rw [ha]; rfl
  | toEval d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.BFV.stepOK_copy_textbook P E s ρ ρ' σ _ d a x ca
      (Or.inr (Or.inl rfl)) hstep hx ha hla⟩
    show (σ a).map (fun ca => σ.set d ca) = _
    rw [ha]; rfl
  | toCoeff d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.BFV.stepOK_copy_textbook P E s ρ ρ' σ _ d a x ca
      (Or.inr (Or.inr rfl)) hstep hx ha hla⟩
    show (σ a).map (fun ca => σ.set d ca) = _
    rw [ha]; rfl
  | dropLimbs d a k =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp [step, hx, hk, guard] at hstep
  | automorph d a g =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.BFV.stepOK_automorph_textbook P E s ρ ρ' σ d a g x ca hstep hx ha
      hla⟩
    show (σ a).map (fun ca => σ.set d (ca.map (automorph g))) = _
    rw [ha]; rfl
  | addPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
    refine ⟨_, ?_, Validation.BFV.stepOK_addPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx
      hy ha hb hla⟩
    show (zenv ρ a).bind (fun x => (σ a).bind fun ca => (σ p).map fun cp =>
      σ.set d (bfvAddPlain P.src.t (P.src.modulus x.level) ca (cp.headD 0))) = _
    rw [hzx, ha, hb]; rfl
  | subPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
    refine ⟨_, ?_, Validation.BFV.stepOK_subPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx
      hy ha hb hla⟩
    show (zenv ρ a).bind (fun x => (σ a).bind fun ca => (σ p).map fun cp =>
      σ.set d (bfvSubPlain P.src.t (P.src.modulus x.level) ca (cp.headD 0))) = _
    rw [hzx, ha, hb]; rfl
  | mulPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    refine ⟨_, ?_, Validation.BFV.stepOK_mulPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx
      hy ha hb hla⟩
    show (σ a).bind (fun ca => (σ p).map fun cp => σ.set d (ca.map (cp.headD 0 * ·))) = _
    rw [ha, hb]; rfl
  | relin d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    have hz : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hn : ((zenv ρ a).elim true fun x =>
        decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch)) = true := hneed
    rw [hz] at hn
    have hn' : decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch) = true := hn
    have hok' := Validation.RealizeBFV.relinBFV_stepOK P lay hP hS hdecl x.level h1 hL
      (hok _ h1 hL) E (of_decide_eq_true hn') s hs _ (hkeys x.level h1 hL).1 ρ ρ' σ d a x ca
      hstep hx ha rfl hla
    refine ⟨_, ?_, hok'⟩
    show (zenv ρ a).bind (fun x => (σ a).map fun ca =>
      σ.set d (relinBFV P lay x.level ca (rk x.level))) = _
    rw [hz, ha]; rfl
  | keySwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    have hz : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hn : ((zenv ρ a).elim true fun x =>
        decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)) =
          true := hneed
    rw [hz] at hn
    have hn' : (decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch) &&
        decide (x.key ∈ rots)) = true := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn'
    have hok' := Validation.RealizeBFV.keySwitchBFV_stepOK P lay hP hS hdecl x.level h1 hL
      (hok _ h1 hL) E hn'.1 s hs ρ ρ' σ d a x ca hstep hx ha rfl hla _
      ((hkeys x.level h1 hL).2 x.key hn'.2)
    refine ⟨_, ?_, hok'⟩
    show (zenv ρ a).bind (fun x => (σ a).map fun ca =>
      σ.set d (keySwitchBFV P lay x.level ca (gk x.key x.level))) = _
    rw [hz, ha]; rfl
  | modSwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨-, hL⟩ := hlv a x hx
    have hz : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hn : ((zenv ρ a).elim true fun x =>
        decide (BudgetBFV.msBudget P ≤ E.modSwitch) && decide (x.parts = 2)) = true := hneed
    rw [hz] at hn
    have hn' : (decide (BudgetBFV.msBudget P ≤ E.modSwitch) && decide (x.parts = 2)) = true := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn'
    refine ⟨_, ?_, Validation.BFV.stepOK_modSwitch_textbook P hP E hn'.1 s hs ρ ρ' σ d a x ca
      hstep hx ha hL hn'.2 (hla.trans hn'.2)⟩
    show (zenv ρ a).bind (fun x => (σ a).map fun ca =>
      σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))) = _
    rw [hz, ha]; rfl

end Run

/-- **The evaluator's run** is a run at the constant profile `E`. -/
theorem bfv_run (D : AbsScheme) (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) (pk : D.PK)
    (s : IntPoly D.P.src.N) (hk : D.P.src.kind = .bfv) (hP : SchemeParamsOK D.Pe)
    (hside : bfvSide D.Pe lay = true) (hs : SecretOK D.P.secretBound s)
    (hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ D.P.src.qs.length →
      Budget.GadgetKeysOK D.Pe lay ℓ .square s (rk pk ℓ) ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK D.Pe lay ℓ (.galois g) s (gk pk g ℓ)) :
    ∀ (body : List Instr) (n : ℕ) (ρ ρf : Env D.P.src) (σ : Trace.CtEnv D.Pe),
    Shape D.Pe ρ σ → Levels D.Pe ρ → bfvNeed D.Pe lay rots E body (zenv ρ) = true →
    body.foldlM (step D.P.src) ρ = some ρf →
    ∃ σf, irun D (bfvStepFn D lay rk gk) pk body (zenv ρ) σ = some σf ∧
      TraceBFV.RunAt D.Pe (fun _ => E) s n body ρ σ σf
  | [], _, _, _, σ, _, _, _, _ => ⟨σ, rfl, rfl⟩
  | i :: is, n, ρ, ρf, σ, hsh, hlv, hneed, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', hstep, hrest⟩ := h
    have hz := (Validation.BFV.SoundAux.step_zenv hk (Validation.IndCpaD.allExact_all ρ) i).1
    rw [hstep, Option.map_some] at hz
    have hn : (bfvNeedAt D.Pe lay rots E (zenv ρ) i &&
        (step D.P.src (zenv ρ) i).elim true (bfvNeed D.Pe lay rots E is)) = true := hneed
    rw [hz, Bool.and_eq_true] at hn
    obtain ⟨σ', he, hok⟩ := bfv_step (P := D.Pe) (rk := rk pk) (gk := gk pk) hk hP hside hs hkeys i hsh hlv
      hn.1 hstep
    obtain ⟨σf, hf, hrun⟩ := bfv_run D lay rots E rk gk pk s hk hP hside hs hkeys is (n + 1) ρ' ρf
      σ' (shape_step_bfv hsh hstep hok) (levels_step hlv hstep) hn.2 hrest
    refine ⟨σf, ?_, ρ', σ', hstep, hok, hrun⟩
    show (step D.P.src (zenv ρ) i).bind (fun ρ0' =>
      (bfvStep D.Pe lay (rk pk) (gk pk) (zenv ρ) σ i).bind fun σ' =>
        irun D (bfvStepFn D lay rk gk) pk is ρ0' σ') = _
    rw [hz, Option.bind_some, he, Option.bind_some]
    exact hf

/-! ## The locked statements -/

theorem bfvEval_meets (D : AbsScheme) (henc : D.EncOKBFV) (lay : Budget.KSLayout)
    (rots : List ℕ) (E : TraceBFV.Budget)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ D.P.src.qs.length →
        Budget.GadgetKeysOK D.P lay ℓ .square (D.sec sk) (rk pk ℓ) ∧
        ∀ g ∈ rots, Budget.GadgetKeysOK D.P lay ℓ (.galois g) (D.sec sk) (gk pk g ℓ)) :
    EvalMeetsBFV D (fun _ _ => E) (bfvClass D lay rots E)
      (interpEval D (bfvStepFn D lay rk gk)) := by
  intro pk sk hk C hC ins hins hlen
  change (admBFV D (fun _ _ => E) C && bfvSide D.Pe lay && bfvNeed D.Pe lay rots E
    (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)) = true at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hadm, hside⟩, hneed⟩ := hC
  obtain ⟨B, outs, hcert, hfit⟩ := Validation.IndCpaDProfile.admBFV_some hadm
  obtain ⟨hP, hkind, -⟩ := Validation.Profile.certifyBFVProfile?_some hcert
  have ht : 0 < D.P.src.t := by have := hP.plaintext.1; exact lt_of_lt_of_le (by norm_num) this
  have hin := Validation.IndCpaDProfile.inputsOK_fit hkind henc C ht hfit pk sk hk ins hins hlen
  obtain ⟨ρ, hρ, -⟩ := Validation.Profile.certifyBFVProfile?_sound D.Pe (fun _ => E) (D.prog C)
    B outs hcert (D.sec sk) _ _ hin
  have hρ' := hρ
  simp only [Source.eval, Option.bind_eq_bind, Option.pure_def] at hρ'
  obtain ⟨hdecl, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨-, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨ρf, hbody, -⟩ := Option.bind_eq_some_iff.mp hρ'
  obtain ⟨hs, hks⟩ := hkeys pk sk hk
  have hsh : Shape D.Pe (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x))
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2))) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have h1 := hin x d hd
    refine ⟨D.cts C (ins.map fun p => D.enc pk p.1 p.2) x, by simp [Trace.initCt, hd], ?_⟩
    split_ifs at h1
    · exact h1.1
    · exact h1.1
  have hlv : Levels D.Pe (initEnv D.P.src (D.prog C)
      fun x => .exact (D.msg C (ins.map Prod.fst) x)) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩
  have hz0 : zenv (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x)) =
      initEnv D.P.src (D.prog C) fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hneed
  obtain ⟨σf, hf, hrun⟩ := bfv_run D lay rots E rk gk pk (D.sec sk) hkind hP hside hs
    (fun ℓ h1 hℓ => hks ℓ h1 hℓ) (D.prog C).body 0 _ ρf _ hsh hlv hneed hbody
  refine ⟨σf, hrun, ?_⟩
  show ((irun D (bfvStepFn D lay rk gk) pk (D.prog C).body
      (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2)))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] = _
  rw [← hz0, hf]; rfl

theorem correct_bfvEval (D : AbsScheme) (henc : D.EncOKBFV) (lay : Budget.KSLayout)
    (rots : List ℕ) (E : TraceBFV.Budget)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ D.P.src.qs.length →
        Budget.GadgetKeysOK D.P lay ℓ .square (D.sec sk) (rk pk ℓ) ∧
        ∀ g ∈ rots, Budget.GadgetKeysOK D.P lay ℓ (.galois g) (D.sec sk) (gk pk g ℓ)) :
    Spec.IndCpaD.Correct (freshScheme D (bfvClass D lay rots E)
      (interpEval D (bfvStepFn D lay rk gk)) D.decBFV) :=
  Validation.IndCpaDProfile.correct_bfv D henc (fun _ _ => E) (bfvClass D lay rots E)
    (fun C h => by
      change (admBFV D (fun _ _ => E) C && bfvSide D.Pe lay && bfvNeed D.Pe lay rots E
        (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)) = true at h
      simp only [Bool.and_eq_true] at h
      exact h.1.1)
    _ (bfvEval_meets D henc lay rots E rk gk hkeys)

/-! ## Keys and encryption -/

theorem keyValid_genBFV (P : FullParams) (hk : P.src.kind = .bfv) (req : KeyReq P.src.N) (f : ℕ)
    (hf : req.factor = const (f : ZMod req.modulus)) (s e a : IntPoly P.src.N)
    (he1 : normInf e ≤ P.keyNoise) (he2 : 2 * normInf e < req.modulus) :
    KeyValid P.src.kind P.src.t P.keyNoise s req
      (ofInt _ (e - a * s + ((f : ℤ)) • req.target.eval s)) (ofInt _ a) := by
  have hbnd : ∀ i, |e.coeff i| ≤ (normInf e : ℤ) := fun i =>
    (normInf_le_iff e (normInf e)).mp le_rfl i
  have heq : ofInt req.modulus (e - a * s + ((f : ℤ)) • req.target.eval s) +
      ofInt req.modulus a * ofInt req.modulus s - req.factor * ofInt req.modulus (req.target.eval s)
      = ofInt req.modulus e := by
    apply eq_of_neZero; intro
    simp only [hf, ofInt_add, ofInt_sub, ofInt_mul, smul_eq_const_mul, ofInt_const]
    simp only [Int.cast_natCast]
    ring
  have hc : centered (ofInt req.modulus e) = e :=
    centered_ofInt _ fun i => by
      have := hbnd i
      have h2 : ((2 * normInf e : ℕ) : ℤ) < req.modulus := by exact_mod_cast he2
      push_cast at h2
      linarith
  refine ⟨?_, fun hb => absurd (hk.symm.trans hb) (by decide)⟩
  show normInf (centered _) ≤ _
  rw [heq, hc]
  exact he1

theorem bfvGadgetGen_ok (P : FullParams) (hk : P.src.kind = .bfv) (lay : Budget.KSLayout)
    (ℓ : ℕ) (tgt : KeyTarget) (s : IntPoly P.src.N) (as es : List (IntPoly P.src.N))
    (hes : ∀ j, normInf (es.getD j 0) ≤ P.keyNoise ∧
      2 * normInf (es.getD j 0) < P.src.modulus ℓ * Budget.specialProd P) :
    Budget.GadgetKeysOK P lay ℓ tgt s (bfvGadgetGen P lay ℓ tgt s as es) := by
  have hlen : (bfvGadgetGen P lay ℓ tgt s as es).length = (lay.sizes ℓ).length := by
    show (List.map _ (List.range _)).length = _
    simp
  refine ⟨hlen, fun j hj => ?_⟩
  have e1 : (bfvGadgetGen P lay ℓ tgt s as es)[j] =
      (es.getD j 0 - as.getD j 0 * s +
        ((Budget.gadgetFactor (Budget.specialProd P) (Budget.digitModuli P lay ℓ) j : ℕ) : ℤ) •
          tgt.eval s, as.getD j 0) := by
    show (List.map _ (List.range _))[j] = _
    simp
  rw [e1]
  exact keyValid_genBFV P hk (Budget.gadgetReq P lay ℓ tgt j)
    (Budget.gadgetFactor (Budget.specialProd P) (Budget.digitModuli P lay ℓ) j) rfl s
    (es.getD j 0) (as.getD j 0) (hes j).1 (hes j).2

theorem bfvKeyGen_keysOK (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (hk : P.src.kind = .bfv) (s e a : IntPoly P.src.N)
    (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk) (ra re : ℕ → List (IntPoly P.src.N))
    (ga ge : ℕ → ℕ → List (IntPoly P.src.N))
    (hre : ∀ ℓ j, normInf ((re ℓ).getD j 0) ≤ P.keyNoise ∧
      2 * normInf ((re ℓ).getD j 0) < P.src.modulus ℓ * Budget.specialProd P)
    (hge : ∀ g ∈ rots, ∀ ℓ j, normInf ((ge g ℓ).getD j 0) ≤ P.keyNoise ∧
      2 * normInf ((ge g ℓ).getD j 0) < P.src.modulus ℓ * Budget.specialProd P) :
    (bfvKSData P lay rots Bk Bu B1 B2).KeysOK (bfvKeyGen P lay s e a ra re ga ge) (s, e) := by
  refine ⟨hs, he, ?_, fun ℓ _ _ => ⟨bfvGadgetGen_ok P hk lay ℓ .square s (ra ℓ) (re ℓ) (hre ℓ),
    fun g hg => bfvGadgetGen_ok P hk lay ℓ (.galois g) s (ga g ℓ) (ge g ℓ) (hge g hg ℓ)⟩⟩
  show ofInt _ (e - a * s + a * s) = ofInt _ (((1 : ℕ) : ℤ) • e)
  congr 1
  apply eq_of_neZero; intro
  rw [sub_add_cancel]
  ext i
  simp

theorem encOK_bfvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (ht : 2 ≤ P.src.t)
    (hdec : decOK P.src.t (P.src.modulus P.src.qs.length) (bfvKSData P lay rots Bk Bu B1 B2).eps
      = true) :
    (bfvKSData P lay rots Bk Bu B1 B2).EncOKBFV := by
  intro pk sk hk m r hr
  change Poly P.src.t P.src.N at m
  change BFVPK P.src.N at pk
  change IntPoly P.src.N × IntPoly P.src.N at sk
  obtain ⟨hs, he, hpk, -⟩ := hk
  obtain ⟨hu, h1, h2⟩ := hr
  have hε := Validation.FreshNoise.freshError_worst sk.1 sk.2 r.1 r.2.1 r.2.2
    P.secretBound Bk Bu B1 B2 hs he hu h1 h2
  exact ⟨rfl, rfl, Validation.BFVEncrypt.encryptBFV_encrypts P.src.t
    (P.src.modulus P.src.qs.length) _ ht sk.1 sk.2 pk.1 pk.2.1 r.1 r.2.1 r.2.2 m hpk hε hdec⟩

/-! ## The instance at `sealBFV` -/

theorem lm_two_stage_bfv_kernel :
    decOK sealBFV.src.t (sealBFV.src.modulus sealBFV.src.qs.length) bfvSealData.eps = true ∧
    admLM mkBFVSeal admBFVSeal bfvG0 bfvStage1 [("a", true), ("b", true)] = true ∧
      admLM mkBFVSeal admBFVSeal (bfvG0.extend bfvStage1) bfvStage2 [("c", true)] = true := by
  decide +kernel

theorem correct_lm_bfvSeal :
    Spec.IndCpaD.Correct (freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV) :=
  correct_bfvEval bfvSealData
    (encOK_bfvKSData sealBFV bfvSealLayout [5] 21 1 21 21 (by decide)
      lm_two_stage_bfv_kernel.1)
    bfvSealLayout [5] bfvSealBudget (fun pk => pk.2.2.1) (fun pk => pk.2.2.2)
    (fun _ _ hk => ⟨hk.1, fun ℓ h1 hℓ => hk.2.2.2 ℓ h1 hℓ⟩)

theorem hmkBFVSeal : ∀ p f c, bfvSealData.prog (mkBFVSeal p f c) = p ∧
    bfvSealData.fresh (mkBFVSeal p f c) = f ∧ bfvSealData.pt (mkBFVSeal p f c) = c :=
  fun _ _ _ => ⟨rfl, rfl, rfl⟩

theorem probLM_eq_bfvSeal [DecidableEq (M bfvSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → bfvSealData.PK) (sk : Ω → bfvSealData.SK) (tape : Ω → ℕ → bfvSealData.ER)
    (coins : Ω → Coins) (A : Coins → bfvSealData.PK → LAdv bfvSealData Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, bfvSealData.KeysOK (pk ω) (sk ω) ∧
      ∀ i, bfvSealData.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty bfvSealData) = true} =
      μ {ω | gameCPA (S := freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV) b
        (pk ω) (tape ω) (reductionLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV A
          (coins ω) (pk ω)) 0 = true} :=
  probLM_eq bfvSealData mkBFVSeal hmkBFVSeal admBFVSeal bfvSealData.decBFV _
    (bfvStep_interpOK bfvSealData bfvSealLayout (fun pk => pk.2.2.1) (fun pk => pk.2.2.2))
    correct_lm_bfvSeal μ pk sk tape coins A b hgood

theorem advLM_le_bfvSeal [DecidableEq (M bfvSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → bfvSealData.PK) (sk : Ω → bfvSealData.SK) (tape : Ω → ℕ → bfvSealData.ER)
    (coins : Ω → Coins) (A : Coins → bfvSealData.PK → LAdv bfvSealData Bool) (q : ℕ)
    (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV true (pk ω) (sk ω)
          (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty bfvSealData) = true}).toReal -
        (μ {ω | gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV false (pk ω) (sk ω)
          (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty bfvSealData) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV)
          true (pk ω) (tape ω) (reductionLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV A
            (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV)
          false (pk ω) (tape ω) (reductionLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV A
            (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (bfvSealData.KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, bfvSealData.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  advLM_le bfvSealData mkBFVSeal hmkBFVSeal admBFVSeal bfvSealData.decBFV _
    (bfvStep_interpOK bfvSealData bfvSealLayout (fun pk => pk.2.2.1) (fun pk => pk.2.2.2))
    correct_lm_bfvSeal μ pk sk tape coins A q hq

theorem bfvKeyGen_noisy_bfvSeal (s e a : IntPoly sealBFV.src.N)
    (hs : SecretOK sealBFV.secretBound s) (he : normInf e ≤ 21)
    (ra : ℕ → List (IntPoly sealBFV.src.N)) (ga : ℕ → ℕ → List (IntPoly sealBFV.src.N)) :
    bfvSealData.KeysOK (bfvKeyGen sealBFV bfvSealLayout s e a ra (onesErr _) ga
      (fun _ => onesErr _)) (s, e) := by
  have h1 : ∀ ℓ j, normInf ((onesErr sealBFV.src.N ℓ).getD j 0) ≤ 1 := by
    intro ℓ j
    have e : (onesErr sealBFV.src.N ℓ).getD j 0 =
        if j < 4 then (⟨fun _ => 1⟩ : IntPoly sealBFV.src.N) else 0 := by
      show (List.replicate 4 _).getD j 0 = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
    rw [e]
    split_ifs
    · rw [normInf_le_iff]; intro i
      show |(1 : ℤ)| ≤ ((1 : ℕ) : ℤ)
      simp
    · rw [normInf_zero]; omega
  have hpos : ∀ ℓ, 1 ≤ sealBFV.src.modulus ℓ := by
    intro ℓ
    show 1 ≤ (sealBFV.src.qs.take ℓ).prod
    have : ∀ x ∈ sealBFV.src.qs, 0 < x := by decide
    exact List.prod_pos fun q hq => this q (List.mem_of_mem_take hq)
  have hb : ∀ ℓ j, normInf ((onesErr sealBFV.src.N ℓ).getD j 0) ≤ sealBFV.keyNoise ∧
      2 * normInf ((onesErr sealBFV.src.N ℓ).getD j 0) <
        sealBFV.src.modulus ℓ * Budget.specialProd sealBFV := by
    intro ℓ j
    have hP2 : 2 < Budget.specialProd sealBFV := by decide
    refine ⟨(h1 ℓ j).trans (by decide), ?_⟩
    calc 2 * normInf ((onesErr sealBFV.src.N ℓ).getD j 0) ≤ 2 * 1 :=
          Nat.mul_le_mul_left 2 (h1 ℓ j)
      _ < 1 * Budget.specialProd sealBFV := by omega
      _ ≤ sealBFV.src.modulus ℓ * Budget.specialProd sealBFV :=
          Nat.mul_le_mul_right _ (hpos ℓ)
  exact bfvKeyGen_keysOK sealBFV bfvSealLayout [5] 21 1 21 21 rfl s e a hs he ra _ ga _ hb
    (fun _ _ => hb)

example := (@bfvStep_interpOK : type_of% @Challenge.IndCpaDLM.bfvStep_interpOK)
example := (@bfvEval_meets : type_of% @Challenge.IndCpaDLM.bfvEval_meets)
example := (@correct_bfvEval : type_of% @Challenge.IndCpaDLM.correct_bfvEval)
example := (@bfvKeyGen_keysOK : type_of% @Challenge.IndCpaDLM.bfvKeyGen_keysOK)
example := (@encOK_bfvKSData : type_of% @Challenge.IndCpaDLM.encOK_bfvKSData)
example := (@correct_lm_bfvSeal : type_of% @Challenge.IndCpaDLM.correct_lm_bfvSeal)
example := (@probLM_eq_bfvSeal : type_of% @Challenge.IndCpaDLM.probLM_eq_bfvSeal)
example := (@advLM_le_bfvSeal : type_of% @Challenge.IndCpaDLM.advLM_le_bfvSeal)
example := (@bfvKeyGen_noisy_bfvSeal : type_of% @Challenge.IndCpaDLM.bfvKeyGen_noisy_bfvSeal)
example := (@lm_two_stage_bfv_kernel : type_of% @Challenge.IndCpaDLM.lm_two_stage_bfv_kernel)

end Validation.IndCpaDLM
