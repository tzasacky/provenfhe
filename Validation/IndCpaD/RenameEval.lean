import Validation.IndCpaD.Rename
import Validation.IndCpaD.LMBFV
import Validation.IndCpaD.LMExact

/-!
# Validation.IndCpaD.RenameEval — renaming and the interpreters

`RenameOK stepF`: a step function on a renamed instruction, in renamed environments, writes the
renamed destination with the same ciphertext. It holds for the three evaluators
(`exactStepFn`, `ksStepFn`, `bfvStepFn`); with it the interpreter's run of a renamed program
is the renamed run.
-/

namespace Validation.IndCpaDRen
open Spec NPoly Scheme Source Spec.IndCpaDProfile Challenge.IndCpaDLM Challenge.IndCpaDProfile
  Challenge.Source Challenge.BFV Challenge.RealizeBFV Challenge.Realize
open Validation.IndCpaDLM (Ext)

/-- Messages of the abstract scheme. -/
abbrev M' (D : AbsScheme) : Type := Poly D.P.src.t D.P.src.N

/-- **Renaming invariance of a step function.** -/
def RenameOK (D : AbsScheme) (stepF : StepFn D) : Prop :=
  ∀ (r : Var → Var), Function.Injective r → ∀ pk (ρ ρ' : Env D.P.src) (σ σ' σ1 : Trace.CtEnv D.Pe)
    (i : Instr), RelR r ρ ρ' → RelR r σ σ' → stepF pk ρ σ i = some σ1 →
    ∃ c, σ1 = σ.set (Trace.dst i) c ∧ stepF pk ρ' σ' (renI r i) = some (σ'.set (r (Trace.dst i)) c)

section Shapes
variable {P : FullParams} {Pr : Params} {r : Var → Var} {σ σ' σ1 : Trace.CtEnv P}
  {ρ ρ' : Env Pr} {d a c : Var}

theorem rshape1 (F : List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (σ a).map (fun ca => σ.set d (F ca)) = some σ1) (hs : RelR r σ σ') :
    ∃ ct, σ1 = σ.set d ct ∧ (σ' (r a)).map (fun ca => σ'.set (r d) (F ca)) = some (σ'.set (r d) ct) := by
  obtain ⟨ca, hca, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F ca, rfl, by rw [hs a, hca]; rfl⟩

theorem rshape2 (F : List (IntPoly P.src.N) → List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (σ a).bind (fun ca => (σ c).map fun cb => σ.set d (F ca cb)) = some σ1)
    (hs : RelR r σ σ') :
    ∃ ct, σ1 = σ.set d ct ∧
      (σ' (r a)).bind (fun ca => (σ' (r c)).map fun cb => σ'.set (r d) (F ca cb)) =
        some (σ'.set (r d) ct) := by
  obtain ⟨ca, hca, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F ca cb, rfl, by rw [hs a, hs c, hca]; simp [hcb]⟩

theorem rshapeR (F : Val Pr → List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (ρ a).bind (fun x => (σ a).map fun ca => σ.set d (F x ca)) = some σ1)
    (hr : RelR r ρ ρ') (hs : RelR r σ σ') :
    ∃ ct, σ1 = σ.set d ct ∧
      (ρ' (r a)).bind (fun x => (σ' (r a)).map fun ca => σ'.set (r d) (F x ca)) =
        some (σ'.set (r d) ct) := by
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ca, hca, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F x ca, rfl, by rw [hr a, hs a, hx]; simp [hca]⟩

theorem rshapeR2 (F : Val Pr → List (IntPoly P.src.N) → List (IntPoly P.src.N) →
      List (IntPoly P.src.N))
    (h : (ρ a).bind (fun x => (σ a).bind fun ca => (σ c).map fun cb => σ.set d (F x ca cb)) =
      some σ1)
    (hr : RelR r ρ ρ') (hs : RelR r σ σ') :
    ∃ ct, σ1 = σ.set d ct ∧
      (ρ' (r a)).bind (fun x => (σ' (r a)).bind fun ca => (σ' (r c)).map fun cb =>
        σ'.set (r d) (F x ca cb)) = some (σ'.set (r d) ct) := by
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ca, hca, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F x ca cb, rfl, by rw [hr a, hs a, hs c, hx]; simp [hca, hcb]⟩

end Shapes

theorem exactStep_renameOK (D : AbsScheme) : RenameOK D (exactStepFn D) := by
  intro r _ pk ρ ρ' σ σ' σ1 i hr hs h
  cases i with
  | add d a c => exact rshape2 (fun ca cb => padZip (· + ·) ca cb) h hs
  | sub d a c => exact rshape2 (fun ca cb => padZip (· - ·) ca cb) h hs
  | mul d a c => exact rshape2 (fun ca cb => tensorParts ca cb) h hs
  | square d a => exact rshape1 (fun ca => tensorParts ca ca) h hs
  | mulConst d a k => exact rshape1 (fun ca => ca.map (k • ·)) h hs
  | copy d a => exact rshape1 (fun ca => ca) h hs
  | toEval d a => exact rshape1 (fun ca => ca) h hs
  | toCoeff d a => exact rshape1 (fun ca => ca) h hs
  | dropLimbs d a k => exact rshape1 (fun ca => ca) h hs
  | automorph d a g => exact rshape1 (fun ca => ca.map (automorph g)) h hs
  | addPlain d a c => exact rshape2 (fun ca cp => padZip (· + ·) ca cp) h hs
  | subPlain d a c => exact rshape2 (fun ca cp => padZip (· - ·) ca cp) h hs
  | mulPlain d a c => exact rshape2 (fun ca cp => ca.map (cp.headD 0 * ·)) h hs
  | relin d a => exact rshape1 (fun ca => ca) h hs
  | keySwitch d a => exact rshape1 (fun ca => ca) h hs
  | modSwitch d a => exact rshape1 (fun ca => ca) h hs

theorem ksStep_renameOK (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    RenameOK D (ksStepFn D lay rk gk) := by
  intro r _ pk ρ ρ' σ σ' σ1 i hr hs h
  cases i with
  | add d a c => exact rshape2 (fun ca cb => padZip (· + ·) ca cb) h hs
  | sub d a c => exact rshape2 (fun ca cb => padZip (· - ·) ca cb) h hs
  | mul d a c => exact rshape2 (fun ca cb => tensorParts ca cb) h hs
  | square d a => exact rshape1 (fun ca => tensorParts ca ca) h hs
  | mulConst d a k => exact rshape1 (fun ca => ca.map (k • ·)) h hs
  | copy d a => exact rshape1 (fun ca => ca) h hs
  | toEval d a => exact rshape1 (fun ca => ca) h hs
  | toCoeff d a => exact rshape1 (fun ca => ca) h hs
  | dropLimbs d a k => exact rshape1 (fun ca => ca) h hs
  | automorph d a g => exact rshape1 (fun ca => ca.map (automorph g)) h hs
  | addPlain d a c => exact rshape2 (fun ca cp => padZip (· + ·) ca cp) h hs
  | subPlain d a c => exact rshape2 (fun ca cp => padZip (· - ·) ca cp) h hs
  | mulPlain d a c => exact rshape2 (fun ca cp => ca.map (cp.headD 0 * ·)) h hs
  | relin d a =>
    exact rshapeR (fun x ca => relinOpenFHE D.Pe lay x.level ca (rk pk)) h hr hs
  | keySwitch d a =>
    exact rshapeR (fun x ca => keySwitchOpenFHE D.Pe lay x.level ca (gk pk x.key)) h hr hs
  | modSwitch d a =>
    exact rshapeR (fun x ca => ca.map (bgvModSwitchComp D.Pe.src.t D.Pe.src.qs[x.level - 1]!))
      h hr hs

theorem bfvStep_renameOK (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    RenameOK D (bfvStepFn D lay rk gk) := by
  intro r _ pk ρ ρ' σ σ' σ1 i hr hs h
  cases i with
  | add d a c => exact rshape2 (fun ca cb => padZip (· + ·) ca cb) h hs
  | sub d a c => exact rshape2 (fun ca cb => padZip (· - ·) ca cb) h hs
  | mul d a c =>
    exact rshapeR2 (fun x ca cb => bfvMul D.Pe.src.t (D.Pe.src.modulus x.level) ca cb) h hr hs
  | square d a =>
    exact rshapeR (fun x ca => bfvMul D.Pe.src.t (D.Pe.src.modulus x.level) ca ca) h hr hs
  | mulConst d a k => exact rshape1 (fun ca => ca.map (bfvMulConst k)) h hs
  | copy d a => exact rshape1 (fun ca => ca) h hs
  | toEval d a => exact rshape1 (fun ca => ca) h hs
  | toCoeff d a => exact rshape1 (fun ca => ca) h hs
  | dropLimbs d a k => exact rshape1 (fun ca => ca) h hs
  | automorph d a g => exact rshape1 (fun ca => ca.map (automorph g)) h hs
  | addPlain d a c =>
    exact rshapeR2 (fun x ca cp => bfvAddPlain D.Pe.src.t (D.Pe.src.modulus x.level) ca
      (cp.headD 0)) h hr hs
  | subPlain d a c =>
    exact rshapeR2 (fun x ca cp => bfvSubPlain D.Pe.src.t (D.Pe.src.modulus x.level) ca
      (cp.headD 0)) h hr hs
  | mulPlain d a c => exact rshape2 (fun ca cp => ca.map (cp.headD 0 * ·)) h hs
  | relin d a =>
    exact rshapeR (fun x ca => relinBFV D.Pe lay x.level ca (rk pk x.level)) h hr hs
  | keySwitch d a =>
    exact rshapeR (fun x ca => keySwitchBFV D.Pe lay x.level ca (gk pk x.key x.level)) h hr hs
  | modSwitch d a =>
    exact rshapeR (fun x ca => ca.map (bfvModSwitchComp D.Pe.src.qs[x.level - 1]!)) h hr hs

/-! ## Renamed circuits -/

theorem idxOf_map_inj {r : Var → Var} (hr : Function.Injective r) :
    ∀ (l : List Var) (x : Var), (l.map r).idxOf? (r x) = l.idxOf? x
  | [], _ => rfl
  | a :: l, x => by
    simp only [List.map_cons, List.idxOf?_cons, idxOf_map_inj hr l x]
    by_cases h : a = x
    · subst h; simp
    · have : r a ≠ r x := hr.ne h
      simp [h, this]

/-- `C'` is `C0` with its names renamed by `r`. -/
def CircRen (D : AbsScheme) (r : Var → Var) (C0 C' : D.Circ) : Prop :=
  IsRen r (D.prog C0) (D.prog C') ∧ D.fresh C' = (D.fresh C0).map r ∧ ∀ x, D.pt C' (r x) = D.pt C0 x

variable {D : AbsScheme}

theorem msg_ren {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C') (ms : List (M' D))
    (x : Var) : D.msg C' ms (r x) = D.msg C0 ms x := by
  unfold AbsScheme.msg
  rw [h.2.1, idxOf_map_inj h.1.inj, h.2.2]

theorem cts_ren {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C')
    (cs : List (ℕ × List (IntPoly D.P.src.N))) (x : Var) : D.cts C' cs (r x) = D.cts C0 cs x := by
  unfold AbsScheme.cts
  rw [h.2.1, idxOf_map_inj h.1.inj, h.2.2]

theorem irun_cons (stepF : StepFn D) (pk : D.PK) (i : Instr) (is : List Instr) (ρ : Env D.P.src)
    (σ : Trace.CtEnv D.Pe) : irun D stepF pk (i :: is) ρ σ =
      (step D.P.src ρ i).bind fun ρ' => (stepF pk ρ σ i).bind fun σ' => irun D stepF pk is ρ' σ' :=
  rfl

theorem irun_ren {stepF : StepFn D} (hR : RenameOK D stepF) {r : Var → Var}
    (hr : Function.Injective r) (pk : D.PK) :
    ∀ (body : List Instr) (ρ ρ' : Env D.P.src) (σ σ' σf : Trace.CtEnv D.Pe), RelR r ρ ρ' →
      RelR r σ σ' → irun D stepF pk body ρ σ = some σf →
      ∃ σf', irun D stepF pk (body.map (renI r)) ρ' σ' = some σf' ∧ RelR r σf σf'
  | [], ρ, ρ', σ, σ', σf, _, hs, h => by
    cases h; exact ⟨σ', rfl, hs⟩
  | i :: is, ρ, ρ', σ, σ', σf, hρ, hs, h => by
    rw [irun_cons] at h
    obtain ⟨ρ1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨σ1, h2, h3⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, rfl, h1'⟩ := step_ren hρ h1
    obtain ⟨c, rfl, h2'⟩ := hR r hr pk ρ ρ' σ σ' _ i hρ hs h2
    obtain ⟨σf', h4, h5⟩ := irun_ren hR hr pk is _ _ _ _ σf (relR_envSet hr hρ _ v)
      (relR_ctSet hr hs _ c) h3
    refine ⟨σf', ?_, h5⟩
    rw [List.map_cons, irun_cons, h1', Option.bind_some, h2', Option.bind_some]
    exact h4

/-- **The interpreter on a renamed circuit** computes what it computes on the circuit. -/
theorem interpEval_ren {stepF : StepFn D} (hI : InterpOK D stepF) (hR : RenameOK D stepF)
    {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C')
    (hz : (Source.eval D.P.src (D.prog C0) fun _ => .exact 0).isSome) (pk : D.PK)
    (cs : List (ℕ × List (IntPoly D.P.src.N))) :
    interpEval D stepF pk C' cs = interpEval D stepF pk C0 cs := by
  obtain ⟨ρz, hρz⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨-, hf, -⟩ := Validation.IndCpaDLM.eval_parts hρz
  obtain ⟨σf, hσf, -⟩ := Validation.IndCpaDLM.irun_progress stepF hI pk _ _ _
    (Trace.initCt D.Pe (D.prog C0) (D.cts C0 cs)) hf
    (Validation.IndCpaDLM.initEnv_dom (P := D.Pe) _ _ _)
  have hrel0 := initEnv_ren (Pr := D.P.src) h.1 (fun _ => .exact 0) (fun _ => .exact 0)
    (fun _ _ => rfl)
  have hct : RelR r (Trace.initCt D.Pe (D.prog C0) (D.cts C0 cs))
      (Trace.initCt D.Pe (D.prog C') (D.cts C' cs)) := by
    intro x
    simp only [Trace.initCt, h.1.inputs, find_ren h.1.inj, Option.map_map]
    refine map_congr_some fun d hfd => ?_
    obtain ⟨hdn, -⟩ := Validation.IndCpaDLM.find_name hfd
    simp only [Function.comp_apply, renD]
    subst hdn
    rw [cts_ren h]
  obtain ⟨σf', hσf', hrel⟩ := irun_ren hR h.1.inj pk _ _ _ _ _ σf hrel0 hct hσf
  obtain ⟨ρz', hρz', hrz⟩ := eval_ren0 h.1 hρz
  unfold interpEval AbsScheme.outLevel
  rw [← h.1.body] at hσf'
  rw [hσf', hσf, h.1.outputs, hρz', hρz]
  simp only [Option.map_some, Option.getD_some, List.map_map]
  apply List.map_congr_left
  intro o _
  simp only [Function.comp_apply, hrel o, Option.bind_eq_bind, Option.bind_some, hrz o]

/-- **What a renamed circuit computes** is what the circuit computes. -/
theorem sem_ren {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C')
    (hz : (Source.eval D.P.src (D.prog C0) fun _ => .exact 0).isSome) (ms : List (M' D)) :
    D.sem C' ms = D.sem C0 ms := by
  obtain ⟨ρz, hρz⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨hok, hf, hout⟩ := Validation.IndCpaDLM.eval_parts hρz
  unfold AbsScheme.sem
  rw [h.2.1, List.length_map]
  split_ifs with hl
  · obtain ⟨ρm, hfm, hz'⟩ := Validation.IndCpaDLM.foldl_of_zero (D.prog C0)
      (fun x => .exact (D.msg C0 ms x)) ρz hf
    have hem : Source.eval D.P.src (D.prog C0) (fun x => .exact (D.msg C0 ms x)) = some ρm := by
      refine Validation.IndCpaDLM.eval_of_parts hok hfm fun o ho => ?_
      have := hout o ho
      rw [← hz', Validation.IndCpaDLM.zenv_apply] at this
      simpa using this
    obtain ⟨ρm', hem', hrel⟩ := eval_ren h.1 (fun x => D.msg C0 ms x) (fun x => D.msg C' ms x)
      (fun d _ => msg_ren h ms d.name) hem
    rw [hem, hem', h.1.outputs]
    unfold RelR at hrel
    simp only [List.map_map, Function.comp_def, hrel]
  · rfl

end Validation.IndCpaDRen
