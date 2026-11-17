import Validation.IndCpaD.Frame

/-!
# Validation.IndCpaD.Rename — renaming the variables of a program

For an injective map `r` on names, the program with every name `x` replaced by `r x` runs as the
original does: every environment of the renamed run at `r x` is the original's at `x`
(`RelR`). Only the direction "the original succeeds, so the renamed one succeeds with related
results" is proved: it is the one the game-level simulation needs.
-/

namespace Validation.IndCpaDRen
open Spec Spec.Source Challenge.Headline Challenge.BFV
open Validation.IndCpaDLM (Ext ext_envSet step_ext find_name)
open Validation.IndCpaDFrame

/-- An instruction with every name renamed. -/
def renI (r : Var → Var) : Instr → Instr
  | .add d a b => .add (r d) (r a) (r b)
  | .sub d a b => .sub (r d) (r a) (r b)
  | .mul d a b => .mul (r d) (r a) (r b)
  | .square d a => .square (r d) (r a)
  | .mulConst d a c => .mulConst (r d) (r a) c
  | .copy d a => .copy (r d) (r a)
  | .toEval d a => .toEval (r d) (r a)
  | .toCoeff d a => .toCoeff (r d) (r a)
  | .relin d a => .relin (r d) (r a)
  | .keySwitch d a => .keySwitch (r d) (r a)
  | .automorph d a g => .automorph (r d) (r a) g
  | .modSwitch d a => .modSwitch (r d) (r a)
  | .addPlain d a p => .addPlain (r d) (r a) (r p)
  | .subPlain d a p => .subPlain (r d) (r a) (r p)
  | .mulPlain d a p => .mulPlain (r d) (r a) (r p)
  | .dropLimbs d a k => .dropLimbs (r d) (r a) k

/-- A declaration renamed. -/
def renD (r : Var → Var) (d : Decl) : Decl := { d with name := r d.name }

theorem dst_renI (r : Var → Var) (i : Instr) : Trace.dst (renI r i) = r (Trace.dst i) := by
  cases i <;> rfl

theorem ops_renI (r : Var → Var) (i : Instr) : ops (renI r i) = (ops i).map r := by
  cases i <;> rfl

/-- The renamed environment agrees with the original through `r`. -/
def RelR {α : Type} (r : Var → Var) (f g : Var → Option α) : Prop := ∀ x, g (r x) = f x

theorem relR_set {α : Type} {r : Var → Var} (hr : Function.Injective r) {f g : Var → Option α}
    (h : RelR r f g) (d : Var) (v : α) :
    RelR r (fun y => if y = d then some v else f y) (fun y => if y = r d then some v else g y) := by
  intro x
  by_cases hx : x = d
  · simp [hx]
  · simp [hx, hr.ne hx, h x]

theorem relR_envSet {Pr : Params} {r : Var → Var} (hr : Function.Injective r) {ρ ρ' : Env Pr}
    (h : RelR r ρ ρ') (d : Var) (v : Val Pr) : RelR r (ρ.set d v) (ρ'.set (r d) v) := by
  intro x
  simp only [Env.set]
  by_cases hx : x = d
  · simp [hx]
  · simp [hx, hr.ne hx, h x]

theorem relR_ctSet {P : FullParams} {r : Var → Var} (hr : Function.Injective r)
    {σ σ' : Trace.CtEnv P} (h : RelR r σ σ') (d : Var) (c : List (IntPoly P.src.N)) :
    RelR r (σ.set d c) (σ'.set (r d) c) := by
  intro x
  simp only [Trace.CtEnv.set]
  by_cases hx : x = d
  · simp [hx]
  · simp [hx, hr.ne hx, h x]

/-- **`Source.step` on a renamed instruction.** -/
theorem step_ren {Pr : Params} {r : Var → Var} {ρ ρ' ρ1 : Env Pr} {i : Instr}
    (hρ : RelR r ρ ρ') (h : step Pr ρ i = some ρ1) :
    ∃ v, ρ1 = ρ.set (Trace.dst i) v ∧
      step Pr ρ' (renI r i) = some (ρ'.set (r (Trace.dst i)) v) := by
  obtain ⟨v, rfl⟩ := Validation.Headline.NoiseAux.step_set h
  refine ⟨v, rfl, ?_⟩
  unfold RelR at hρ
  cases i <;> simp only [step, renI, hρ, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, guard, Trace.dst] at h ⊢
  all_goals (aesop (add safe forward Validation.IndCpaDLM.envSet_inj))

theorem foldl_ren {Pr : Params} {r : Var → Var} (hr : Function.Injective r) :
    ∀ (body : List Instr) (ρ ρ' ρf : Env Pr), RelR r ρ ρ' →
      body.foldlM (step Pr) ρ = some ρf →
      ∃ ρf', (body.map (renI r)).foldlM (step Pr) ρ' = some ρf' ∧ RelR r ρf ρf'
  | [], ρ, ρ', ρf, hρ, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨ρ', rfl, hρ⟩
  | i :: is, ρ, ρ', ρf, hρ, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ1, h1, h2⟩ := h
    obtain ⟨v, rfl, h1'⟩ := step_ren hρ h1
    obtain ⟨ρf', h3, h4⟩ := foldl_ren hr is _ _ ρf (relR_envSet hr hρ _ v) h2
    refine ⟨ρf', ?_, h4⟩
    simp only [List.map_cons, List.foldlM_cons, h1', Option.bind_eq_bind, Option.bind_some]
    exact h3

/-! ## Programs -/

theorem find_ren {r : Var → Var} (hr : Function.Injective r) (l : List Decl) (x : Var) :
    (l.map (renD r)).find? (·.name = r x) = (l.find? (·.name = x)).map (renD r) := by
  rw [List.find?_map]
  congr 2
  funext d
  simp only [Function.comp_apply, renD, hr.eq_iff]

theorem map_congr_some {α β : Type} {o : Option α} {f g : α → β}
    (h : ∀ a, o = some a → f a = g a) : o.map f = o.map g := by
  cases o <;> simp_all

/-- The hypotheses on a renamed program `p'` of `p`. -/
structure IsRen (r : Var → Var) (p p' : Program) : Prop where
  inj : Function.Injective r
  inputs : p'.inputs = p.inputs.map (renD r)
  body : p'.body = p.body.map (renI r)
  outputs : p'.outputs = p.outputs.map r
  bounds : ∀ d ∈ p.inputs, p'.boundOf (r d.name) = p.boundOf d.name

theorem initEnv_ren {Pr : Params} {r : Var → Var} {p p' : Program} (h : IsRen r p p')
    (m m' : Var → Msg Pr.t Pr.N) (hm : ∀ d ∈ p.inputs, m' (r d.name) = m d.name) :
    RelR r (initEnv Pr p m) (initEnv Pr p' m') := by
  intro x
  simp only [initEnv, h.inputs, find_ren h.inj, Option.map_map]
  refine map_congr_some fun d hf => ?_
  obtain ⟨hdn, hdm⟩ := find_name hf
  simp only [Function.comp_apply, renD]
  rw [← hdn, hm d hdm]

theorem all_ren_ok {Pr : Params} (r : Var → Var) (l : List Decl) :
    ((l.map (renD r)).all fun d => d.ok Pr) = (l.all fun d => d.ok Pr) := by
  simp only [List.all_map]; rfl

theorem eval_ren {Pr : Params} {r : Var → Var} {p p' : Program} (h : IsRen r p p')
    (m m' : Var → Poly Pr.t Pr.N) (hm : ∀ d ∈ p.inputs, m' (r d.name) = m d.name) {ρ : Env Pr}
    (he : Source.eval Pr p (fun x => .exact (m x)) = some ρ) :
    ∃ ρ', Source.eval Pr p' (fun x => .exact (m' x)) = some ρ' ∧ RelR r ρ ρ' := by
  obtain ⟨hok, hf, hout⟩ := Validation.IndCpaDLM.eval_parts he
  obtain ⟨ρ', hf', hrel⟩ := foldl_ren h.inj p.body _ _ ρ
    (initEnv_ren h _ (fun x => .exact (m' x)) fun d hd => by rw [hm d hd]) hf
  refine ⟨ρ', Validation.IndCpaDLM.eval_of_parts (by rw [h.inputs, all_ren_ok]; exact hok)
    (by rw [h.body]; exact hf') ?_, hrel⟩
  intro o ho
  rw [h.outputs] at ho
  obtain ⟨o0, ho0, rfl⟩ := List.mem_map.mp ho
  rw [hrel o0]; exact hout o0 ho0

theorem eval_ren0 {Pr : Params} {r : Var → Var} {p p' : Program} (h : IsRen r p p') {ρ : Env Pr}
    (he : Source.eval Pr p (fun _ => .exact 0) = some ρ) :
    ∃ ρ', Source.eval Pr p' (fun _ => .exact 0) = some ρ' ∧ RelR r ρ ρ' :=
  eval_ren h (fun _ => 0) (fun _ => 0) (fun _ _ => rfl) he

/-! ## The BGV reference analysis -/

section BGV
variable {P : FullParams} {E : Trace.Budget}

theorem refBound_ren {r : Var → Var} {ρ ρ' : Env P.src} {β β' : Var → Option ℕ}
    (hρ : RelR r ρ ρ') (hβ : RelR r β β') (i : Instr) :
    refBound P E ρ' β' (renI r i) = refBound P E ρ β i := by
  rw [refBound_eq, refBound_eq]
  unfold RelR at hρ hβ
  cases i <;> simp only [renI, refBoundV, hρ, hβ]

theorem refRun_ren {r : Var → Var} (hr : Function.Injective r) :
    ∀ (body : List Instr) (ρ ρ' ρf : Env P.src) (β β' βf : Var → Option ℕ), RelR r ρ ρ' →
      RelR r β β' → refRun P E body ρ β = some (ρf, βf) →
      ∃ ρf' βf', refRun P E (body.map (renI r)) ρ' β' = some (ρf', βf') ∧ RelR r ρf ρf' ∧
        RelR r βf βf'
  | [], ρ, ρ', ρf, β, β', βf, hρ, hβ, h => by
    simp only [Validation.Headline.NoiseAux.refRun_nil P E, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ρ', β', rfl, hρ, hβ⟩
  | i :: is, ρ, ρ', ρf, β, β', βf, hρ, hβ, h => by
    obtain ⟨ρ1, b, v, h1, h2, h3, h4, h5⟩ := Validation.Headline.NoiseAux.refRun_cons_some P E h
    obtain ⟨w, rfl, h1'⟩ := step_ren hρ h1
    have hw : w = v := by simpa [Env.set] using h3
    subst hw
    obtain ⟨ρf', βf', h6, h7, h8⟩ := refRun_ren hr is _ _ ρf _ _ βf (relR_envSet hr hρ _ w)
      (relR_set hr hβ _ b) h5
    refine ⟨ρf', βf', ?_, h7, h8⟩
    rw [List.map_cons, refRun_cons, h1', refBound_ren hρ hβ, h2]
    simp only [Option.bind_eq_bind, Option.bind_some, dst_renI, Env.set, if_pos rfl, h4, guard,
      if_true, Option.pure_def]
    exact h6

theorem mapM_ren {α : Type} {r : Var → Var} {f g : Var → Option α} (h : RelR r f g) :
    ∀ l : List Var, (l.map r).mapM g = l.mapM f
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.mapM_cons, h a, mapM_ren h l]

theorem all_ren {r : Var → Var} {f : Var → Bool} (l : List Var) :
    (l.map r).all f = l.all (f ∘ r) := by simp [List.all_map]

/-- **The BGV reference analysis of a renamed program.** -/
theorem refAnalyze_ren {r : Var → Var} {p p' : Program} (h : IsRen r p p') {B : ℕ}
    (hB : refAnalyze P E p = some B) : refAnalyze P E p' = some B := by
  have hok := refAnalyze_ok hB
  rw [refAnalyze_eq] at hB ⊢
  rcases hrun : refRun P E p.body (initEnv P.src p fun _ => .exact 0) (beta0 P p) with
    _ | ⟨ρf, βf⟩
  · simp [hrun] at hB
  have hrel0 := initEnv_ren (Pr := P.src) h (fun _ => .exact 0) (fun _ => .exact 0)
    (fun _ _ => rfl)
  have hβ0 : RelR r (beta0 P p) (beta0 P p') := by
    intro x
    simp only [beta0, h.inputs, find_ren h.inj, Option.map_map]
    refine map_congr_some fun d hf => ?_
    obtain ⟨hdn, hdm⟩ := find_name hf
    simp only [Function.comp_apply]
    rw [← hdn, h.bounds d hdm]
  obtain ⟨ρf', βf', h6, h7, h8⟩ := refRun_ren h.inj _ _ _ _ _ _ _ hrel0 hβ0 hrun
  have hfun : ((fun o => (ρf' o).isSome) ∘ r) = fun o => (ρf o).isSome := funext fun o => by
    simp [h7 o]
  simp only [hrun, Option.bind_eq_bind, Option.bind_some] at hB
  rw [h.body, h6]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [h.outputs, h.inputs, all_ren_ok, mapM_ren h8, all_ren, hfun]
  exact hB

end BGV

theorem isRen_outputs {r : Var → Var} {p p' : Program} (h : IsRen r p p') (o : Var) :
    IsRen r { p with outputs := [o] } { p' with outputs := [r o] } :=
  ⟨h.inj, h.inputs, h.body, rfl, h.bounds⟩

theorem outputsUnderS_ren {Pr : Params} {r : Var → Var} {p p' : Program} (h : IsRen r p p')
    {ρ : Env Pr} (he : Source.eval Pr p (fun _ => .exact 0) = some ρ) :
    Encrypt.outputsUnderS? Pr p' = Encrypt.outputsUnderS? Pr p := by
  obtain ⟨ρ', he', hrel⟩ := eval_ren0 h he
  unfold Encrypt.outputsUnderS? Encrypt.outputKey?
  rw [h.outputs, all_ren]
  simp only [he, he', Option.bind_eq_bind, Option.bind_some]
  congr 1
  funext o
  simp [hrel o]

theorem mapM_isSome_ren {α β : Type} {r : Var → Var} {f : Var → Option α} {g : Var → Option β}
    (h : ∀ o, (f o).isSome → (g (r o)).isSome) :
    ∀ l : List Var, (l.mapM f).isSome → ((l.map r).mapM g).isSome
  | [], _ => rfl
  | a :: l, hl => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hl
    rcases hfa : f a with _ | x
    · simp [hfa] at hl
    rcases hfl : l.mapM f with _ | xs
    · simp [hfa, hfl] at hl
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h a (by rw [hfa]; rfl))
    obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp (mapM_isSome_ren h l (by rw [hfl]; rfl))
    simp [List.mapM_cons, hy, hys]

theorem inputsMsgOK_ren {P : FullParams} {r : Var → Var} {p p' : Program} (h : IsRen r p p') :
    Challenge.Certify.inputsMsgOK? P p' = Challenge.Certify.inputsMsgOK? P p := by
  have e : ∀ q : Program, Challenge.Certify.inputsMsgOK? P q = q.inputs.all fun d =>
      decide (P.src.t < P.src.modulus d.level) &&
        (q.boundOf d.name).all fun b => decide (P.src.t / 2 ≤ b) := fun _ => rfl
  rw [e, e, h.inputs, List.all_map]
  refine all_congr_mem _ fun d hd => ?_
  simp only [Function.comp_apply, renD, h.bounds d hd]
  rfl

theorem plainBoundsOK_ren {P : FullParams} {r : Var → Var} {p p' : Program} (h : IsRen r p p') :
    Challenge.CertifyBFV.plainBoundsOK P p' = Challenge.CertifyBFV.plainBoundsOK P p := by
  have e : ∀ q : Program, Challenge.CertifyBFV.plainBoundsOK P q = q.inputs.all fun d =>
      decide (d.parts ≠ 1) || decide (P.src.t / 2 ≤ TraceBFV.inputBound P q d) := fun _ => rfl
  rw [e, e, h.inputs, List.all_map]
  refine all_congr_mem _ fun d hd => ?_
  simp only [Function.comp_apply, renD, TraceBFV.inputBound, h.bounds d hd]
  rfl

section BGV2
variable {P : FullParams} {E : Trace.Budget}

/-- **The BGV profile certificate of a renamed program.** -/
theorem certifyProfile_ren {r : Var → Var} {p p' : Program} (h : IsRen r p p')
    (hc : (Challenge.Profile.certifyProfile? P E p false).isSome) :
    (Challenge.Profile.certifyProfile? P E p' false).isSome := by
  rw [certifyProfile_eq] at hc ⊢
  rcases hB : refAnalyze P E p with _ | B
  · simp [hB] at hc
  have hB' := refAnalyze_ren h hB
  have hmap : ∀ o, (Challenge.Certify.outputBound? P E p false o).isSome →
      (Challenge.Certify.outputBound? P E p' false (r o)).isSome := by
    intro o ho
    rw [outputBound_eq] at ho ⊢
    rcases hb : refAnalyze P E { p with outputs := [o] } with _ | b
    · simp [hb] at ho
    have hb' := refAnalyze_ren (isRen_outputs h o) hb
    obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.mp (refAnalyze_eval hb)
    have hu := outputsUnderS_ren (isRen_outputs h o) hρ
    simp only [hb, hb', Option.bind_eq_bind, Option.bind_some, Encrypt.certOK?, hu] at ho ⊢
    exact ho
  have hne : (!p'.outputs.isEmpty) = (!p.outputs.isEmpty) := by
    rw [h.outputs]; cases p.outputs <;> rfl
  rw [hne, inputsMsgOK_ren h, hB']
  rw [hB] at hc
  rcases hm : p.outputs.mapM (fun o =>
      (Challenge.Certify.outputBound? P E p false o).map fun b => (o, b)) with _ | outs
  · simp [hm] at hc
  have hm' := mapM_isSome_ren (r := r)
    (f := fun o => (Challenge.Certify.outputBound? P E p false o).map fun b => (o, b))
    (g := fun o => (Challenge.Certify.outputBound? P E p' false o).map fun b => (o, b))
    (fun o ho => by simpa using hmap o (by simpa using ho)) p.outputs (by rw [hm]; rfl)
  obtain ⟨outs', hout'⟩ := Option.isSome_iff_exists.mp hm'
  rw [h.outputs, hout']
  simp only [hm, Option.bind_eq_bind, Option.bind_some] at hc
  revert hc
  simp only [guard]
  split_ifs <;> simp

end BGV2

/-! ## The BFV reference analysis -/

section BFV
open Spec.TraceBFV (Bnd)
variable {P : FullParams} {E : TraceBFV.Budget}

theorem refBoundBFV_ren {r : Var → Var} {β β' : Var → Option Bnd} (hβ : RelR r β β') (ℓ : ℕ)
    (i : Instr) : refBoundBFV P E ℓ β' (renI r i) = refBoundBFV P E ℓ β i := by
  rw [refBoundBFV_eq, refBoundBFV_eq]
  unfold RelR at hβ
  cases i <;> simp only [renI, refBoundBFVV, hβ]

theorem domainOK_ren {Pr : Params} {r : Var → Var} {ρ ρ' : Env Pr} (hρ : RelR r ρ ρ') (i : Instr) :
    domainOK ρ' (renI r i) = domainOK ρ i := by
  rw [domainOK_eq, domainOK_eq]
  unfold RelR at hρ
  cases i <;> simp only [renI, domainOKV, hρ]

theorem refRunBFV_ren {r : Var → Var} (hr : Function.Injective r) :
    ∀ (body : List Instr) (ρ ρ' ρf : Env P.src) (β β' βf : Var → Option Bnd), RelR r ρ ρ' →
      RelR r β β' → refRunBFV P E body ρ β = some (ρf, βf) →
      ∃ ρf' βf', refRunBFV P E (body.map (renI r)) ρ' β' = some (ρf', βf') ∧ RelR r ρf ρf' ∧
        RelR r βf βf'
  | [], ρ, ρ', ρf, β, β', βf, hρ, hβ, h => by
    simp only [Validation.BFV.SoundAux.refRun_nil P E, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ρ', β', rfl, hρ, hβ⟩
  | i :: is, ρ, ρ', ρf, β, β', βf, hρ, hβ, h => by
    obtain ⟨ρ1, v, b, h1, h2, h3, h4, h5, h6⟩ := Validation.BFV.SoundAux.refRun_cons_some P E h
    obtain ⟨w, rfl, h1'⟩ := step_ren hρ h1
    have hw : w = v := by simpa [Env.set] using h2
    subst hw
    obtain ⟨ρf', βf', h7, h8, h9⟩ := refRunBFV_ren hr is _ _ ρf _ _ βf (relR_envSet hr hρ _ w)
      (relR_set hr hβ _ b) h5
    refine ⟨ρf', βf', ?_, h8, h9⟩
    rw [List.map_cons, Validation.BFV.PerInstrAux.refRun_cons, domainOK_ren hρ, h6, h1']
    simp only [guard, if_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some, dst_renI,
      Env.set, ite_true, refBoundBFV_ren hβ, h3, h4]
    exact h7

theorem beta0B_ren {r : Var → Var} {p p' : Program} (h : IsRen r p p') :
    RelR r (beta0B P p) (beta0B P p') := by
  intro x
  simp only [beta0B, h.inputs, find_ren h.inj, Option.map_map]
  refine map_congr_some fun d hf => ?_
  obtain ⟨hdn, hdm⟩ := find_name hf
  simp only [Function.comp_apply, renD, TraceBFV.inputBound, h.bounds d hdm]
  rfl

theorem refAnalyzeBFV_ren {r : Var → Var} {p p' : Program} (h : IsRen r p p') {B : ℕ}
    (hB : refAnalyzeBFVAt P (fun _ => E) p = some B) :
    refAnalyzeBFVAt P (fun _ => E) p' = some B := by
  have hok := refAnalyzeBFV_ok hB
  rw [refAnalyzeBFV_eq] at hB ⊢
  rcases hrun : refRunBFV P E p.body (initEnv P.src p fun _ => .exact 0) (beta0B P p) with
    _ | ⟨ρf, βf⟩
  · simp [hrun] at hB
  have hrel0 := initEnv_ren (Pr := P.src) h (fun _ => .exact 0) (fun _ => .exact 0)
    (fun _ _ => rfl)
  obtain ⟨ρf', βf', h6, h7, h8⟩ := refRunBFV_ren h.inj _ _ _ _ _ _ _ hrel0 (beta0B_ren h) hrun
  have hfun : ((fun o => (ρf' o).isSome) ∘ r) = fun o => (ρf o).isSome := funext fun o => by
    simp [h7 o]
  have hct : ∀ o, ctBound βf' (r o) = ctBound βf o := fun o => by
    rw [ctBound_eq, ctBound_eq, h8 o]
  simp only [hrun, Option.bind_eq_bind, Option.bind_some] at hB
  rw [h.body, h6]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [h.outputs, h.inputs, all_ren_ok, mapM_ren (f := ctBound βf) (g := ctBound βf') hct, all_ren,
    hfun]
  exact hB

theorem inputsDecOK_ren {r : Var → Var} {p p' : Program} (h : IsRen r p p') :
    Challenge.Profile.inputsDecOK P p' = Challenge.Profile.inputsDecOK P p := by
  have e : ∀ q : Program, Challenge.Profile.inputsDecOK P q = q.inputs.all fun d =>
      decide (d.parts = 1) || !d.ok P.src ||
        decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P q d) := fun _ => rfl
  rw [e, e, h.inputs, List.all_map]
  refine all_congr_mem _ fun d hd => ?_
  simp only [Function.comp_apply, renD, TraceBFV.inputBound, h.bounds d hd]
  rfl

set_option maxHeartbeats 4000000 in
theorem certifyBFVProfile_ren {r : Var → Var} {p p' : Program} (h : IsRen r p p')
    (hc : (Challenge.Profile.certifyBFVProfile? P (fun _ => E) p).isSome) :
    (Challenge.Profile.certifyBFVProfile? P (fun _ => E) p').isSome := by
  rw [certifyBFVProfile_eq] at hc ⊢
  rcases hB : refAnalyzeBFVAt P (fun _ => E) p with _ | B
  · simp [hB] at hc
  have hB' := refAnalyzeBFV_ren h hB
  obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.mp (refAnalyzeBFV_eval hB)
  have hu := outputsUnderS_ren h hρ
  have hne : (!p'.outputs.isEmpty) = (!p.outputs.isEmpty) := by
    rw [h.outputs]; cases p.outputs <;> rfl
  rw [hB] at hc
  rcases hm : p.outputs.mapM (fun o =>
      (refAnalyzeBFVAt P (fun _ => E) { p with outputs := [o] }).map fun b => (o, b)) with
    _ | outs
  · simp [hm] at hc
  have hm' := mapM_isSome_ren (r := r)
    (f := fun o => (refAnalyzeBFVAt P (fun _ => E) { p with outputs := [o] }).map fun b => (o, b))
    (g := fun o => (refAnalyzeBFVAt P (fun _ => E) { p' with outputs := [o] }).map fun b => (o, b))
    (fun o ho => by
      rcases hb : refAnalyzeBFVAt P (fun _ => E) { p with outputs := [o] } with _ | b
      · simp [hb] at ho
      · simp [refAnalyzeBFV_ren (isRen_outputs h o) hb]) p.outputs (by rw [hm]; rfl)
  obtain ⟨outs', hout'⟩ := Option.isSome_iff_exists.mp hm'
  rw [hne, inputsDecOK_ren h, plainBoundsOK_ren h, hB', hu, h.outputs, hout']
  simp only [hm, Option.bind_eq_bind, Option.bind_some] at hc
  revert hc
  simp only [guard]
  split_ifs <;> simp

end BFV

/-! ## Checks along the replay -/

theorem needFold_ren {Pr : Params} {r : Var → Var} (hr : Function.Injective r)
    {f : Env Pr → Instr → Bool} (hf : ∀ ρ ρ' i, RelR r ρ ρ' → f ρ' (renI r i) = f ρ i) :
    ∀ (body : List Instr) (ρ ρ' ρf : Env Pr), RelR r ρ ρ' → body.foldlM (step Pr) ρ = some ρf →
      needFold f (body.map (renI r)) ρ' = needFold f body ρ
  | [], _, _, _, _, _ => rfl
  | i :: is, ρ, ρ', ρf, hρ, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ1, h1, h2⟩ := h
    obtain ⟨v, rfl, h1'⟩ := step_ren hρ h1
    show (f ρ' (renI r i) && (step Pr ρ' (renI r i)).elim true (needFold f (is.map (renI r)))) =
      (f ρ i && (step Pr ρ i).elim true (needFold f is))
    rw [hf ρ ρ' i hρ, h1, h1']
    simp only [Option.elim_some]
    rw [needFold_ren hr hf is _ _ ρf (relR_envSet hr hρ _ v) h2]

theorem ksNeedAt_ren (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ) (E : Trace.Budget)
    {r : Var → Var} (ρ ρ' : Env P.src) (i : Instr) (hρ : RelR r ρ ρ') :
    Challenge.IndCpaDProfile.ksNeedAt P lay rots E ρ' (renI r i) =
      Challenge.IndCpaDProfile.ksNeedAt P lay rots E ρ i := by
  rw [ksNeedAt_eq, ksNeedAt_eq]
  unfold RelR at hρ
  cases i <;> simp only [renI, ksNeedAtV, hρ]

theorem bfvNeedAt_ren (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (E : TraceBFV.Budget) {r : Var → Var} (ρ ρ' : Env P.src) (i : Instr) (hρ : RelR r ρ ρ') :
    Challenge.IndCpaDLM.bfvNeedAt P lay rots E ρ' (renI r i) =
      Challenge.IndCpaDLM.bfvNeedAt P lay rots E ρ i := by
  rw [bfvNeedAt_eq, bfvNeedAt_eq]
  unfold RelR at hρ
  cases i <;> simp only [renI, bfvNeedAtV, hρ]

theorem exactInstr_ren (r : Var → Var) (i : Instr) :
    Challenge.IndCpaDProfile.exactInstr (renI r i) = Challenge.IndCpaDProfile.exactInstr i := by
  cases i <;> rfl

end Validation.IndCpaDRen
