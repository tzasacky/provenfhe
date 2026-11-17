import Challenge.IndCpaD.LM
import Validation.IndCpaD.ProfileBGV
import Validation.Headline.Noise

/-!
# Validation.IndCpaD.LMBasic — environments, extensions and interpreter runs

The facts the proof of `Challenge.IndCpaD.LM` is built on: `Source.step` and a local interpreter
write only the destination, and give the same written value on any extension of the
environments they read (`step_ext`); hence folds and interpreter runs over a body give, on an
extension of the start, an extension of the result (`foldl_ext`, `irun_ext`), leave every
non-destination unchanged (`foldl_nodst`, `irun_nodst`), and an interpreter run over an appended
body is the run over the second part from the state after the first (`irun_append`). The
zero-message replay is the message run with zeroed messages, for both kinds (`foldl_zenv`).
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM Challenge.IndCpaDLM
open Validation.BFV.SoundAux (zenv zv)

/-- `g` extends `f`. -/
def Ext {α : Type} (f g : Var → Option α) : Prop := ∀ x v, f x = some v → g x = some v

theorem ext_refl {α : Type} (f : Var → Option α) : Ext f f := fun _ _ h => h

theorem ext_trans {α : Type} {f g h : Var → Option α} (h1 : Ext f g) (h2 : Ext g h) : Ext f h :=
  fun x v hx => h2 x v (h1 x v hx)

theorem ext_envSet {Pr : Params} {ρ ρ₂ : Env Pr} (h : Ext ρ ρ₂) (d : Var) (v : Val Pr) :
    Ext (ρ.set d v) (ρ₂.set d v) := by
  intro x w hx
  simp only [Env.set] at hx ⊢
  split_ifs at hx ⊢
  · exact hx
  · exact h x w hx

theorem ext_ctSet {P : FullParams} {σ σ₂ : Trace.CtEnv P} (h : Ext σ σ₂) (d : Var)
    (c : List (IntPoly P.src.N)) : Ext (σ.set d c) (σ₂.set d c) := by
  intro x w hx
  simp only [Trace.CtEnv.set] at hx ⊢
  split_ifs at hx ⊢
  · exact hx
  · exact h x w hx

theorem envSet_inj {Pr : Params} {ρ : Env Pr} {d : Var} {X Y : Val Pr}
    (h : ρ.set d X = ρ.set d Y) : X = Y := by
  have := congrFun h d
  simpa [Env.set] using this

/-! ## `Source.step` -/

/-- **`Source.step` on an extension** writes the same value. -/
theorem step_ext {Pr : Params} {ρ ρ₂ ρ' : Env Pr} {i : Instr} (h : step Pr ρ i = some ρ')
    (hx : Ext ρ ρ₂) :
    ∃ v, ρ' = ρ.set (Trace.dst i) v ∧ step Pr ρ₂ i = some (ρ₂.set (Trace.dst i) v) := by
  obtain ⟨v, rfl⟩ := Validation.Headline.NoiseAux.step_set h
  refine ⟨v, rfl, ?_⟩
  cases i <;> simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, guard, Trace.dst] at h ⊢
  all_goals (unfold Ext at hx; aesop (add safe forward envSet_inj))

theorem foldl_ext {Pr : Params} : ∀ (body : List Instr) (ρ ρ₂ ρf : Env Pr),
    body.foldlM (step Pr) ρ = some ρf → Ext ρ ρ₂ →
    ∃ ρf₂, body.foldlM (step Pr) ρ₂ = some ρf₂ ∧ Ext ρf ρf₂
  | [], ρ, ρ₂, ρf, h, hx => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨ρ₂, rfl, hx⟩
  | i :: is, ρ, ρ₂, ρf, h, hx => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', h1, h2⟩ := h
    obtain ⟨v, rfl, h1'⟩ := step_ext h1 hx
    obtain ⟨ρf₂, h3, h4⟩ := foldl_ext is _ _ ρf h2 (ext_envSet hx (Trace.dst i) v)
    refine ⟨ρf₂, ?_, h4⟩
    simp only [List.foldlM_cons, Option.bind_eq_bind, h1', Option.bind_some]
    exact h3

theorem foldl_nodst {Pr : Params} : ∀ (body : List Instr) (ρ ρf : Env Pr),
    body.foldlM (step Pr) ρ = some ρf → ∀ x, x ∉ body.map Trace.dst → ρf x = ρ x
  | [], ρ, ρf, h, x, _ => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | i :: is, ρ, ρf, h, x, hx => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', h1, h2⟩ := h
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [foldl_nodst is ρ' ρf h2 x hx.2]
    obtain ⟨v, rfl⟩ := Validation.Headline.NoiseAux.step_set h1
    simp only [Env.set, hx.1, ↓reduceIte]

theorem foldl_dom {Pr : Params} : ∀ (body : List Instr) (ρ ρf : Env Pr),
    body.foldlM (step Pr) ρ = some ρf → ∀ x, (ρf x).isSome →
      (ρ x).isSome ∨ x ∈ body.map Trace.dst
  | [], ρ, ρf, h, x, hx => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact Or.inl hx
  | i :: is, ρ, ρf, h, x, hx => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', h1, h2⟩ := h
    rcases foldl_dom is ρ' ρf h2 x hx with h3 | h3
    · obtain ⟨v, rfl⟩ := Validation.Headline.NoiseAux.step_set h1
      by_cases hxd : x = Trace.dst i
      · exact Or.inr (by simp [hxd])
      · left; simpa [Env.set, hxd] using h3
    · exact Or.inr (by simp [h3])

/-- The zero-message replay is the message run with zeroed messages, for both kinds. -/
theorem foldl_zenv {Pr : Params} (body : List Instr) (ρ : Env Pr) :
    body.foldlM (step Pr) (zenv ρ) = (body.foldlM (step Pr) ρ).map zenv := by
  rcases hk : Pr.kind with _ | _
  · exact Validation.IndCpaDProfile.foldlM_zenv_bgv hk body ρ
  · exact Validation.IndCpaD.foldlM_zenv hk body ρ

theorem zenv_initEnv {Pr : Params} (prog : Program) (msgs : Var → Msg Pr.t Pr.N) :
    zenv (initEnv Pr prog msgs) = initEnv Pr prog fun _ => .exact 0 := by
  funext x; simp only [zenv, initEnv, Option.map_map]; rfl

/-! ## Interpreter runs -/

section Interp
variable {D : AbsScheme} (stepF : StepFn D) (hI : InterpOK D stepF) (pk : D.PK)
include hI

theorem irun_ext : ∀ (body : List Instr) (ρ ρ₂ : Env D.P.src) (σ σ₂ σf : Trace.CtEnv D.Pe),
    irun D stepF pk body ρ σ = some σf → Ext ρ ρ₂ → Ext σ σ₂ →
    ∃ σf₂, irun D stepF pk body ρ₂ σ₂ = some σf₂ ∧ Ext σf σf₂
  | [], ρ, ρ₂, σ, σ₂, σf, h, _, hs => by
    have : σ = σf := Option.some.inj h
    subst this; exact ⟨σ₂, rfl, hs⟩
  | i :: is, ρ, ρ₂, σ, σ₂, σf, h, hr, hs => by
    change (step D.P.src ρ i).bind (fun ρ' => (stepF pk ρ σ i).bind fun σ' =>
      irun D stepF pk is ρ' σ') = some σf at h
    obtain ⟨ρ', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨σ', h2, h3⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, rfl, h1'⟩ := step_ext h1 hr
    obtain ⟨ct, rfl, h2'⟩ := hI.1 pk ρ ρ₂ σ σ₂ i σ' hr hs h2
    obtain ⟨σf₂, h4, h5⟩ := irun_ext is _ _ _ _ σf h3 (ext_envSet hr _ v) (ext_ctSet hs _ ct)
    refine ⟨σf₂, ?_, h5⟩
    change (step D.P.src ρ₂ i).bind (fun ρ' => (stepF pk ρ₂ σ₂ i).bind fun σ' =>
      irun D stepF pk is ρ' σ') = some σf₂
    rw [h1', Option.bind_some, h2', Option.bind_some]
    exact h4

theorem irun_nodst : ∀ (body : List Instr) (ρ : Env D.P.src) (σ σf : Trace.CtEnv D.Pe),
    irun D stepF pk body ρ σ = some σf → ∀ x, x ∉ body.map Trace.dst → σf x = σ x
  | [], ρ, σ, σf, h, x, _ => by
    have : σ = σf := Option.some.inj h
    subst this; rfl
  | i :: is, ρ, σ, σf, h, x, hx => by
    change (step D.P.src ρ i).bind (fun ρ' => (stepF pk ρ σ i).bind fun σ' =>
      irun D stepF pk is ρ' σ') = some σf at h
    obtain ⟨ρ', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨σ', h2, h3⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [irun_nodst is ρ' σ' σf h3 x hx.2]
    obtain ⟨ct, rfl, -⟩ := hI.1 pk ρ ρ σ σ i σ' (ext_refl _) (ext_refl _) h2
    simp only [Trace.CtEnv.set, hx.1, ↓reduceIte]

/-- **Progress**: where the replay runs and every replayed variable has a ciphertext, the
interpreter runs, and keeps that property. -/
theorem irun_progress : ∀ (body : List Instr) (ρ ρf : Env D.P.src) (σ : Trace.CtEnv D.Pe),
    body.foldlM (step D.P.src) ρ = some ρf → (∀ x, (ρ x).isSome → (σ x).isSome) →
    ∃ σf, irun D stepF pk body ρ σ = some σf ∧ ∀ x, (ρf x).isSome → (σf x).isSome
  | [], ρ, ρf, σ, h, hd => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨σ, rfl, hd⟩
  | i :: is, ρ, ρf, σ, h, hd => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', h1, h2⟩ := h
    obtain ⟨σ', h3⟩ := Option.isSome_iff_exists.mp (hI.2 pk ρ σ i ρ' h1 hd)
    obtain ⟨ct, rfl, -⟩ := hI.1 pk ρ ρ σ σ i σ' (ext_refl _) (ext_refl _) h3
    obtain ⟨v, rfl⟩ := Validation.Headline.NoiseAux.step_set h1
    have hd' : ∀ x, ((ρ.set (Trace.dst i) v) x).isSome → ((σ.set (Trace.dst i) ct) x).isSome := by
      intro x hx
      simp only [Env.set, Trace.CtEnv.set] at hx ⊢
      split_ifs at hx ⊢
      · rfl
      · exact hd x hx
    obtain ⟨σf, h4, h5⟩ := irun_progress is _ ρf _ h2 hd'
    refine ⟨σf, ?_, h5⟩
    change (step D.P.src ρ i).bind (fun ρ' => (stepF pk ρ σ i).bind fun σ' =>
      irun D stepF pk is ρ' σ') = some σf
    rw [h1, Option.bind_some, h3, Option.bind_some]
    exact h4

omit hI in
/-- **An interpreter run over an appended body.** -/
theorem irun_append : ∀ (b1 b2 : List Instr) (ρ ρ1 : Env D.P.src) (σ σ1 : Trace.CtEnv D.Pe),
    irun D stepF pk b1 ρ σ = some σ1 → b1.foldlM (step D.P.src) ρ = some ρ1 →
    irun D stepF pk (b1 ++ b2) ρ σ = irun D stepF pk b2 ρ1 σ1
  | [], b2, ρ, ρ1, σ, σ1, h, h' => by
    have : σ = σ1 := Option.some.inj h
    subst this
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h'
    subst h'; rfl
  | i :: is, b2, ρ, ρ1, σ, σ1, h, h' => by
    change (step D.P.src ρ i).bind (fun ρ' => (stepF pk ρ σ i).bind fun σ' =>
      irun D stepF pk is ρ' σ') = some σ1 at h
    obtain ⟨ρ', e1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨σ', e2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.foldlM_cons, Option.bind_eq_bind, e1, Option.bind_some] at h'
    change (step D.P.src ρ i).bind (fun ρ' => (stepF pk ρ σ i).bind fun σ' =>
      irun D stepF pk (is ++ b2) ρ' σ') = _
    rw [e1, Option.bind_some, e2, Option.bind_some]
    exact irun_append is b2 ρ' ρ1 σ' σ1 h h'

end Interp

end Validation.IndCpaDLM
