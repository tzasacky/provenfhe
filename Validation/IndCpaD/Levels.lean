import Challenge.IndCpaD.Defs
import Validation.BFV.Sound

/-!
# Validation.IndCpaD.Levels — the levels of the outputs do not depend on the messages
-/

namespace Validation.IndCpaD
open Spec NPoly Scheme Source Spec.CertifyBFV Challenge.IndCpaD Spec.IndCpaDBFV

variable {St : Setting}

open Validation.BFV.SoundAux in
theorem allExact_all {Pr : Params} (ρ : Env Pr) : AllExact ρ := by
  intro x v _
  cases h : v.msg with
  | exact m => exact ⟨m, rfl⟩

open Validation.BFV.SoundAux in
theorem foldlM_zenv {Pr : Params} (hk : Pr.kind = .bfv) :
    ∀ (body : List Instr) (ρ : Env Pr),
      body.foldlM (step Pr) (zenv ρ) = (body.foldlM (step Pr) ρ).map zenv := by
  intro body
  induction body with
  | nil => intro ρ; rfl
  | cons i is ih =>
    intro ρ
    obtain ⟨hz, -⟩ := step_zenv hk (allExact_all ρ) i
    simp only [List.foldlM_cons, Option.bind_eq_bind]
    rw [hz]
    rcases step Pr ρ i with _ | ρ'
    · rfl
    · simp only [Option.map_some, Option.bind_some]; exact ih ρ'

/-- G3. -/
theorem outLevel_eq (C : Circ St) (hk : St.base.P.src.kind = .bfv)
    (ms : List (Poly St.base.P.src.t St.base.P.src.N)) (ρ : Env St.base.P.src)
    (h : Source.eval St.base.P.src C.prog (fun x => .exact (C.msg ms x)) = some ρ)
    (o : Var) (v : Val St.base.P.src) (hv : ρ o = some v) : C.outLevel o = v.level := by
  open Validation.BFV.SoundAux in
  have hz0 : zenv (initEnv St.base.P.src C.prog (fun x => .exact (C.msg ms x))) =
      initEnv St.base.P.src C.prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  open Validation.BFV.SoundAux in
  have hf := foldlM_zenv hk C.prog.body (initEnv St.base.P.src C.prog (fun x => .exact (C.msg ms x)))
  rw [hz0] at hf
  have hfits : ∀ (msgs : Var → Msg St.base.P.src.t St.base.P.src.N),
      (C.prog.inputs.all fun dcl => (msgs dcl.name).fits St.base.P.src.kind) = true := by
    intro msgs; rw [List.all_eq_true]; intro dcl _
    cases msgs dcl.name; rw [hk]; rfl
  have hf1 := hfits (fun x => .exact (C.msg ms x))
  have hf0 := hfits (fun _ => .exact 0)
  by_cases hdecl : (C.prog.inputs.all fun dcl => dcl.ok St.base.P.src) = true
  swap
  · simp [Source.eval, guard, hdecl] at h
  rcases hρ : C.prog.body.foldlM (step St.base.P.src)
      (initEnv St.base.P.src C.prog (fun x => .exact (C.msg ms x))) with _ | ρf
  · simp [Source.eval, guard, hdecl, hf1, hρ] at h
  rw [hρ] at hf
  by_cases hout : ∀ x ∈ C.prog.outputs, (ρf x).isSome = true
  swap
  · simp [Source.eval, guard, hdecl, hf1, hρ, hout] at h
  simp [Source.eval, guard, hdecl, hf1, hρ] at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true hout)] at h
  simp only [Option.bind_some, Option.some.injEq] at h
  subst h
  have e : C.outLevel o = ((Source.eval St.base.P.src C.prog (fun _ => .exact 0) >>= fun ρ => ρ o).map
      (·.level)).getD 0 := rfl
  rw [e]
  simp [Source.eval, guard, hdecl, hf0, hf, Validation.BFV.SoundAux.zenv]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hout)]
  simp [Validation.BFV.SoundAux.zenv, hv, Validation.BFV.SoundAux.zv]

end Validation.IndCpaD
