import FHE.Noise.FastScaling
import Validation.Fast
import FHE.Holes

/-!
# Validation.FastScaling — the fast user-level scaling check equals the locked one

`FHE.Noise.FastScaling.scaleOK = Spec.Scaling.scaleOK?` on every input (`scaleOK_eq`), and the
tree of factors it computes is looked up as `Spec.Scaling.factors?` (`factors_eq`). The proof:

* a tree built by `mapOf` is looked up as `List.find?` reads the list
  (`Validation.Fast.Aux.mapOf_get`), so the declared factors are `List.lookup`'s (`lookup_eq`) and
  the initial tree is `facInit` (`facInitMap_get`);
* `Spec.Scaling.facStep` changes only the destination of the instruction (`facStep_upd`), so the
  lookup function of the tree after the insertion *is* the function `facStep` returned, and
  `facRunGo` computes `facRun` (`facRunGo_eq`).
-/

namespace Validation.FastScaling
open Spec Spec.Source Spec.Scaling
open FHE.Noise.Fast (VMap mapOf)
open FHE.Noise.FastScaling
open Validation.Fast.Aux (mapOf_get insert_get)

theorem lookup_eq {β : Type} (l : List (Var × β)) (x : Var) :
    l.lookup x = (l.find? fun a => a.1 = x).map (·.2) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨k, b⟩ := a
    by_cases h : k = x
    · subst h; simp [List.lookup]
    · have h' : (x == k) = false := by simp [Ne.symm h]
      simp [List.lookup, h', ih, h]

theorem factorMap_get (sd : ScaleData) (x : Var) : (factorMap sd)[x]? = sd.factors.lookup x := by
  rw [factorMap, mapOf_get, lookup_eq]

theorem inputFactorM_eq (P : Params) (sd : ScaleData) :
    inputFactorM P (factorMap sd) = inputFactor P sd := by
  funext x; simp only [inputFactorM, inputFactor, factorMap_get]

theorem facInitMap_get (P : Params) (prog : Program) (sd : ScaleData) :
    (fun x => (facInitMap P prog (factorMap sd))[x]?) = facInit P prog sd := by
  funext x
  rw [facInitMap, mapOf_get, inputFactorM_eq]
  simp only [facInit]
  cases h : prog.inputs.find? (fun a => a.name = x) with
  | none => simp [h]
  | some d =>
    have hx : d.name = x := by simpa using List.find?_some h
    simp [h, hx]

/-- `facStep` changes only the destination, to a defined factor. -/
theorem facStep_upd {P : Params} {tracks adj : Bool} {F F' : Var → Option (Fac P.t)} {i : Instr}
    (h : facStep P tracks adj F i = some F') : ∃ v, F' = upd F (Trace.dst i) (some v) := by
  cases i <;> simp only [facStep, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h <;>
    simp only [Trace.dst] <;>
    first
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := h; exact ⟨_, rfl⟩)
    | (obtain ⟨_, _, _, _, rfl⟩ := h; exact ⟨_, rfl⟩)
    | (obtain ⟨_, _, rfl⟩ := h; exact ⟨_, rfl⟩)

theorem upd_get {P : Params} (F : Var → Option (Fac P.t)) (d : Var) (v : Fac P.t) :
    upd F d (some v) d = some v := by simp [upd]

theorem facRunGo_eq (P : Params) (tracks : Bool) :
    ∀ (is : List Instr) (ms : List Bool) (m : VMap (Fac P.t)),
      (facRunGo P tracks is ms m).map (fun m x => m[x]?) = facRun P tracks is ms (fun x => m[x]?) := by
  intro is
  induction is with
  | nil => intro ms m; rfl
  | cons i is ih =>
    intro ms m
    simp only [facRunGo, facRun, Option.bind_eq_bind]
    cases hs : facStep P tracks (ms.headD false) (fun x => m[x]?) i with
    | none => rfl
    | some F' =>
      obtain ⟨v, hv⟩ := facStep_upd hs
      simp only [Option.bind_some, hv, upd_get]
      rw [ih]
      congr 1
      rw [insert_get]; rfl

theorem factors_eq (P : Params) (prog : Program) (sd : ScaleData) :
    (factors P prog sd).map (fun m x => m[x]?) = factors? P prog sd := by
  simp only [factors, factors?, Option.bind_eq_bind]
  have hall : (prog.inputs.all fun d => ((factorMap sd)[d.name]?).isSome) =
      (prog.inputs.all fun d => (sd.factors.lookup d.name).isSome) := by
    simp only [factorMap_get]
  rw [hall]
  by_cases hk : P.kind = .bgv <;> by_cases ha : (prog.inputs.all fun d => (sd.factors.lookup d.name).isSome) = true <;>
    simp [guard, hk, ha, facRunGo_eq, facInitMap_get]

theorem scaleOK_eq (P : Params) (prog : Program) (sd : ScaleData) :
    scaleOK P prog sd = scaleOK? P prog sd := by
  have h := factors_eq P prog sd
  simp only [scaleOK, scaleOK?]
  cases hf : factors P prog sd with
  | none => rw [hf] at h; simp at h; rw [← h]
  | some m => rw [hf] at h; simp at h; rw [← h]; rfl

end Validation.FastScaling

namespace Validation.Fast

/-- The locked equality pin for the fast user-level scaling check (`Challenge.Fast.scaleOKFast_eq`). -/
theorem scaleOKFast_eq : Challenge.Fast.ScaleOKEqRef FHE.Holes.scaleOKFast :=
  fun P prog sd => Validation.FastScaling.scaleOK_eq P prog sd

end Validation.Fast
