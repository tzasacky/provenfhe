import Std.Data.TreeMap
import Spec.Scaling
import FHE.Noise.Fast

/-!
# FHE.Noise.FastScaling — the user-level scaling check in near-linear time
(UNTRUSTED, audited as part of the holes)

`Spec.Scaling.factors?` keeps the factors of the variables as a function: every instruction wraps
the previous one in a closure (`Spec.Scaling.upd`), the initial factors are found by a list search
over the inputs (`facInit`), and every input's declared factor by a list search over the declared
factors (`inputFactor`, `List.lookup`). So `Spec.Scaling.scaleOK?`, which `fhe_check` evaluates on
every OpenFHE BGV program (the user-level decryption check), is quadratic in the program length and
in the number of inputs (measured: 18.7 s at 30,000 instructions).

Here the factors are kept in a search tree (`Std.TreeMap` on variable names) and the body is run
once, calling the locked `Spec.Scaling.facStep` on a lookup function backed by the tree; `facStep`
changes only the destination of the instruction, whose new factor is read back and stored.

Nothing here is trusted: `Validation.FastScaling` proves `scaleOK = Spec.Scaling.scaleOK?` and
`factors = Spec.Scaling.factors?` (as lookup functions) on every input.
-/

namespace FHE.Noise.FastScaling
open Spec Spec.Source Spec.Scaling
open FHE.Noise.Fast (VMap mapOf)

/-- The declared input factors, looked up as `List.lookup` reads the list (first entry). -/
def factorMap (sd : ScaleData) : VMap ℕ := mapOf (·.1) (·.2) sd.factors

/-- `Spec.Scaling.inputFactor`, read from the tree. -/
def inputFactorM (P : Params) (fm : VMap ℕ) (x : Var) : ZMod P.t :=
  (((fm[x]?).getD 0 : ℕ) : ZMod P.t)

/-- `Spec.Scaling.facInit` as a tree. -/
def facInitMap (P : Params) (prog : Program) (fm : VMap ℕ) : VMap (Fac P.t) :=
  mapOf (·.name) (fun d => ⟨inputFactorM P fm d.name, inputFactorM P fm d.name, d.level⟩)
    prog.inputs

/-- `Spec.Scaling.facRun` with the factors in a tree. -/
def facRunGo (P : Params) (tracks : Bool) :
    List Instr → List Bool → VMap (Fac P.t) → Option (VMap (Fac P.t))
  | [], _, m => some m
  | i :: is, ms, m => do
    let F' ← facStep P tracks (ms.headD false) (fun x => m[x]?) i
    let v ← F' (Trace.dst i)
    facRunGo P tracks is ms.tail (m.insert (Trace.dst i) v)

/-- `Spec.Scaling.factors?` as a tree (`Validation.FastScaling.factors_eq`). -/
def factors (P : Params) (prog : Program) (sd : ScaleData) : Option (VMap (Fac P.t)) := do
  let fm := factorMap sd
  guard (P.kind = .bgv)
  guard (prog.inputs.all fun d => (fm[d.name]?).isSome)
  facRunGo P sd.tracks prog.body sd.marks (facInitMap P prog fm)

/-- **`Spec.Scaling.scaleOK?`** with the factors in a tree (`Validation.FastScaling.scaleOK_eq`). -/
def scaleOK (P : Params) (prog : Program) (sd : ScaleData) : Bool :=
  match factors P prog sd with
  | none => false
  | some m => prog.outputs.all fun o =>
    match m[o]? with
    | none => false
    | some x =>
      decide (decodeFactor P sd.tracks x = x.phi * Decrypt.decScale P x.level) &&
        decide (decodeFactor P sd.tracks x * (decodeFactor P sd.tracks x)⁻¹ = 1)

end FHE.Noise.FastScaling
