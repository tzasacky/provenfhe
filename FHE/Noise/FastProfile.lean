import FHE.Noise.Fast
import FHE.Noise.FastBFV
import Challenge.Profile.Defs
import Challenge.Profile.Tool

/-!
# FHE.Noise.FastProfile — the profile decisions and the BFV coverage checks in near-linear time
(UNTRUSTED, audited as part of the holes)

The decisions of `Challenge.Profile.Defs` at a budget the user supplies, and the BFV coverage
checks, with the environments in search trees and the body run once:

* `certifyProfile` is `Challenge.Profile.certifyProfile?`: the same guards, then ONE run of the
  fast BGV analysis (`FHE.Noise.Fast.run`) at the given budget, from whose final environments the
  whole-program bound and every per-output bound and output check are read (as
  `FHE.Noise.Fast.checked` does for `Challenge.Certify.checked?`, minus the guards that only
  serve the realizability of the computed budget);
* `certifyBFVProfile` is `Challenge.Profile.certifyBFVProfile?`, with the input clause
  `inputsDecOKWith` reading the declared bounds from a tree and one run of the fast BFV analysis
  (`FHE.Noise.FastBFV.run`) at the given per-instruction budget;
* `coversBFV` is `Challenge.Profile.coversBFV?` in one pass over the body (the locked one reads
  `body[k]?` for every `k`), with the largest key-switching bound over the levels computed once
  (`ksMax`);
* `coversBFVAt` is `Challenge.Profile.coversBFVAt?` with the replay in a tree and the
  key-switching bounds of the levels `0, …, L` in a table (`ksTable`).

The per-instruction requirements (`needAtWith`) are the locked `Challenge.Profile.needAt` word for
word, with the numbers it recomputes at every instruction (`mulLiftApprox P U`,
`mulRoundApprox P r`, `msBudget P`, `ksBoundAt P lay ℓ`) as parameters; instantiated at the locked
values they are the locked function by `rfl` (`Validation.FastProfile`).

Nothing here is trusted: `Challenge.Fast.Profile` states, and `Validation.FastProfile` proves,
that the four functions are **equal** to the locked ones on every input.
-/

namespace FHE.Noise.FastProfile
open Spec Spec.Source Spec.TraceBFV
open FHE.Noise.Fast (VMap mapOf boundMap initEnvMap)

/-! ## The decisions -/

/-- **The fast BGV profile decision**: equal to `Challenge.Profile.certifyProfile?`
(`Challenge.Fast.certifyProfileFast_eq`). -/
def certifyProfile (P : FullParams) (E : Trace.Budget) (prog : Program) (switched : Bool) :
    Option (ℕ × List (Var × ℕ)) := do
  guard (Spec.schemeParamsOK? P)
  guard (P.src.kind = .bgv)
  guard (!prog.outputs.isEmpty)
  guard (FHE.Noise.Fast.inputsMsgOK P prog)
  let r ← FHE.Noise.Fast.run P E prog
  let B ← FHE.Noise.Fast.outBound r prog.outputs
  let outs ← prog.outputs.mapM fun o =>
    (FHE.Noise.Fast.outputBound P r switched o).map fun b => (o, b)
  pure (B, outs)

/-- `Challenge.Profile.inputsDecOK` with the input bound `ib` as a parameter (for
`TraceBFV.inputBound P prog`, a list search per input). -/
def inputsDecOKWith (P : FullParams) (prog : Program) (ib : Decl → ℕ) : Bool :=
  prog.inputs.all fun d => decide (d.parts = 1) || !d.ok P.src ||
    Challenge.BFV.decOK P.src.t (P.src.modulus d.level) (ib d)

/-- **The fast BFV profile decision**: equal to `Challenge.Profile.certifyBFVProfile?`
(`Challenge.Fast.certifyBFVProfileFast_eq`). -/
def certifyBFVProfile (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    Option (ℕ × List (Var × ℕ)) := do
  guard (Spec.schemeParamsOK? P)
  guard (P.src.kind = .bfv)
  guard (!prog.outputs.isEmpty)
  guard (inputsDecOKWith P prog (FHE.Noise.FastBFV.inputBound P (boundMap prog)))
  guard (FHE.Noise.FastBFV.plainBoundsOKWith P prog
    (FHE.Noise.FastBFV.inputBound P (boundMap prog)))
  guard (P.src.t - 1 ≤ P.src.qs.headD 0 / 2)
  let r ← FHE.Noise.FastBFV.run P E prog
  let B ← FHE.Noise.FastBFV.outBound r prog.outputs
  guard (prog.outputs.all fun o => (r.1[o]?).map (·.key) == some 1)
  let outs ← prog.outputs.mapM fun o => (FHE.Noise.FastBFV.outBound r [o]).map fun b => (o, b)
  pure (B, outs)

/-! ## The conservative coverage check (`Challenge.Profile.coversBFV?`) -/

/-- The largest `ksBoundAt` over the levels `1, …, L`. -/
def ksMax (P : FullParams) (lay : Budget.KSLayout) : ℕ :=
  ((List.range P.src.qs.length).map fun j => BudgetBFV.ksBoundAt P lay (j + 1)).foldl max 0

/-- What instruction `i` asks of its budget `Ek` under the conservative check, with the numbers
of the families as parameters (`ml`, `mr`: the multiplication lift and rounding;
`km`: the largest key-switching bound; `ms`: the modulus switch). -/
def needWith (ml mr km ms : ℕ) (Ek : TraceBFV.Budget) : Instr → Bool
  | .mul .. | .square .. => decide (ml ≤ Ek.mulLift) && decide (mr ≤ Ek.mulRound)
  | .relin .. | .keySwitch .. => decide (km ≤ Ek.keySwitch)
  | .modSwitch .. => decide (ms ≤ Ek.modSwitch)
  | _ => true

/-- `needWith` at every instruction of a body, from position `n`. -/
def needAllGo (ml mr km ms : ℕ) (E : ℕ → TraceBFV.Budget) : ℕ → List Instr → Bool
  | _, [] => true
  | n, i :: is => needWith ml mr km ms (E n) i && needAllGo ml mr km ms E (n + 1) is

/-- **The fast conservative BFV coverage check**: equal to `Challenge.Profile.coversBFV?`
(`Challenge.Fast.coversBFVFast_eq`). -/
def coversBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) : Bool :=
  Spec.schemeParamsOK? P && Budget.specialOK? P &&
    (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
    needAllGo (BudgetBFV.mulLiftApprox P U) (BudgetBFV.mulRoundApprox P r) (ksMax P lay)
      (BudgetBFV.msBudget P) E 0 body

/-! ## The level-exact coverage check (`Challenge.Profile.coversBFVAt?`) -/

/-- `ksBoundAt P lay ℓ` for `ℓ = 0, …, L`, computed once. -/
def ksTable (P : FullParams) (lay : Budget.KSLayout) : Array ℕ :=
  ((List.range (P.src.qs.length + 1)).map (BudgetBFV.ksBoundAt P lay)).toArray

/-- `ksBoundAt P lay ℓ`, read from the table. -/
def ksAtT (P : FullParams) (lay : Budget.KSLayout) (tbl : Array ℕ) (ℓ : ℕ) : ℕ :=
  match tbl[ℓ]? with
  | some b => b
  | none => BudgetBFV.ksBoundAt P lay ℓ

/-- `Challenge.Profile.needAt` with the numbers of the families as parameters (`ks ℓ` for
`ksBoundAt P lay ℓ`). -/
def needAtWith {Pr : Params} (ml mr ms : ℕ) (ks : ℕ → ℕ) (Ek : TraceBFV.Budget) (ρ : Env Pr) :
    Instr → Bool
  | .mul .. | .square .. => decide (ml ≤ Ek.mulLift) && decide (mr ≤ Ek.mulRound)
  | .relin _ a | .keySwitch _ a => decide (ks (Challenge.CertifyBFV.levelOf ρ a) ≤ Ek.keySwitch)
  | .modSwitch .. => decide (ms ≤ Ek.modSwitch)
  | _ => true

/-- `Challenge.Profile.needAux` with the environment in a tree. -/
def needGo (Pr : Params) (ml mr ms : ℕ) (ks : ℕ → ℕ) (E : ℕ → TraceBFV.Budget) :
    ℕ → List Instr → VMap (Val Pr) → Bool
  | _, [], _ => true
  | n, i :: is, ρ =>
    needAtWith ml mr ms ks (E n) (fun x => ρ[x]?) i &&
      match step Pr (fun x => ρ[x]?) i with
      | some ρ' =>
        match ρ' (Trace.dst i) with
        | some v => needGo Pr ml mr ms ks E (n + 1) is (ρ.insert (Trace.dst i) v)
        | none => true
      | none => true

/-- **The fast level-exact BFV coverage check**: equal to `Challenge.Profile.coversBFVAt?`
(`Challenge.Fast.coversBFVAtFast_eq`). -/
def coversBFVAt (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) : Bool :=
  Spec.schemeParamsOK? P && decide (P.src.kind = .bfv) && Budget.specialOK? P &&
    (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
    needGo P.src (BudgetBFV.mulLiftApprox P U) (BudgetBFV.mulRoundApprox P r)
      (BudgetBFV.msBudget P) (ksAtT P lay (ksTable P lay)) E 0 prog.body (initEnvMap P.src prog)

end FHE.Noise.FastProfile
