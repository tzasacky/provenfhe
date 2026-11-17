import Challenge.Certify.Defs
import Challenge.CertifyBFV.Defs

/-!
# Challenge.Profile.Defs — certificates at a budget the user supplies   (LOCKED definitions)

`Challenge.Certify.certify?` and `Challenge.CertifyBFV.certifyBFV?` compute the budget they
certify against from the parameters, the key-switching layout and (for BFV) the declared
multiplication technique and its table of slacks. The soundness proofs never use where the budget
came from: they hold at every budget. This file states the decisions with the budget as an input,
an **implementation profile**:

* `certifyProfile? P E prog switched` (BGV): one budget `E : Spec.Trace.Budget` for every
  instruction; the same checks as `Challenge.Certify.checked?` minus those that only serve the
  realizability of the computed budget (special primes, layout, key restriction); the input
  check `Challenge.Certify.inputsMsgOK?` is among them;
* `certifyBFVProfile? P E prog` (BFV): one budget `E k : Spec.TraceBFV.Budget` per instruction
  `k` of the body; the checks of `Challenge.CertifyBFV.Defs.checksOK` that do not concern the
  technique: the parameters, the scheme, an output, the decryption condition of every declared
  input ciphertext bound at its level (`inputsDecOK`, item 2 of `checksOK`: with it the noise
  bound of an input alone gives that it decrypts), the plaintext-bound check
  `Challenge.CertifyBFV.plainBoundsOK` (item 2), and the packed-encoding condition
  `t − 1 ≤ ⌊q₀/2⌋` (item 5a), then the reference analysis at `E` for the whole program and for
  each output.

**What a profile certificate is not.** It is sound for ANY budget, the zero budget included: an
accepted profile says that every run meeting the contracts within `E` ends in outputs that
decrypt, and nothing about whether any implementation's steps stay within `E`. (At the zero
budget no key switch, rounding multiplication or modulus switch meets its contract, and the
statement may be about no run of a program that uses them.) Achievability comes only from a
realizability statement: the coverage checks below (`coversBFV?`, `coversBGV?`) with the
corollaries of `Challenge.Profile`, or a proof for a specific implementation.

**Coverage.** `coversBFV? P lay U r body E` decides that at every instruction `k` of `body` the
budget `E k` is at least what the realizability pins need for the algorithm families named by
`(lay, U, r)`: at a `mul` or `square`, `mulLiftApprox P U` and `mulRoundApprox P r` (every
multiplication that multiplies lifts `[c]_Q + Q·u` with `‖u‖∞ ≤ U` and rounds within `r/2`,
`Challenge.BFVMul.stepOK_mul_approx`); at a `relin` or `keySwitch`, `ksBoundAt P lay ℓ` for every
level `ℓ = 1, …, L` (hybrid key switching on the digits of `lay`,
`Challenge.BFV.relin_realizable`, `keySwitch_realizable`); at a `modSwitch`, `msBudget P` (the
rounding of every component, `Challenge.BFV.stepOK_modSwitch_textbook`). It also checks the side
conditions of those pins (parameters, special primes, the layout at every level). The level of a
key switch is not replayed: the key-switching check is made at every level of the chain, which
is conservative. `coversBGV? P lay K E` is the same for BGV, with the modulus-switching budget
checked for operands of `1, …, K` components.
-/

namespace Challenge.Profile
open Spec Spec.Source Challenge.Headline Challenge.BFV

/-! ## The decisions -/

/-- **The BGV decision at a profile `E`.** The whole-program bound and the per-output bounds, as
`Challenge.Certify.checked?` computes them, at the budget `E`. -/
def certifyProfile? (P : FullParams) (E : Trace.Budget) (prog : Program) (switched : Bool) :
    Option (ℕ × List (Var × ℕ)) := do
  guard (schemeParamsOK? P)
  guard (P.src.kind = .bgv)
  guard (!prog.outputs.isEmpty)
  guard (Challenge.Certify.inputsMsgOK? P prog)
  let B ← refAnalyze P E prog
  let outs ← prog.outputs.mapM fun o =>
    (Challenge.Certify.outputBound? P E prog switched o).map fun b => (o, b)
  pure (B, outs)

/-- Every declared input ciphertext (not a one-component plaintext) whose declaration is well
formed has a bound that passes the decryption condition `Challenge.BFV.decOK` at its level: the
input clause of `Challenge.CertifyBFV.Defs.checksOK`. -/
def inputsDecOK (P : FullParams) (prog : Program) : Bool :=
  prog.inputs.all fun d => decide (d.parts = 1) || !d.ok P.src ||
    decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P prog d)

/-- **The BFV decision at a per-instruction profile `E`** (module docstring). -/
def certifyBFVProfile? (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    Option (ℕ × List (Var × ℕ)) := do
  guard (schemeParamsOK? P)
  guard (P.src.kind = .bfv)
  guard (!prog.outputs.isEmpty)
  guard (inputsDecOK P prog)
  guard (Challenge.CertifyBFV.plainBoundsOK P prog)
  guard (P.src.t - 1 ≤ P.src.qs.headD 0 / 2)
  let B ← refAnalyzeBFVAt P E prog
  guard (Encrypt.outputsUnderS? P.src prog)
  let outs ← prog.outputs.mapM fun o =>
    (refAnalyzeBFVAt P E { prog with outputs := [o] }).map fun b => (o, b)
  pure (B, outs)

/-! ## Budget order -/

/-- `E` is below `E'` in every number a BFV contract reads. -/
def BudgetLEBFV (E E' : TraceBFV.Budget) : Prop :=
  E.keySwitch ≤ E'.keySwitch ∧ E.modSwitch ≤ E'.modSwitch ∧ E.mulLift ≤ E'.mulLift ∧
    E.mulRound ≤ E'.mulRound ∧ E.plainAdd ≤ E'.plainAdd

/-- `E` is below `E'` in every number a BGV contract reads (the modulus-switching bound for
every number of components). -/
def BudgetLEBGV (E E' : Trace.Budget) : Prop :=
  E.keySwitch ≤ E'.keySwitch ∧ ∀ k, E.modSwitchAt k ≤ E'.modSwitchAt k

/-! ## Coverage -/

/-- The layout is usable at every level `1, …, L`, and `b` bounds `ksBoundAt` at each of them
(BFV). -/
def ksCoversBFV (P : FullParams) (lay : Budget.KSLayout) (b : ℕ) : Bool :=
  (List.range P.src.qs.length).all fun j => decide (BudgetBFV.ksBoundAt P lay (j + 1) ≤ b)

/-- **The BFV profile covers the families `(lay, U, r)`** (module docstring). -/
def coversBFV? (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) : Bool :=
  schemeParamsOK? P && Budget.specialOK? P &&
    (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
    (List.range body.length).all fun k =>
      match body[k]? with
      | some (.mul ..) | some (.square ..) =>
        decide (BudgetBFV.mulLiftApprox P U ≤ (E k).mulLift) &&
          decide (BudgetBFV.mulRoundApprox P r ≤ (E k).mulRound)
      | some (.relin ..) | some (.keySwitch ..) => ksCoversBFV P lay (E k).keySwitch
      | some (.modSwitch ..) => decide (BudgetBFV.msBudget P ≤ (E k).modSwitch)
      | _ => true

/-- **The BGV profile covers hybrid key switching on `lay` and the centred t-corrected modulus
switch of operands with `1, …, K` components** (module docstring). -/
def coversBGV? (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget) : Bool :=
  schemeParamsOK? P && decide (P.src.kind = .bgv) && Budget.specialOK? P &&
    (List.range P.src.qs.length).all (fun j =>
      lay.okAt (j + 1) && decide (Budget.ksBoundAt P lay (j + 1) ≤ E.keySwitch)) &&
    (List.range K).all fun j => decide (Budget.msBudgetAt P (j + 1) ≤ E.modSwitchAt (j + 1))

end Challenge.Profile
