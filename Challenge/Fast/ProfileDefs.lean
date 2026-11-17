import Challenge.Profile.Defs
import Challenge.Profile.Tool

/-!
# Challenge.Fast.ProfileDefs — what "the fast profile mode is the locked decision" means   (LOCKED definitions)

`fhe_check --profile FILE` decides the library-neutral certificate of `Challenge.Profile.Defs`:
the locked `Challenge.Profile.certifyProfile?` (BGV, one budget `E`) and
`Challenge.Profile.certifyBFVProfile?` (BFV, one budget `E k` per instruction) at the budget the
user declares, and reports the coverage checks `Challenge.Profile.coversBFV?` (every level at
every key switch) and `Challenge.Profile.coversBFVAt?` (the level-exact check of
`Challenge.Profile.Tool`). Those definitions are written to be read: the analyses keep their
environments as functions, and the BFV coverage checks index the body by position or replay it
on closures, so all four are quadratic in the program length. (`Challenge.Profile.coversBGV?`
does not read the program and is run as it is.)

The tool runs faster functions instead. This file says what they must satisfy: they are
**equal** to the locked ones on every input, at every budget. The predicates are over an
arbitrary function; `Challenge/Fast/Profile.lean` applies them to the definition holes
`FHE.Holes.certifyProfileFast`, `certifyBFVProfileFast`, `coversBFVFast` and `coversBFVAtFast`,
and `Validation/FastProfile.lean` proves them. A CERTIFIED verdict of the profile mode is
therefore a value `certifyProfile? P E prog sw = some (B, outs)`
(`certifyBFVProfile? P E prog = some (B, outs)`) at the decoded `E`, and every statement of
`Challenge.Profile` applies to it unchanged; a "covered" line is a value
`coversBFVAt? P lay U r prog E = true` (`coversBFV? P lay U r prog.body E = true`).

This file imports locked definitions only.
-/

namespace Challenge.Fast
open Spec Spec.Source

/-- The type of a BGV profile decision: parameters, a budget, a program and whether the outputs
are switched to one limb ↦ the whole-program bound and the per-output bounds, or `none`. -/
abbrev ProfileDecision : Type :=
  FullParams → Trace.Budget → Source.Program → Bool → Option (ℕ × List (Var × ℕ))

/-- `f` returns what `Challenge.Profile.certifyProfile?` returns, on every input and at every
budget. -/
def ProfileEqRef (f : ProfileDecision) : Prop :=
  ∀ (P : FullParams) (E : Trace.Budget) (prog : Source.Program) (sw : Bool),
    f P E prog sw = Challenge.Profile.certifyProfile? P E prog sw

/-- The type of a BFV profile decision: parameters, one budget per instruction and a program ↦
the whole-program bound and the per-output bounds, or `none`. -/
abbrev ProfileDecisionBFV : Type :=
  FullParams → (ℕ → TraceBFV.Budget) → Source.Program → Option (ℕ × List (Var × ℕ))

/-- `f` returns what `Challenge.Profile.certifyBFVProfile?` returns, on every input and at every
per-instruction budget. -/
def ProfileBFVEqRef (f : ProfileDecisionBFV) : Prop :=
  ∀ (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Source.Program),
    f P E prog = Challenge.Profile.certifyBFVProfile? P E prog

/-- The type of the conservative BFV coverage check: parameters, a key-switching layout, the
multiplication family `(U, r)`, a body and one budget per instruction ↦ covered or not. -/
abbrev CoverageBFV : Type :=
  FullParams → Budget.KSLayout → ℕ → ℕ → List Instr → (ℕ → TraceBFV.Budget) → Bool

/-- `f` returns what `Challenge.Profile.coversBFV?` returns, on every input. -/
def CoversBFVEqRef (f : CoverageBFV) : Prop :=
  ∀ (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget), f P lay U r body E = Challenge.Profile.coversBFV? P lay U r body E

/-- The type of the level-exact BFV coverage check: as `CoverageBFV`, with the whole program
(its inputs give the levels of the replay). -/
abbrev CoverageBFVAt : Type :=
  FullParams → Budget.KSLayout → ℕ → ℕ → Source.Program → (ℕ → TraceBFV.Budget) → Bool

/-- `f` returns what `Challenge.Profile.coversBFVAt?` returns, on every input. -/
def CoversBFVAtEqRef (f : CoverageBFVAt) : Prop :=
  ∀ (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Source.Program)
    (E : ℕ → TraceBFV.Budget),
    f P lay U r prog E = Challenge.Profile.coversBFVAt? P lay U r prog E

end Challenge.Fast
