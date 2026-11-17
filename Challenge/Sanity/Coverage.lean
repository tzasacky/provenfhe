import Challenge.Profile.Tool

/-!
# Challenge.Sanity.Coverage — the conservative BFV coverage check is conservative   (LOCKED statements; proofs in `Validation/Sanity/Coverage.lean`)

`Challenge.Profile.coversBFV?` checks every key switch against `ksBoundAt` at EVERY level of the
chain; `Challenge.Profile.coversBFVAt?` checks it at the level of its operand on the zero-message
replay (`Challenge.CertifyBFV.levelOf`, which defaults to level `0` for an undefined operand). The
module docstring of `Challenge.Profile.Defs` calls the first conservative; this says so: for every
program the profile decision accepts, the conservative check implies the level-exact one, so the
corollaries of either apply.
-/

namespace Challenge.Sanity
open Spec Source Challenge.Profile

/-- **For an accepted program, `coversBFV?` implies `coversBFVAt?`.** -/
theorem coversBFV?_coversBFVAt? (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs))
    (hc : coversBFV? P lay U r prog.body E = true) :
    coversBFVAt? P lay U r prog E = true := sorry

end Challenge.Sanity
