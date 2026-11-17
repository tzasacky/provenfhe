import Challenge.BFVMul

/-!
# Challenge.BFV.PerInstr — the BFV noise headline with one budget per instruction   (LOCKED statements)

`Spec.TraceBFV.RunAt` and `Challenge.BFV.refAnalyzeBFVAt` (`Challenge/BFV/Defs.lean`) are the run
contract and the reference analysis with a budget `E k` for instruction `k` of the program. The
step contract (`Spec.TraceBFV.StepOK`) and the rules (`refBoundBFV`) are unchanged, so every
realizability pin about one step applies as it is.

* `runAt_const`, `refAnalyzeBFVAt_const`: at a constant budget these are `Run` and
  `refAnalyzeBFV`; nothing about the one-budget statements changes.
* `runAt_congr`, `refAnalyzeBFVAt_congr`: only the budgets of the positions `0, …, body.length − 1`
  matter.
* `refAnalyzeBFVAt_sound`: the headline, `NoiseSoundBFVAt refAnalyzeBFVAt`.
* `certifiedAt_decrypts`: the certificate (`Challenge.BFVMul.certified_decrypts`) per instruction.
-/

namespace Challenge.BFV
open Spec NPoly Scheme Source Correct

variable (P : FullParams)

/-- **A run at a constant budget is a run in the sense of `Spec.TraceBFV.Run`**, from every
position. -/
theorem runAt_const (E : TraceBFV.Budget) (s : IntPoly P.src.N) (n : ℕ) (body : List Instr)
    (ρ : Env P.src) (σ σf : Trace.CtEnv P) :
    TraceBFV.RunAt P (fun _ => E) s n body ρ σ σf ↔ TraceBFV.Run P E s body ρ σ σf := sorry

/-- **`RunAt` reads only the budgets of the positions of its instructions.** -/
theorem runAt_congr (E E' : ℕ → TraceBFV.Budget) (s : IntPoly P.src.N) (n : ℕ)
    (body : List Instr) (h : ∀ j, j < body.length → E (n + j) = E' (n + j))
    (ρ : Env P.src) (σ σf : Trace.CtEnv P) :
    TraceBFV.RunAt P E s n body ρ σ σf ↔ TraceBFV.RunAt P E' s n body ρ σ σf := sorry

/-- **At a constant budget the per-instruction analysis is the reference analysis.** -/
theorem refAnalyzeBFVAt_const (E : TraceBFV.Budget) (prog : Source.Program) :
    refAnalyzeBFVAt P (fun _ => E) prog = refAnalyzeBFV P E prog := sorry

/-- **The per-instruction analysis reads only the budgets of the positions of the body.** -/
theorem refAnalyzeBFVAt_congr (E E' : ℕ → TraceBFV.Budget) (prog : Source.Program)
    (h : ∀ j, j < prog.body.length → E j = E' j) :
    refAnalyzeBFVAt P E prog = refAnalyzeBFVAt P E' prog := sorry

end Challenge.BFV

namespace Challenge.BFV
open Spec NPoly Scheme Source Correct

/-- **The BFV noise headline with one budget per instruction.** -/
theorem refAnalyzeBFVAt_sound : NoiseSoundBFVAt refAnalyzeBFVAt := sorry

/-- `refAnalyzeBFVAt` rejects every program outside BFV. -/
theorem refAnalyzeBFVAt_rejects_nonBFV (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Source.Program) (hk : P.src.kind ≠ .bfv) : refAnalyzeBFVAt P E prog = none := sorry

end Challenge.BFV

namespace Challenge.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV

variable (P : FullParams)

/-- `OutputsDecrypt` for runs with one budget per instruction (`Spec.TraceBFV.RunAt`). -/
def OutputsDecryptAt (E : ℕ → TraceBFV.Budget) (prog : Program)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
    ∀ σ, TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
        v.key = 1 ∧ bfvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m

/-- **The worst-case BFV certificate with one budget per instruction**: `certified_decrypts`
for `refAnalyzeBFVAt` and `RunAt`. -/
theorem certifiedAt_decrypts (E : ℕ → TraceBFV.Budget) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bfv)
    (h : refAnalyzeBFVAt P E prog = some B)
    (hc : Encrypt.outputsUnderS? P.src prog = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    OutputsDecryptAt P E prog s msgs cts := sorry

end Challenge.BFVMul
