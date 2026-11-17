import Challenge.IndCpaD.Generic

/-!
# Challenge.IndCpaD.Textbook — a second evaluator that meets the contracts   (LOCKED statements; proofs in `Validation/IndCpaD/Textbook.lean`)

`Challenge.IndCpaD.Generic` states the IND-CPA-D reduction for every evaluator that meets the
contracts within the certified budget (`EvalMeets`). This file gives an evaluator other than the
library transcription for which `EvalMeets` is proved, so that the interface is not about one
function only.

`textEval St`: every multiplication and squaring is the **textbook** Fan–Vercauteren product
(centred lift, integer tensor product, exact rounding of `t·c/Q`: `Challenge.BFV.bfvMul`),
whatever technique the setting declares; every other operation is the transcription's
(`Challenge.CertifyBFV.libStep` of the circuit's input with the technique replaced by
`textbook`): hybrid key switching `relinBFV`/`keySwitchBFV` at the operand's level, the declared
plaintext-addition method, rounding modulus switch. No binary64 step is performed.

* `textEval_meets`: for every setting whose technique is not `HPSPOVERQLEVELED` (whose key switch
  at the top level scales down by the declared drop: the budget of such a key switch was computed
  for it), `EvalMeets St (textEval St)`. With HPS, BEHZ or P-over-Q declared, the certificate's
  budget was computed for that technique's multiplication, and the textbook product stays within
  it because every budget's multiplication numbers are at least the textbook ones
  (`Challenge.CertifyBFV.certifyBFV?_textbook_mul`). No `Spec.Float.Conforms` hypothesis.
* `correct_textEval`: hence `Correct (schemeWith St (textEval St))`, and `meets_prob_eq`,
  `meets_prob_le` apply to it.
* `correct_textEval_seal`: the instance at `sealSetting` (`N = 2¹³`, HPS multiplication with its
  binary64 tolerance, HYBRID key switching, rotation keys for `g = 5`), every hypothesis
  discharged (`freshDecOK` kernel-checked). There the evaluator differs from the transcription at
  every product (exact FV against OpenFHE's binary64 HPS), and the class is nonempty (the compiled
  `#guard` on `sealCirc` in `Challenge.IndCpaD`). `correct_textEval_tiny`: the same at
  `tinySetting`, whose class membership is kernel-checked (`admissible_tiny`; there the declared
  technique is itself `textbook`, so the two evaluators agree).

What this does not show: that any library computes `textEval` (none does for an HPS setting:
OpenFHE multiplies by HPS); it shows only that the reduction is not tied to the transcription.
-/

namespace Challenge.IndCpaD
open Spec NPoly Scheme Source Spec.CertifyBFV Challenge.CertifyBFV Spec.IndCpaDBFV
open Spec.IndCpaD (Correct)

variable {St : Setting}

variable (St) in
/-- **The textbook-multiplication evaluator** (module docstring): the transcription's execution
of the circuit with the technique `textbook`, the outputs in order with their levels. -/
def textEval (pk : PK (St := St)) (C : Circ St) (cs : List (CT (St := St))) :
    List (CT (St := St)) :=
  C.prog.outputs.map fun o =>
    (C.outLevel o, (runLibrary { C.input with mul := some .textbook } Spec.Float.exact pk.rk pk.gk
      (C.cts cs) o).getD [])

/-- **The textbook-multiplication evaluator meets the contracts within the certified budget**,
for every setting whose technique is not `HPSPOVERQLEVELED`. -/
theorem textEval_meets (St : Setting) (hnl : ∀ Ps, St.base.mul ≠ some (.leveled Ps)) :
    EvalMeets St (textEval St) := sorry

/-- **Perfect correctness with the textbook-multiplication evaluator**, with no floating-point
hypothesis. -/
theorem correct_textEval (St : Setting) (hSt : freshDecOK St = true)
    (hnl : ∀ Ps, St.base.mul ≠ some (.leveled Ps)) : Correct (schemeWith St (textEval St)) :=
  sorry

/-- **The instance at `tinySetting`**, every hypothesis discharged. -/
theorem correct_textEval_tiny : Correct (schemeWith tinySetting (textEval tinySetting)) := sorry

/-- **The instance at `sealSetting`** (HPS declared; the evaluator multiplies by the textbook
algorithm), every hypothesis discharged. -/
theorem correct_textEval_seal : Correct (schemeWith sealSetting (textEval sealSetting)) := sorry

end Challenge.IndCpaD
