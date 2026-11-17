import Spec.MSBScale
import Challenge.MSB
import Challenge.Scaling

/-!
# Challenge.MSBScale — what the user of an MSB library reads   (LOCKED statements; proofs in `Validation/MSBScale.lean`)

`Challenge.MSB.certifyProfile?_sound_msb` says every output MSB-decrypts to the message
`Source.eval` computes. That message is the plain result times the factor `phi` the scale rules
of `Spec.MSBScale` track (`Challenge.Scaling.eval_scaled`). The statement here connects the two:
if `certifyProfile?` accepts and the scale check `Spec.MSBScale.scaleOK?` passes, every output
of every MSB run, decrypted at its own level and divided by its scale (`userDecrypt` with the
scale of `decodeAt?`), is the plain semantics of the program on the user's messages
(`Spec.Scaling.plainEval`).

**What remains assumed**: that the library's scale follows the rules of `Spec.MSBScale` (so that
its scale is `phi`); that the marks are exactly the library's scale-matching multiplications;
that the declared input factors are the scales the encoder applied; and the hypotheses of
`certifyProfile?_sound_msb`.
-/

namespace Challenge.MSBScale
open Spec NPoly Scheme Source Correct Spec.Scaling Spec.MSB Challenge.Profile

/-- **The user-level statement in MSB form.** -/
theorem certifyProfile?_user_msb (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (sd : ScaleData) (hsc : Spec.MSBScale.scaleOK? P.src prog sd = true)
    (Bin : ℕ) (hBin : Bin ≤ P.inputNoise) (hbnd : ∀ x b, prog.boundOf x = some b → Bin ≤ b)
    (hwrap : ∀ d ∈ prog.inputs, 2 * Bin < P.src.modulus d.level)
    (s : IntPoly P.src.N) (u : Var → Poly P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N))
    (hin : MSB.InputsOK P s Bin prog (scaledMsgs P.src sd u) cts) :
    ∀ σ, MSB.Run P E s prog.body (initEnv P.src prog (scaledMsgs P.src sd u))
        (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ ct lam ℓ, σ o = some ct ∧
        Spec.MSBScale.decodeAt? P.src prog sd o = some (lam, ℓ) ∧
        Spec.MSBScale.userDecrypt P.src lam ℓ s ct = plainEval prog sd.marks u o := sorry

end Challenge.MSBScale
