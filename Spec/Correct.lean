import Spec.Params

/-!
# Spec.Correct — what it means for ciphertexts to encrypt source values   (TRUSTED)

This file defines what the noise certificates mean by "a list of integer polynomials encrypts a
`Source` value at a level" (`Encrypts`), the value an input variable starts with (`inputVal`), and
the hypothesis that every input of a program is such an encryption (`InputsOK`). The BGV
certificates use all three (`Challenge.Certify`); the BFV contracts of `Spec.TraceBFV` use
`Encrypts` and `inputVal`.
-/

namespace Spec.Correct
open NPoly Scheme Layout Source

variable (P : FullParams)

/-- `ct` (integer representatives) encrypts the value `v` under `s` with noise at most `B`. The
modulus is the level's `q₀⋯q_{ℓ-1}` and the key is `σ_key(s)`. -/
def Encrypts (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N)) : Prop :=
  let Q := P.src.modulus v.level
  let sk := automorph v.key s
  ct.length = v.parts ∧
  match P.src.kind, v.msg with
  | .bgv, .exact m => BGVEncrypts P.src.t B sk (ct.map (ofInt Q)) m
  | .bfv, .exact m => BFVEncrypts P.src.t B sk (ct.map (ofInt Q)) m

/-- The value an input variable starts with (as in `Source.initEnv`). -/
def inputVal (msgs : Var → Msg P.src.t P.src.N) (d : Decl) : Val P.src :=
  { msg := msgs d.name, parts := d.parts, level := d.level, key := d.key, scale := d.scale }

/-- Every input ciphertext encrypts its message with noise at most `P.inputNoise`, as declared
by the *first* declaration of its name: the declaration `Source.initEnv` and `Trace.initCt` use.
(Quantifying over every declaration would make this hypothesis unsatisfiable for a program that
declares one name twice with different shapes, and every statement assuming it vacuous.) -/
def InputsOK (s : IntPoly P.src.N) (prog : Program) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∀ x d, prog.inputs.find? (·.name = x) = some d →
    Encrypts P s P.inputNoise (inputVal P msgs d) (cts x)

end Spec.Correct
