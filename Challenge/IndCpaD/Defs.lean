import Spec.IndCpaDBFV
import Challenge.CertifyBFV.Library
import Challenge.BFVEncrypt.Defs

/-!
# Challenge.IndCpaD.Defs — the BFV instance of the IND-CPA-D game   (LOCKED definitions)

The scheme `scheme St` of `Spec.IndCpaD.HEScheme` for a fixed setting `St`:

* **encryption**: OpenFHE's BFV public-key encryption `Spec.EncryptBFV.encryptBFV` (`STANDARD`)
  of the packed storage `liftMsg m`, at the **top level**, with randomness `(u, e₁, e₂)`;
* **the evaluator**: `Challenge.CertifyBFV.runLibrary`, the transcription of the library's
  algorithms, run with the relinearization keys `rk` and the rotation keys `gk` of the public
  key, the setting's technique, plaintext-addition method, modulus switch and floating-point
  arithmetic `St.A`, and the circuit's declared drops; each output is returned with its level;
* **decryption**: textbook BFV decryption `Spec.Scheme.bfvDecrypt` at the ciphertext's level.
  Not a library's decryption routine: OpenFHE's raw output is only congruent to the message
  modulo `t` (`Spec.DecryptBFV`, `bfvDecryptLib_correct`), and a value that depends on the noise
  cannot be simulated from the messages;
* **messages**: `Poly t N`; what a circuit computes: `Spec.Source.eval` of its program;
* **the declared class** (`admissible`): `certifyBFVFresh?` accepts the circuit in the
  worst-case mode at the setting's sampler bounds, the certificate does not record `idealised`,
  and `extraOK`: every fresh input is declared at the top level (the oracle encrypts before
  the circuit is chosen), every plaintext operand that declares a bound declares at least
  `t − 1` (the circuit's constants are stored as `liftMsg`), and every key switch of the
  program, in the message-independent replay the evaluator itself performs, uses a Galois index
  in `St.rots`, the indices whose rotation keys the public key carries;
* **good keys** (`KeysOK`): the secret within `secretBound`, the public key `(b, a)` for it at
  the top level with noise scale 1 and error within `Bk`, relinearization keys valid at the top
  level, and for each index `g ∈ St.rots` rotation keys valid at the top level for `(s', σ_g(s'))`
  with `σ_g(s') = s`; the errors of the relinearization and rotation keys are bounded by
  `St.base.P.keyNoise` (`Budget.GadgetKeysOK`), a fifth sampler bound besides `Bk`, `Bu`, `B1`, `B2`. Key generation itself is not modelled: these are hypotheses (they hold with
  probability one only for samplers of bounded support);
* **good encryption randomness** (`GoodE`): `‖u‖∞ ≤ Bu`, `‖e₁‖∞ ≤ B1`, `‖e₂‖∞ ≤ B2` (the same
  remark).

**What this is not.** No claim about OpenFHE's security or its code: the evaluator is the
transcription `runLibrary` (whose agreement with the library is what the conformance harness
compares), the drops are declared by the circuit (not computed by `FindLevelsToDrop`), the
machine words and the NTT are exact modular arithmetic, and the binary64 steps are those of the
arithmetic `St.A` (the statements assume `Spec.Float.Conforms St.A`).
-/

namespace Challenge.IndCpaD
open Spec NPoly Scheme Source Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
  Challenge.CertifyBFV Challenge.BFVEncrypt Spec.IndCpaDBFV

variable {St : Setting}

variable (St) in
/-- A fresh encryption at the top level decrypts (checked once for the setting): `t ≥ 2` and the
worst case of the fresh noise passes the decryption condition at the top level. -/
def freshDecOK : Bool :=
  decide (2 ≤ St.base.P.src.t) &&
    Challenge.BFV.decOK St.base.P.src.t (Qtop St)
      (freshNoiseBFV St.base.P.src.t (Qtop St)
        (worstError St.base.P.src.N St.base.P.secretBound St.Bk St.Bu St.B1 St.B2))

/-- **The declared class** (module docstring). -/
def admissible (C : Circ St) : Bool :=
  match certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with
  | some fc => !(fc.cert.assumed.contains .idealised) && C.extraOK
  | none => false

/-- **The public evaluator**: the library's execution, the outputs in order, with their levels. -/
def eval (pk : PK (St := St)) (C : Circ St) (cs : List (CT (St := St))) : List (CT (St := St)) :=
  if cs.length = C.fresh.length then
    let σ := runLibrary C.input St.A pk.rk pk.gk (C.cts cs)
    C.prog.outputs.map fun o => (C.outLevel o, (σ o).getD [])
  else []

variable (St) in
/-- **The BFV scheme of the setting `St`**, as an `HEScheme`. -/
abbrev scheme : Spec.IndCpaD.HEScheme where
  PK := PK (St := St)
  SK := SK (St := St)
  CT := CT (St := St)
  M := Poly St.base.P.src.t St.base.P.src.N
  ER := ER (St := St)
  Circ := Circ St
  enc := enc
  eval := eval
  dec := dec
  sem := sem
  admissible := admissible
  KeysOK := KeysOK
  GoodE := GoodE

end Challenge.IndCpaD
