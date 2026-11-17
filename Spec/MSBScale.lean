import Spec.MSB
import Spec.Scaling

/-!
# Spec.MSBScale — what the user of an MSB library reads after decoding   (TRUSTED)

`Spec.MSB` and `Challenge.MSB` are about the message an MSB ciphertext *holds*: the message
`Spec.Source.eval` computes, which carries a factor `q_last⁻¹ mod t` per `modSwitch` and `c` per
`mulConst c`. An MSB library tracks a per-ciphertext **scale** `λ ∈ Z_t` and decodes by
multiplying the decrypted polynomial by `λ⁻¹`. This file states that bookkeeping for a library
whose scale follows the rules below, so that a statement can be about what the user reads
(`Challenge.MSBScale`).

**The scale rules** (Lattigo v6.2.0, commit `c1fd095f`, `schemes/bgv`, `file:line`):

* **Encode** (`encoder.go:203-248`, `EncodeRingT`: the slots, as a polynomial, times
  `scale`; `encoder.go:143-200` the same in the coefficient domain): the stored plaintext is
  `λ · u` with `u` the user's message. Encryption copies the plaintext's scale. So an input's
  scale is its declared factor (`Spec.Scaling.ScaleData.factors`, `scaledMsgs`).
* **Products** (`evaluator.go:592-596`, `tensorStandard`): `λ = λ₀ · λ₁`, for a ciphertext or a
  plaintext operand alike.
* **Rescale** (`evaluator.go:1363-1393`): `λ = λ₀ · q⁻¹`, `q` the dropped prime.
* **Scale matching in addition and subtraction** (`evaluator.go:122-140` and `:287-305`, `Add`
  and `Sub`, calling `matchScaleThenEvaluateInPlace`, `:227-244`): the operands are multiplied by
  constants `r₀`, `r₁` with `λ₀·r₀ = λ₁·r₁ (mod t)` and the result has scale `λ₀·r₀`. In a
  `Spec.Source` program these multiplications are `mulConst` instructions **marked** as
  adjustments (`ScaleData.marks`): the constant multiplies the message and the scale, and the
  plain semantics ignores it (`Spec.Scaling.plainInstr`).
* **Everything else** (unmarked multiplication by an integer constant, relinearization, key
  switching, automorphisms, dropping limbs): the scale is unchanged.
* **Decode** (`encoder.go:470-500`, `Decode`, and `:341-345`, `DecodeRingT`): MSB decryption at
  the ciphertext's own level (`RingQ2T`, no switching down to one limb), then multiplication by
  `λ⁻¹ mod t`.

These are exactly the rules by which `Spec.Scaling.facStep` computes the **true** factor `phi`
(the message the ciphertext holds is `phi •` the plain message). So the scale such a library
tracks is `phi` itself: `decodeAt?` reads `phi`, not the OpenFHE-specific tracked factor `lam`
of `Spec.Scaling` (whose plaintext-product and decryption rules differ). That a given library
execution follows these rules is an assumption about the library, as `Spec.Trace.Run` is for the
noise.
-/

namespace Spec.MSBScale
open NPoly Source Scaling Spec.MSB

/-- The decode scale and the level of output `o`: the true factor `phi` and the level computed
by `Spec.Scaling.factors?` (module docstring: the scale an MSB library with these rules tracks). -/
def decodeAt? (P : Params) (prog : Program) (sd : ScaleData) (o : Var) :
    Option (ZMod P.t × ℕ) := do
  let F ← factors? P prog sd
  let x ← F o
  pure (x.phi, x.level)

/-- **What the user reads** (at polynomial level) from an MSB ciphertext `ct` at level `ℓ` with
scale `λ`: `λ⁻¹ •` its MSB decryption at that level. -/
def userDecrypt (P : Params) (lam : ZMod P.t) (ℓ : ℕ) (s : IntPoly P.N)
    (ct : List (IntPoly P.N)) : Poly P.t P.N :=
  lam⁻¹ • msbDecrypt P.t s (ct.map (ofInt (P.modulus ℓ)))

/-- **The check.** The factors of the program exist and the scale of every output is a unit
modulo `t` (`λ · λ⁻¹ = 1`). -/
def scaleOK? (P : Params) (prog : Program) (sd : ScaleData) : Bool :=
  match factors? P prog sd with
  | none => false
  | some F => prog.outputs.all fun o =>
    match F o with
    | none => false
    | some x => decide (x.phi * x.phi⁻¹ = 1)

end Spec.MSBScale
