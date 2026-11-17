import Respec.BFV
import Respec.Equiv.Decrypt
import Challenge.BFV.Defs

/-!
# Respec.Equiv.BFV — item 12 (brief): BFV decryption, the invariant, `decOK`

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Verdicts

* **Decryption: EQUAL (PROVED)** `bfvDecrypt_eq` : B's `BFV.decrypt` is A's `bfvDecrypt`
  (`roundDiv` and `rdiv` are the same formula, rounding halves up; the phase is centred on both
  sides).
* **Invariant: EQUAL (PROVED)** `bfvEncrypts_iff` : A's `BFVEncrypts t B s ct m` is
  `B.decrypt = m ∧ EncryptsDelta .floorDelta .canonical s ct m B`: A's `Δ`-form noise with
  `Δ = ⌊Q/t⌋` and the message lifted to `[0, t)` (OpenFHE's encoding; B's `encodeOpenFHE` differs
  from `floorDelta` only in how it computes the same residue).
* **`decOK` is the exact worst-case condition** (kernel-checked at B's counterexample
  `Q = 2115473`, `t = 5`, `Δ = 423094`, `r = Q mod t = 3`): `decOK 5 Q 211544 = true`,
  `decOK 5 Q 211545 = false` (`decOK_threshold`), while `211545 < Δ/2`; and the one-coefficient
  ciphertext `Δ·4 − 211545` (noise `211545 < Δ/2`, message `4` lifted to `[0,t)`) does **not**
  decrypt to `4` (`deltaHalf_fails`): B's finding holds, and A's `decOK` (with its
  `(Q mod t)·(t − 1)` term) rejects exactly this bound. The condition
  `2·(t·B + r·(t − 1)) < Q` is necessary in the worst case (`m̃ = t − 1`, `v = −B`) and sufficient
  (A's `Challenge.BFV.bfv_decrypt_of_noise`).
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Respec Validation.Ring Validation.Scheme

variable {N : ℕ}

theorem bfvDecrypt_eq (t : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) :
    BFV.decrypt t s ct = bfvDecrypt t s ct := by
  ext i
  show (BFV.decrypt t s ct).coeff i =
    (((2 * ((t : ℤ) * (centeredPhase s ct).coeff i) + (Q : ℤ)) / (2 * (Q : ℤ)) : ℤ) : ZMod t)
  simp only [BFV.decrypt, force_eq, crit_eq, rdiv]

theorem bfvEncrypts_iff (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) :
    BFVEncrypts t B s ct m ↔
      BFV.decrypt t s ct = m ∧ BFV.EncryptsDelta .floorDelta .canonical s ct m B := by
  rw [bfvDecrypt_eq]
  unfold BFVEncrypts BFV.EncryptsDelta BFV.noiseDelta
  have : BGV.phase s ct ⊟ BFV.encode .floorDelta .canonical Q m =
      phase (ofInt Q s) ct - ofInt Q ⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩ := by
    rw [psub_eq, phase_eq]
    congr 1
    ext i
    simp [BFV.encode, BFV.encodeZ, Lift.rep, ofInt_unfold]
  rw [liftC_eq, this]

/-- B's counterexample, threshold form: the largest accepted bound is `211544`, below `Δ/2`. -/
theorem decOK_threshold :
    Challenge.BFV.decOK 5 2115473 211544 = true ∧ Challenge.BFV.decOK 5 2115473 211545 = false ∧
      2 * 211545 < 2115473 / 5 := by
  decide +kernel

/-- **`‖v‖ < Δ/2` does not imply correct decryption with a `[0, t)` lift**: the phase
`Δ·4 − 211545` (`N = 1`, `s = 0`) has `Δ`-noise `−211545` for the message `4`, yet does not
decrypt to `4`. -/
theorem deltaHalf_fails :
    bfvDecrypt 5 (0 : IntPoly 1) [(⟨fun _ => ((423094 * 4 - 211545 : ℤ) : ZMod 2115473)⟩ :
        Poly 2115473 1)] ≠ (⟨fun _ => 4⟩ : Poly 5 1) := by
  intro h
  have h1 := congrArg (fun p : Poly 5 1 => p.coeff 0) h
  revert h1
  unfold bfvDecrypt centeredPhase
  decide +kernel

end Respec.Equiv
