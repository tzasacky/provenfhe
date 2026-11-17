import Spec.Correct
import Mathlib.Data.Rat.Floor

/-!
# Challenge.Sanity.Conventions — the rounding, lift and noise conventions, pinned   (LOCKED statements; proofs in `Validation/Sanity/Conventions.lean`)

`docs/TRUSTED-CORE.md` (F7) states the conventions in prose; these statements prove them.

* `roundDiv_eq_floor`: `Spec.Scheme.roundDiv` is `⌊a/b + 1/2⌋` (round half up), the textbook
  `⌊·⌉` of [FV12] with ties up.
* `bfvDecrypt_any_lift`, `bfvDecrypt_canonical`: BFV decryption does not depend on which integer
  lift of the phase is used: the centred one of `Spec.Scheme.bfvDecrypt`, the `[0, Q)` one, or any
  other congruent one give the same message.
* `bfvEncrypts_centred_noise`: the BFV noise is measured with the message's representative in
  `[0, t)`; with the centred representative (as [FV12] writes `Δ·[m]_t`), the noise is larger by at
  most `Q mod t`.
* `encrypts_mono`, `encrypts_msg_unique`: a bound is an upper bound (raising it keeps
  `Encrypts`), and a ciphertext at a given level and key encrypts at most one message.
-/

namespace Challenge.Sanity
open Spec NPoly Scheme Correct

variable {N : ℕ}

/-- **`roundDiv` is round-half-up division**: `roundDiv a b = ⌊a/b + 1/2⌋` for `b > 0`. -/
theorem roundDiv_eq_floor (a : ℤ) (b : ℕ) (hb : 0 < b) :
    roundDiv a b = ⌊(a : ℚ) / b + 1 / 2⌋ := sorry

/-- **BFV decryption is the same for every integer lift of the phase**: if `a` is any integer
polynomial congruent to the phase modulo `Q`, decryption is `[⌊t·a/Q⌉]_t` coefficientwise. -/
theorem bfvDecrypt_any_lift (t Q : ℕ) (hQ : 0 < Q) (s : IntPoly N) (ct : List (Poly Q N))
    (a : IntPoly N) (ha : ofInt Q a = phase (ofInt Q s) ct) :
    bfvDecrypt t s ct = ⟨fun i => (roundDiv (t * a.coeff i) Q : ZMod t)⟩ := sorry

/-- **In particular with the `[0, Q)` lift** (`Spec.NPoly.canonical`). -/
theorem bfvDecrypt_canonical (t Q : ℕ) (hQ : 0 < Q) (s : IntPoly N) (ct : List (Poly Q N)) :
    bfvDecrypt t s ct =
      ⟨fun i => (roundDiv (t * ((canonical (phase (ofInt Q s) ct)).coeff i : ℤ)) Q : ZMod t)⟩ :=
  sorry

/-- **The noise with the centred message representative is within `Q mod t` of the one
`BFVEncrypts` bounds**: `‖[⟨ct, s⟩ − ⌊Q/t⌋·[m]_t]_Q‖∞ ≤ B + Q mod t`, `[m]_t` the centred
representative. -/
theorem bfvEncrypts_centred_noise (t B Q : ℕ) (ht : 0 < t) (s : IntPoly N) (ct : List (Poly Q N))
    (m : Poly t N) (h : BFVEncrypts t B s ct m) :
    normInf (centered (phase (ofInt Q s) ct -
      ofInt Q ⟨fun i => ((Q / t : ℕ) : ℤ) * (m.coeff i).valMinAbs⟩)) ≤ B + Q % t := sorry

/-- **A bound is an upper bound**: `Encrypts` at `B` gives `Encrypts` at every `B' ≥ B`. -/
theorem encrypts_mono (P : FullParams) (s : IntPoly P.src.N) (B B' : ℕ) (hB : B ≤ B')
    (v : Source.Val P.src) (ct : List (IntPoly P.src.N)) (h : Encrypts P s B v ct) :
    Encrypts P s B' v ct := sorry

/-- **A ciphertext encrypts at most one message** at a given level and key, whatever the two
bounds. -/
theorem encrypts_msg_unique (P : FullParams) (s : IntPoly P.src.N) (B B' : ℕ)
    (v v' : Source.Val P.src) (ct : List (IntPoly P.src.N)) (hl : v.level = v'.level)
    (hk : v.key = v'.key) (h : Encrypts P s B v ct) (h' : Encrypts P s B' v' ct) :
    v.msg = v'.msg := sorry

end Challenge.Sanity
