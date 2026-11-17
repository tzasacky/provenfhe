import Spec.Ring

/-!
# Spec.Scheme — what it means for a ciphertext to encrypt something   (TRUSTED)

Decryption and the noise invariants for BGV and BFV, plus validity of key-switching keys.
Everything is stated over `Spec.NPoly`, whose arithmetic is pinned to Mathlib's
`R[X]/(X^N + 1)` (see `Spec.Ring`).

Conventions:
- A ciphertext is the list of its components `[c₀, c₁, …]`; it decrypts with `(1, s, s², …)`.
- The secret `s` is an integer polynomial; it is reduced modulo whatever modulus is in use.
- "Noise" is always a function of `(s, ct)`, never data carried by a ciphertext.
- **For BGV, "noise" means the whole centred phase `m + t·e`, message included**, not the error
  `e` and not `t·e`: `BGVEncrypts t B` bounds `‖m + t·e‖∞ ≤ B`. Every bound on a BGV
  *ciphertext* in this development (`inputNoise`, the bounds of the analyzers, the bounds in a
  certificate) is a bound of this kind. Bounds on what is *added* to a phase are not: the key
  noise (`keyNoise`, `KeyValid`: the error `e` of a key, a multiple of `t` for BGV) and the
  budgets (`Trace.Budget`: the error a key switch or modulus switch adds) bound an error alone. A noiseless encryption of a message with a coefficient `⌊t/2⌋` has "noise"
  `⌊t/2⌋`. Decryption is exact as long as this quantity stays below `Q/2`. For BFV the
  bound is on the error alone (`BFVEncrypts`).
-/

namespace Spec.Scheme
open NPoly

variable {N : ℕ}

/-- The schemes covered. -/
inductive Kind
  | bgv
  | bfv
  deriving DecidableEq, Repr

/-- `⟨ct, (1, s, s², …)⟩ = c₀ + s·(c₁ + s·(c₂ + …))`. -/
def phase {q : ℕ} (s : Poly q N) : List (Poly q N) → Poly q N
  | [] => 0
  | c :: cs => c + s * phase s cs

/-- The phase under the integer secret `s`, centered: the unique integer polynomial with
coefficients in `(-Q/2, Q/2]` congruent to `⟨ct, (1, s, …)⟩` modulo `Q`. -/
def centeredPhase {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) : IntPoly N :=
  centered (phase (ofInt Q s) ct)

/-! ### BGV -/

/-- BGV decryption: `[[⟨ct, s⟩]_Q]_t`. -/
def bgvDecrypt (t : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) : Poly t N :=
  ofInt t (centeredPhase s ct)

/-- `ct` is a BGV encryption of `m` under `s` with noise at most `B`: it decrypts to `m`, and its
centered phase (`m + t·e`) has every coefficient of absolute value at most `B`. The bound is on
the whole phase, **message included**; it is not a bound on `e` or on `t·e` (module docstring). -/
def BGVEncrypts (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) : Prop :=
  bgvDecrypt t s ct = m ∧ normInf (centeredPhase s ct) ≤ B

/-! ### BFV -/

/-- `⌊a / b⌉`, rounding halves up; `b > 0` in every use. -/
def roundDiv (a : ℤ) (b : ℕ) : ℤ := (2 * a + b) / (2 * b)

/-- BFV decryption: `[⌊t·[⟨ct, s⟩]_Q / Q⌉]_t`. -/
def bfvDecrypt (t : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) : Poly t N :=
  ⟨fun i => (roundDiv (t * (centeredPhase s ct).coeff i) Q : ZMod t)⟩

/-- `ct` is a BFV encryption of `m` with noise at most `B`: it decrypts to `m`, and
`⟨ct, s⟩ = ⌊Q/t⌋·m + e (mod Q)` with `‖e‖∞ ≤ B`, taking `m`'s representatives in `[0, t)`. -/
def BFVEncrypts (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) : Prop :=
  bfvDecrypt t s ct = m ∧
    normInf (centered (phase (ofInt Q s) ct - ofInt Q ⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩))
      ≤ B

/-! ### Keys -/

/-- A secret key: an integer polynomial with every coefficient in `[-B, B]` (ternary: `B = 1`). -/
def SecretOK (B : ℕ) (s : IntPoly N) : Prop := normInf s ≤ B

/-- What a key-switching key encrypts: `s²` (relinearization) or `σ_g(s)` (rotation). -/
inductive KeyTarget
  | square
  | galois (g : ℕ)
  deriving DecidableEq, Repr

/-- The secret-dependent polynomial a key of this target encrypts. -/
def KeyTarget.eval (s : IntPoly N) : KeyTarget → IntPoly N
  | .square => s * s
  | .galois g => automorph g s

/-- A key the compiled program needs: a key-switching key modulo `modulus` encrypting
`factor · target(s)`. The compiler chooses `modulus` and `factor` (public constants, e.g. the
special prime `P` times a CRT gadget entry); the host generates keys to match. -/
structure KeyReq (N : ℕ) where
  modulus : ℕ
  factor : Poly modulus N
  target : KeyTarget

/-- `(b, a)` is a valid key for `req` under `s` with noise at most `B`:
`b + a·s = factor·target(s) + e (mod modulus)` with `‖e‖∞ ≤ B`, and for BGV `t ∣ e`.

The BGV clause `t ∣ e` is the LSB convention (OpenFHE, HElib: the key error is `t·e'`). Libraries
that implement BGV in MSB form (scale-invariant, plain error `e`) generate keys that do
not satisfy it. This affects only statements that take `KeyValid` keys as a hypothesis
with `kind = .bgv`: the BGV key-switching
realizability pins (`Challenge.Budget.relin_realizable`, `keySwitch_realizable` and their `_top`
versions), the key-restriction pins (`Challenge.Budget.gadgetKeys_restrict*`) and
`Challenge.Certify.certify?_keys_restrict`. The noise soundness statements (the predicate
`Challenge.Headline.NoiseSoundBGV`, and the soundness statements about `certify?`) mention no
keys: key switching enters them only through the error bound `Trace.Budget.keySwitch` and its
contract. -/
def KeyValid (kind : Kind) (t B : ℕ) (s : IntPoly N) (req : KeyReq N)
    (b a : Poly req.modulus N) : Prop :=
  let e := centered (b + a * ofInt req.modulus s - req.factor * ofInt req.modulus (req.target.eval s))
  normInf e ≤ B ∧ (kind = .bgv → ∀ i, (t : ℤ) ∣ e.coeff i)

end Spec.Scheme
