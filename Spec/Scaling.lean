import Spec.Decrypt

/-!
# Spec.Scaling — what a BGV library's user reads after decoding   (TRUSTED)

`Spec.Source.step` is about the message a BGV ciphertext *holds*: it multiplies it by
`q_last⁻¹ mod t` at every `modSwitch` and by `c` at every `mulConst c`, and the switched
decryption returns it times `Spec.Decrypt.decScale`. A library's user does not read that message.
OpenFHE keeps a factor `scalingFactorInt` with every plaintext and ciphertext, multiplies the
encoded slots by it when encoding, and divides by the factor that `Decrypt` hands back when
decoding. This file states that bookkeeping, so that a statement can be about what the user reads
(`Challenge.Scaling`).

**Slots are not modelled.** OpenFHE's packed encoding maps slot vectors to polynomials by the
inverse NTT modulo `t`, a ring isomorphism `Z_t^N ≅ Z_t[X]/(X^N+1)` (when `t ≡ 1 mod 2N`); scaling
the slots by a constant scales the polynomial by it. Everything here is at polynomial level: the
user's message is a polynomial `u ∈ Z_t[X]/(X^N+1)` (the encoding of the slots), and "decode" is
multiplication by the inverse of the factor modulo `t`. Decoding back to slots is the inverse
isomorphism and is not stated.

## The three pieces

1. **Plain semantics** (`plainInstr`, `plainEval`): what the program computes on the user's
   messages: ring operations modulo `t` (`add`, `sub`, `mul`, `square`, the plaintext operations,
   `automorph`), the identity for `modSwitch`, `dropLimbs`, `relin`, `keySwitch`, `copy`,
   `toEval`, `toCoeff`, and for `mulConst c`:
   multiplication by `c`, unless the instruction is **marked** as a scale adjustment (then the
   identity). The marks are a `List Bool` beside the body (`ScaleData.marks`; entry `i` for
   instruction `i`, missing entries unmarked); `Source.Instr` is unchanged.
2. **Factors** (`Fac`, `facStep`, `factors?`): for each variable, the *true* factor `phi` (the
   message the ciphertext holds is `phi • (plain message)`), the factor `lam` the *library*
   tracks, and the level. Inputs start with both equal to the declared factor
   (`ScaleData.factors`).
3. **User-level decryption** (`decodeFactor`, `userDecrypt`): the switched decryption
   (`Spec.Decrypt.bgvDecryptSwitched`, which is OpenFHE's `Decrypt` at polynomial level) times the
   inverse of the factor `Decrypt` hands to `Decode`.

`scaleOK?` decides, for every output, that the factor `Decrypt` hands to `Decode` equals
`phi · decScale` and is a unit modulo `t`. Then decoding cancels exactly the factor the switched
decryption leaves (`Challenge.Scaling.certify?_user`).

## The library's factor-tracking policy: OpenFHE v1.6.1 (commit b59e1f29), as `facStep` encodes it

**This section, and `facStep`/`decodeFactor` below, are library-specific trusted text**: they
transcribe how one library (OpenFHE v1.6.1, BGV) updates its `scalingFactorInt`. The plain
semantics (`plainEval`), `userDecrypt` and the shape of the check are generic; the tracking rules
are this library's policy and must be re-read for another library or version.

Paths are under `src/pke/`. "Tracking" (`ScaleData.tracks`) means the technique is `FLEXIBLEAUTO`
or `FLEXIBLEAUTOEXT`; the code that updates `scalingFactorInt` is guarded by that test everywhere
cited below except where said.

* **Encode** (`lib/encoding/packedencoding.cpp:68-91`): the slots are multiplied by the
  plaintext's factor (raised to its noise-scale degree, which becomes the recorded factor) before
  packing. **Make a plaintext** (`include/cryptocontext.h:195-205`): the factor is
  `GetScalingFactorInt(level)` under tracking (`GetScalingFactorIntBig(0)` at level 0 under
  `FLEXIBLEAUTOEXT`), else 1. **Encrypt** (`include/cryptocontext.h:1394,1431`): the ciphertext
  copies the plaintext's factor. So an input's true factor and tracked factor are the same number,
  the one recorded with it: `facInit`.
* **Products** (`lib/schemebase/base-leveledshe.cpp:657-658` for `EvalMultCore`, `:707-708` for
  `EvalSquareCore`): the factors multiply, **unconditionally** (any technique).
* **Plaintext product** (`lib/scheme/bgvrns/bgvrns-leveledshe.cpp:241-249`): after
  `LeveledSHERNS::EvalMultInPlace` (`lib/schemerns/rns-leveledshe.cpp:262-277`, which does not
  touch the factor) the BGV wrapper sets the factor to the **square of the ciphertext's own
  factor**, under tracking. That is the true product only when the plaintext's factor equals the
  ciphertext's. (The `EvalMultMutable*` variants, `rns-leveledshe.cpp:291,308`, multiply by the
  plaintext's factor instead; `facStep` models `EvalMult`, the in-place path.)
* **Adjustment by a constant** (`bgvrns-leveledshe.cpp:227-239`, `EvalMultCoreInPlace(ct,
  NativeInteger)`, called from `AdjustLevelsAndDepthInPlace`, `:86-214`): every component is
  multiplied by the constant; under tracking the factor too. This is a marked `mulConst`. The
  explicit `SetScalingFactorInt(...)` calls at the end of the branches of
  `AdjustLevelsAndDepthInPlace` (`:111,127,138,149,165,181,192,203`) are not modelled: they set
  the factor to the value the multiplications and switches already produced when every factor is
  the one OpenFHE's tables (`GetScalingFactorInt`, `GetScalingFactorIntBig`, `rns-cryptoparameters.h:1176-1215`)
  predict for its level and degree.
* **Modulus switch** (`bgvrns-leveledshe.cpp:47-77`, `ModReduceInternalInPlace`): the factor is
  multiplied by `(q_last mod t)⁻¹`, under tracking only. **LevelReduce** (`:79-83`): factor
  unchanged. **Negation, addition, subtraction, rotation, relinearization, key switching**: the
  result keeps the (first) ciphertext operand's factor: it is a `Clone` of it
  (`lib/schemebase/base-leveledshe.cpp:55` `EvalNegate`, `:569,596` `EvalAddCore`, `EvalSubCore`,
  `:575-610` their in-place forms, which change only the elements) or a `CloneEmpty`, which copies
  the factor (`include/ciphertext.h:449-457`; `base-leveledshe.cpp:439,448` automorphism,
  `lib/keyswitch/keyswitch-hybrid.cpp:241,271` key switching). **Plaintext addition and
  subtraction** (`rns-leveledshe.cpp:118-140,184-193`): the plaintext is morphed into a one-part
  ciphertext carrying its own factor (`base-leveledshe.cpp:522-534`) and added with
  `EvalAddCoreInPlace`, so the result keeps the ciphertext's factor.
* **Decrypt** (`lib/scheme/bgvrns/bgvrns-pke.cpp:48-102`, the `EVALUATION` branch `:56-75`):
  switches the phase down to one limb (`bgvDecryptSwitched`) and, under tracking only, multiplies
  the returned factor by `(q_i mod t)⁻¹` for each dropped limb `q_{ℓ-1}, …, q_1` (`:66-73`), i.e.
  by `decScale`. `lib/cryptocontext.cpp:490` stores it in the result plaintext; **Decode**
  (`packedencoding.cpp:195-215`) multiplies by its inverse modulo `t` (after unpacking: the same
  at polynomial level).
* **Without tracking** (`FIXEDMANUAL`, `FIXEDAUTO`) OpenFHE chooses every prime `≡ 1 mod t`
  (`lib/scheme/bgvrns/bgvrns-parametergeneration.cpp:146-163` for `FIXEDAUTO` with automatic
  sizes, `:514-543` otherwise): every `q_last⁻¹ mod t` is 1, so every factor stays 1. `facStep`
  does not assume this; `scaleOK?` checks the outcome.

What is *not* established here: that a given OpenFHE execution follows these rules (that its
`scalingFactorInt` at each step is the `lam` computed here), that the marks are exactly OpenFHE's
adjustments, and that the declared input factors are the factors the encoder applied. These are
assumptions about the library and the frontend, as `Spec.Trace.Run` is for the noise.
-/

namespace Spec.Scaling
open NPoly Source Decrypt

/-- Update a function at one variable. -/
def upd {α : Type} (f : Var → α) (d : Var) (v : α) : Var → α :=
  fun y => if y = d then v else f y

/-! ## Plain semantics -/

section Plain
variable {t N : ℕ}

/-- One instruction on the user's messages. `adj`: the instruction is a scale adjustment (only
read by `mulConst`). Total: every variable has a message (undefined ones are irrelevant). -/
def plainInstr (adj : Bool) (μ : Var → Poly t N) : Instr → (Var → Poly t N)
  | .add d a b | .addPlain d a b => upd μ d (μ a + μ b)
  | .sub d a b | .subPlain d a b => upd μ d (μ a - μ b)
  | .mul d a b | .mulPlain d a b => upd μ d (μ a * μ b)
  | .square d a => upd μ d (μ a * μ a)
  | .mulConst d a c => upd μ d (if adj then μ a else (c : ZMod t) • μ a)
  | .automorph d a g => upd μ d (automorph g (μ a))
  | .copy d a | .toEval d a | .toCoeff d a | .relin d a | .keySwitch d a | .modSwitch d a
  | .dropLimbs d a _ => upd μ d (μ a)

/-- Run a body; `ms` are the marks of its instructions, in order. -/
def plainRun : List Instr → List Bool → (Var → Poly t N) → (Var → Poly t N)
  | [], _, μ => μ
  | i :: is, ms, μ => plainRun is ms.tail (plainInstr (ms.headD false) μ i)

/-- **What the program computes on the user's messages** `u` (one per variable; the inputs'
are read). -/
def plainEval (prog : Program) (marks : List Bool) (u : Var → Poly t N) : Var → Poly t N :=
  plainRun prog.body marks u

end Plain

/-! ## Factors -/

/-- The scaling data that goes with a program: the factor of each input (OpenFHE: the
`scalingFactorInt` recorded with the input ciphertext or plaintext), the adjustment marks, and
whether the library tracks factors (`FLEXIBLEAUTO`, `FLEXIBLEAUTOEXT`). Numbers are read modulo
`t`. -/
structure ScaleData where
  factors : List (Var × ℕ)
  marks : List Bool
  tracks : Bool
  deriving Repr

/-- The factor of variable `x` (of an input: its declared factor; `0` if none is declared, which
`factors?` rejects for an input). -/
def inputFactor (P : Params) (sd : ScaleData) (x : Var) : ZMod P.t :=
  (((sd.factors.lookup x).getD 0 : ℕ) : ZMod P.t)

/-- The messages the input ciphertexts hold: the user's message `u x` times the input's factor. -/
def scaledMsgs (P : Params) (sd : ScaleData) (u : Var → Poly P.t P.N) : Var → Msg P.t P.N :=
  fun x => .exact (inputFactor P sd x • u x)

/-- The factors of one variable: `phi`, the true factor (the message the ciphertext holds is
`phi •` the plain message); `lam`, the factor the library tracks; and the level. -/
structure Fac (t : ℕ) where
  phi : ZMod t
  lam : ZMod t
  level : ℕ

/-- Inputs: both factors are the declared one; the level of the (first) declaration. -/
def facInit (P : Params) (prog : Program) (sd : ScaleData) : Var → Option (Fac P.t) :=
  fun x => (prog.inputs.find? (·.name = x)).map fun d =>
    ⟨inputFactor P sd x, inputFactor P sd x, d.level⟩

/-- One instruction on the factors (module docstring for the OpenFHE lines). `none`: an undefined
operand, operands of an addition or subtraction with different true factors (the sum would not be
a multiple of one plain message), or a `modSwitch` without a limb to drop. -/
def facStep (P : Params) (tracks adj : Bool) (F : Var → Option (Fac P.t)) :
    Instr → Option (Var → Option (Fac P.t))
  | .add d a b | .sub d a b | .addPlain d a b | .subPlain d a b => do
    let x ← F a; let y ← F b
    guard (x.phi = y.phi)
    pure (upd F d (some x))
  | .mul d a b => do
    let x ← F a; let y ← F b
    pure (upd F d (some ⟨x.phi * y.phi, x.lam * y.lam, x.level⟩))
  | .square d a => do
    let x ← F a
    pure (upd F d (some ⟨x.phi * x.phi, x.lam * x.lam, x.level⟩))
  | .mulPlain d a p => do
    let x ← F a; let y ← F p
    pure (upd F d (some ⟨x.phi * y.phi, if tracks then x.lam * x.lam else x.lam, x.level⟩))
  | .mulConst d a c => do
    let x ← F a
    pure (upd F d (some (if adj then
      ⟨(c : ZMod P.t) * x.phi, if tracks then (c : ZMod P.t) * x.lam else x.lam, x.level⟩
      else x)))
  | .modSwitch d a => do
    let x ← F a
    guard (2 ≤ x.level)
    let q ← P.qs[x.level - 1]?
    pure (upd F d (some ⟨((q : ZMod P.t))⁻¹ * x.phi,
      if tracks then ((q : ZMod P.t))⁻¹ * x.lam else x.lam, x.level - 1⟩))
  | .dropLimbs d a k => do
    let x ← F a
    pure (upd F d (some { x with level := x.level - k }))
  | .copy d a | .toEval d a | .toCoeff d a | .relin d a | .keySwitch d a | .automorph d a _ => do
    let x ← F a
    pure (upd F d (some x))

/-- Run a body on the factors. -/
def facRun (P : Params) (tracks : Bool) :
    List Instr → List Bool → (Var → Option (Fac P.t)) → Option (Var → Option (Fac P.t))
  | [], _, F => some F
  | i :: is, ms, F => do
    let F' ← facStep P tracks (ms.headD false) F i
    facRun P tracks is ms.tail F'

/-- The factors of every variable after the program, if the program is BGV, every input has a
declared factor, and no step fails. -/
def factors? (P : Params) (prog : Program) (sd : ScaleData) : Option (Var → Option (Fac P.t)) := do
  guard (P.kind = .bgv)
  guard (prog.inputs.all fun d => (sd.factors.lookup d.name).isSome)
  facRun P sd.tracks prog.body sd.marks (facInit P prog sd)

/-! ## User-level decryption -/

/-- The factor `Decrypt` hands to `Decode` for a ciphertext with factors `x`: under tracking the
tracked factor times the inverses of the dropped limbs (`decScale`), else the tracked factor. -/
def decodeFactor (P : Params) (tracks : Bool) (x : Fac P.t) : ZMod P.t :=
  if tracks then x.lam * decScale P x.level else x.lam

/-- The decode factor and the level of output `o`. -/
def decodeAt? (P : Params) (prog : Program) (sd : ScaleData) (o : Var) : Option (ZMod P.t × ℕ) := do
  let F ← factors? P prog sd
  let x ← F o
  pure (decodeFactor P sd.tracks x, x.level)

/-- **What the user reads** (at polynomial level) from a ciphertext `ct` at level `ℓ` whose
`Decrypt` hands the factor `dF` to `Decode`: the switched decryption times `dF⁻¹`. -/
def userDecrypt (P : Params) (dF : ZMod P.t) (ℓ : ℕ) (s : IntPoly P.N)
    (ct : List (IntPoly P.N)) : Poly P.t P.N :=
  dF⁻¹ • bgvDecryptSwitched P.t (P.qs.take ℓ) s (ct.map (ofInt (P.qs.take ℓ).prod))

/-- **The check.** The factors of the program exist (`factors?`) and for every output: the factor
`Decrypt` hands to `Decode` is `phi · decScale` (exactly what the switched decryption leaves on the
plain message) and is a unit modulo `t` (`d · d⁻¹ = 1`, which for `ZMod t` is `gcd(d, t) = 1`:
`ZMod.mul_inv_eq_gcd`). -/
def scaleOK? (P : Params) (prog : Program) (sd : ScaleData) : Bool :=
  match factors? P prog sd with
  | none => false
  | some F => prog.outputs.all fun o =>
    match F o with
    | none => false
    | some x =>
      decide (decodeFactor P sd.tracks x = x.phi * decScale P x.level) &&
        decide (decodeFactor P sd.tracks x * (decodeFactor P sd.tracks x)⁻¹ = 1)

end Spec.Scaling
