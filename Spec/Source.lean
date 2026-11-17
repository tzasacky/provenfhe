import Spec.Scheme

/-!
# Spec.Source — homomorphic programs and what they compute   (TRUSTED)

A source program is a straight-line list of homomorphic operations on named ciphertexts. It is
what every statement of this development is about, and what the frontends of `fhe_check`
produce: the OpenFHE frontend (BGV and BFV; a trace of the library's own calls) and the HEIR
frontend, both untrusted (`harness/frontend/`). The pins in `Challenge/`
also use small programs written by hand.

**The message of a variable is the message the ciphertext holds, not the user's value.** For BGV,
`step` multiplies the message by `q_last⁻¹ mod t` at every `modSwitch` (the exact effect of the
t-corrected switch on the phase modulo `t`). A library hides this factor from its user by
bookkeeping (OpenFHE: `scalingFactorInt`, divided out when a plaintext is decoded); that
bookkeeping is not part of `step`.

The meaning of a ciphertext variable is a `Val`: the message it decrypts to, plus the bookkeeping
the decryption needs (number of components, level, and which Galois conjugate of the secret it
is under). Nothing here mentions RNS limbs, NTT form or Montgomery form; those
are representation choices of an implementation.

Operation set: the homomorphic operations of the BGV and BFV libraries the frontends read
(addition, subtraction, tensor product, squaring, multiplication by a constant, copy, change of
representation form, relinearization, key switching, automorphism, modulus switching), the
ciphertext–plaintext operations (`addPlain`, `subPlain`, `mulPlain`) and `dropLimbs` (HEIR
`level_reduce`, OpenFHE `LevelReduce`). Key switching applies to an already-permuted ciphertext:
a rotation is `automorph` followed by `keySwitch`. Steps internal to an algorithm (such as the
basis extension of hybrid key switching) have no meaning at this level and are not source ops.

**Plaintexts.** A plaintext operand is a *one-component* value: an integer polynomial `p`, read as
the ciphertext `[p]`. Its phase is `p` itself under every key, so it "encrypts" the message
`p mod t` with "noise" `‖p‖∞`. Nothing here fixes which representative `p` of the message an
encoder stores: that is a convention of the encoder, and the only thing a noise claim uses of it
is a **declared bound** on `‖p‖∞` (`Program.bounds`). The two standard conventions are instances
(`Challenge.Source.encrypts_plain_bgv` for any representative within a declared bound;
`encrypts_plain_canonical`, `encrypts_plain_centred`): the representative in `[0, t)`, bound
`t − 1` (OpenFHE's packed encoding), and the centred one, bound `⌊t/2⌋`. A stored polynomial can
also be larger than both (OpenFHE's coefficient-packed plaintexts under `FLEXIBLEAUTO*` are
scaled without reduction modulo `t`: module docstring of `Spec.Encrypt`); then the declared bound
must say so.

A program takes a run-time plaintext as an ordinary declared input with `parts = 1`, at the level
where it is used, and declares its bound in `Program.bounds`.

The plaintext operations `addPlain`, `subPlain` and `mulPlain` are `add`, `sub` and `mul` with a
one-component second operand, except that they do not compare keys (a one-component value has
none).
-/

namespace Spec.Source
open NPoly Scheme

/-- Ciphertext variable names. -/
abbrev Var := String

/-- Scheme parameters that the meaning of a program depends on. Representation choices (word
size, size of the moduli, NTT-friendliness) are an implementation's business and are not assumed
here. -/
structure Params where
  kind : Kind
  /-- Ring dimension. -/
  N : ℕ
  /-- Ciphertext moduli `q₀, …, q_{L-1}`; a ciphertext at level `ℓ` lives modulo `q₀⋯q_{ℓ-1}`. -/
  qs : List ℕ
  /-- Plaintext modulus (BGV, BFV). -/
  t : ℕ
  deriving Repr

/-- The ciphertext modulus at level `ℓ`. -/
def Params.modulus (P : Params) (ℓ : ℕ) : ℕ := (P.qs.take ℓ).prod

/-- Messages: elements of `Z_t[X]/(X^N+1)` (BGV and BFV). -/
inductive Msg (t N : ℕ)
  | exact (m : Poly t N)

/-- What a ciphertext variable holds. -/
structure Val (P : Params) where
  msg : Msg P.t P.N
  /-- Number of components (2 after encryption, 3 after `mul` before `relin`). -/
  parts : ℕ
  /-- Number of ciphertext limbs in use. -/
  level : ℕ
  /-- The ciphertext decrypts under `σ_key(s)` (`key = 1`: under `s`). Taken mod `2N`. -/
  key : ℕ
  /-- A scale. Carried along by `step` and read by no statement (a remnant of an approximate
  scheme that is not part of this development; kept because the declaration literals
  `⟨name, parts, level, scale, key⟩` of the locked statements include it). -/
  scale : ℚ

/-- Homomorphic operations. `dst` may equal an operand. -/
inductive Instr
  | add (dst a b : Var)
  | sub (dst a b : Var)
  /-- Tensor product without relinearization: `p + p' - 1` parts. -/
  | mul (dst a b : Var)
  | square (dst a : Var)
  /-- Multiply by an integer constant. -/
  | mulConst (dst a : Var) (c : ℤ)
  | copy (dst a : Var)
  /-- Forward NTT: change of representation form only; the meaning (`Val`) is unchanged. At this
  level `toEval`, `toCoeff` and `copy` are the same operation (`step` treats them alike): which
  form a variable is represented in is not part of its `Val`. See `step`. -/
  | toEval (dst a : Var)
  /-- Inverse NTT: as `toEval`; the meaning is unchanged and equal to that of `copy`. -/
  | toCoeff (dst a : Var)
  /-- 3 parts under `(1, s, s²)` to 2 parts under `(1, s)`. Uses a key with target `s²`. -/
  | relin (dst a : Var)
  /-- Key switching: switch a 2-part ciphertext from `σ_g(s)` back to `s`, where `g` is the
  operand's `key`. Uses a key with target `σ_g(s)`. -/
  | keySwitch (dst a : Var)
  /-- Apply `X ↦ X^g` (odd `g`) to every component: the message becomes `σ_g(msg)` and the
  ciphertext is now under `σ_g` of its previous key. -/
  | automorph (dst a : Var) (g : ℕ)
  /-- Modulus switching: drop the last limb. BGV: exact t-corrected switch, which multiplies the
  message by `q_last⁻¹ mod t`. BFV: the message is unchanged. -/
  | modSwitch (dst a : Var)
  /-- Add the plaintext `p` (a one-component value at the same level) to `a`. -/
  | addPlain (dst a p : Var)
  /-- Subtract the plaintext `p` from `a`. -/
  | subPlain (dst a p : Var)
  /-- Multiply `a` by the plaintext `p` (every component is multiplied by the polynomial). -/
  | mulPlain (dst a p : Var)
  /-- HEIR `level_reduce`, OpenFHE `LevelReduce`: drop the last `k` limbs *without* dividing.
  The message and (for BGV) the phase as an integer polynomial are unchanged; the modulus
  becomes the shorter product. Not a BFV operation (the BFV message is scaled by `⌊Q/t⌋`). -/
  | dropLimbs (dst a : Var) (k : ℕ)
  deriving Repr

/-- A declared input: name, number of parts, level, scale (unused, see `Val.scale`), and the Galois index `key` of the
secret it is under: the input decrypts under `σ_key(s)`. `key = 1` (the default) is a ciphertext
under `s`; an already-permuted ciphertext, which is what a key switch after an automorphism
takes (`Instr.keySwitch`), is declared with `key = g`. -/
structure Decl where
  name : Var
  parts : ℕ
  level : ℕ
  scale : ℚ
  key : ℕ := 1
  deriving Repr

/-- Whether an input declaration is well formed: at least one part; a level inside the modulus
chain (`1 ≤ level ≤ L`); and a key that is a Galois index in canonical form (odd, below `2N`;
`step` keeps keys reduced modulo `2N` and compares them by equality). `eval` rejects a program
with any other declaration. -/
def Decl.ok (P : Params) (d : Decl) : Bool :=
  decide (1 ≤ d.parts ∧ 1 ≤ d.level ∧ d.level ≤ P.qs.length ∧ d.key % 2 = 1 ∧ d.key < 2 * P.N)

/-- A straight-line program. Outputs name variables defined by the end of `body`.

`bounds` declares input noise bounds (name, bound): BGV: tighter than `FullParams.inputNoise`; BFV
(`Spec.TraceBFV.inputBound`): used in place of it, and possibly larger. A plaintext input (one
component) declares a bound on the norm of the polynomial its encoder stores (`t − 1` in `[0, t)`,
`⌊t/2⌋` centred: module docstring). The meaning of a program (`eval`) does not depend on `bounds`; a
noise claim assumes the declared bounds of its inputs (`Spec.Trace.BoundsOK`). -/
structure Program where
  inputs : List Decl
  body : List Instr
  outputs : List Var
  bounds : List (Var × ℕ) := []
  deriving Repr

/-- The declared bound of input `x` (first entry for its name), if any. -/
def Program.boundOf (prog : Program) (x : Var) : Option ℕ :=
  (prog.bounds.find? (·.1 = x)).map (·.2)

/-- Environments map variables to values. -/
abbrev Env (P : Params) := Var → Option (Val P)

def Env.set {P : Params} (ρ : Env P) (x : Var) (v : Val P) : Env P :=
  fun y => if y = x then some v else ρ y

namespace Msg
variable {t N : ℕ}

/-- Apply a binary ring operation to two messages. -/
def lift₂ (f : Poly t N → Poly t N → Poly t N) : Msg t N → Msg t N → Option (Msg t N)
  | exact m, exact m' => some (exact (f m m'))

/-- Apply a unary operation. -/
def lift₁ (f : Poly t N → Poly t N) : Msg t N → Msg t N
  | exact m => exact (f m)

end Msg

/-- Whether a message has the shape the scheme expects. -/
def Msg.fits {t N : ℕ} : Kind → Msg t N → Bool
  | .bgv, .exact _ | .bfv, .exact _ => true

/-- Execute one instruction. `none` means the program is ill-formed at this point: an undefined
operand, mismatched level/key/scale, a wrong number of parts, a level outside the modulus chain
(`modSwitch` needs the modulus `q_{ℓ-1}` it drops to exist; `dropLimbs` must leave
at least one limb), a plaintext operand with more than one component, or an op the scheme
lacks.

**`copy`, `toEval` and `toCoeff` have the same meaning**: the destination gets the operand's
value, unchanged. This is deliberate. A `Val` is a message with decryption bookkeeping and says
nothing about representation (coefficient or evaluation form, Montgomery or plain residues, slot
order). A reader who wants "the output is in evaluation form" cannot read it in the source
instruction. The same holds in `Spec.Trace` and the noise analyzers, which give the three the
same contract. -/
def step (P : Params) (ρ : Env P) : Instr → Option (Env P)
  | .add d a b => do
    let x ← ρ a; let y ← ρ b
    guard (x.level = y.level ∧ x.key = y.key)
    let m ← Msg.lift₂ (· + ·) x.msg y.msg
    pure (ρ.set d { x with msg := m, parts := max x.parts y.parts })
  | .sub d a b => do
    let x ← ρ a; let y ← ρ b
    guard (x.level = y.level ∧ x.key = y.key)
    let m ← Msg.lift₂ (· - ·) x.msg y.msg
    pure (ρ.set d { x with msg := m, parts := max x.parts y.parts })
  | .mul d a b => do
    let x ← ρ a; let y ← ρ b
    guard (x.level = y.level ∧ x.key = y.key ∧ 1 ≤ x.parts ∧ 1 ≤ y.parts)
    let m ← Msg.lift₂ (· * ·) x.msg y.msg
    pure (ρ.set d { x with msg := m, parts := x.parts + y.parts - 1, scale := x.scale * y.scale })
  | .square d a => do
    let x ← ρ a
    guard (1 ≤ x.parts)
    let m ← Msg.lift₂ (· * ·) x.msg x.msg
    pure (ρ.set d { x with msg := m, parts := 2 * x.parts - 1, scale := x.scale * x.scale })
  | .mulConst d a c => do
    let x ← ρ a
    pure (ρ.set d { x with msg := x.msg.lift₁ ((c : ZMod P.t) • ·) })
  | .copy d a | .toEval d a | .toCoeff d a => do
    let x ← ρ a
    pure (ρ.set d x)
  | .relin d a => do
    let x ← ρ a
    guard (x.parts = 3 ∧ x.key = 1)
    pure (ρ.set d { x with parts := 2 })
  | .keySwitch d a => do
    let x ← ρ a
    guard (x.parts = 2)
    pure (ρ.set d { x with key := 1 })
  | .automorph d a g => do
    let x ← ρ a
    guard (g % 2 = 1)
    pure (ρ.set d { x with msg := x.msg.lift₁ (automorph g),
                           key := (x.key * g) % (2 * P.N) })
  | .modSwitch d a => do
    let x ← ρ a
    guard (2 ≤ x.level)
    let qLast ← P.qs[x.level - 1]?
    let m := match P.kind with
      | .bgv => x.msg.lift₁ (((qLast : ZMod P.t)⁻¹) • ·)
      | .bfv => x.msg
    pure (ρ.set d { x with msg := m, level := x.level - 1 })
  | .addPlain d a p => do
    let x ← ρ a; let y ← ρ p
    guard (y.parts = 1 ∧ x.level = y.level)
    let m ← Msg.lift₂ (· + ·) x.msg y.msg
    pure (ρ.set d { x with msg := m, parts := max x.parts y.parts })
  | .subPlain d a p => do
    let x ← ρ a; let y ← ρ p
    guard (y.parts = 1 ∧ x.level = y.level)
    let m ← Msg.lift₂ (· - ·) x.msg y.msg
    pure (ρ.set d { x with msg := m, parts := max x.parts y.parts })
  | .mulPlain d a p => do
    let x ← ρ a; let y ← ρ p
    guard (y.parts = 1 ∧ x.level = y.level ∧ 1 ≤ x.parts)
    let m ← Msg.lift₂ (· * ·) x.msg y.msg
    pure (ρ.set d { x with msg := m, scale := x.scale * y.scale })
  | .dropLimbs d a k => do
    let x ← ρ a
    guard (P.kind ≠ .bfv ∧ k < x.level)
    pure (ρ.set d { x with level := x.level - k })

/-- Initial environment: input `i` holds message `msgs i`, with the parts, level, key and scale of
its (first) declaration. Whether the declarations are well formed is checked by `eval`. -/
def initEnv (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) : Env P :=
  fun x => (prog.inputs.find? (·.name = x)).map fun dcl =>
    { msg := msgs x, parts := dcl.parts, level := dcl.level, key := dcl.key, scale := dcl.scale }

/-- Run a program. `none` if it is ill-formed (including an input declaration that is not
`Decl.ok`, an input message of the wrong kind, or a missing output). -/
def eval (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) : Option (Env P) := do
  guard (prog.inputs.all fun dcl => dcl.ok P)
  guard (prog.inputs.all fun dcl => (msgs dcl.name).fits P.kind)
  let ρ ← prog.body.foldlM (step P) (initEnv P prog msgs)
  guard (prog.outputs.all fun o => (ρ o).isSome)
  pure ρ

end Spec.Source
