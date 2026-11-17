import Spec.IndCpaD
import Spec.TraceBFV
import Spec.Trace
import Spec.Correct
import Spec.Encrypt

/-!
# Spec.IndCpaDProfile — an abstract RNS BGV/BFV scheme for the IND-CPA-D game on a profile class   (TRUSTED)

The data of a homomorphic scheme of the RNS BGV/BFV family with NO library in it: the parameters,
an abstract encryption algorithm with abstract keys and randomness, an abstract type of circuits
with public accessors, and the generic message-level and decryption-level parts the game needs.
The class of circuits (through a profile certificate, `Challenge.Profile.certifyBFVProfile?` or
`certifyProfile?`), the assembled `Spec.IndCpaD.HEScheme` and the hypotheses on the evaluator
are in `Challenge.IndCpaD.Profile` (BFV) and `Challenge.IndCpaD.ProfileBGV` (BGV).

* **Ciphertexts** are pairs `(ℓ, c)`: a level `ℓ` (the modulus `q₀⋯q_{ℓ-1}`) and the integer
  representatives `c` of the components.
* **Encryption** `enc pk m r` is arbitrary; what the statements assume of it is `EncOKBFV`
  (resp. `EncOKBGV`): for good keys and good randomness, the ciphertext is at the declared level
  `lvl`, has two components, and encrypts `m` under the secret `sec sk` with noise at most `eps`
  in the scheme's sense (`BFVEncrypts`: phase `⌊Q/t⌋·m + e` with `‖e‖∞ ≤ eps`; `BGVEncrypts`:
  centred phase `m + t·e` of norm at most `eps`). Both relations include that the ciphertext
  decrypts to `m`, so fresh correctness is part of the hypothesis and no separate decryption
  check is needed.
* **Circuits** are an abstract type with three public accessors: the program `prog C`, the names
  of its fresh ciphertext inputs in the order the oracle's indices fill them (`fresh C`), and the
  plaintext operands `pt C` (public constants, stored as `liftMsg`, the representative in
  `[0, t)`).
* **Decryption** is textbook decryption at the ciphertext's level with the secret `sec sk`
  (`decBFV`, `decBGV`); **what a circuit computes** (`sem`) is `Source.eval` of its program on
  the messages and the constants, which for BGV includes the factors `q⁻¹ mod t` of its modulus
  switches: it is exactly what textbook decryption of a correct output returns.
* `inputsFit`: the shape of the inputs that the class requires: the fresh inputs are declared as
  two-component ciphertexts under `s` at the level `lvl` with no bound of their own (their noise
  is `eps`), and every other input is a one-component plaintext operand whose declared bound, if
  any, is at least `t − 1`, at a level where `t − 1 ≤ Q/2`.

Nothing here names a library, a key-switching technique, a multiplication algorithm or a
floating-point model.
-/

namespace Spec.IndCpaDProfile
open Spec NPoly Scheme Source Spec.Encrypt

/-- **An abstract RNS BGV/BFV scheme** (module docstring). `P.inputNoise` is not read: the input
noise of the fresh ciphertexts is `eps`. -/
structure AbsScheme where
  P : FullParams
  /-- The noise bound of a fresh encryption (in the sense of `Spec.Correct.Encrypts`). -/
  eps : ℕ
  /-- The level at which the encryption oracle encrypts. -/
  lvl : ℕ
  PK : Type
  SK : Type
  /-- The randomness of one encryption. -/
  ER : Type
  Circ : Type
  /-- The secret polynomial of a secret key. -/
  sec : SK → IntPoly P.src.N
  enc : PK → Poly P.src.t P.src.N → ER → ℕ × List (IntPoly P.src.N)
  KeysOK : PK → SK → Prop
  GoodE : PK → SK → ER → Prop
  prog : Circ → Program
  fresh : Circ → List Var
  pt : Circ → Var → Poly P.src.t P.src.N

variable (D : AbsScheme)

/-- The parameters at which circuits are analysed: input noise `eps`. -/
abbrev AbsScheme.Pe : FullParams := { D.P with inputNoise := D.eps }

/-- The message of input `x`: the `i`-th message if `x` is the `i`-th fresh name, otherwise the
circuit's constant. -/
def AbsScheme.msg (C : D.Circ) (ms : List (Poly D.P.src.t D.P.src.N)) (x : Var) :
    Poly D.P.src.t D.P.src.N :=
  match (D.fresh C).idxOf? x with
  | some i => ms[i]?.getD 0
  | none => D.pt C x

/-- The ciphertext of input `x`, in the same way (a constant is stored as `liftMsg`). -/
def AbsScheme.cts (C : D.Circ) (cs : List (ℕ × List (IntPoly D.P.src.N))) (x : Var) :
    List (IntPoly D.P.src.N) :=
  match (D.fresh C).idxOf? x with
  | some i => (cs[i]?.map (·.2)).getD []
  | none => [liftMsg (D.pt C x)]

/-- The level of output `o` (message independent: replayed on zero messages). -/
def AbsScheme.outLevel (C : D.Circ) (o : Var) : ℕ :=
  ((Source.eval D.P.src (D.prog C) (fun _ => .exact 0) >>= fun ρ => ρ o).map (·.level)).getD 0

/-- Textbook BFV decryption at the ciphertext's level. -/
def AbsScheme.decBFV (sk : D.SK) (c : ℕ × List (IntPoly D.P.src.N)) : Poly D.P.src.t D.P.src.N :=
  bfvDecrypt D.P.src.t (D.sec sk) (c.2.map (ofInt (D.P.src.modulus c.1)))

/-- Textbook BGV decryption at the ciphertext's level. -/
def AbsScheme.decBGV (sk : D.SK) (c : ℕ × List (IntPoly D.P.src.N)) : Poly D.P.src.t D.P.src.N :=
  bgvDecrypt D.P.src.t (D.sec sk) (c.2.map (ofInt (D.P.src.modulus c.1)))

/-- What the program computes (`Source.eval`), the outputs in order. -/
def AbsScheme.sem (C : D.Circ) (ms : List (Poly D.P.src.t D.P.src.N)) :
    List (Poly D.P.src.t D.P.src.N) :=
  if ms.length = (D.fresh C).length then
    match Source.eval D.P.src (D.prog C) (fun x => .exact (D.msg C ms x)) with
    | some ρ => (D.prog C).outputs.map fun o =>
        match ρ o with
        | some v => match v.msg with | .exact m => m
        | none => 0
    | none => []
  else []

/-- **The encryption hypothesis, BFV** (module docstring): for good keys and good randomness, the
ciphertext is at level `lvl`, has two components, and is a BFV encryption of the message under
`sec sk` with noise at most `eps` (`BFVEncrypts`, which includes that it decrypts). -/
def AbsScheme.EncOKBFV : Prop :=
  ∀ pk sk, D.KeysOK pk sk → ∀ m r, D.GoodE pk sk r →
    (D.enc pk m r).1 = D.lvl ∧ (D.enc pk m r).2.length = 2 ∧
      BFVEncrypts D.P.src.t D.eps (D.sec sk)
        ((D.enc pk m r).2.map (ofInt (D.P.src.modulus D.lvl))) m

/-- **The encryption hypothesis, BGV**: as `EncOKBFV` with `BGVEncrypts` (the centred phase
`m + t·e` has norm at most `eps`, and the ciphertext decrypts to `m`). -/
def AbsScheme.EncOKBGV : Prop :=
  ∀ pk sk, D.KeysOK pk sk → ∀ m r, D.GoodE pk sk r →
    (D.enc pk m r).1 = D.lvl ∧ (D.enc pk m r).2.length = 2 ∧
      BGVEncrypts D.P.src.t D.eps (D.sec sk)
        ((D.enc pk m r).2.map (ofInt (D.P.src.modulus D.lvl))) m

/-- **The input shape the class requires** (module docstring). -/
def AbsScheme.inputsFit (C : D.Circ) : Bool :=
  (D.prog C).inputs.all fun d =>
    if d.name ∈ D.fresh C then
      d.parts == 2 && d.key == 1 && d.level == D.lvl && ((D.prog C).boundOf d.name).isNone
    else
      d.parts == 1 && decide (D.P.src.t - 1 ≤ D.P.src.modulus d.level / 2) &&
        match (D.prog C).boundOf d.name with
        | some b => decide (D.P.src.t - 1 ≤ b)
        | none => true

end Spec.IndCpaDProfile
