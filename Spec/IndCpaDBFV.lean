import Spec.IndCpaD
import Spec.CertifyBFV
import Spec.EncryptBFV
import Spec.TraceBFV
import Spec.Float
import Spec.Budget

/-!
# Spec.IndCpaDBFV — the BFV scheme of the IND-CPA-D game: data, encryption, decryption, keys   (TRUSTED)

The parts of the BFV instance of `Spec.IndCpaD.HEScheme` that do not need a locked function: the
setting, circuits, keys, ciphertexts, OpenFHE's encryption at the top level, textbook decryption,
what a circuit computes, and the input filling. The evaluator (`runLibrary`), the class
(`certifyBFVFresh?` plus `Circ.extraOK`) and the assembled scheme are in
`Challenge.IndCpaD.Defs`, whose docstring describes the whole instance.
-/

namespace Spec.IndCpaDBFV
open Spec NPoly Scheme Source Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV

/-- The fixed scheme: parameters, layout, technique, plaintext-addition method and modulus
switch of `base` (its program and drops are not used), the sampler support bounds of the key
error (`Bk`) and of the encryption randomness (`Bu`, `B1`, `B2`), the platform's binary64
arithmetic, and the Galois indices whose rotation keys the public key carries. -/
structure Setting where
  base : InputBFV
  Bk : ℕ
  Bu : ℕ
  B1 : ℕ
  B2 : ℕ
  A : Spec.Float.Arith
  rots : List ℕ

variable (St : Setting)

/-- The number of limbs at the top level: the oracle encrypts there. -/
def top : ℕ := St.base.P.src.qs.length

/-- The modulus at the top level. -/
def Qtop : ℕ := St.base.P.src.modulus (top St)

/-- A circuit: a program with its declared drops, the ciphertext inputs in the order the
oracle's indices fill them, and the plaintext operands (public constants), stored as `liftMsg`. -/
structure Circ where
  prog : Program
  drops : List ℕ
  fresh : List Var
  pt : Var → Poly St.base.P.src.t St.base.P.src.N

variable {St}

/-- The circuit as an input of the certificate and of the evaluator. -/
def Circ.input (C : Circ St) : InputBFV := { St.base with prog := C.prog, drops := C.drops }

/-- Every key switch, in the message-independent replay of `body` from `ρ` (`Source.step`, as
`runLibraryAux` does it), uses a Galois index in `rots`. -/
def ksKeysIn (P : Source.Params) (rots : List ℕ) : List Instr → Env P → Bool
  | [], _ => true
  | i :: is, ρ =>
    match step P ρ i with
    | some ρ' =>
      (match i with
        | .keySwitch _ a => rots.contains (((ρ a).map (·.key)).getD 1)
        | _ => true) && ksKeysIn P rots is ρ'
    | none => true

/-- The checks of the class that the certificate does not make (module docstring). -/
def Circ.extraOK (C : Circ St) : Bool :=
  (C.prog.inputs.all fun d =>
    if d.name ∈ C.fresh then d.level == top St
    else match C.prog.boundOf d.name with
      | some b => decide (St.base.P.src.t - 1 ≤ b)
      | none => true) &&
  ksKeysIn St.base.P.src St.rots C.prog.body (initEnv St.base.P.src C.prog fun _ => .exact 0)

/-- The public key: encryption key `(b, a)`, relinearization keys, rotation keys per index. -/
structure PK where
  b : IntPoly St.base.P.src.N
  a : IntPoly St.base.P.src.N
  rk : List (IntPoly St.base.P.src.N × IntPoly St.base.P.src.N)
  gk : ℕ → List (IntPoly St.base.P.src.N × IntPoly St.base.P.src.N)

/-- The secret state of key generation: the secret and the public key's error. -/
structure SK where
  s : IntPoly St.base.P.src.N
  e : IntPoly St.base.P.src.N

/-- A ciphertext with its level (the library's ciphertext object carries it). -/
abbrev CT := ℕ × List (IntPoly St.base.P.src.N)

/-- The randomness `(u, e₁, e₂)` of one encryption. -/
abbrev ER := IntPoly St.base.P.src.N × IntPoly St.base.P.src.N × IntPoly St.base.P.src.N

def enc (pk : PK (St := St)) (m : Poly St.base.P.src.t St.base.P.src.N) (r : ER (St := St)) :
    CT (St := St) :=
  (top St, encryptBFV St.base.P.src.t (Qtop St) pk.b pk.a (liftMsg m) r.1 r.2.1 r.2.2)

/-- The message of input `x`: the `i`-th message if `x` is the `i`-th fresh name, otherwise
the circuit's constant. -/
def Circ.msg (C : Circ St) (ms : List (Poly St.base.P.src.t St.base.P.src.N)) (x : Var) :
    Poly St.base.P.src.t St.base.P.src.N :=
  match C.fresh.idxOf? x with
  | some i => ms[i]?.getD 0
  | none => C.pt x

/-- The ciphertext of input `x`, in the same way. -/
def Circ.cts (C : Circ St) (cs : List (CT (St := St))) (x : Var) : List (IntPoly St.base.P.src.N) :=
  match C.fresh.idxOf? x with
  | some i => (cs[i]?.map (·.2)).getD []
  | none => [liftMsg (C.pt x)]

/-- The level of output `o` (message independent: replayed on zero messages). -/
def Circ.outLevel (C : Circ St) (o : Var) : ℕ :=
  ((Source.eval St.base.P.src C.prog (fun _ => .exact 0) >>= fun ρ => ρ o).map (·.level)).getD 0

/-- Textbook BFV decryption at the ciphertext's level. -/
def dec (sk : SK (St := St)) (c : CT (St := St)) : Poly St.base.P.src.t St.base.P.src.N :=
  bfvDecrypt St.base.P.src.t sk.s (c.2.map (ofInt (St.base.P.src.modulus c.1)))

/-- What the program computes (`Source.eval`), the outputs in order. -/
def sem (C : Circ St) (ms : List (Poly St.base.P.src.t St.base.P.src.N)) :
    List (Poly St.base.P.src.t St.base.P.src.N) :=
  if ms.length = C.fresh.length then
    match Source.eval St.base.P.src C.prog (fun x => .exact (C.msg ms x)) with
    | some ρ => C.prog.outputs.map fun o =>
        match ρ o with
        | some v => match v.msg with | .exact m => m
        | none => 0
    | none => []
  else []

/-- Good keys (module docstring). -/
def KeysOK (pk : PK (St := St)) (sk : SK (St := St)) : Prop :=
  SecretOK St.base.P.secretBound sk.s ∧ normInf sk.e ≤ St.Bk ∧
  PublicKeyOK 1 (Qtop St) sk.s sk.e pk.b pk.a ∧
  Budget.GadgetKeysOK St.base.P St.base.lay (top St) .square sk.s pk.rk ∧
  ∀ g ∈ St.rots, ∀ s', automorph g s' = sk.s →
    Budget.GadgetKeysOK St.base.P St.base.lay (top St) (.galois g) s' (pk.gk g)

/-- Good encryption randomness (module docstring). -/
def GoodE (_ : PK (St := St)) (_ : SK (St := St)) (r : ER (St := St)) : Prop :=
  normInf r.1 ≤ St.Bu ∧ normInf r.2.1 ≤ St.B1 ∧ normInf r.2.2 ≤ St.B2

/-- Equality of messages is decided coefficient by coefficient (the decryption oracle compares
the two messages of an entry). Scoped: active only where `Spec.IndCpaDBFV` is opened (the
IND-CPA-D statements and proofs), not for any other statement of the project. -/
scoped instance polyDecEq (q n : ℕ) : DecidableEq (Poly q n) := fun x y =>
  decidable_of_iff (x.coeff = y.coeff)
    ⟨fun h => by cases x; cases y; cases h; rfl, fun h => h ▸ rfl⟩

end Spec.IndCpaDBFV
