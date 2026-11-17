/-!
# Spec.IndCpaD — IND-CPA-D and IND-CPA for an exact homomorphic scheme on a declared circuit class   (TRUSTED)

The games of Li and Micciancio (EUROCRYPT 2021) for an *exact* scheme, restricted to a declared
("application-aware", in the sense of Alexandru, Al Badawi, Micciancio and Polyakov) circuit
class, and the reduction from the first to the second. The statements are in
`Challenge.IndCpaD`; the BFV instance is in `Challenge.IndCpaD.Defs`.

**The IND-CPA-D game** (`gameD`) with challenge bit `b`. The game keeps a table of entries
`(m₀, m₁, c, fresh)`. The adversary may ask, in any order and adaptively:
* *encryption* of a pair `(m₀, m₁)`: the game encrypts `m_b` under `pk`, appends a fresh entry
  and returns the ciphertext;
* *evaluation* of a circuit `C` on table indices: if `C` is in the declared class and every
  index names a **fresh** entry, the game runs the public evaluator, appends one entry per output
  (its two messages are what `C` computes on the `m₀`s and on the `m₁`s) and returns the outputs;
  otherwise it returns `none` and changes nothing;
* *decryption* of the entry at an index: the decryption of its ciphertext if its two messages are
  equal, otherwise `none` (Li–Micciancio's oracle for exact schemes).
It ends with the adversary's guess.

**The IND-CPA game** (`gameCPA`): multi-query left-or-right encryption under the same `pk`, which
contains the evaluation keys. The reduction `reduce` turns an IND-CPA-D adversary into an
IND-CPA adversary: its arguments are the public key and the adversary, nothing secret.

**What is modelled and what is not.**
* No running time. The adversary is a well-founded tree of oracle queries (`Adv`: every run is
  finite, the branching is not); its own coins are a parameter of the tree. The IND-CPA
  assumption is to be applied with the coins independent of the secret key and the encryption
  randomness (the statements hold for any joint measure, but only then is the reduction's
  advantage an IND-CPA advantage). The reduction does the adversary's work plus the public evaluator per
  evaluation query; that this is efficient is not stated.
* The games are deterministic functions of `(b, pk, sk, tape)`, where `tape n` is the randomness
  of the `n`-th encryption the game performs. Probability enters only in the statements, through
  an arbitrary measure on the joint randomness.
* Only ciphertexts the oracles produced are in the table: the adversary cannot submit ciphertexts
  of its own to the evaluation or decryption oracle.
* Evaluation only on fresh entries: evaluated ciphertexts cannot be evaluated again. (Since the
  evaluator is deterministic and runs instruction by instruction, evaluating `C₂` on the outputs
  of `C₁` is the same as one query of the concatenated program, when that program is in the
  class; what is excluded is composition beyond what the class certifies.)
* Decryption is the scheme's `dec` (for BFV: textbook decryption, not a library's routine).
* That the scheme is IND-CPA *with the evaluation keys in the public key* (which includes a
  circular-security assumption for the relinearization and rotation keys) is the assumption the
  reduction reduces to; it is not proved anywhere.
* Not the stronger sIND-CPA-D variants (decryption of arbitrary submitted ciphertexts, or of
  entries with different messages, or of evaluations outside the class).
-/

namespace Spec.IndCpaD

/-- An abstract homomorphic scheme with a deterministic public evaluator. `PK` contains the
evaluation keys, so an IND-CPA adversary receives them too. -/
structure HEScheme where
  PK : Type
  SK : Type
  CT : Type
  M : Type
  /-- The randomness of one encryption. -/
  ER : Type
  Circ : Type
  enc : PK → M → ER → CT
  /-- The public evaluator: a deterministic function of the public key, a circuit and the
  input ciphertexts. -/
  eval : PK → Circ → List CT → List CT
  dec : SK → CT → M
  /-- What a circuit computes on messages: the game's message-level semantics. -/
  sem : Circ → List M → List M
  /-- The declared class: decidable and public. -/
  admissible : Circ → Bool
  /-- The keys are within the bounds correctness is proved for. -/
  KeysOK : PK → SK → Prop
  /-- The randomness of one encryption is within the bounds correctness is proved for. -/
  GoodE : PK → SK → ER → Prop

variable (S : HEScheme)

/-- **Perfect correctness on the declared class**, for good keys and good fresh encryptions:
every fresh encryption decrypts to its message, and the decryptions of the evaluator's outputs
on good fresh encryptions of `ms` are `sem C ms`. -/
structure Correct : Prop where
  fresh : ∀ pk sk, S.KeysOK pk sk → ∀ m er, S.GoodE pk sk er → S.dec sk (S.enc pk m er) = m
  eval : ∀ pk sk, S.KeysOK pk sk → ∀ C, S.admissible C = true →
    ∀ ins : List (S.M × S.ER), (∀ p ∈ ins, S.GoodE pk sk p.2) →
      (S.eval pk C (ins.map fun p => S.enc pk p.1 p.2)).map (S.dec sk) =
        S.sem C (ins.map Prod.fst)

/-- A table entry: the two messages, the ciphertext, and whether it is a fresh encryption. -/
structure Entry where
  m0 : S.M
  m1 : S.M
  c : S.CT
  fresh : Bool

/-- An IND-CPA-D adversary: a well-founded tree of oracle queries ending in a guess. -/
inductive Adv (α : Type) where
  | ret (a : α)
  | enc (m0 m1 : S.M) (k : S.CT → Adv α)
  | eval (C : S.Circ) (idx : List Nat) (k : Option (List S.CT) → Adv α)
  | dec (j : Nat) (k : Option S.M → Adv α)

/-- An IND-CPA adversary: left-or-right encryption queries only. -/
inductive CpaAdv (α : Type) where
  | ret (a : α)
  | lr (m0 m1 : S.M) (k : S.CT → CpaAdv α)

variable {S}

/-- The challenge bit selects a message: `x` for `false`, `y` for `true`. -/
def pick {β : Type} (b : Bool) (x y : β) : β := if b then y else x

/-- The fresh entry at index `j`, if there is one. -/
def freshAt (T : List (Entry S)) (j : Nat) : Option (Entry S) :=
  match T[j]? with
  | some e => if e.fresh then some e else none
  | none => none

/-- **The evaluation oracle** (public data only): if `C` is in the declared class and every
index names a fresh entry, the evaluator's outputs and the new (not fresh) entries. -/
def evalStep (pk : S.PK) (T : List (Entry S)) (C : S.Circ) (idx : List Nat) :
    Option (List S.CT × List (Entry S)) :=
  if S.admissible C then
    match idx.mapM (freshAt T) with
    | some es =>
      let outs := S.eval pk C (es.map (·.c))
      let s0 := S.sem C (es.map (·.m0))
      let s1 := S.sem C (es.map (·.m1))
      some (outs, (outs.zip (s0.zip s1)).map fun p => ⟨p.2.1, p.2.2, p.1, false⟩)
    | none => none
  else none

/-- **The IND-CPA game** (multi-query left-or-right) with bit `b`, from the counter `n`. -/
def gameCPA (b : Bool) (pk : S.PK) (tape : Nat → S.ER) : CpaAdv S Bool → Nat → Bool
  | .ret a, _ => a
  | .lr m0 m1 k, n => gameCPA b pk tape (k (S.enc pk (pick b m0 m1) (tape n))) (n + 1)

/-- Every encryption the run of `A` performs, from counter `n`, uses good randomness. -/
def TapeOK (pk : S.PK) (sk : S.SK) (tape : Nat → S.ER) : Adv S Bool → Nat → Prop
  | .ret _, _ => True
  | .enc _ _ k, n => S.GoodE pk sk (tape n) ∧ ∀ c, TapeOK pk sk tape (k c) (n + 1)
  | .eval _ _ k, n => ∀ r, TapeOK pk sk tape (k r) n
  | .dec _ k, n => ∀ r, TapeOK pk sk tape (k r) n

/-- The adversary makes at most `q` encryption queries on every path. -/
inductive Bounded : Adv S Bool → Nat → Prop
  | ret (a q) : Bounded (.ret a) q
  | enc (m0 m1 k q) : (∀ c, Bounded (k c) q) → Bounded (.enc m0 m1 k) (q + 1)
  | eval (C idx k q) : (∀ r, Bounded (k r) q) → Bounded (.eval C idx k) q
  | dec (j k q) : (∀ r, Bounded (k r) q) → Bounded (.dec j k) q

variable [DecidableEq S.M]

/-- **The decryption oracle**: answers only on entries whose two messages are equal. -/
def decAns (sk : S.SK) (T : List (Entry S)) (j : Nat) : Option S.M :=
  match T[j]? with
  | some e => if e.m0 = e.m1 then some (S.dec sk e.c) else none
  | none => none

/-- **The simulated decryption oracle** (the reduction's): the message the table records. -/
def simAns (T : List (Entry S)) (j : Nat) : Option S.M :=
  match T[j]? with
  | some e => if e.m0 = e.m1 then some e.m0 else none
  | none => none

/-- **The IND-CPA-D game** with bit `b`, keys `pk, sk` and encryption randomness `tape`, from
the encryption counter `n` and the table `T` (start: `0`, `[]`). -/
def gameD (b : Bool) (pk : S.PK) (sk : S.SK) (tape : Nat → S.ER) :
    Adv S Bool → Nat → List (Entry S) → Bool
  | .ret a, _, _ => a
  | .enc m0 m1 k, n, T =>
    let c := S.enc pk (pick b m0 m1) (tape n)
    gameD b pk sk tape (k c) (n + 1) (T ++ [⟨m0, m1, c, true⟩])
  | .eval C idx k, n, T =>
    match evalStep pk T C idx with
    | some (outs, new) => gameD b pk sk tape (k (some outs)) n (T ++ new)
    | none => gameD b pk sk tape (k none) n T
  | .dec j k, n, T => gameD b pk sk tape (k (decAns sk T j)) n T

/-- **The reduction**: an IND-CPA adversary from an IND-CPA-D one, given the public key only.
It forwards encryption queries to its own left-or-right oracle, runs the evaluation oracle
itself (`evalStep`: public key and public evaluator), and answers decryption queries from its
table (`simAns`). -/
def reduce (pk : S.PK) : Adv S Bool → List (Entry S) → CpaAdv S Bool
  | .ret a, _ => .ret a
  | .enc m0 m1 k, T => .lr m0 m1 fun c => reduce pk (k c) (T ++ [⟨m0, m1, c, true⟩])
  | .eval C idx k, T =>
    match evalStep pk T C idx with
    | some (outs, new) => reduce pk (k (some outs)) (T ++ new)
    | none => reduce pk (k none) T
  | .dec j k, T => reduce pk (k (simAns T j)) T

/-- The IND-CPA adversary built from an IND-CPA-D adversary `A` with coins `r`: the reduction
from the empty table. -/
def reduction {Coins : Type} (A : Coins → S.PK → Adv S Bool) (r : Coins) (pk : S.PK) :
    CpaAdv S Bool :=
  reduce pk (A r pk) []

end Spec.IndCpaD
