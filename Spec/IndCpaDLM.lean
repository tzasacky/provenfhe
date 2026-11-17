import Spec.IndCpaDProfile

/-!
# Spec.IndCpaDLM — IND-CPA-D with evaluation on earlier results (Li–Micciancio), for program circuits   (TRUSTED)

`Spec.IndCpaD.gameD` lets the adversary evaluate circuits on FRESH encryptions only. This file
states the game of Li and Micciancio (EUROCRYPT 2021, IND-CPA-D for exact schemes) in which
an evaluation query may take ANY earlier table entry, fresh or derived, as input, for an abstract
scheme of `Spec.IndCpaDProfile.AbsScheme` (circuits are programs) with a public evaluator `ev`,
a decryption `dec` and a declared class `adm` of circuits over fresh inputs.

**What matches Li–Micciancio.** The table of entries `(m₀, m₁, c)`; the encryption oracle encrypts
`m_b` and appends a fresh entry; the evaluation oracle runs the public evaluator **on the
ciphertexts of the selected entries** (`ev pk C cs`, whatever entries they are) and appends one
entry per output, whose two messages are what the circuit computes on the selected entries' `m₀`s
and on their `m₁`s; the decryption oracle answers on entries with `m₀ = m₁`; the adversary ends
with a guess.

**What differs.**
* **Admissibility is checked on the inlined program.** Each entry carries a name in one growing
  *global program* `G` over the fresh entries (its provenance): a fresh entry is an input of `G`,
  and a derived entry is a variable of `G`. A query circuit `C` names its entry inputs by the
  entries' names and must define only new names (the adversary renames). The query is answered
  only if the composite program `G.body ++ C.body` (the INLINED program over the fresh inputs,
  `composite`) is in the declared class `adm`, and `C`'s own declarations agree with what `G`
  gives its inputs (`admLM`). The oracle still evaluates `C` alone on the entries' ciphertexts.
* **Declared input bounds are carried.** A query may declare bounds for its inputs
  (`Program.bounds`). The global program keeps, for every inlined query, the declared bounds of
  that query's plaintext constants (`constNames`), which become inputs of the global program
  under names no earlier query used, so the bounds of different queries never concern the same
  name. Bounds a query declares for its ENTRY inputs are not carried: an entry is a fresh input
  of `G` (whose noise is the encryption noise) or an internal variable of `G`, never a declared
  constant. So on a query over fresh entries alone, the inlined program declares exactly the
  bounds the query declares for its constants.
* **The whole history is inlined**, not only the provenance of the selected entries: `G`
  contains every earlier query, so whether a query is answered may in principle depend on earlier
  queries it does not use. (For a query on fresh entries alone and the certificate classes at
  a constant budget it does not: `Challenge.IndCpaD.LMAgree`. For queries on derived entries
  this is not claimed.)
* **Names.** Queries name their entry inputs by the entries' global names and use new names for
  everything they define.
* Encryption queries name the new entry; a name already used in `G` gives an entry that cannot
  be evaluated on (it can still be decrypted). The encryption itself is the same in either case.
* Decryption is the scheme's `dec` (textbook decryption for the instances); the evaluation keys
  are in the public key; no running time; ciphertexts not produced by the oracles cannot be
  submitted (no sIND-CPA-D).

`Reach` is the set of global programs the game can reach: built from the empty one by naming
fresh entries and by inlining accepted queries.
-/

namespace Spec.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile

variable (D : AbsScheme)

/-- Messages. -/
abbrev M : Type := Poly D.P.src.t D.P.src.N
/-- Ciphertexts: level and components. -/
abbrev CT : Type := ℕ × List (IntPoly D.P.src.N)
/-- A query circuit: its program, the names of its entry inputs in the order of the queried
indices, and its plaintext constants. -/
abbrev QCirc : Type := Program × List Var × (Var → M D)

/-- **The global program** (the provenance of every entry): its inputs (fresh entries and the
constants of the queries), its body (the queried bodies, in order), the names of the fresh
inputs in encryption order, the constants, and the declared bounds of the constants. -/
structure Global where
  inputs : List Decl
  body : List Instr
  fresh : List Var
  pt : Var → M D
  bounds : List (Var × ℕ)

variable {D}

/-- The global program as a program (no outputs; the carried bounds). -/
def Global.prog (G : Global D) : Program := ⟨G.inputs, G.body, [], G.bounds⟩

/-- The names the global program uses. -/
def Global.names (G : Global D) : List Var := G.inputs.map (·.name) ++ G.body.map Trace.dst

variable (D) in
/-- The empty global program. -/
def Global.empty : Global D := ⟨[], [], [], fun _ => 0, []⟩

variable (D) in
/-- The declaration of a fresh entry: two components under `s` at the encryption level. -/
def freshDecl (x : Var) : Decl := { name := x, parts := 2, level := D.lvl, scale := 0, key := 1 }

/-- A fresh entry named `x` becomes an input of the global program, unless the name is used. -/
def Global.link (G : Global D) (x : Var) : Global D :=
  if x ∈ G.names then G else { G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] }

/-- The constants of a query: its declared inputs that are not entry inputs. -/
def constNames (C : QCirc D) : List Var := (C.1.inputs.map (·.name)).filter (· ∉ C.2.1)

/-- The global program after the query `C`: its constants become inputs with their declared
bounds, its body is appended. -/
def Global.extend (G : Global D) (C : QCirc D) : Global D :=
  { inputs := G.inputs ++ C.1.inputs.filter (·.name ∉ C.2.1)
    body := G.body ++ C.1.body
    fresh := G.fresh
    pt := fun x => if x ∈ constNames C then C.2.2 x else G.pt x
    bounds := G.bounds ++ C.1.bounds.filter (·.1 ∈ constNames C) }

/-- **The inlined program** of the query `C` over the fresh inputs, with `C`'s outputs. -/
def composite (G : Global D) (C : QCirc D) : Program :=
  { (G.extend C).prog with outputs := C.1.outputs }

/-- The global program replayed on zero messages (public metadata of every variable). -/
def Global.replay (G : Global D) : Option (Env D.P.src) :=
  G.body.foldlM (step D.P.src) (initEnv D.P.src G.prog fun _ => .exact 0)

/-- `C`'s declaration of an entry input agrees with what the global program gives it. -/
def metaOK (ρ : Env D.P.src) (d : Decl) : Bool :=
  (ρ d.name).elim false fun v =>
    v.parts == d.parts && v.level == d.level && v.key == d.key && v.scale == d.scale

variable (mk : Program → List Var → (Var → M D) → D.Circ) (adm : D.Circ → Bool)

/-- **Admissibility of a query** on entries with names and link flags `en` (module docstring):
the entry inputs are the selected entries, all linked; the query's constants and destinations
are new names; the query runs on zero messages alone and so does the inlined program; the query's
declarations of its entry inputs agree with the global program; and `adm` accepts the inlined
program. -/
def admLM (G : Global D) (C : QCirc D) (en : List (Var × Bool)) : Bool :=
  decide (C.2.1 = en.map (·.1)) && en.all (·.2) &&
  (constNames C ++ C.1.body.map Trace.dst).all (fun x => decide (x ∉ G.names)) &&
  (Source.eval D.P.src C.1 fun _ => .exact 0).isSome &&
  G.replay.elim false (fun ρ => C.1.inputs.all fun d => decide (d.name ∉ C.2.1) || metaOK ρ d) &&
  (Source.eval D.P.src (composite G C) fun _ => .exact 0).isSome &&
  adm (mk (composite G C) G.fresh (G.extend C).pt)

/-- **The reachable global programs**: from the empty one, by naming a fresh entry and by
inlining a query the oracle accepts. -/
inductive Reach : Global D → Prop
  | empty : Reach (Global.empty D)
  | link (G : Global D) (x : Var) : Reach G → Reach (G.link x)
  | extend (G : Global D) (C : QCirc D) (en : List (Var × Bool)) :
      Reach G → admLM mk adm G C en = true → Reach (G.extend C)

/-- A table entry: the two messages, the ciphertext, the name, and whether it is in the global
program. -/
structure LEntry (D : AbsScheme) where
  m0 : M D
  m1 : M D
  c : CT D
  name : Var
  linked : Bool

variable (ev : D.PK → D.Circ → List (CT D) → List (CT D))

/-- **The evaluation oracle on any entries** (module docstring): the evaluator runs on the
selected entries' ciphertexts; the new entries are named by the query's outputs. -/
def evalLM (pk : D.PK) (T : List (LEntry D)) (G : Global D) (C : QCirc D) (idx : List Nat) :
    Option (List (CT D) × List (LEntry D) × Global D) :=
  match idx.mapM (fun j => T[j]?) with
  | some es =>
    if admLM mk adm G C (es.map fun e => (e.name, e.linked)) then
      let outs := ev pk (mk C.1 C.2.1 C.2.2) (es.map (·.c))
      let s0 := D.sem (mk C.1 C.2.1 C.2.2) (es.map (·.m0))
      let s1 := D.sem (mk C.1 C.2.1 C.2.2) (es.map (·.m1))
      some (outs, (outs.zip (C.1.outputs.zip (s0.zip s1))).map
        (fun p => ⟨p.2.2.1, p.2.2.2, p.1, p.2.1, true⟩), G.extend C)
    else none
  | none => none

/-- An adversary: encryption queries name the new entry. -/
inductive LAdv (D : AbsScheme) (α : Type) where
  | ret (a : α)
  | enc (m0 m1 : M D) (x : Var) (k : CT D → LAdv D α)
  | eval (C : QCirc D) (idx : List Nat) (k : Option (List (CT D)) → LAdv D α)
  | dec (j : Nat) (k : Option (M D) → LAdv D α)

variable (dec : D.SK → CT D → M D)

variable (D) in
/-- The scheme of the fresh-only game with the same encryption, evaluator, decryption and class
(the IND-CPA game is played against it). -/
abbrev freshScheme : HEScheme where
  PK := D.PK
  SK := D.SK
  CT := CT D
  M := M D
  ER := D.ER
  Circ := D.Circ
  enc := D.enc
  eval := fun pk C cs => if cs.length = (D.fresh C).length then ev pk C cs else []
  dec := dec
  sem := D.sem
  admissible := adm
  KeysOK := D.KeysOK
  GoodE := D.GoodE

/-- Every encryption the run of `A` performs, from counter `n`, uses good randomness. -/
def TapeOKLM (pk : D.PK) (sk : D.SK) (tape : Nat → D.ER) : LAdv D Bool → Nat → Prop
  | .ret _, _ => True
  | .enc _ _ _ k, n => D.GoodE pk sk (tape n) ∧ ∀ c, TapeOKLM pk sk tape (k c) (n + 1)
  | .eval _ _ k, n => ∀ r, TapeOKLM pk sk tape (k r) n
  | .dec _ k, n => ∀ r, TapeOKLM pk sk tape (k r) n

/-- At most `q` encryption queries on every path. -/
inductive BoundedLM : LAdv D Bool → Nat → Prop
  | ret (a q) : BoundedLM (.ret a) q
  | enc (m0 m1 x k q) : (∀ c, BoundedLM (k c) q) → BoundedLM (.enc m0 m1 x k) (q + 1)
  | eval (C idx k q) : (∀ r, BoundedLM (k r) q) → BoundedLM (.eval C idx k) q
  | dec (j k q) : (∀ r, BoundedLM (k r) q) → BoundedLM (.dec j k) q

variable [DecidableEq (M D)]

/-- The decryption oracle: on entries with equal messages. -/
def decAnsLM (sk : D.SK) (T : List (LEntry D)) (j : Nat) : Option (M D) :=
  (T[j]?).elim none fun e => if e.m0 = e.m1 then some (dec sk e.c) else none

/-- The simulated decryption oracle: the recorded message. -/
def simAnsLM (T : List (LEntry D)) (j : Nat) : Option (M D) :=
  (T[j]?).elim none fun e => if e.m0 = e.m1 then some e.m0 else none

/-- **The IND-CPA-D game with evaluation on earlier results** (module docstring), from the
counter `n`, the table `T` and the global program `G` (start: `0`, `[]`, `Global.empty D`). -/
def gameLM (b : Bool) (pk : D.PK) (sk : D.SK) (tape : Nat → D.ER) :
    LAdv D Bool → Nat → List (LEntry D) → Global D → Bool
  | .ret a, _, _, _ => a
  | .enc m0 m1 x k, n, T, G =>
    let c := D.enc pk (pick b m0 m1) (tape n)
    gameLM b pk sk tape (k c) (n + 1) (T ++ [⟨m0, m1, c, x, decide (x ∉ G.names)⟩]) (G.link x)
  | .eval C idx k, n, T, G =>
    match evalLM mk adm ev pk T G C idx with
    | some (outs, new, G') => gameLM b pk sk tape (k (some outs)) n (T ++ new) G'
    | none => gameLM b pk sk tape (k none) n T G
  | .dec j k, n, T, G => gameLM b pk sk tape (k (decAnsLM dec sk T j)) n T G

/-- **The reduction**: public key and adversary only; it runs the evaluation oracle itself and
answers decryption queries from the table. -/
def reduceLM (pk : D.PK) :
    LAdv D Bool → List (LEntry D) → Global D → CpaAdv (freshScheme D adm ev dec) Bool
  | .ret a, _, _ => .ret a
  | .enc m0 m1 x k, T, G => .lr m0 m1 fun c =>
    reduceLM pk (k c) (T ++ [⟨m0, m1, c, x, decide (x ∉ G.names)⟩]) (G.link x)
  | .eval C idx k, T, G =>
    match evalLM mk adm ev pk T G C idx with
    | some (outs, new, G') => reduceLM pk (k (some outs)) (T ++ new) G'
    | none => reduceLM pk (k none) T G
  | .dec j k, T, G => reduceLM pk (k (simAnsLM T j)) T G

/-- The IND-CPA adversary from `A` with coins `r`. -/
def reductionLM {Coins : Type} (A : Coins → D.PK → LAdv D Bool) (r : Coins) (pk : D.PK) :
    CpaAdv (freshScheme D adm ev dec) Bool :=
  reduceLM mk adm ev dec pk (A r pk) [] (Global.empty D)

end Spec.IndCpaDLM
