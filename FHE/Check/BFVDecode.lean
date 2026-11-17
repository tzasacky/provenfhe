import FHE.Check.Decode

/-!
# FHE.Check.BFVDecode — the BFV part of `fhe-check/v1`   (UNTRUSTED glue)

A BFV input file (`params.scheme = "BFV"`) has the same parameters, key-switching section and
program as a BGV one, plus a top-level object `bfv` that says how the library multiplies and how
it adds plaintexts. This file decodes it by

1. handing the document to the BGV decoder `FHE.Check.decode` (so that field access, number
   limits, duplicate-name refusal, digit layouts, `expect` annotations and provenance are the one
   implementation both schemes share), with `params.scheme` rewritten for that call only, and
   setting `kind := .bfv` in the parameters it returns;
2. refusing what BFV does not have (`dropLimbs`, the BGV decryption that switches to one limb);
3. decoding `$.bfv`.

As in `FHE.Check.Decode`, nothing here is read as a fact: the multiplication technique, the
auxiliary basis, the plaintext-addition method and the numbers `inputNoise`, `keyNoise`,
`secretBound`, `internalDrops` are declared ASSUMPTIONS that the report prints.

**`bfv.multiplication.internalDrops`** (`HPSPOVERQLEVELED`): an array of naturals, one per
instruction of `program.body`, in order: the number of limbs the library drops internally at that
instruction (inside `EvalMult`, `EvalSquare`, `RelinearizeCore`; `0` at every other instruction).
It becomes `Spec.CertifyBFV.InputBFV.drops`. `resolveDrops`:

* `HPSPOVERQLEVELED`: REQUIRED if the program has a `mul`, `square`, `relin` or `keySwitch`
  (INVALID INPUT if it is missing or does not have exactly one entry per instruction, or if an
  entry is nonzero at an instruction of another kind); a program with none of these may omit it
  (all zero).
* any other technique: absent or all zero (INVALID INPUT otherwise: only `HPSPOVERQLEVELED` drops
  limbs internally).
* `maxInternalDrop`, `maxInternalDropKS` (the two summary numbers older files carried instead)
  are still accepted, as a CROSS-CHECK only: if present, `maxInternalDrop` must be at least every
  entry at a `mul`, `square` or `relin`, and `maxInternalDropKS` at least every entry at a
  `keySwitch` (INVALID INPUT otherwise). They do not enter the budget.

The checker cannot tell from the file whether a declared drop is the one the library performs: an
UNDERSTATED drop (0 where the library drops 1) gives a smaller budget. The drops are an input
ASSUMPTION; the OpenFHE extractor establishes them by a three-way consistency check (the drop
the library recorded at run time, the `FindLevelsToDrop` table it dumped, a Python replica).

**Meaning of the BFV fields** (the checker's reading of them is in `FHE.Check.BFVBudget`):

* `params.inputNoise`: every input ciphertext's BFV noise `e = [phase − ⌊Q/t⌋·m]_Q` has
  `‖e‖∞ ≤ inputNoise` (no lower bound, unlike BGV). `params.keyNoise`: bound on the errors of
  the key-switching keys (not required to be multiples of `t`).
* `program.inputs[].bound`: for a ciphertext input (parts ≠ 1) its noise bound, used INSTEAD of
  `inputNoise` whether smaller or larger; for a plaintext input (parts = 1) the bound on
  `‖p‖∞`, used instead of `t − 1` (`Spec.TraceBFV.inputBound`).
* `negate` is `mulConst` by `−1` (as for BGV: `FHE.Check.decodeInstr`).
-/

namespace FHE.Check.BFV
open Lean Spec Spec.Source

/-- The multiplication techniques the format names. -/
inductive Technique
  /-- Fan–Vercauteren: centred lift, integer tensor product, exact rounding of `t·c/Q`. -/
  | textbook
  /-- Halevi–Polyakov–Shoup (OpenFHE `HPS`). -/
  | hps
  /-- OpenFHE `HPSPOVERQ`. -/
  | hpsPOverQ
  /-- OpenFHE `HPSPOVERQLEVELED`. -/
  | hpsPOverQLeveled
  /-- Bajard–Eynard–Hasan–Zucca (OpenFHE `BEHZ`). -/
  | behz
  deriving BEq, Repr

def Technique.name : Technique → String
  | .textbook => "textbook" | .hps => "HPS" | .hpsPOverQ => "HPSPOVERQ"
  | .hpsPOverQLeveled => "HPSPOVERQLEVELED" | .behz => "BEHZ"

def Technique.all : List Technique := [.textbook, .hps, .hpsPOverQ, .hpsPOverQLeveled, .behz]

def Technique.ofString? (s : String) : Option Technique := Technique.all.find? (·.name == s)

/-- `$.bfv.multiplication`: which multiplication the library runs. An ASSUMPTION. -/
structure MulConfig where
  technique : Technique
  /-- HPS: the auxiliary primes `P`; the P-over-Q variants: `P_l`; BEHZ: the base `B`. -/
  auxBasis : List Nat := []
  /-- BEHZ only. -/
  mSk : Option Nat := none
  /-- BEHZ only. -/
  mTilde : Option Nat := none
  /-- `HPSPOVERQLEVELED` only: for each instruction of the body, the number of limbs the library
  drops internally at it. An ASSUMPTION. -/
  internalDrops : Option (List Nat) := none
  /-- Cross-check only: an upper bound of `internalDrops` over `mul`, `square`, `relin`. -/
  maxInternalDrop : Option Nat := none
  /-- Cross-check only: an upper bound of `internalDrops` over `keySwitch`. -/
  maxInternalDropKS : Option Nat := none
  /-- The budget allows each float-assisted conversion to be off by one unit. -/
  floatTolerant : Bool := true
  source : String := ""
  deriving Repr

/-- `$.bfv.plainAdd.method`. -/
inductive PlainAddMethod
  /-- The library adds `⌊Q/t⌋·p` exactly (deviation 0). -/
  | delta
  /-- The library adds `⌊Q·p/t⌉` (deviation at most `Spec.BudgetBFV.plainAddRounded`). -/
  | rounded
  /-- The library adds some polynomial within one unit of `Q·p/t`, coefficient by coefficient
  (rounding up, down or to nearest; deviation at most `Spec.BudgetBFV.plainAddScaled`). `how` is
  the name the file used: `ceil`, `floor` or `scaled`. -/
  | scaled (how : String)
  deriving BEq, Repr

def PlainAddMethod.name : PlainAddMethod → String
  | .delta => "delta" | .rounded => "rounded" | .scaled how => how

structure PlainAddConfig where
  method : PlainAddMethod
  source : String := ""
  deriving Repr

/-- A decoded BFV input file: the shared part (`base`, with `base.P.src.kind = .bfv`) and
`$.bfv`. -/
structure Input where
  base : FHE.Check.Input
  mul : Option MulConfig := none
  plainAdd : Option PlainAddConfig := none
  /-- The internal drops as `Challenge.CertifyBFV.certifyBFV?` reads them (`resolveDrops`): one
  per instruction under `HPSPOVERQLEVELED`, `[]` otherwise. -/
  drops : List Nat := []
  /-- `$.bfv.encryption`: printed, never read. -/
  encryption : Json := Json.null

inductive Decoded
  | ok (inp : Input)
  | unsupported (what : String) (idx : Option Nat) (why : String)

/-- Whether the document declares `params.scheme = "BFV"` (the dispatch of `fhe_check`). -/
def isBFV (j : Json) : Bool :=
  match j.getObjVal? "params" with
  | .ok p => (match p.getObjVal? "scheme" with
    | .ok (.str s) => s == "BFV"
    | _ => false)
  | .error _ => false

def optStr (j : Json) (k : String) : String :=
  match j.getObjValAs? String k with
  | .ok s => s
  | .error _ => ""

def asBool (ctx : String) (j : Json) : DecodeM Bool :=
  match j with
  | .bool b => pure b
  | _ => throw s!"{ctx}: expected true or false"

def asObj (ctx : String) (j : Json) : DecodeM Json :=
  match j with
  | .obj _ => pure j
  | _ => throw s!"{ctx}: expected an object"

/-- Decode `$.bfv.multiplication`. An unknown technique name is `.error (.inr name)`. -/
def decodeMul (j : Json) : DecodeM (Except String MulConfig) := do
  let ctx := "$.bfv.multiplication"
  let _ ← asObj ctx j
  onlyKeys ctx j ["technique", "source", "auxBasis", "auxBasisRule", "mSk", "mTilde", "gamma", "floatTolerant",
    "internalDrops", "maxInternalDrop", "maxInternalDropKS", "mulLimbs"]
  let tn ← strField ctx j "technique"
  let some technique := Technique.ofString? tn | return .error tn
  let auxBasis ← match field? j "auxBasis" with
    | some v => (← asArr s!"{ctx}.auxBasis" v).toList.mapIdxM fun i x => asNat s!"{ctx}.auxBasis[{i}]" x
    | none => pure []
  let mSk ← (field? j "mSk").mapM (asNat s!"{ctx}.mSk")
  let mTilde ← (field? j "mTilde").mapM (asNat s!"{ctx}.mTilde")
  let drop := fun (k : String) => match field? j k with
    | some v => do
      let d ← asInt s!"{ctx}.{k}" v
      if d < 0 then throw s!"{ctx}.{k}: {d} is negative"
      pure (some d.toNat)
    | none => (pure none : DecodeM (Option Nat))
  let internalDrops ← match field? j "internalDrops" with
    | some v => do
      let ds ← (← asArr s!"{ctx}.internalDrops" v).toList.mapIdxM fun i x => do
        let d ← asInt s!"{ctx}.internalDrops[{i}]" x
        if d < 0 then throw s!"{ctx}.internalDrops[{i}]: {d} is negative"
        pure d.toNat
      pure (some ds)
    | none => pure none
  let maxInternalDrop ← drop "maxInternalDrop"
  let maxInternalDropKS ← drop "maxInternalDropKS"
  let floatTolerant ← match field? j "floatTolerant" with
    | some v => asBool s!"{ctx}.floatTolerant" v
    | none => pure true
  return .ok { technique, auxBasis, mSk, mTilde, internalDrops, maxInternalDrop, maxInternalDropKS, floatTolerant,
               source := optStr j "source" }

/-- The internal drops of a decoded multiplication configuration for the program `prog` (module
docstring): the list `certifyBFV?` reads, or why the declaration is malformed. -/
def resolveDrops (prog : Program) (m : MulConfig) : DecodeM (List Nat) := do
  let ctx := "$.bfv.multiplication"
  let n := prog.body.length
  let dropsAt := fun (i : Instr) => match i with
    | .mul .. | .square .. | .relin .. | .keySwitch .. => true
    | _ => false
  if m.technique != .hpsPOverQLeveled then
    match m.internalDrops with
    | some ds =>
      if let some k := ds.findIdx? (· != 0) then
        throw s!"{ctx}.internalDrops[{k}]: an internal drop of {ds.getD k 0} limb(s) is declared under the technique {m.technique.name}; only HPSPOVERQLEVELED drops limbs internally (the field must be absent or all zero)"
      return []
    | none => return []
  let ds ← match m.internalDrops with
    | some ds =>
      if ds.length != n then
        throw s!"{ctx}.internalDrops: {ds.length} entries, but the program has {n} instructions (HPSPOVERQLEVELED: one entry per instruction of program.body, 0 where the library drops nothing)"
      pure ds
    | none =>
      if let some k := prog.body.findIdx? dropsAt then
        throw s!"{ctx}.internalDrops: missing; HPSPOVERQLEVELED drops limbs internally inside a multiplication or key switch (body[{k}]), and the number dropped at each instruction is an assumption the file must state (one entry per instruction of program.body, 0 where the library drops nothing)"
      pure (List.replicate n 0)
  let zipped := (prog.body.zip ds).zipIdx
  if let some ((_, d), k) := zipped.find? fun ((i, d), _) => d != 0 && !dropsAt i then
    throw s!"{ctx}.internalDrops[{k}]: {d}, but body[{k}] is not a mul, square, relin or keySwitch: the library drops limbs only inside those (0 at every other instruction)"
  let isKS := fun (i : Instr) => match i with
    | .keySwitch .. => true
    | _ => false
  if let some mx := m.maxInternalDrop then
    if let some ((_, d), k) := zipped.find? fun ((i, d), _) => !isKS i && d > mx then
      throw s!"{ctx}.maxInternalDrop: {mx}, but internalDrops[{k}] = {d} (maxInternalDrop is a cross-check: it must be at least every internal drop at a mul, square or relin)"
  if let some mx := m.maxInternalDropKS then
    if let some ((_, d), k) := zipped.find? fun ((i, d), _) => isKS i && d > mx then
      throw s!"{ctx}.maxInternalDropKS: {mx}, but internalDrops[{k}] = {d} (maxInternalDropKS is a cross-check: it must be at least every internal drop at a keySwitch)"
  return ds

/-- Decode a whole BFV `fhe-check/v1` document (one with `isBFV`). -/
def decode (j : Json) : DecodeM Decoded := do
  -- 1. the shared part, by the BGV decoder
  let p ← field "$" j "params"
  let j' ← match j, p with
    | .obj jk, .obj pk =>
      pure (Json.obj (jk.insert "params" (Json.obj (pk.insert "scheme" (Json.str "BGV")))))
    | _, _ => throw "$.params: expected an object"
  let base ← match ← FHE.Check.decode j' ["bfv"] with
    | .ok inp => pure inp
    | .unsupported what idx why =>
      -- the BGV decoder's wording for the one operation it names a scheme for
      let why := if what == "operation rescale" then "rescale is not an operation of the BFV programs this tool covers" else why
      return .unsupported what idx why
  let base : FHE.Check.Input :=
    { base with P := { base.P with src := { base.P.src with kind := .bfv } } }
  -- 2. what BFV does not have
  if let some i := base.prog.body.findIdx? (fun | .dropLimbs .. => true | _ => false) then
    return (.unsupported "operation dropLimbs" (some i)
      "not a BFV operation (Spec.TraceBFV: the BFV message is scaled by floor(Q/t), so dropping limbs without dividing changes it); a BFV level change is modSwitch")
  if base.decryption != .atOutputLevel then
    return (.unsupported s!"decryption method {base.decryption.name}" none
      "for BFV only decryption at the output's own level (\"at-output-level\", Spec.Scheme.bfvDecrypt) has a proved statement")
  -- 3. `$.bfv`
  let some bj := field? j "bfv" | return .ok { base }
  let _ ← asObj "$.bfv" bj
  onlyKeys "$.bfv" bj ["multiplication", "plainAdd", "encryption"]
  let mul ← match field? bj "multiplication" with
    | none => pure none
    | some mj =>
      match ← decodeMul mj with
      | .ok m => pure (some m)
      | .error tn =>
        return (.unsupported s!"multiplication technique {tn}" none
          s!"unknown BFV multiplication technique ({" | ".intercalate (Technique.all.map (·.name))})")
  let plainAdd ← match field? bj "plainAdd" with
    | none => pure none
    | some pj =>
      let _ ← asObj "$.bfv.plainAdd" pj
      onlyKeys "$.bfv.plainAdd" pj ["method", "source", "deviationBound"]
      match ← strField "$.bfv.plainAdd" pj "method" with
      | "delta" => pure (some { method := .delta, source := optStr pj "source" : PlainAddConfig })
      | "rounded" => pure (some { method := .rounded, source := optStr pj "source" })
      | "ceil" => pure (some { method := .scaled "ceil", source := optStr pj "source" })
      | "floor" => pure (some { method := .scaled "floor", source := optStr pj "source" })
      | "scaled" => pure (some { method := .scaled "scaled", source := optStr pj "source" })
      | m => return (.unsupported s!"plaintext-addition method {m}" none
          "no proved deviation for this way of adding a plaintext (delta | rounded | ceil | floor | scaled)")
  let drops ← match mul with
    | some m => resolveDrops base.prog m
    | none => pure []
  return .ok { base, mul, plainAdd, drops, encryption := (field? bj "encryption").getD Json.null }

end FHE.Check.BFV
