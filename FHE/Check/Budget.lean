import FHE.Check.Decode
import Spec.Budget
import FHE.Noise.Fast
import Std.Data.HashMap

set_option autoImplicit false

/-!
# FHE.Check.Budget — the key-switching and modulus-switching budgets   (UNTRUSTED glue)

**SWITCH-OVER POINT 1 (budget), switched to the trusted `Spec.Budget`.** This file is the only
place where the `Spec.Trace.Budget` handed to the analyzer is chosen. It is
`Spec.Budget.certified P lay` = `⟨ksBudget P lay, msBudget P, msBudgetOne P, msBudgetAt P⟩`, where

* `lay` is the key-switching layout from the input: `Spec.Budget.uniformLayout α canonical` for
  consecutive digits of `α` limbs (OpenFHE, Lattigo), or explicit digit sizes per level;
  `canonical` is `true` for the `openfhe` / `canonical` variants (canonical representatives, the
  larger bound) and `false` for `centred`;
* `ksBudget` is the maximum of `ksBoundAt` over all levels `1..L` of the chain;
* `msBudget P = ⌈t·(1 + N·B_s)/2⌉` (two-part ciphertexts), `msBudgetOne P = ⌈t/2⌉` (a one-part
  value: a plaintext operand, which OpenFHE's automatic scaling modes modulus-switch), and
  `msBudgetAt P k = ⌈t·Σ_{i<k} (N·B_s)ⁱ/2⌉` for a value with `k` parts (e.g. a product that has
  not been relinearized: `k = 3`).

The locked pins `Challenge.Budget.relin_realizable`, `keySwitch_realizable`,
`modSwitch_realizable_parts` (every number of parts; `modSwitch_realizable`,
`modSwitch_realizable_one` are its cases 2 and 1) and `ksBoundAt_le_ksBudget` (proved, under
`SchemeParamsOK` and `SpecialOK` only, any prime size) say that key switching and modulus
switching *can* be done within these budgets. Nothing is refused here on the number of parts:
the verdict is `Challenge.Certify.certify?`'s, which runs the analysis at this budget. The parts
at each modulus switch are read from `Source.step` (the verified semantics) on all-zero messages,
for printing only.
-/

namespace FHE.Check
open Spec Spec.Source

/-- The operand of a key-switching or modulus-switching instruction. -/
def ksOrMsOperand : Instr → Option (Bool × Var)
  | .relin _ a | .keySwitch _ a => some (true, a)
  | .modSwitch _ a => some (false, a)
  | _ => none

/-- The environment of `Source.step` on all-zero messages, kept in a search tree so that a replay
of the program is near-linear in its length. The locked `Source.step` is called on a lookup
function backed by the tree; it changes only the destination of the instruction (`Env.set`),
whose new value is read back and stored. So `ZEnv.step` gives exactly the values of folding
`step` over `initEnv` (whose closures make each lookup linear in the number of earlier
instructions). A persistent tree, not a hash map: the environment `step` returns is a closure
that still holds the old map when the new value is inserted, so a hash map's bucket array would
be copied at every instruction (measured: quadratic). Diagnostic replays only: the verdict is
computed by the verified functions themselves. -/
structure ZEnv (P : Params) where
  m : Std.TreeMap Var (Val P)

namespace ZEnv

def get {P : Params} (e : ZEnv P) (x : Var) : Option (Val P) := e.m[x]?

/-- The inputs as `Source.initEnv` holds them (on all-zero messages): the first declaration of
each name (`FHE.Noise.Fast.initEnvMap`; `Validation.Fast.Aux.initEnvMap_get`). -/
def init (P : Params) (prog : Program) : ZEnv P := ⟨FHE.Noise.Fast.initEnvMap P prog⟩

/-- One `Source.step`. -/
def step {P : Params} (e : ZEnv P) (i : Instr) : Option (ZEnv P) := do
  let ρ' ← Source.step P e.get i
  let v ← ρ' (Trace.dst i)
  pure ⟨e.m.insert (Trace.dst i) v⟩

end ZEnv

/-- `(isKeySwitch, body index, level, parts)` of the operand at every key switch and modulus
switch, replaying `Source.step` on zero messages up to the first ill-formed instruction. -/
def switchSites (P : Params) (prog : Program) : List (Bool × Nat × Nat × Nat) := Id.run do
  let mut ρ := ZEnv.init P prog
  let mut out := #[]
  let mut idx := 0
  for i in prog.body do
    if let some (ks, a) := ksOrMsOperand i then
      if let some v := ρ.get a then out := out.push (ks, idx, v.level, v.parts)
    match ρ.step i with
    | some ρ' => ρ := ρ'
    | none => break
    idx := idx + 1
  return out.toList

/-- The `Spec.Budget.KSLayout` described by the input. Explicit digits must be consecutive runs
of limbs in order (`KSLayout` lists digit sizes), given for every level `1..L`. -/
def layoutOf (P : FullParams) (ks : KsConfig) : Except String Budget.KSLayout := do
  let canonical := ks.variant != .centred
  match ks.digits with
  | .consecutive α => return Budget.uniformLayout α canonical
  | .explicit pl =>
    let mut tbl : List (Nat × List Nat) := []
    for ℓ in (List.range P.src.qs.length).map (· + 1) do
      let some (_, ds) := pl.find? (·.1 = ℓ)
        | throw s!"keySwitching.digits.perLevel has no entry for level {ℓ} (needed: the budget covers every level)"
      let sizes := ds.map List.length
      let starts := (List.range ds.length).map fun j => ((sizes.take j).sum)
      let consecutive := (ds.zip starts).all fun (d, s0) => d == (List.range d.length).map (s0 + ·)
      unless consecutive && sizes.sum == ℓ && sizes.all (0 < ·) do
        throw s!"the key-switching digits at level {ℓ} are not consecutive runs partitioning limbs 0..{ℓ - 1}: {ds}"
      tbl := (ℓ, sizes) :: tbl
    let t := tbl
    return { sizes := fun ℓ => ((t.find? (·.1 = ℓ)).map (·.2)).getD [], canonical }

/-- One level's key-switching bound (`Spec.Budget.ksBoundAt`) and its digits. -/
structure KsLevel where
  level : Nat
  bound : Nat
  /-- (number of limbs, product) per digit. -/
  digits : List (Nat × Nat)

/-- The budget, the per-level detail, and the sites it was derived from. -/
structure BudgetReport where
  E : Trace.Budget
  layout : Budget.KSLayout
  /-- `ksBoundAt` at every level `1..L`. -/
  ksLevels : List KsLevel
  /-- Levels at which the program key-switches. -/
  usedKsLevels : List Nat
  hasKs : Bool
  /-- The program modulus-switches a two-part ciphertext / a one-part value. -/
  hasMs : Bool
  hasMsOne : Bool
  /-- The numbers of parts `k ≥ 3` of the values the program modulus-switches (printed with
  `Spec.Budget.msBudgetAt P k`). -/
  msManyParts : List Nat := []

/-- Why no certified budget exists. -/
inductive BudgetError
  | invalid (msg : String)
  | unsupported (what : String) (idx : Option Nat) (why : String)

/-- Compute the budget for a program. -/
def computeBudget (inp : Input) : Except BudgetError BudgetReport := do
  let P := inp.P
  let lay ← match layoutOf P inp.ks with
    | .ok l => pure l
    | .error e => throw (.invalid e)
  let sites := switchSites P.src inp.prog
  let used := (sites.filter (·.1)).map (·.2.2.1) |>.eraseDups |>.mergeSort (· ≥ ·)
  let msSites := sites.filter (!·.1)
  -- `Challenge.Budget.modSwitch_realizable_parts` covers every number of parts, at
  -- `msBudgetAt P k`: nothing is refused here.
  -- DIAGNOSTIC: the refusal itself is `Challenge.Certify.certify?`'s, which returns no
  -- certificate for a declared method other than the centred one, whatever the program
  -- (`Challenge.Certify.certify?_centred`); this only words it.
  if inp.msMethod != "t-corrected-centred" then
    throw (.unsupported s!"modulus-switching method {inp.msMethod}" (msSites.head?.map (·.2.1))
      "only the centred t-corrected modulus switch (\"t-corrected-centred\") has a proved budget (Challenge.Certify.certify?_centred)")
  let levels := (List.range P.src.qs.length).map (· + 1)
  let ksLevels := levels.reverse.map fun ℓ =>
    { level := ℓ, bound := Budget.ksBoundAt P lay ℓ,
      digits := (lay.sizes ℓ).zip (Budget.digitModuli P lay ℓ) : KsLevel }
  return { E := Budget.certified P lay, layout := lay, ksLevels, usedKsLevels := used,
           hasKs := !used.isEmpty, hasMs := msSites.any (·.2.2.2 == 2),
           hasMsOne := msSites.any (·.2.2.2 == 1),
           msManyParts := ((msSites.map (·.2.2.2)).filter (fun k => k != 1 && k != 2)).eraseDups
             |>.mergeSort (· ≤ ·) }

end FHE.Check
