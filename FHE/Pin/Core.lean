import FHE.Pin.Sound
import FHE.Pin.Load
import Challenge.Headline.Defs

/-!
# FHE.Pin.Core — shared state and helpers of the `openfhe_pin` checks   (UNTRUSTED glue)

Nothing here decides anything by itself: the helpers wrap arrays, call the trusted definitions
(`normInf`, `centered`, `ofInt`, …) and format result lines.
-/

namespace FHE.Pin
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source

/-- Command-line options. -/
structure Opts where
  /-- Chunks (tasks) per forced polynomial. -/
  K : Nat := 32
  /-- Largest `N` at which the literal trusted definitions are also run. -/
  litMaxN : Nat := 32
  /-- The same for 3-component ciphertexts (cost `N⁴`). -/
  lit3MaxN : Nat := 16
  /-- Budget (coefficient accesses) for the literal `Source.eval` of one variable. -/
  litCost : Nat := 2000000
  mu : Mut := .none
  mutName : String := "none"
  only : Option (List String) := none

/-- Per-case context. -/
structure Cx where
  c : Case
  o : Opts
  P : FullParams
  s : Array Int
  out : IO.Ref (Array Json)
  keyCache : IO.Ref (Std.HashMap Nat (Array Int))
  objCache : IO.Ref (Std.HashMap String Ph)

def natJ (n : Nat) : Json := Json.str (toString n)
def intJ (n : Int) : Json := Json.str (toString n)
def boolJ (b : Bool) : Json := Json.bool b
def optBoolJ : Option Bool → Json
  | some b => Json.bool b
  | none => Json.null

/-- `log₂` for printing only. -/
def bitsJ (n : Nat) : Json := FHE.Check.jsonF (FHE.Check.log2F n)

namespace Cx

def want (x : Cx) (group : String) : Bool :=
  match x.o.only with
  | none => true
  | some l => l.contains group

/-- Append a result line. -/
def emit (x : Cx) (check id op : String) (ok : Option Bool) (impl : String)
    (extra : List (String × Json) := []) : IO Unit := do
  let base : List (String × Json) :=
    [("case", Json.str x.c.name), ("check", Json.str check), ("id", Json.str id),
     ("op", Json.str op), ("ok", optBoolJ ok), ("impl", Json.str impl),
     ("N", Json.num x.c.N), ("scaling", Json.str x.c.scaling), ("suite", Json.str x.c.generator),
     ("arbitrary", Json.bool (jBool x.c.pin "inputsArbitrary"))]
  let base := if x.o.mu = .none then base else base ++ [("mutate", Json.str x.o.mutName)]
  x.out.modify (·.push (Json.mkObj (base ++ extra)))

abbrev N (x : Cx) : Nat := x.P.src.N
abbrev t (x : Cx) : Nat := x.P.src.t
def K (x : Cx) : Nat := x.o.K
def mt (x : Cx) : Mut := x.o.mu

/-- Whether the literal trusted definitions are run for a value with `parts` components. -/
def literal (x : Cx) (parts : Nat) : Bool :=
  x.o.mu = .none && (if parts ≥ 3 then x.N ≤ x.o.lit3MaxN else x.N ≤ x.o.litMaxN) && parts ≤ 3

/-- The secret under the Galois element `key` (forced `automorph key s`), cached. -/
def sKey (x : Cx) (key : Nat) : IO (Array Int) := do
  match (← x.keyCache.get)[key]? with
  | some a => return a
  | none =>
    let a := autoA x.N x.K x.mt key x.s
    x.keyCache.modify (·.insert key a)
    return a

/-- Forced phase of `comps` at `level` under `key`. -/
def mkPh (x : Cx) (comps : List (Array Int)) (level key : Nat) : IO Ph := do
  let sk ← x.sKey key
  let Z := phaseZ x.N x.K x.mt sk comps
  let Φ := centredA x.N x.K x.mt (x.P.src.modulus level) Z
  return { comps, level, key, Z, Φ }

end Cx

/-- Canonical representatives of residues. -/
def valsOf {n : Nat} (a : Array (ZMod n)) : Array Int := a.map fun z => (z.val : Int)

/-- Number of positions where two arrays differ (for diagnostics). -/
def diffCount {α : Type} [BEq α] [Inhabited α] (a b : Array α) : Nat := Id.run do
  let mut k := if a.size == b.size then 0 else 1
  for i in [0:min a.size b.size] do
    if !(a[i]! == b[i]!) then k := k + 1
  return k

def liftExcept {α : Type} (e : Except String α) : IO α :=
  match e with
  | .ok a => pure a
  | .error m => throw (IO.userError m)

namespace Cx

/-- The components of a ciphertext object (CRT lift over `qs.take towers`), its towers and parts. -/
def objComps (x : Cx) (id : String) : IO (List (Array Int) × Nat) := do
  let some o := x.c.object? id | throw (IO.userError s!"pin.json has no object {id}")
  let some towers := jNat? o "towers" | throw (IO.userError s!"object {id}: towers")
  let expect := x.c.qs.take towers
  if expect.length != towers then
    throw (IO.userError s!"object {id}: {towers} towers exceed the chain of {x.c.qs.length}")
  if jStr? o "kind" == some "pt" then
    let some nm := jStr? o "poly" | throw (IO.userError s!"object {id}: poly")
    return ([← liftExcept (x.c.rnsPoly nm expect)], towers)
  let names := (jArr o "polys").toList.filterMap fun j => j.getStr?.toOption
  let comps ← names.mapM fun nm => liftExcept (x.c.rnsPoly nm expect)
  if comps.isEmpty then throw (IO.userError s!"object {id}: no polys")
  return (comps, towers)

/-- The forced phase of a ciphertext object under `s` at its own towers, cached. -/
def objPh (x : Cx) (id : String) : IO Ph := do
  match (← x.objCache.get)[id]? with
  | some p => return p
  | none =>
    let (comps, towers) ← x.objComps id
    let p ← x.mkPh comps towers 1
    x.objCache.modify (·.insert id p)
    return p

/-- A raw decryption line: residues modulo `m`. -/
def rawPoly (x : Cx) (nm : String) (m : Nat) : IO (Array Int) := do
  let some e := x.c.polys[nm]? | throw (IO.userError s!"polys.txt has no entry {nm}")
  if e.moduli != #[m] then
    throw (IO.userError s!"{nm}: modulus {e.moduli.toList} is not the expected [{m}]")
  return e.limbs[0]!

end Cx
end FHE.Pin
