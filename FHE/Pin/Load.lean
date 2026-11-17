import FHE.Check.Decode
import FHE.Check.Budget
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# FHE.Pin.Load — reading an `openfhe-pin/v1` case directory   (UNTRUSTED glue, self-checking)

* `parsePolys`: a hand-written splitter for `polys.txt` (one RNS limb per line).
* `crt`: CRT reconstruction of an RNS polynomial to canonical integers in `[0, ∏ moduli)`. The
  result is **verified against every limb** (`x mod qᵢ = rᵢ`), so a wrong reconstruction cannot go
  unnoticed.
* `loadCase`: `pin.json`, `polys.txt`, `prog.fhecheck.json` (through the existing decoder
  `FHE.Check.decode`), `trace.jsonl`.
-/

namespace FHE.Pin
open Lean

/-- One named polynomial of `polys.txt`: its limb moduli and residues (`moduli = #[0]`: an exact
signed integer polynomial). -/
structure Entry where
  moduli : Array Nat
  limbs : Array (Array Int)
  deriving Inhabited

/-- Parse `polys.txt`. Every line: `<name> <limb> <modulus> <c_0> … <c_{N-1}>`. -/
def parsePolys (bytes : ByteArray) : Except String (Std.HashMap String Entry) := Id.run do
  let mut map : Std.HashMap String Entry := {}
  let mut err : Option String := none
  let mut tok : Nat := 0            -- index of the field being read
  let mut start : Nat := 0          -- start of the current field
  let mut acc : Nat := 0
  let mut neg := false
  let mut digits : Nat := 0
  let mut name : String := ""
  let mut limb : Nat := 0
  let mut modulus : Nat := 0
  let mut coeffs : Array Int := #[]
  let mut line : Nat := 1
  let n := bytes.size
  for i in [0:n + 1] do
    if err.isSome then break
    let b : UInt8 := if i < n then bytes[i]! else 10
    if b == 32 || b == 10 then
      -- end of a field
      if i == n && tok == 0 && start == i then break   -- file ended with a newline
      if tok == 0 then
        if b == 10 && start == i then
          -- empty line
          line := line + 1; start := i + 1; continue
        match String.fromUTF8? (bytes.extract start i) with
        | some s => name := s
        | none => err := some s!"polys.txt:{line}: name is not UTF-8"
      else
        if digits == 0 then err := some s!"polys.txt:{line}: empty or non-numeric field {tok}"
        else if tok == 1 then limb := acc
        else if tok == 2 then modulus := acc
        else coeffs := coeffs.push (if neg then -(acc : Int) else (acc : Int))
        if neg && tok ≤ 2 then err := some s!"polys.txt:{line}: negative limb index or modulus"
      tok := tok + 1; start := i + 1; acc := 0; neg := false; digits := 0
      if b == 10 then
        if tok < 4 then err := some s!"polys.txt:{line}: fewer than 4 fields"
        else
          match map[name]? with
          | none =>
            if limb != 0 then err := some s!"polys.txt:{line}: {name}: first limb has index {limb}"
            else map := map.insert name { moduli := #[modulus], limbs := #[coeffs] }
          | some e =>
            if limb != e.moduli.size then
              err := some s!"polys.txt:{line}: {name}: limb {limb} out of order (expected {e.moduli.size})"
            else if modulus == 0 || e.moduli[0]! == 0 then
              err := some s!"polys.txt:{line}: {name}: an integer polynomial (modulus 0) has one line"
            else
              map := map.insert name { moduli := e.moduli.push modulus, limbs := e.limbs.push coeffs }
        tok := 0; coeffs := #[]; line := line + 1
    else if tok == 0 then
      pure ()
    else if b == 45 && digits == 0 && !neg then neg := true
    else if 48 ≤ b && b ≤ 57 then
      acc := acc * 10 + (b - 48).toNat; digits := digits + 1
    else err := some s!"polys.txt:{line}: unexpected byte {b} in a number"
  match err with
  | some e => return .error e
  | none => return .ok map

/-- Modular inverse by the extended Euclidean algorithm (`0` if none). Verified by its use: the
CRT result is checked against every limb. -/
def invMod (a q : Nat) : Nat := Id.run do
  let mut r0 : Int := q
  let mut r1 : Int := a % q
  let mut t0 : Int := 0
  let mut t1 : Int := 1
  for _ in [0:4 * (Nat.log2 q + 2)] do
    if r1 == 0 then break
    let k := r0 / r1
    (r0, r1) := (r1, r0 - k * r1)
    (t0, t1) := (t1, t0 - k * t1)
  if r0 != 1 then return 0
  return (t0 % (q : Int)).toNat

/-- CRT reconstruction to `[0, ∏ moduli)`, verified against every limb. -/
def crt (what : String) (N : Nat) (moduli : Array Nat) (limbs : Array (Array Int)) :
    Except String (Array Int) := do
  if moduli.size == 0 || moduli.size != limbs.size then throw s!"{what}: no limbs"
  if moduli.any (· == 0) then throw s!"{what}: an integer polynomial where residues are expected"
  for l in limbs do
    if l.size != N then throw s!"{what}: a limb has {l.size} coefficients, expected N = {N}"
  let M : Nat := moduli.foldl (fun a b => a * b) 1
  let cs : Array Int := moduli.map fun q => let Mi := M / q; ((Mi * invMod (Mi % q) q : Nat) : Int)
  let out : Array Int := Array.ofFn (n := N) fun j => Id.run do
    let mut x : Int := 0
    for i in [0:moduli.size] do
      x := x + (limbs[i]!)[j.val]! * cs[i]!
    return x % (M : Int)
  -- verification
  for i in [0:moduli.size] do
    let q : Int := moduli[i]!
    let l := limbs[i]!
    for j in [0:N] do
      let r := l[j]!
      if r < 0 || r ≥ q then throw s!"{what}: limb {i} coefficient {j} is not in [0, modulus)"
      if out[j]! % q != r then throw s!"{what}: CRT reconstruction disagrees with limb {i} at coefficient {j}"
  return out

/-! ### JSON access -/

def jStr? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def jNat? (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok v => (FHE.Check.asNat k v).toOption
  | _ => none

def jObj? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok Json.null => none
  | .ok v => some v
  | _ => none

def jArr (j : Json) (k : String) : Array Json :=
  match j.getObjVal? k with
  | .ok (.arr a) => a
  | _ => #[]

def jBool (j : Json) (k : String) : Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => b
  | _ => false

/-- One `ModReduceInternalInPlace` call of the trace: operand id, result id, number of levels. -/
structure ModReduceCall where
  src : String
  dst : String
  levels : Nat
  line : Nat

/-- Scan `trace.jsonl` for `ModReduceInternalInPlace` calls (first ciphertext `in`, last
ciphertext `out`, integer `levels`). -/
def scanCalls (needle : String) (text : String) : Array ModReduceCall := Id.run do
  let mut out := #[]
  -- stack of open frames: (fn, first ct in, last ct out, levels)
  let mut stack : Array (String × Option String × Option String × Nat × Nat) := #[]
  let mut ln := 0
  for l in text.splitOn "\n" do
    ln := ln + 1
    if l.isEmpty then continue
    let .ok j := Json.parse l | continue
    match jStr? j "ev" with
    | some "begin" => stack := stack.push ((jStr? j "fn").getD "", none, none, 1, ln)
    | some "in" =>
      if let some (fn, i, o, k, b) := stack.back? then
        if jStr? j "kind" == some "ct" && i.isNone then
          stack := stack.pop.push (fn, jStr? j "id", o, k, b)
        else if jStr? j "kind" == some "int" && jStr? j "name" == some "levels" then
          stack := stack.pop.push (fn, i, o, (jNat? j "v").getD 1, b)
    | some "out" =>
      if let some (fn, i, _, k, b) := stack.back? then
        if jStr? j "kind" == some "ct" then
          stack := stack.pop.push (fn, i, jStr? j "id", k, b)
    | some "end" =>
      if let some (fn, i, o, k, b) := stack.back? then
        stack := stack.pop
        if (fn.splitOn needle).length > 1 then
          if let (some a, some d) := (i, o) then
            out := out.push { src := a, dst := d, levels := k, line := b }
    | _ => pure ()
  return out

/-- A loaded case. -/
structure Case where
  dir : String
  name : String
  pin : Json
  N : Nat
  t : Nat
  qs : List Nat
  special : List Nat
  scaling : String
  generator : String
  polys : Std.HashMap String Entry
  /-- The decoded `prog.fhecheck.json`, or why there is none. -/
  inp : Except String FHE.Check.Input
  /-- The raw `prog.fhecheck.json` (for `program.inputs[].origin`). -/
  progJson : Json
  modReduces : Array ModReduceCall
  /-- Traced `EvalNegate*` calls (operand, result). -/
  negates : Array ModReduceCall := #[]
  /-- The distinct function names of the trace's call frames. -/
  traceFns : Array String := #[]

def natList (j : Json) (k : String) : Except String (List Nat) := do
  (jArr j k).toList.mapM fun v => FHE.Check.asNat k v

/-- A directory path without trailing slashes. -/
def trimDir (dir : String) : String :=
  String.ofList (dir.toList.reverse.dropWhile (· == '/')).reverse

def loadCase (dir : String) : IO (Except String Case) := do
  let dir := trimDir dir
  try
    let d : System.FilePath := dir
    let name := (d.fileName).getD dir
    let pinText ← IO.FS.readFile (d / "pin.json")
    let pin ← match Json.parse pinText with
      | .ok j => pure j
      | .error e => return .error s!"pin.json: {e}"
    if jStr? pin "format" != some "openfhe-pin/v1" then
      return .error "pin.json: format is not openfhe-pin/v1"
    let some N := jNat? pin "N" | return .error "pin.json: N"
    let some t := jNat? pin "t" | return .error "pin.json: t"
    let qs ← match natList pin "qs" with
      | .ok l => pure l
      | .error e => return .error s!"pin.json: {e}"
    let special ← match natList pin "special" with
      | .ok l => pure l
      | .error e => return .error s!"pin.json: {e}"
    if N == 0 || qs.isEmpty then return .error "pin.json: N = 0 or empty chain"
    let bytes ← IO.FS.readBinFile (d / "polys.txt")
    let polys ← match parsePolys bytes with
      | .ok m => pure m
      | .error e => return .error e
    for (k, e) in polys.toList do
      for l in e.limbs do
        if l.size != N then
          return .error s!"polys.txt: {k}: a line has {l.size} coefficients, expected N = {N}"
    let progPath := d / "prog.fhecheck.json"
    let (inp, progJson) ←
      if !(← progPath.pathExists) then pure (.error "prog.fhecheck.json is missing", Json.null)
      else
        let text ← IO.FS.readFile progPath
        match FHE.Check.lexCheck text with
        | .error e => pure (.error s!"prog.fhecheck.json refused before parsing: {e}", Json.null)
        | .ok () =>
          match Json.parse text with
          | .error e => pure (.error s!"prog.fhecheck.json: malformed JSON: {e}", Json.null)
          | .ok j =>
            match FHE.Check.decode j with
            | .error e => pure (.error s!"prog.fhecheck.json: {e}", j)
            | .ok (.unsupported what idx why) =>
              pure (.error s!"prog.fhecheck.json: unsupported {what} {idx}: {why}", j)
            | .ok (.ok inp) => pure (.ok inp, j)
    let tracePath := d / "trace.jsonl"
    let traceText ← if ← tracePath.pathExists then IO.FS.readFile tracePath else pure ""
    let modReduces := scanCalls "ModReduceInternalInPlace" traceText
    let negates := scanCalls "EvalNegate" traceText
    let traceFns : Array String := Id.run do
      let mut seen : Std.HashSet String := {}
      for l in traceText.splitOn "\n" do
        if l.startsWith "{\"ev\":\"begin\"" then
          if let .ok j := Json.parse l then
            if let some fn := jStr? j "fn" then seen := seen.insert fn
      return seen.toArray
    return .ok { dir, name, pin, N, t, qs, special
                 scaling := (jStr? pin "scaling").getD "?"
                 generator := (jStr? pin "generator").getD ""
                 polys, inp, progJson, modReduces, negates, traceFns }
  catch e => return .error s!"{e}"

namespace Case

/-- A modulus-0 (exact integer) polynomial. -/
def intPoly (c : Case) (nm : String) : Except String (Array Int) := do
  let some e := c.polys[nm]? | throw s!"polys.txt has no entry {nm}"
  if e.moduli != #[0] then throw s!"{nm}: expected an exact integer polynomial (modulus 0)"
  return e.limbs[0]!

/-- An RNS polynomial whose limb moduli must be exactly `expect`, CRT-lifted to `[0, ∏)`. -/
def rnsPoly (c : Case) (nm : String) (expect : List Nat) : Except String (Array Int) := do
  let some e := c.polys[nm]? | throw s!"polys.txt has no entry {nm}"
  if e.moduli.toList != expect then
    throw s!"{nm}: limb moduli {e.moduli.toList} are not the expected {expect}"
  crt nm c.N e.moduli e.limbs

/-- The limb moduli of an entry. -/
def moduliOf (c : Case) (nm : String) : Except String (List Nat) := do
  let some e := c.polys[nm]? | throw s!"polys.txt has no entry {nm}"
  return e.moduli.toList

/-- CRT lift over whatever limbs the entry has. -/
def rnsPolyAny (c : Case) (nm : String) : Except String (List Nat × Array Int) := do
  let some e := c.polys[nm]? | throw s!"polys.txt has no entry {nm}"
  return (e.moduli.toList, ← crt nm c.N e.moduli e.limbs)

def object? (c : Case) (id : String) : Option Json := jObj? ((jObj? c.pin "objects").getD Json.null) id

end Case
end FHE.Pin
