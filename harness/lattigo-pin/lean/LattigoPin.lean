import FHE.Pin.Sound
import Challenge.Instances.Lattigo.Defs

/-!
# lattigo_pin — the phase-contract check of recorded Lattigo BGV runs (UNTRUSTED driver)

Run (from the repository root, after `lake build FHE.Pin.Sound Challenge.Instances.Lattigo.Defs`):

    lake env lean --run harness/lattigo-pin/lean/LattigoPin.lean OUT.jsonl CASE.json...

Reads `lattigo-pin/v1` cases (`harness/lattigo-pin/FORMAT.md`) and writes one JSON line per
check. What is reused, unchanged, from the OpenFHE pin core (`FHE/Pin/Force.lean`,
`FHE/Pin/Sound.lean`):

* the forced phase `phaseAtZ` and centred lift `centredA` (`phaseAtZ_spec`,
  `centredA_phaseAtZ_spec`: equal to `Spec.Trace.phaseAt` and its centred lift), from which every
  `Ph` is built, so `Ph.Good` holds by construction;
* the decision `stepOKb` of `Spec.Trace.StepOK` (`stepOKb_sound`), for `add`, `sub`, `mul`,
  `mulConst`, `relin`, `automorph`, `keySwitch`, `modSwitch`;
* the budget: `Challenge.Instances.Lattigo.profile` at `Challenge.Instances.Lattigo.params` of the
  case (locked definitions), never read from the input.

What this driver adds, and is NOT covered by a theorem: the JSON loading, the CRT reconstruction
(checked against every limb at run time), the t-reading (each limb times `t mod q_i`), the
operand lookup (the `GetOK` hypothesis of `stepOKb_sound`; this driver does not replay
`Spec.Source.step`: levels, keys and numbers of components are the recorded ones), the
synthesized intermediate of a rotation (`σ_g` of the operand's components, see `rotate`), and the
fresh-encryption check (`enc.*`: the forced centred phase compared with the profile's input-noise
bounds and with the stored plaintext modulo `t`; a direct computation, not a proved decision).
-/

open Lean Spec Spec.Source Spec.NPoly FHE.Pin

namespace LattigoPin

def K : Nat := 1

def jStr (j : Json) (k : String) : Except String String := do
  match (← j.getObjVal? k) with
  | Json.str s => pure s
  | Json.num n => pure (toString n)
  | v => throw s!"{k}: not a string: {v.compress}"

def jNat (j : Json) (k : String) : Except String Nat := do
  let s ← jStr j k
  match s.toNat? with
  | some n => pure n
  | none => throw s!"{k}: not a natural: {s}"

def natOf (j : Json) : Except String Nat :=
  match j with
  | Json.str s => match s.toNat? with | some n => pure n | none => throw s!"bad nat {s}"
  | Json.num n => match n.mantissa.toNat, n.exponent with
    | m, 0 => pure m
    | _, _ => throw "bad nat"
  | _ => throw "bad nat"

def intOf (j : Json) : Except String Int :=
  match j with
  | Json.str s => match s.toInt? with | some n => pure n | none => throw s!"bad int {s}"
  | Json.num n => if n.exponent = 0 then pure n.mantissa else throw "bad int"
  | _ => throw "bad int"

def natArr (j : Json) : Except String (Array Nat) := do (← j.getArr?).mapM natOf

/-- `a⁻¹ mod m` for coprime `a`, `m`. -/
def invMod (a m : Nat) : Nat :=
  let g := Nat.gcdA a m
  (g % (m : Int)).toNat

/-- CRT: the integer in `[0, Π mods)` with the given residues. -/
def crt (mods : List Nat) (res : List Nat) : Nat :=
  let Q := mods.foldl (· * ·) 1
  let terms := (mods.zip res).map fun (q, r) =>
    let h := Q / q
    r % q * h % Q * invMod (h % q) q % Q
  terms.foldl (fun acc x => (acc + x) % Q) 0

/-- A poly (list of limbs, each `N` residues) at the limbs `mods`, t-read and CRT-reconstructed:
the integers in `[0, Q)`; fails if a limb does not match. -/
def readPoly (N t : Nat) (mods : List Nat) (j : Json) : Except String (Array Int) := do
  let limbs ← (← j.getArr?).mapM natArr
  if limbs.size ≠ mods.length then throw s!"limb count {limbs.size} ≠ {mods.length}"
  for l in limbs do
    if l.size ≠ N then throw "limb length"
  let tl : Array (Array Nat) := (limbs.zip mods.toArray).map fun (l, q) => l.map fun r => t * r % q
  let out := (Array.range N).map fun i => crt mods (tl.toList.map fun l => l[i]!)
  for i in [0:N] do
    for (l, q) in tl.zip mods.toArray do
      if out[i]! % q ≠ l[i]! then throw "CRT mismatch"
  pure (out.map fun (x : Nat) => (Int.ofNat x))

structure Obj where
  level : Nat
  parts : Nat
  comps : List (Array Int)

def normI (a : Array Int) : Nat := a.foldl (fun m x => max m x.natAbs) 0

def emit (out : IO.FS.Handle) (fields : List (String × Json)) : IO Unit :=
  out.putStrLn (Json.mkObj fields).compress

def runCase (out : IO.FS.Handle) (path : String) : IO (Nat × Nat) := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  let get {α} (e : Except String α) : IO α := IO.ofExcept (e.mapError fun m => IO.userError s!"{path}: {m}")
  let caseName ← get (jStr j "case")
  let N ← get (jNat j "N")
  let t ← get (jNat j "t")
  let qs ← get (do (← (← j.getObjVal? "qs").getArr?).toList.mapM natOf)
  let ps ← get (do (← (← j.getObjVal? "ps").getArr?).toList.mapM natOf)
  let base2 ← get (jNat j "base2")
  let gen ← get (jStr j "generator")
  let s ← get (do (← (← j.getObjVal? "secret").getArr?).mapM intOf)
  let P := Challenge.Instances.Lattigo.params N qs ps t
  let E0 := Challenge.Instances.Lattigo.profile P
  -- base-2 decomposition is not modelled: a conservative bound (argued, not proved) is the
  -- canonical-representative hybrid bound with one limb per digit.
  let E : Trace.Budget := if base2 = 0 then E0 else
    { E0 with keySwitch := Budget.ksBudget P (Budget.uniformLayout 1 true) }
  let budgetKind := if base2 = 0 then "profile" else "base2-argued-canonical"
  let objsJ ← get (do (← j.getObjVal? "objects").getObj?)
  let mut objs : Std.HashMap String Obj := {}
  for ⟨id, o⟩ in objsJ.toArray do
    let kind ← get (jStr o "kind")
    let level ← get (jNat o "level")
    let mods := qs.take level
    if kind = "ct" then
      let comps ← get (do (← (← o.getObjVal? "comps").getArr?).toList.mapM (readPoly N t mods))
      objs := objs.insert id { level, parts := comps.length, comps }
    else
      let p ← get (do readPoly N t mods (← o.getObjVal? "poly"))
      objs := objs.insert id { level, parts := 1, comps := [p] }
  let mkPh (o : Obj) (key : Nat) : Ph :=
    let Z := phaseAtZ N K .none key s o.comps
    { comps := o.comps, level := o.level, key, Z, Φ := centredA N K .none (P.src.modulus o.level) Z }
  let common := [("case", Json.str caseName), ("suite", Json.str gen), ("N", Json.num N),
    ("budgetKind", Json.str budgetKind)]
  let ops ← get (do (← j.getObjVal? "ops").getArr?)
  let mut nOK : Nat := 0
  let mut nBad : Nat := 0
  let mut k : Nat := 0
  for op in ops do
    k := k + 1
    let opn ← get (jStr op "op")
    let outId ← get (jStr op "out")
    let some o := objs[outId]? | throw (IO.userError s!"{path}: no object {outId}")
    let dPh := mkPh o 1
    let getOp (id : String) : Option (Ph × Nat) := (objs[id]?).map fun x => (mkPh x 1, x.parts)
    let lineBase := common ++ [("op", Json.str opn), ("idx", Json.num k), ("out", Json.str outId),
      ("level", Json.num o.level), ("parts", Json.num o.parts)]
    let mut lines : List (List (String × Json)) := []
    if opn = "encSk" || opn = "encPk" then
      let ptId ← get (jStr op "pt")
      let some pt := objs[ptId]? | throw (IO.userError s!"{path}: no pt {ptId}")
      let Q := P.src.modulus o.level
      let p := centredA N K .none Q pt.comps.head!
      let Φ := dPh.Φ
      let bound := if opn = "encSk" then Challenge.Instances.Lattigo.skFresh t
        else Challenge.Instances.Lattigo.pkFresh N t ps
      let diff := (Φ.zip p).map fun (a, b) => a - b
      let dvd := diff.all fun x => x % (t : Int) = 0
      let eMSB := normI (diff.map fun x => x / (t : Int))
      let nrm := normI Φ
      let ok := decide (nrm ≤ bound) && dvd
      lines := [lineBase ++ [("check", Json.str "enc.fresh"), ("ok", Json.bool ok),
        ("measured", Json.str (toString nrm)), ("bound", Json.str (toString bound)),
        ("errMSB", Json.str (toString eMSB)), ("msgModT", Json.bool dvd),
        ("ptNorm", Json.str (toString (normI p)))]]
    else if opn = "rotate" then
      let a ← get (jStr op "a")
      let g ← get (jNat op "g")
      let some x := objs[a]? | throw (IO.userError s!"{path}: no object {a}")
      let mid : Obj := { x with comps := x.comps.map (autoA N K .none g) }
      let midPh := mkPh mid g
      let r1 := stepOKb P E K .none (.automorph "mid" a g) mid.level midPh getOp
      let getMid (id : String) : Option (Ph × Nat) := if id = "mid" then some (midPh, mid.parts) else getOp id
      let r2 := stepOKb P E K .none (.keySwitch outId "mid") o.level dPh getMid
      let Q := P.src.modulus o.level
      let e := toArr K (centered (ofInt Q (ofArr (N := N) dPh.Z) - ofInt Q (ofArr (N := N) midPh.Z)))
      let nrm := normA N e
      lines := [lineBase ++ [("check", Json.str "e.step"), ("instr", Json.str "automorph"),
          ("composite", Json.bool true), ("ok", Json.bool (r1 == some true))],
        lineBase ++ [("check", Json.str "e.step"), ("instr", Json.str "keySwitch"),
          ("composite", Json.bool true), ("ok", Json.bool (r2 == some true)),
          ("measured", Json.str (toString nrm)), ("bound", Json.str (toString E.keySwitch)),
          ("errMSB", Json.str (toString (nrm / t))), ("g", Json.num g)]]
    else
      let a ← get (jStr op "a")
      let b := (op.getObjValAs? String "b").toOption.getD ""
      let some x := objs[a]? | throw (IO.userError s!"{path}: no object {a}")
      let instr : Option Instr :=
        if opn = "add" then some (.add outId a b) else if opn = "sub" then some (.sub outId a b)
        else if opn = "mul" then some (.mul outId a b) else if opn = "relin" then some (.relin outId a)
        else if opn = "rescale" then some (.modSwitch outId a)
        else if opn = "mulConst" then
          match (op.getObjValAs? String "c").toOption.bind String.toInt? with
          | some c => some (.mulConst outId a c) | none => none
        else none
      match instr with
      | none => lines := [lineBase ++ [("check", Json.str "e.step"), ("ok", Json.null),
          ("why", Json.str "unknown op")]]
      | some i =>
        let r := stepOKb P E K .none i o.level dPh getOp
        let mut extra : List (String × Json) := []
        if opn = "relin" then
          let Q := P.src.modulus o.level
          let xPh := mkPh x 1
          let e := toArr K (centered (ofInt Q (ofArr (N := N) dPh.Z) - ofInt Q (ofArr (N := N) xPh.Z)))
          let nrm := normA N e
          extra := [("measured", Json.str (toString nrm)), ("bound", Json.str (toString E.keySwitch)),
            ("errMSB", Json.str (toString (nrm / t)))]
        if opn = "rescale" then
          let xPh := mkPh x 1
          let q := qs[x.level - 1]!
          let δ := toArr K ((q : ℤ) • ofArr (N := N) dPh.Φ - ofArr (N := N) xPh.Φ)
          let nrm := normA N δ
          let Eb := Mut.none.msBudgetM E x.parts
          extra := [("measured", Json.str (toString nrm)), ("bound", Json.str (toString (q * Eb))),
            ("measuredOverQ", Json.str (toString ((nrm + q - 1) / q))), ("budget", Json.str (toString Eb)),
            ("operandParts", Json.num x.parts)]
        lines := [lineBase ++ [("check", Json.str "e.step"), ("instr", Json.str opn),
          ("ok", match r with | some v => Json.bool v | none => Json.null)] ++ extra]
    for l in lines do
      match (Json.mkObj l).getObjVal? "ok" with
      | .ok (Json.bool true) => nOK := nOK + 1
      | _ => nBad := nBad + 1
      emit out l
  -- What the user reads (NOT a phase contract): Lattigo's Decrypt+Decode under its tracked scale
  -- against the exporter's cleartext evaluation of the program (both recorded by the exporter;
  -- this line compares them and is outside every theorem).
  let mut nUserBad : Nat := 0
  match (j.getObjVal? "slots").toOption.bind (·.getObj?.toOption) with
  | none => pure ()
  | some sl =>
    for ⟨id, v⟩ in sl.toArray do
      let ex := ((v.getObjVal? "expected").toOption.bind (·.getArr?.toOption)).getD #[]
      let de := ((v.getObjVal? "decoded").toOption.bind (·.getArr?.toOption)).getD #[]
      let exN := ex.map fun x => (natOf x).toOption
      let deN := de.map fun x => (natOf x).toOption
      let same := exN == deN && ex.size > 0
      let scale := ((objsJ.get? id).bind fun o => (jStr o "scale").toOption).getD "?"
      if !same then nUserBad := nUserBad + 1
      emit out (common ++ [("check", Json.str "user.decoded"), ("out", Json.str id),
        ("ok", Json.bool same), ("scale", Json.str scale),
        ("level", Json.num ((objs[id]?).map (·.level) |>.getD 0))])
  let _ := nUserBad
  pure (nOK, nBad)

end LattigoPin

def main (args : List String) : IO UInt32 := do
  match args with
  | outPath :: cases =>
    let out ← IO.FS.Handle.mk outPath .write
    let mut ok := 0
    let mut bad := 0
    for c in cases do
      try
        let (a, b) ← LattigoPin.runCase out c
        ok := ok + a; bad := bad + b
      catch e =>
        LattigoPin.emit out [("case", Json.str c), ("check", Json.str "load"), ("ok", Json.bool false),
          ("why", Json.str (toString e))]
        bad := bad + 1
    IO.println s!"cases {cases.length}: ok {ok}, not ok {bad}"
    pure (if bad = 0 then 0 else 1)
  | _ => IO.eprintln "usage: LattigoPin OUT.jsonl CASE.json..."; pure 2
