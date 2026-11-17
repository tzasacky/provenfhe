import FHE.Pin.ChecksUser
import FHE.Pin.Algo
import FHE.Pin.BFV.Run
import FHE.Pin.BFV.Algo

/-!
# openfhe_pin — run the trusted BGV definitions on exact data dumped from OpenFHE
(UNTRUSTED glue around trusted definitions; differential test harness)

    openfhe_pin [--threads K] [--chunks C] [--literal-max-n M] [--literal3-max-n M] [--literal-max-cost C]
                [--mutate NAME] [--only a,b,c,d,e,f,x,algo] [--with-algo] --out results.jsonl [--list FILE] CASEDIR…
                [--algo-mutate NAME] [--algo-only encrypt,lin,tensor,ks,modreduce] [--algo-literal-max-n M]
                [--variants-max-n M] [--library-max-n M] [--forced-max-n M] [--max-ks n] [--max-tensor n]

`--with-algo` adds the check family `algo.*` (`FHE.Pin.Algo`: the proved reference algorithms
against OpenFHE's outputs, limb by limb) to the selected groups; `--only algo` runs it alone.

A case whose `pin.json` has `"scheme": "BFV"` is checked by `FHE.Pin.BFV.runCase` (the trusted BFV
definitions; `--mutate` then takes a BFV mutant, `FHE.Pin.BFV.BMut.all`); every other case is a BGV
case and is checked exactly as before.

Each case directory is an `openfhe-pin/v1` dump (`harness/openfhe-pin/FORMAT.md`). One JSON object
per check is appended to the results file; exit code 1 iff some check has `"ok": false`.
See `harness/openfhe-pin/lean/README.md`.
-/

open Lean FHE.Pin Spec

def usage : String :=
  "usage: openfhe_pin [--threads K] [--chunks C] [--literal-max-n M] [--literal3-max-n M] [--literal-max-cost C]\n" ++
  "                   [--mutate NAME] [--only a,b,c,d,e,f,x,algo] [--with-algo] --out results.jsonl [--list FILE] CASEDIR...\n" ++
  "                   [--algo-mutate NAME] [--algo-only encrypt,lin,tensor,ks,modreduce] [--algo-literal-max-n M]\n" ++
  "                   [--variants-max-n M] [--library-max-n M] [--forced-max-n M] [--max-ks n] [--max-tensor n]\n" ++
  s!"mutants: {String.intercalate ", " (Mut.all.map (·.1))}\n" ++
  s!"algo mutants: {String.intercalate ", " (Algo.AMut.all.map (·.1))}\n" ++
  s!"BFV mutants (cases with \"scheme\": \"BFV\"): {String.intercalate ", " (FHE.Pin.BFV.BMut.all.map (·.name))}"

/-- Run every check group on one case; never throws. -/
def runCase (o : Opts) (bmu : FHE.Pin.BFV.BMut) (ao : Algo.Opts) (withAlgo : Bool) (dir : String) :
    IO (Array Json) := do
  let out ← IO.mkRef (#[] : Array Json)
  let fallbackName := ((trimDir dir : System.FilePath).fileName).getD dir
  let loadFail := fun (why : String) => do
    out.modify (·.push (Json.mkObj
      [("case", Json.str fallbackName), ("check", Json.str "load"), ("id", Json.str dir),
       ("op", Json.str "load"), ("ok", Json.bool false), ("impl", Json.str "glue"), ("why", Json.str why)]))
    out.get
  try
    let c ← match ← loadCase dir with
      | .ok c => pure c
      | .error e => return (← loadFail e)
    -- DISPATCH: a BFV case (`pin.json: "scheme": "BFV"`) runs the BFV checks and nothing else
    if jStr? c.pin "scheme" == some "BFV" then
      let lines ← FHE.Pin.BFV.runCase o bmu c dir
      -- BFV-ALGO CALL SITE: the bit-exact family `algo.*` of BFV (`FHE/Pin/BFV/Algo.lean`)
      if withAlgo || (o.only.getD []).contains "algo" then
        try return lines ++ (← FHE.Pin.BFV.Algo.runCase c { ao with K := o.K })
        catch e => return lines.push (Json.mkObj [("case", Json.str c.name),
          ("check", Json.str "algo.error"), ("ok", Json.bool false), ("why", Json.str s!"{e}")])
      return lines
    let special := c.special
    let fallbackP : FullParams :=
      { src := { kind := .bgv, N := c.N, qs := c.qs, t := c.t }
        store := { W := c.N, limbs := c.qs.map (⟨·, 0⟩), special := special.map (⟨·, 0⟩) }
        secretBound := 1
        inputNoise := Encrypt.freshNoise c.t (c.t - 1) (Encrypt.worstError c.N 1 39 1 39 39)
        keyNoise := c.t * 39
        outputNoise := 0 }
    let P := match c.inp with
      | .ok inp => inp.P
      | .error _ => fallbackP
    let some sName := jStr? c.pin "secret" | return (← loadFail "pin.json: secret")
    let s ← match c.intPoly sName with
      | .ok s => pure s
      | .error e => return (← loadFail e)
    let x : Cx := { c, o, P, s, out, keyCache := ← IO.mkRef {}, objCache := ← IO.mkRef {} }
    -- parameters of the program file against pin.json
    let paramsOK := P.src.N == c.N && P.src.t == c.t && P.src.qs == c.qs &&
      P.store.special.map (·.q) == c.special
    x.emit "load.params" "params" "load" (some paramsOK) "glue"
      [("progQs", Json.arr (P.src.qs.map natJ).toArray), ("pinQs", Json.arr (c.qs.map natJ).toArray),
       ("inputNoise", natJ P.inputNoise), ("keyNoise", natJ P.keyNoise),
       ("inputNoiseIsFreshWorst", boolJ (P.inputNoise == fallbackP.inputNoise)),
       ("keyNoiseIsT39", boolJ (P.keyNoise == fallbackP.keyNoise)),
       ("schemeParamsOK", boolJ (schemeParamsOK? P)), ("specialOK", boolJ (Budget.specialOK? P))]
    if !paramsOK then return (← out.get)
    match c.inp with
    | .ok _ => x.emit "load.prog" "prog.fhecheck.json" "load" (some true) "glue"
    | .error e =>
      x.emit "load.prog" "prog.fhecheck.json" "load" none "glue"
        [("why", Json.str s!"no program: {e}; checks b, e, f are not run")]
      -- group `x` (on unless `--only` leaves it out): the refusal must be an expected one
      if x.want "x" then checkRefusal x
    -- the declared bound of the stored plaintext of a fresh encryption (none: extractor refusal)
    let declBp : Option Nat := match c.inp with
      | .ok inp => some (match inp.fresh with | some fm => fm.bp c.t | none => c.t - 1)
      | .error _ => none
    if let some b := jObj? c.pin "build" then
      x.emit "info.build" "build" "info" none "glue" [("why", Json.str "information"), ("build", b),
        ("notes", Json.arr (jArr c.pin "notes"))]
    -- the secret as OpenFHE stores it
    if let some rn := jStr? c.pin "secretRns" then
      match c.polys[rn]? with
      | some e =>
        let ok := (List.range e.moduli.size).all fun i =>
          let q : Int := e.moduli[i]!
          e.limbs[i]! == s.map (· % q)
        x.emit "load.secret" rn "load" (some (ok && e.moduli.toList == c.qs.take e.moduli.size)) "glue"
          [("limbs", Json.num e.moduli.size)]
      | none => x.emit "load.secret" rn "load" (some false) "glue" [("why", Json.str "missing")]
    let guard := fun (g : String) (act : IO Unit) => do
      if x.want g then
        try act catch e => x.emit s!"{g}.error" "group" g (some false) "glue" [("why", Json.str s!"{e}")]
    let lay : Budget.KSLayout ← match c.inp with
      | .ok inp =>
        match FHE.Check.layoutOf P inp.ks with
        | .ok l => pure l
        | .error e =>
          x.emit "load.layout" "layout" "load" (some false) "glue" [("why", Json.str e)]
          pure (Budget.uniformLayout ((jNat? c.pin "towersPerDigit").getD 0) true)
      | .error _ => pure (Budget.uniformLayout ((jNat? c.pin "towersPerDigit").getD 0) true)
    guard "a" (checkA x)
    guard "c" (do checkC x declBp; checkPt x declBp)
    guard "d" (checkD x lay)
    match c.inp with
    | .ok inp =>
      if x.want "b" || x.want "e" || x.want "f" then
        let recs? ← try
            pure (some (← checkProg x inp lay))
          catch e =>
            x.emit "b.error" "program" "program" (some false) "glue" [("why", Json.str s!"{e}")]
            pure none
        -- b.user.*: what the user reads after Decode (FHE/Pin/ChecksUser.lean)
        if let some recs := recs? then
          if x.want "b" then
            try
              checkUser x inp fun v => (recs[v]?).map fun r =>
                { tainted := r.tainted, premiseBad := r.premiseBad, cost := r.cost }
            catch e => x.emit "b.user.error" "program" "program" (some false) "glue" [("why", Json.str s!"{e}")]
    | .error _ => pure ()
    guard "e" (checkModReduce x lay)
    guard "b" (checkNegate x)
    -- check family `algo.*` (FHE/Pin/Algo.lean: the proved reference algorithms, bit for bit,
    -- against OpenFHE's outputs). Opt-in: `--only …,algo`.
    if withAlgo || (o.only.getD []).contains "algo" then
      try
        let declLay : Option Budget.KSLayout := match c.inp with
          | .ok inp => (FHE.Check.layoutOf P inp.ks).toOption
          | .error _ => none
        let ls ← FHE.Pin.Algo.runCase c { ao with K := o.K } (some P) declLay
        out.modify (· ++ ls)
      catch e => x.emit "algo.error" "group" "algo" (some false) "glue" [("why", Json.str s!"{e}")]
    out.get
  catch e => loadFail s!"{e}"

structure Args where
  o : Opts := {}
  threads : Nat := 32
  chunks : Nat := 0
  out : Option String := none
  dirs : Array String := #[]
  /-- The mutant of the BFV checks (`--mutate` with a BFV name). -/
  bmu : FHE.Pin.BFV.BMut := {}
  /-- Options of the `algo.*` family (`FHE.Pin.Algo`). -/
  ao : Algo.Opts := {}
  withAlgo : Bool := false

partial def parseArgs : List String → Args → IO (Except String Args)
  | [], a => pure (.ok a)
  | "--threads" :: v :: r, a => parseArgs r { a with threads := max 1 v.toNat! }
  | "--chunks" :: v :: r, a => parseArgs r { a with chunks := v.toNat! }
  | "--literal-max-n" :: v :: r, a => parseArgs r { a with o := { a.o with litMaxN := v.toNat!, lit3MaxN := min a.o.lit3MaxN v.toNat! } }
  | "--literal3-max-n" :: v :: r, a => parseArgs r { a with o := { a.o with lit3MaxN := v.toNat! } }
  | "--literal-max-cost" :: v :: r, a => parseArgs r { a with o := { a.o with litCost := v.toNat! } }
  | "--mutate" :: v :: r, a =>
    -- a name may be a BGV mutant, a BFV mutant, or both (each applies to the cases of its scheme)
    match Mut.ofString? v, FHE.Pin.BFV.BMut.ofString? v with
    | some m, bm => parseArgs r { a with o := { a.o with mu := m, mutName := v }, bmu := bm.getD {} }
    | none, some bm => parseArgs r { a with bmu := bm }
    | none, none => pure (.error s!"unknown mutant {v}")
  | "--only" :: v :: r, a => parseArgs r { a with o := { a.o with only := some (v.splitOn ",") } }
  | "--out" :: v :: r, a => parseArgs r { a with out := some v }
  | "--with-algo" :: r, a => parseArgs r { a with withAlgo := true }
  | "--algo-mutate" :: v :: r, a =>
    match Algo.AMut.ofString? v with
    | some m => parseArgs r { a with ao := { a.ao with mu := m, mutName := v } }
    | none =>
      -- the BFV algo mutants (FHE/Pin/BFV/AlgoMutants.lean) are selected by name
      if (FHE.Pin.BFV.AlgoMut.ofString? v).isSome then parseArgs r { a with ao := { a.ao with mutName := v } }
      else pure (.error s!"unknown algo mutant {v}; known: {String.intercalate ", " (Algo.AMut.all.map (·.1) ++ FHE.Pin.BFV.AlgoMut.all.map (·.name))}")
  | "--algo-only" :: v :: r, a => parseArgs r { a with ao := { a.ao with only := some (v.splitOn ",") } }
  | "--algo-literal-max-n" :: v :: r, a => parseArgs r { a with ao := { a.ao with litMaxN := v.toNat! } }
  | "--library-max-n" :: v :: r, a => parseArgs r { a with ao := { a.ao with libMaxN := v.toNat! } }
  | "--forced-max-n" :: v :: r, a => parseArgs r { a with ao := { a.ao with forcedMaxN := v.toNat! } }
  | "--variants-max-n" :: v :: r, a => parseArgs r { a with ao := { a.ao with variantsMaxN := v.toNat! } }
  | "--max-ks" :: v :: r, a => parseArgs r { a with ao := { a.ao with maxKS := some v.toNat! } }
  | "--max-tensor" :: v :: r, a => parseArgs r { a with ao := { a.ao with maxTensor := some v.toNat! } }
  | "--list" :: v :: r, a => do
    let text ← IO.FS.readFile v
    let ds := (text.splitOn "\n").filter (fun l => !l.isEmpty)
    parseArgs r { a with dirs := a.dirs ++ ds.toArray }
  | v :: r, a =>
    if v.startsWith "--" then pure (.error s!"unknown option {v}")
    else parseArgs r { a with dirs := a.dirs.push v }

/-- `N` of a case, read from `pin.json` only (to schedule small cases in parallel). -/
def peekN (dir : String) : IO Nat := do
  try
    let text ← IO.FS.readFile ((dir : System.FilePath) / "pin.json")
    match Json.parse text with
    | .ok j => pure ((jNat? j "N").getD 0)
    | .error _ => pure 0
  catch _ => pure 0

def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "--help" then IO.println usage; return 4
  let a ← match ← parseArgs args {} with
    | .ok a => pure a
    | .error e => IO.eprintln s!"openfhe_pin: {e}\n{usage}"; return 4
  let some outPath := a.out | IO.eprintln usage; return 4
  let h ← IO.FS.Handle.mk outPath .write
  let counts ← IO.mkRef ({} : Std.HashMap String (Nat × Nat × Nat))
  let failed ← IO.mkRef (0 : Nat)
  let lock ← IO.mkRef ()   -- serialises output through `finish` (called from one thread at a time)
  let _ := lock
  let finish := fun (dir : String) (lines : Array Json) (ms : Nat) => do
    let mut okN := 0
    let mut failN := 0
    let mut nullN := 0
    let mut firstFail := ""
    let mut text := ""
    for l in lines do
      text := text ++ l.compress ++ "\n"
      let check := (jStr? l "check").getD "?"
      let st := match l.getObjVal? "ok" with
        | .ok (.bool true) => 0
        | .ok (.bool false) => 1
        | _ => 2
      if st == 0 then okN := okN + 1
      else if st == 1 then
        failN := failN + 1
        if firstFail.isEmpty then firstFail := s!"{check}:{(jStr? l "id").getD "?"}"
      else nullN := nullN + 1
      counts.modify fun m =>
        let (p, f, u) := m.getD check (0, 0, 0)
        m.insert check (if st == 0 then (p + 1, f, u) else if st == 1 then (p, f + 1, u) else (p, f, u + 1))
    h.putStr text
    h.flush
    failed.modify (· + failN)
    IO.println s!"{if failN == 0 then "ok  " else "FAIL"} {dir}: {okN} ok, {failN} FAIL, {nullN} unchecked, {ms} ms{if failN == 0 then "" else s!" (first: {firstFail})"}"
    (← IO.getStdout).flush
  -- Cases run in parallel workers, each case sequentially inside its worker (`K = chunks`,
  -- default 0: no tasks inside a case). Threads inside one case scale badly: the big integers of
  -- a case are shared between its tasks and every access is an atomic reference-count update.
  let next ← IO.mkRef (0 : Nat)
  let results ← IO.mkRef (#[] : Array (String × Array Json × Nat))
  let dirs := a.dirs
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun n => (n, n + 1)
      if i ≥ dirs.size then break
      let t0 ← IO.monoMsNow
      let lines ← runCase { a.o with K := a.chunks } a.bmu a.ao a.withAlgo dirs[i]!
      let t1 ← IO.monoMsNow
      results.modify (·.push (dirs[i]!, lines, t1 - t0))
  let nWorkers := min a.threads (max 1 dirs.size)
  let tasks ← (List.range nWorkers).mapM fun _ => IO.asTask worker (prio := .dedicated)
  -- drain results while the workers run
  let mut live := true
  while live do
    let done ← tasks.allM fun t => IO.hasFinished t
    let rs ← results.modifyGet fun r => (r, #[])
    for (d, lines, ms) in rs do finish d lines ms
    if done then
      let rs ← results.modifyGet fun r => (r, #[])
      for (d, lines, ms) in rs do finish d lines ms
      live := false
    else IO.sleep 20
  for t in tasks do
    if let .error e := t.get then IO.eprintln s!"openfhe_pin: worker failed: {e}"
  IO.println "--- summary (check: ok / FAIL / unchecked) ---"
  let cs := (← counts.get).toArray.qsort (fun x y => x.1 < y.1)
  for (k, (p, f, u)) in cs do
    IO.println s!"{k}: {p} / {f} / {u}"
  let nf ← failed.get
  IO.println s!"cases: {a.dirs.size}, failing checks: {nf}{if a.o.mu = .none then (if a.bmu.isNone then "" else s!" (BFV mutant {a.bmu.name})") else s!" (mutant {a.o.mutName})"}"
  return (if nf == 0 then 0 else 1)
