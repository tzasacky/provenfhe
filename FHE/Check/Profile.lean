import FHE.Check.Report
import FHE.Check.BFVReport
import FHE.Holes
import Challenge.Profile.Defs
import Challenge.CertifyBFV.Defs

/-!
# FHE.Check.Profile — `fhe_check --profile FILE` and `--emit-profile`   (UNTRUSTED glue)

**The profile mode.** The user declares an *implementation profile*: the budget every operation
of the program is claimed to meet (BGV: one `Spec.Trace.Budget`; BFV: one `Spec.TraceBFV.Budget`
for every instruction, or one per instruction). The verdict is CERTIFIED only when the locked
`Challenge.Profile.certifyProfile? P E prog sw` (BGV) or `Challenge.Profile.certifyBFVProfile? P E
prog` (BFV) accepts at the declared `E`, computed by the holes `FHE.Holes.certifyProfileFast`,
`certifyBFVProfileFast`, which are equal to them (`Challenge.Fast.Profile`), and whenever it does,
except that a frontend `expect` that disagrees with `Source.step` withholds it. No library, technique
table or layout enters the decision. The report adds whether the coverage check passes: the
locked `Challenge.Profile.coversBGV?` (run as it is; it does not read the program) or the
level-exact `Challenge.Profile.coversBFVAt?` (by the hole `FHE.Holes.coversBFVAtFast`), and the
conservative `Challenge.Profile.coversBFV?` (by `FHE.Holes.coversBFVFast`). The per-class lines
under it are diagnostics computed here; the "covered" claim is the Bool of the locked check.

**The profile file** (`fhe-check-profile/v1`; numbers are decimal strings or JSON integers):

    { "format": "fhe-check-profile/v1", "scheme": "BGV" | "BFV",
      "source": { ... printed only ... },
      -- BGV: one budget (`Spec.Trace.Budget`)
      "budget": { "keySwitch": n, "modSwitch": n, "modSwitchOne": n,
                  "modSwitchMany": { "default": n, "at": [ { "parts": k, "bound": n }, ... ] } },
      -- BFV: exactly one of
      "uniform": { "keySwitch": n, "modSwitch": n, "mulLift": n, "mulRound": n, "plainAdd": n },
      "perInstruction": { "budgets": [ {five numbers}, ... ], "at": [ i_0, ..., i_{n-1} ] },
      -- optional, for the coverage check only
      "coverage": { "keySwitching": { as in the program file },
                    "mulFamily": { "U": n, "r": n },     -- BFV; default U = 0, r = 1 (textbook)
                    "modSwitchParts": K } }              -- BGV; default: from the program

`modSwitchMany k` is the bound listed for `k` (k ≥ 3), else `default`. BFV `perInstruction`:
instruction `k` gets `budgets[at[k]]`; `at` has one entry per instruction of the body, and the
budget is `Challenge.CertifyBFV.budgetFn` of that array (the zero budget past the body), which is
how `certifyBFV?` stores the budget it computes: the profile `--emit-profile` writes for a BFV file
decodes to exactly the table mode's `c.budget`.
-/

namespace FHE.Check.Profile
open Lean Spec Spec.Source
open FHE.Noise.Fast (VMap)

def formatP : String := "fhe-check-profile/v1"

/-! ## The decoded profile -/

/-- The BGV budget with its finite description of `modSwitchMany`. -/
structure BGVProf where
  keySwitch : Nat
  modSwitch : Nat
  modSwitchOne : Nat
  manyDefault : Nat
  manyAt : List (Nat × Nat)

def BGVProf.budget (p : BGVProf) : Trace.Budget :=
  { keySwitch := p.keySwitch, modSwitch := p.modSwitch, modSwitchOne := p.modSwitchOne,
    modSwitchMany := fun k => ((p.manyAt.find? (·.1 == k)).map (·.2)).getD p.manyDefault }

inductive BFVProf
  | uniform (b : TraceBFV.Budget)
  /-- The distinct budgets, and the budget of every instruction (`budgets[at[k]]`). -/
  | perInstr (budgets : Array TraceBFV.Budget) (arr : Array TraceBFV.Budget)

/-- The per-instruction budget function (for `perInstr`: the locked `budgetFn` of the array). -/
def BFVProf.fn : BFVProf → (ℕ → TraceBFV.Budget)
  | .uniform b => fun _ => b
  | .perInstr _ arr => Challenge.CertifyBFV.budgetFn arr

structure Coverage where
  ks : Option KsConfig := none
  U : Nat := 0
  r : Nat := 1
  K : Option Nat := none

inductive Body
  | bgv (p : BGVProf)
  | bfv (p : BFVProf)

structure Prof where
  body : Body
  cov : Coverage := {}
  source : Json := Json.null

/-! ## Decoding -/

def budgetBFVOf (ctx : String) (j : Json) : DecodeM TraceBFV.Budget := do
  onlyKeys ctx j ["keySwitch", "modSwitch", "mulLift", "mulRound", "plainAdd"]
  return { keySwitch := ← natField ctx j "keySwitch", modSwitch := ← natField ctx j "modSwitch",
           mulLift := ← natField ctx j "mulLift", mulRound := ← natField ctx j "mulRound",
           plainAdd := ← natField ctx j "plainAdd" }

def decodeKs (ctx : String) (ksj : Json) : DecodeM KsConfig := do
  onlyKeys ctx ksj ["method", "variant", "digits", "source", "technique"]
  let method ← strField ctx ksj "method"
  unless method == "hybrid" do
    throw s!"{ctx}.method: \"{method}\": the coverage check knows hybrid (RNS digit) key switching only"
  let variant ← match ← strField ctx ksj "variant" with
    | "centred" => pure KsVariant.centred
    | "openfhe" => pure .openfhe
    | "canonical" => pure .canonical
    | v => throw s!"{ctx}.variant: \"{v}\" (centred | canonical | openfhe)"
  let digits ← decodeDigits s!"{ctx}.digits" (← field ctx ksj "digits")
  return { variant, digits }

/-- Decode a profile file; `scheme` must be the program's. -/
def decode (j : Json) : DecodeM Prof := do
  let fmt ← strField "profile" j "format"
  unless fmt == formatP do throw s!"profile.format: \"{fmt}\" is not {formatP}"
  let scheme ← strField "profile" j "scheme"
  let cov ← match field? j "coverage" with
    | none => pure ({} : Coverage)
    | some cj => do
      onlyKeys "profile.coverage" cj ["keySwitching", "mulFamily", "modSwitchParts"]
      let ks ← (field? cj "keySwitching").mapM (decodeKs "profile.coverage.keySwitching")
      let (U, r) ← match field? cj "mulFamily" with
        | none => pure (0, 1)
        | some mj => do
          onlyKeys "profile.coverage.mulFamily" mj ["U", "r"]
          pure (← natField "profile.coverage.mulFamily" mj "U",
                ← natField "profile.coverage.mulFamily" mj "r")
      let K ← (field? cj "modSwitchParts").mapM (asNat "profile.coverage.modSwitchParts")
      if scheme == "BGV" && (field? cj "mulFamily").isSome then
        throw "profile.coverage.mulFamily: a BFV field (the BGV coverage check has no multiplication family: the BGV tensor product is exact)"
      if scheme == "BFV" && K.isSome then
        throw "profile.coverage.modSwitchParts: a BGV field (the BFV coverage check reads two-component modulus switches only)"
      pure { ks, U, r, K }
  let source := (field? j "source").getD Json.null
  match scheme with
  | "BGV" =>
    onlyKeys "profile" j ["format", "scheme", "source", "budget", "coverage"]
    let b ← field "profile" j "budget"
    onlyKeys "profile.budget" b ["keySwitch", "modSwitch", "modSwitchOne", "modSwitchMany"]
    let mj ← field "profile.budget" b "modSwitchMany"
    onlyKeys "profile.budget.modSwitchMany" mj ["default", "at"]
    let dflt ← natField "profile.budget.modSwitchMany" mj "default"
    let at_ ← match field? mj "at" with
      | none => pure []
      | some a => do
        (← asArr "profile.budget.modSwitchMany.at" a).toList.mapIdxM fun i e => do
          let c := s!"profile.budget.modSwitchMany.at[{i}]"
          onlyKeys c e ["parts", "bound"]
          let k ← natField c e "parts"
          if k < 3 then
            throw s!"{c}.parts: {k}; modSwitchMany is read only at k >= 3 components (k = 1: modSwitchOne, k = 2: modSwitch)"
          pure (k, ← natField c e "bound")
    if let some k := (at_.map (·.1)).find? fun k => (at_.filter (·.1 == k)).length > 1 then
      throw s!"profile.budget.modSwitchMany.at: parts = {k} is listed more than once"
    return { body := .bgv { keySwitch := ← natField "profile.budget" b "keySwitch",
                            modSwitch := ← natField "profile.budget" b "modSwitch",
                            modSwitchOne := ← natField "profile.budget" b "modSwitchOne",
                            manyDefault := dflt, manyAt := at_ },
             cov, source }
  | "BFV" =>
    onlyKeys "profile" j ["format", "scheme", "source", "uniform", "perInstruction", "coverage"]
    match field? j "uniform", field? j "perInstruction" with
    | some u, none => return { body := .bfv (.uniform (← budgetBFVOf "profile.uniform" u)), cov, source }
    | none, some pj =>
      onlyKeys "profile.perInstruction" pj ["budgets", "at"]
      let bs ← (← asArr "profile.perInstruction.budgets" (← field "profile.perInstruction" pj "budgets")).mapIdxM
        fun i b => budgetBFVOf s!"profile.perInstruction.budgets[{i}]" b
      let at_ ← (← asArr "profile.perInstruction.at" (← field "profile.perInstruction" pj "at")).mapIdxM
        fun i e => asNat s!"profile.perInstruction.at[{i}]" e
      if let some k := at_.findIdx? (· ≥ bs.size) then
        throw s!"profile.perInstruction.at[{k}] = {at_[k]!}: there are only {bs.size} budgets"
      return { body := .bfv (.perInstr bs (at_.map fun i => bs.getD i (Spec.BudgetBFV.budgetOf 0 0 0 0 0))),
               cov, source }
    | some _, some _ => throw "profile: both uniform and perInstruction; give exactly one"
    | none, none => throw "profile: a BFV profile needs uniform (one budget for every instruction) or perInstruction"
  | s => throw s!"profile.scheme: \"{s}\" (BGV | BFV)"

/-! ## Encoding -/

def nj (n : Nat) : Json := Json.str (toString n)

def budgetBFVJson (b : TraceBFV.Budget) : Json :=
  Json.mkObj [("keySwitch", nj b.keySwitch), ("modSwitch", nj b.modSwitch),
              ("mulLift", nj b.mulLift), ("mulRound", nj b.mulRound), ("plainAdd", nj b.plainAdd)]

def budgetBGVJson (p : BGVProf) : Json :=
  Json.mkObj [("keySwitch", nj p.keySwitch), ("modSwitch", nj p.modSwitch),
              ("modSwitchOne", nj p.modSwitchOne),
              ("modSwitchMany", Json.mkObj [("default", nj p.manyDefault),
                ("at", Json.arr (p.manyAt.map fun (k, v) =>
                  Json.mkObj [("parts", toJson k), ("bound", nj v)]).toArray)])]

def budgetEq (a b : TraceBFV.Budget) : Bool :=
  a.keySwitch == b.keySwitch && a.modSwitch == b.modSwitch && a.mulLift == b.mulLift &&
    a.mulRound == b.mulRound && a.plainAdd == b.plainAdd

/-- The distinct budgets of a list, and the index of each entry (first occurrence order). -/
def tabulate (bs : List TraceBFV.Budget) : Array TraceBFV.Budget × Array Nat := Id.run do
  let key := fun (b : TraceBFV.Budget) => (b.keySwitch, b.modSwitch, b.mulLift, b.mulRound, b.plainAdd)
  let mut idx : Std.HashMap (Nat × Nat × Nat × Nat × Nat) Nat := {}
  let mut tbl : Array TraceBFV.Budget := #[]
  let mut at_ : Array Nat := #[]
  for b in bs do
    match idx[key b]? with
    | some i => at_ := at_.push i
    | none =>
      idx := idx.insert (key b) tbl.size
      at_ := at_.push tbl.size
      tbl := tbl.push b
  return (tbl, at_)

/-! ## Replays on all-zero messages (diagnostics, and the defaults of the coverage check) -/

/-- What a replay of `Source.step` on all-zero messages (search trees) sees: per instruction the
level and parts of its first operand (if defined), and the final environment. Stops at the first
instruction `Source.step` rejects. -/
structure ZeroRun (Pr : Params) where
  opLevel : Array (Option Nat) := #[]
  opParts : Array (Option Nat) := #[]
  final : VMap (Val Pr) := ∅
  stoppedAt : Option Nat := none

def zeroRun (Pr : Params) (prog : Program) : ZeroRun Pr := Id.run do
  let mut ρ : VMap (Val Pr) := FHE.Noise.Fast.initEnvMap Pr prog
  let mut r : ZeroRun Pr := {}
  let mut idx := 0
  for i in prog.body do
    let a := Challenge.CertifyBFV.operand i
    let v := ρ[a]?
    r := { r with opLevel := r.opLevel.push (v.map (·.level)), opParts := r.opParts.push (v.map (·.parts)) }
    let m := ρ
    match step Pr (fun x => m[x]?) i with
    | some ρ' =>
      match ρ' (Trace.dst i) with
      | some w => ρ := ρ.insert (Trace.dst i) w
      | none => return { r with final := ρ, stoppedAt := some idx }
    | none => return { r with final := ρ, stoppedAt := some idx }
    idx := idx + 1
  return { r with final := ρ }

/-- The numbers of components of the operands of the modulus switches the replay reaches. -/
def msParts {Pr : Params} (prog : Program) (z : ZeroRun Pr) : List Nat := Id.run do
  let mut out : List Nat := []
  let mut k := 0
  for i in prog.body do
    if let .modSwitch .. := i then
      if let some (some p) := z.opParts[k]? then
        unless out.contains p do out := p :: out
    k := k + 1
  return out.mergeSort

/-! ## `--emit-profile` -/

/-- The profile the OpenFHE-table mode computes for a BGV file: `Spec.Budget.certified P lay`, with
`modSwitchMany` listed at the numbers of components `k ≥ 3` the program switches. -/
def emitBGV (inp : FHE.Check.Input) : Except String Json := do
  let lay ← layoutOf inp.P inp.ks
  let E := Spec.Budget.certified inp.P lay
  let ks := (msParts inp.prog (zeroRun inp.P.src inp.prog)).filter (3 ≤ ·)
  let at_ := ks.map fun k => (k, E.modSwitchMany k)
  let dflt := (at_.map (·.2)).foldl max (E.modSwitchMany 3)
  let p : BGVProf := { keySwitch := E.keySwitch, modSwitch := E.modSwitch,
                       modSwitchOne := E.modSwitchOne, manyDefault := dflt, manyAt := at_ }
  let ksj : Json := Json.mkObj [("method", "hybrid"),
    ("variant", match inp.ks.variant with
      | .centred => "centred" | .openfhe => "openfhe" | .canonical => "canonical"),
    ("digits", match inp.ks.digits with
      | .consecutive a => Json.mkObj [("kind", "consecutive"), ("towersPerDigit", toJson a)]
      | .explicit pl => Json.mkObj [("kind", "explicit"),
          ("perLevel", Json.mkObj (pl.map fun (l, ds) => (toString l, toJson ds)))])]
  return Json.mkObj [("format", formatP), ("scheme", "BGV"),
    ("source", Json.mkObj [("tool", "fhe_check --emit-profile"),
      ("what", "the budget the OpenFHE-table mode computes for this file: Spec.Budget.certified P lay (hybrid key switching on the file's layout, the centred t-corrected modulus switch); modSwitchMany is msBudgetAt P k, listed at the numbers of components k >= 3 the program switches, and repeated as the default")]),
    ("budget", budgetBGVJson p),
    ("coverage", Json.mkObj [("keySwitching", ksj)])]

/-- The profile the OpenFHE-table mode computes for a BFV file: the locked
`Challenge.CertifyBFV.budgetsBFV x` (by `FHE.Noise.FastBFV.budgets`, equal to it:
`Validation.FastBFV.budgets_eq`), one budget per instruction. -/
def emitBFV (inp : BFV.Input) : Except String Json := do
  let lay ← layoutOf inp.base.P inp.base.ks
  let x := BFV.inputBFV inp lay
  -- `budgetsBFV` stops at the first instruction `Source.step` rejects; `budgetFn` reads the zero
  -- budget past its end, so the zero budget is written there (the same function)
  let bs := FHE.Noise.FastBFV.budgets x
  let n := inp.base.prog.body.length
  let (tbl, at_) := tabulate (bs ++ List.replicate (n - bs.length) (Spec.BudgetBFV.budgetOf 0 0 0 0 0))
  let ksj : Json := Json.mkObj [("method", "hybrid"),
    ("variant", match inp.base.ks.variant with
      | .centred => "centred" | .openfhe => "openfhe" | .canonical => "canonical"),
    ("digits", match inp.base.ks.digits with
      | .consecutive a => Json.mkObj [("kind", "consecutive"), ("towersPerDigit", toJson a)]
      | .explicit pl => Json.mkObj [("kind", "explicit"),
          ("perLevel", Json.mkObj (pl.map fun (l, ds) => (toString l, toJson ds)))])]
  return Json.mkObj [("format", formatP), ("scheme", "BFV"),
    ("source", Json.mkObj [("tool", "fhe_check --emit-profile"),
      ("what", "the per-instruction budget the OpenFHE-table mode computes for this file: Challenge.CertifyBFV.budgetsBFV (the declared technique's slacks, hybrid key switching on the file's layout at each operand's level, the rounding modulus switch, the declared plaintext addition)")]),
    ("perInstruction", Json.mkObj [("budgets", Json.arr (tbl.map budgetBFVJson)),
                                   ("at", Json.arr (at_.map toJson))]),
    ("coverage", Json.mkObj [("keySwitching", ksj),
      ("mulFamily", Json.mkObj [("U", toJson (0 : Nat)), ("r", toJson (1 : Nat))])])]

/-! ## The check -/

structure Res where
  verdict : Verdict
  headline : String
  lines : List String := []
  json : List (String × Json) := []

def layoutName (ks : KsConfig) : String :=
  let v := match ks.variant with | .centred => "centred" | .openfhe => "openfhe" | .canonical => "canonical"
  match ks.digits with
  | .consecutive a => s!"hybrid, {v} digits, {a} limb(s) per digit"
  | .explicit _ => s!"hybrid, {v} digits, explicit per-level digits"

def uncoveredSentence : String :=
  "Acceptance at a profile that is not covered is a CONDITIONAL statement: every run in which each instruction meets its contract within the declared budget ends in outputs that decrypt correctly. It does not say that any implementation stays within the declared budget; nothing here shows that one does."

def coveredTail : String :=
  "these algorithm families meet the contract of every instruction of this program within the declared budget, for every secret within params.secretBound and keys meeting Spec.Budget.GadgetKeysOK (hypotheses of the realizability statements)."

/-- The coverage half of the verdict line, from the coverage JSON. -/
def coverageClause (cov : Json) : String :=
  match cov.getObjValAs? Bool "checked", cov.getObjValAs? Bool "covered" with
  | .ok true, .ok true => "the profile IS covered by the proved algorithm families (COVERAGE below)"
  | .ok true, .ok false => "the profile is NOT covered by the proved algorithm families, so this is a conditional statement about implementations that meet the profile, not a claim that one exists (COVERAGE below)"
  | _, _ => "coverage was not checked, so this is a conditional statement about implementations that meet the profile, not a claim that one exists (COVERAGE below)"

/-- A numbered line. -/
def need (what : String) (needed declared : Nat) : String :=
  s!"{what}: needs {needed} ({pow2 needed}), declared {declared} ({pow2 declared})"

/-! ### BGV -/

def checkBGV (inp : FHE.Check.Input) (pf : Prof) (p : BGVProf) : Res := Id.run do
  let P := inp.P
  let prog := inp.prog
  let E := p.budget
  let sw := inp.decryption == .switched
  -- THE VERDICT: the hole, equal to the locked `certifyProfile?` (`certifyProfileFast_eq`)
  let cert := FHE.Holes.certifyProfileFast P E prog sw
  let z := zeroRun P.src prog
  let (steps, _) := replay P E prog
  let mism := inp.expects.filterMap fun e =>
    match steps[e.idx]? with
    | some s =>
      if s.ill.isNone && ((e.level.isSome && e.level != some s.level) || (e.parts.isSome && e.parts != some s.parts)) then
        some s!"body[{e.idx}] ({e.dst}): the frontend says level {e.level.getD 0}, parts {e.parts.getD 0}; Source.step gives level {s.level}, parts {s.parts}"
      else none
    | none => none
  -- coverage (locked `coversBGV?`, run directly)
  let ks := pf.cov.ks.getD inp.ks
  let covLines : List String × Json := match layoutOf P ks with
    | .error e => ([s!"COVERAGE: not checked: the key-switching layout is unusable ({e})"],
                   Json.mkObj [("checked", false), ("why", e)])
    | .ok lay =>
      -- at least the largest number of components the program switches (so that the coverage
      -- line is about every modulus switch of this program); a declared larger K is kept
      let K := max (pf.cov.K.getD 0) ((msParts prog z).foldl max 2)
      let covered := Challenge.Profile.coversBGV? P lay K E
      let fams := s!"hybrid key switching ({layoutName ks}), the centred t-corrected modulus switch of 1..{K} components"
      let L := P.src.qs.length
      let side := [("Spec.schemeParamsOK?", Spec.schemeParamsOK? P), ("scheme BGV", decide (P.src.kind = .bgv)),
                   ("Spec.Budget.specialOK?", Spec.Budget.specialOK? P),
                   ("layout usable at levels 1..L", (List.range L).all fun j => lay.okAt (j + 1))]
      let ksNeed := ((List.range L).map fun j => Spec.Budget.ksBoundAt P lay (j + 1)).foldl max 0
      let msRows := (List.range K).map fun j =>
        (j + 1, Spec.Budget.msBudgetAt P (j + 1), E.modSwitchAt (j + 1))
      let cls := [s!"  side conditions: " ++ ", ".intercalate (side.map fun (n, b) => s!"{n} {if b then "passed" else "FAILS"}"),
                  s!"  key switching ({if ksNeed ≤ E.keySwitch then "covered" else "NOT covered"}): " ++
                    need "max over levels 1..L of Spec.Budget.ksBoundAt" ksNeed E.keySwitch] ++
                  msRows.map fun (k, nd, dc) =>
                    s!"  modulus switch of {k} component(s) ({if nd ≤ dc then "covered" else "NOT covered"}): " ++
                      need "Spec.Budget.msBudgetAt" nd dc
      let diagAll := side.all (·.2) && ksNeed ≤ E.keySwitch && msRows.all fun (_, nd, dc) => nd ≤ dc
      let head := if covered then
          s!"COVERAGE: the profile IS covered by the proved families (Challenge.Profile.coversBGV? = true, families: {fams}): " ++ coveredTail
        else s!"COVERAGE: the profile is NOT covered by the proved families (Challenge.Profile.coversBGV? = false, families checked: {fams}). " ++ uncoveredSentence
      let internal := if diagAll != covered then ["INTERNAL: the per-class diagnostic disagrees with coversBGV?; the coverage line above is the locked check's"] else []
      (head :: cls ++ internal,
       Json.mkObj [("checked", true), ("check", "Challenge.Profile.coversBGV?"), ("covered", covered),
         ("family", Json.mkObj [("keySwitching", layoutName ks), ("modSwitchParts", toJson K)]),
         ("keySwitchNeeded", nj ksNeed),
         ("modSwitchNeeded", Json.arr (msRows.map fun (k, nd, _) => Json.mkObj [("parts", toJson k), ("bound", nj nd)]).toArray)])
  let budgetLines := [s!"Declared profile (BGV, Spec.Trace.Budget): keySwitch = {p.keySwitch} ({pow2 p.keySwitch}), modSwitch = {p.modSwitch} ({pow2 p.modSwitch}), modSwitchOne = {p.modSwitchOne} ({pow2 p.modSwitchOne}), modSwitchMany = {p.manyAt.map fun (k, v) => s!"{k}: {v}"} else {p.manyDefault}"]
  let notes := (securityWarning P).toList ++ [
    s!"ASSUMPTION: every input ciphertext has noise at most params.inputNoise = {P.inputNoise} ({pow2 P.inputNoise}) (and its declared bound, if smaller); in profile mode freshEncryption, --kappa, the modSwitch.method and the scaling section are not read.",
    "NOT COVERED by this verdict: the library's own decryption routine and user-level decoding (the statement is about textbook decryption " ++
      (if sw then "after switching to one limb" else "at the output's level") ++ "), and the library's key generation."]
  let theorems := [
    "Challenge.Profile.certifyProfile?_sound: if certifyProfile? accepts at E, for every secret s, all messages and all inputs within their bounds, every output of every run in which each instruction meets its contract within E decrypts with s to what the program computes, with noise at most its own bound",
    "Challenge.Fast.certifyProfileFast_eq: the function fhe_check runs, FHE.Holes.certifyProfileFast, returns exactly what Challenge.Profile.certifyProfile? returns, at every budget",
    "Challenge.Profile.coversBGV?_relin, _keySwitch, _modSwitch: when coversBGV? passes, the named families meet the contracts within E"]
  match cert with
  | some (B, outs) =>
    if !mism.isEmpty then
      return { verdict := .notCertified,
               headline := "the frontend and the verified semantics disagree on the program's shape, so the certificate is withheld",
               lines := mism ++ budgetLines ++ covLines.1 }
    let outLines := outs.map fun (o, b) =>
      let lvl := ((z.final[o]?).map (·.level)).getD 0
      let Q := P.src.modulus lvl
      s!"  {o}: noise <= {b} ({pow2 b}), level {lvl}, Q/2 = {pow2 (Q / 2)}, margin {fmt2 (log2F (Q / 2) - log2F b)} bits"
    { verdict := .certified,
      headline := "for every implementation within the declared profile (Challenge.Profile.certifyProfile? accepts at the declared budget); " ++ coverageClause covLines.2,
      lines := covLines.1 ++ [""] ++ budgetLines ++ [s!"Whole-program bound: {B} ({pow2 B})", "Outputs:"] ++ outLines ++ [""] ++ notes ++ [""] ++ ["Theorems:"] ++ theorems.map ("  " ++ ·),
      json := [("bound", nj B), ("outputs", Json.arr (outs.map fun (o, b) => Json.mkObj [("name", o), ("bound", nj b)]).toArray),
               ("coverage", covLines.2), ("profile", budgetBGVJson p)] }
  | none =>
    let why := Id.run do
      if !Spec.schemeParamsOK? P then return "Spec.schemeParamsOK? = false"
      match steps.back? with
      | some s =>
        if let some w := s.ill then return s!"body[{s.idx}] ({instrStr s.instr}) is rejected: {w}"
        if 2 * s.bound ≥ s.Q then
          return s!"the noise bound overflows at body[{s.idx}] ({instrStr s.instr}): 2*B >= Q at level {s.level} (B = {pow2 s.bound}, Q = {pow2 s.Q})"
        return "an output check failed (an output not under the original key, missing, or not decrypting after the switch to one limb)"
      | none => return "an output check failed"
    { verdict := .notCertified,
      headline := s!"at the declared profile: {why}",
      lines := budgetLines ++ covLines.1 ++ [""] ++ notes,
      json := [("coverage", covLines.2), ("profile", budgetBGVJson p),
               ("failedAt", match steps.back? with
                 | some s => if s.ill.isSome || 2 * s.bound ≥ s.Q then toJson s.idx else Json.null
                 | none => Json.null)] }

/-! ### BFV -/

def checkBFV (inp : BFV.Input) (pf : Prof) (p : BFVProf) : Res := Id.run do
  let P := inp.base.P
  let prog := inp.base.prog
  let n := prog.body.length
  if let .perInstr _ at_ := p then
    if at_.size != n then
      return { verdict := .invalid,
               headline := s!"profile.perInstruction.at has {at_.size} entries; the program has {n} instructions (one budget per instruction)" }
  -- the array of `perInstruction` is built by the decoder
  let E : ℕ → TraceBFV.Budget := match p with
    | .uniform b => fun _ => b
    | .perInstr _ arr => Challenge.CertifyBFV.budgetFn arr
  -- THE VERDICT: the hole, equal to the locked `certifyBFVProfile?` (`certifyBFVProfileFast_eq`)
  let cert := FHE.Holes.certifyBFVProfileFast P E prog
  let z := zeroRun P.src prog
  let steps := BFV.replay P E prog
  let mism := inp.base.expects.filterMap fun e =>
    match steps[e.idx]? with
    | some s =>
      if s.ill.isNone && ((e.level.isSome && e.level != some s.level) || (e.parts.isSome && e.parts != some s.parts)) then
        some s!"body[{e.idx}] ({e.dst}): the frontend says level {e.level.getD 0}, parts {e.parts.getD 0}; Source.step gives level {s.level}, parts {s.parts}"
      else none
    | none => none
  let ks := pf.cov.ks.getD inp.base.ks
  let (U, r) := (pf.cov.U, pf.cov.r)
  let covLines : List String × Json := match layoutOf P ks with
    | .error e => ([s!"COVERAGE: not checked: the key-switching layout is unusable ({e})"],
                   Json.mkObj [("checked", false), ("why", e)])
    | .ok lay => Id.run do
      -- the locked checks, by the holes equal to them
      let at_ := FHE.Holes.coversBFVAtFast P lay U r prog E
      let cons := FHE.Holes.coversBFVFast P lay U r prog.body E
      let fams := s!"multiplication lifting [c]_Q + Q*u with |u| <= U = {U} and rounding within r/2, r = {r} (Challenge.BFVMul.stepOK_mul_approx; U = 0, r = 1 is the textbook multiplication), hybrid key switching ({layoutName ks}), the rounding modulus switch"
      let L := P.src.qs.length
      let side := [("Spec.schemeParamsOK?", Spec.schemeParamsOK? P), ("scheme BFV", decide (P.src.kind = .bfv)),
                   ("Spec.Budget.specialOK?", Spec.Budget.specialOK? P),
                   ("layout usable at levels 1..L", (List.range L).all fun j => lay.okAt (j + 1))]
      let ml := Spec.BudgetBFV.mulLiftApprox P U
      let mr := Spec.BudgetBFV.mulRoundApprox P r
      let ms := Spec.BudgetBFV.msBudget P
      -- per class: the first instruction (in the replay) whose budget is below the family's need
      let mut mulBad : Option String := none
      let mut ksBad : Option String := none
      let mut msBad : Option String := none
      let mut nMul := 0
      let mut nKs := 0
      let mut nMs := 0
      let stop := z.stoppedAt.getD n
      let mut k := 0
      for i in prog.body do
        if k > stop then break
        let Ek := E k
        match i with
        | .mul .. | .square .. =>
          nMul := nMul + 1
          if mulBad.isNone && !(ml ≤ Ek.mulLift && mr ≤ Ek.mulRound) then
            mulBad := some (s!"body[{k}] ({instrStr i}): " ++ need "mulLift = mulLiftApprox P U" ml Ek.mulLift ++ "; " ++ need "mulRound = mulRoundApprox P r" mr Ek.mulRound)
        | .relin .. | .keySwitch .. =>
          nKs := nKs + 1
          let ℓ := (z.opLevel[k]?.getD none).getD 0
          let nd := Spec.BudgetBFV.ksBoundAt P lay ℓ
          if ksBad.isNone && !(nd ≤ Ek.keySwitch) then
            ksBad := some (s!"body[{k}] ({instrStr i}, operand at level {ℓ}): " ++ need "Spec.BudgetBFV.ksBoundAt at that level" nd Ek.keySwitch)
        | .modSwitch .. =>
          nMs := nMs + 1
          if msBad.isNone && !(ms ≤ Ek.modSwitch) then
            msBad := some (s!"body[{k}] ({instrStr i}): " ++ need "Spec.BudgetBFV.msBudget" ms Ek.modSwitch)
        | _ => pure ()
        k := k + 1
      let clsLine := fun (name : String) (cnt : Nat) (bad : Option String) =>
        if cnt == 0 then s!"  {name}: none in the program"
        else match bad with
          | none => s!"  {name} ({cnt}): covered"
          | some b => s!"  {name} ({cnt}): NOT covered, first at {b}"
      let cls := [s!"  side conditions: " ++ ", ".intercalate (side.map fun (n, b) => s!"{n} {if b then "passed" else "FAILS"}"),
                  clsLine "mul/square" nMul mulBad, clsLine "relin/keySwitch (at the operand's level)" nKs ksBad,
                  clsLine "modSwitch" nMs msBad]
      let diagAll := side.all (·.2) && mulBad.isNone && ksBad.isNone && msBad.isNone
      let head := if at_ then
          s!"COVERAGE: the profile IS covered by the proved families, level by level (Challenge.Profile.coversBFVAt? = true; families: {fams}): " ++ coveredTail
        else s!"COVERAGE: the profile is NOT covered by the proved families (Challenge.Profile.coversBFVAt? = false; families checked: {fams}). " ++ uncoveredSentence
      let consLine := s!"  conservative check, key switching charged at every level of the chain (Challenge.Profile.coversBFV?): {if cons then "passes" else "fails"}"
      let internal := if diagAll != at_ then ["INTERNAL: the per-class diagnostic disagrees with coversBFVAt?; the coverage line above is the locked check's"] else []
      return (head :: cls ++ [consLine] ++ internal,
       Json.mkObj [("checked", true), ("check", "Challenge.Profile.coversBFVAt?"), ("covered", at_),
         ("coversBFV", cons),
         ("family", Json.mkObj [("keySwitching", layoutName ks), ("U", toJson U), ("r", toJson r)]),
         ("classes", Json.mkObj [("mul", toJson (mulBad.isNone)), ("keySwitch", toJson ksBad.isNone), ("modSwitch", toJson msBad.isNone)])])
  let maxOf := fun (f : TraceBFV.Budget → Nat) => ((List.range n).map fun k => f (E k)).foldl max 0
  let budgetLines := [match p with
    | .uniform b => s!"Declared profile (BFV, one budget for every instruction): keySwitch = {pow2 b.keySwitch}, modSwitch = {pow2 b.modSwitch}, mulLift = {pow2 b.mulLift}, mulRound = {pow2 b.mulRound}, plainAdd = {pow2 b.plainAdd}"
    | .perInstr bs _ => s!"Declared profile (BFV, one budget per instruction, {bs.size} distinct): largest keySwitch = {pow2 (maxOf (·.keySwitch))}, modSwitch = {pow2 (maxOf (·.modSwitch))}, mulLift = {pow2 (maxOf (·.mulLift))}, mulRound = {pow2 (maxOf (·.mulRound))}, plainAdd = {pow2 (maxOf (·.plainAdd))}"]
  let notes := (securityWarning P).toList ++ [
    s!"ASSUMPTION: every input ciphertext has noise at most params.inputNoise = {P.inputNoise} ({pow2 P.inputNoise}) (or its declared bound); in profile mode freshEncryption, --kappa, the bfv section (technique, internal drops, plaintext-addition method) and the modSwitch.method are not read.",
    "NOT COVERED by this verdict: the library's own decryption routine (the statement is about textbook BFV decryption at the output's level, Spec.Scheme.bfvDecrypt) and the library's key generation."]
  let theorems := [
    "Challenge.Profile.certifyBFVProfile?_sound: if certifyBFVProfile? accepts at E, for every secret s, all messages and all inputs within their bounds, every output of every run in which instruction k meets its contract within E k is under s, decrypts with s to what the program computes, and has noise at most its own bound",
    "Challenge.Fast.certifyBFVProfileFast_eq: the function fhe_check runs, FHE.Holes.certifyBFVProfileFast, returns exactly what Challenge.Profile.certifyBFVProfile? returns, at every per-instruction budget",
    "Challenge.Fast.coversBFVAtFast_eq, coversBFVFast_eq: the coverage checks fhe_check runs are the locked coversBFVAt?, coversBFV?",
    "Challenge.Profile.coversBFVAt?_mul, _square, _relin, _keySwitch, _modSwitch: when coversBFVAt? passes, the named families meet the contract of instruction k within E k"]
  let profJson : Json := match p with
    | .uniform b => Json.mkObj [("uniform", budgetBFVJson b)]
    | .perInstr bs at_ => Json.mkObj [("distinctBudgets", toJson bs.size), ("instructions", toJson at_.size)]
  match cert with
  | some (B, outs) =>
    if !mism.isEmpty then
      return { verdict := .notCertified,
               headline := "the frontend and the verified semantics disagree on the program's shape, so the certificate is withheld",
               lines := mism ++ budgetLines ++ covLines.1 }
    let outLines := outs.map fun (o, b) =>
      let lvl := ((z.final[o]?).map (·.level)).getD 0
      let Q := P.src.modulus lvl
      s!"  {o}: noise <= {b} ({pow2 b}), level {lvl}, log2 Q = {fmt2 (log2F Q)}"
    { verdict := .certified,
      headline := "for every implementation within the declared profile (Challenge.Profile.certifyBFVProfile? accepts at the declared per-instruction budget); " ++ coverageClause covLines.2,
      lines := covLines.1 ++ [""] ++ budgetLines ++ [s!"Whole-program bound: {B} ({pow2 B})", "Outputs:"] ++ outLines ++ [""] ++ notes ++ [""] ++ ["Theorems:"] ++ theorems.map ("  " ++ ·),
      json := [("bound", nj B), ("outputs", Json.arr (outs.map fun (o, b) => Json.mkObj [("name", o), ("bound", nj b)]).toArray),
               ("coverage", covLines.2), ("profile", profJson)] }
  | none =>
    let failed := steps.toList.find? (·.failed)
    let why := Id.run do
      if !Spec.schemeParamsOK? P then return "Spec.schemeParamsOK? = false"
      if !Challenge.Profile.inputsDecOK P prog then return "a declared input ciphertext bound does not pass the decryption condition at its level"
      if !decide (P.src.t - 1 ≤ P.src.qs.headD 0 / 2) then return s!"t - 1 <= floor(q0/2) fails (t = {P.src.t})"
      match failed with
      | some s =>
        if let some w := s.ill then return s!"body[{s.idx}] ({instrStr s.instr}) is rejected: {w}"
        return s!"the noise bound fails the decryption condition at body[{s.idx}] ({instrStr s.instr}), level {s.level} (log2 Q = {fmt2 (log2F s.Q)})"
      | none => return "an output check failed (an output not under the original key, or missing)"
    { verdict := .notCertified,
      headline := s!"at the declared profile: {why}",
      lines := budgetLines ++ covLines.1 ++ [""] ++ notes,
      json := [("coverage", covLines.2), ("profile", profJson),
               ("failedAt", match failed with | some s => toJson s.idx | none => Json.null)] }

/-! ### Entry points -/

/-- Run the profile mode on a parsed program file and a parsed profile file. -/
def check (prog : Json) (prof : Json) (maxInstr : Nat) : Res :=
  match decode prof with
  | .error e => { verdict := .invalid, headline := s!"profile: {e}" }
  | .ok pf =>
    if BFV.isBFV prog then
      match BFV.decode prog with
      | .error e => { verdict := .invalid, headline := e }
      | .ok (.unsupported what idx why) =>
        { verdict := .unsupported, headline := s!"{what}{match idx with | some i => s!" (body[{i}])" | none => ""}: {why}" }
      | .ok (.ok inp) =>
        if maxInstr != 0 && inp.base.prog.body.length > maxInstr then
          { verdict := .unsupported, headline := tooLargeHeadline inp.base.prog.body.length maxInstr }
        else match pf.body with
          | .bfv p => checkBFV inp pf p
          | .bgv _ => { verdict := .invalid, headline := "profile.scheme is BGV; the program is BFV" }
    else
      match FHE.Check.decode prog with
      | .error e => { verdict := .invalid, headline := e }
      | .ok (.unsupported what idx why) =>
        { verdict := .unsupported, headline := s!"{what}{match idx with | some i => s!" (body[{i}])" | none => ""}: {why}" }
      | .ok (.ok inp) =>
        if maxInstr != 0 && inp.prog.body.length > maxInstr then
          { verdict := .unsupported, headline := tooLargeHeadline inp.prog.body.length maxInstr }
        else match pf.body with
          | .bgv p => checkBGV inp pf p
          | .bfv _ => { verdict := .invalid, headline := "profile.scheme is BFV; the program is BGV" }

/-- `--emit-profile`: the profile the OpenFHE-table mode computes for the program file. -/
def emit (prog : Json) : Except String Json :=
  if BFV.isBFV prog then
    match BFV.decode prog with
    | .error e => .error e
    | .ok (.unsupported what _ why) => .error s!"{what}: {why}"
    | .ok (.ok inp) => emitBFV inp
  else
    match FHE.Check.decode prog with
    | .error e => .error e
    | .ok (.unsupported what _ why) => .error s!"{what}: {why}"
    | .ok (.ok inp) => emitBGV inp

def renderHuman (path profPath : String) (r : Res) : String :=
  let v := match r.verdict with
    | .certified => "CERTIFIED"
    | .notCertified => "NOT CERTIFIED"
    | .unsupported => "UNSUPPORTED"
    | .invalid => "INVALID INPUT"
  "\n".intercalate ([s!"fhe_check --profile {profPath}: {path}", s!"VERDICT: {v} {r.headline}"] ++
    (if r.lines.isEmpty then [] else [""] ++ r.lines))

def renderJson (path profPath : String) (r : Res) : Json :=
  Json.mkObj (([("tool", Json.str "fhe_check"), ("format", "fhe-check-profile-report/v1"), ("mode", "profile"),
    ("input", Json.str path), ("profile", Json.str profPath),
    ("verdict", Json.str r.verdict.label), ("summary", Json.str r.headline)] : List (String × Json)) ++
    r.json.map (fun (k, v) => (if k == "profile" then "declared" else k, v)) ++
    [("notes", toJson r.lines)])

end FHE.Check.Profile
