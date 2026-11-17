import FHE.Pin.ChecksA

/-!
# FHE.Pin.ChecksProg — message-level semantics (b), phase contracts (e), analyzer bounds (f)
(UNTRUSTED glue around the trusted definitions)

The extracted program (`prog.fhecheck.json`, decoded by `FHE.Check.decode`) is run one instruction
at a time with `FHE.Pin.stepA` (= `Spec.Source.step`, `stepA_spec`). Every variable that has an
OpenFHE object is compared with it:

* b: level, parts, key; the message `Source.step` computes against the textbook decryption of
  OpenFHE's ciphertext and against OpenFHE's own `Decrypt`;
* e: the conjuncts of `Spec.Trace.StepOK`, with witnesses computed from the data;
* f: the bound of `Challenge.Headline.refBound` against the measured centred phase.
-/

namespace FHE.Pin
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source

/-- What the checker knows about a program variable. -/
structure VarRec where
  ph : Option Ph := none
  parts : Nat := 0
  level : Nat := 0
  key : Nat := 1
  synthetic : Bool := false
  /-- A `modSwitch` chain through variables without an OpenFHE object: the last variable with
  data and the limbs dropped since (first dropped first). -/
  pend : Option (Var × List Nat) := none
  depth : Nat := 0
  /-- The reference analysis' guard `2·β < Q` failed here or at an ancestor: the phase may wrap. -/
  tainted : Bool := false
  /-- An input this value depends on exceeds its own bound `β₀` (the premise of the analysis,
  `InputsOK` / `BoundsOK`, is false for this run): bounds downstream are not claims. -/
  premiseBad : Bool := false
  scale : Option Nat := none
  /-- Per-coefficient cost of the literal (unmemoised) message. -/
  cost : Nat := 1
  deriving Inhabited

def operands : Instr → List Var
  | .add _ a b | .sub _ a b | .mul _ a b | .addPlain _ a b | .subPlain _ a b | .mulPlain _ a b => [a, b]
  | .square _ a | .mulConst _ a _ | .copy _ a | .toEval _ a | .toCoeff _ a | .relin _ a
  | .keySwitch _ a | .automorph _ a _ | .modSwitch _ a | .dropLimbs _ a _ => [a]

def opName : Instr → String
  | .add .. => "add" | .sub .. => "sub" | .mul .. => "mul" | .square .. => "square"
  | .mulConst .. => "mulConst" | .copy .. => "copy" | .toEval .. => "toEval"
  | .toCoeff .. => "toCoeff" | .relin .. => "relin" | .keySwitch .. => "keySwitch"
  | .automorph .. => "automorph" | .modSwitch .. => "modSwitch"
  | .addPlain .. => "addPlain" | .subPlain .. => "subPlain" | .mulPlain .. => "mulPlain"
  | .dropLimbs .. => "dropLimbs"

structure StepRes where
  ok : Bool
  fields : List (String × Json) := []

/-- The verdict and the diagnostic fields of `e.step` for the destination `d` (at level `vLevel`)
of instruction `i`. **The verdict is `FHE.Pin.stepOKb`** (`FHE/Pin/Sound.lean`, proved sound for
`Spec.Trace.StepOK`: `stepOKb_sound`); the fields (measured norms, budgets, mismatch counts) are
recomputed here for the report only. `none`: an operand has no ciphertext data. -/
def stepCheck (P : FullParams) (E : Trace.Budget) (K : Nat) (mt : Mut) (i : Instr) (vLevel : Nat)
    (d : Ph) (get : Var → Option (Ph × Nat)) : Option StepRes := do
  let ok ← stepOKb P E K mt i vLevel d get
  let N := P.src.N
  let Q := P.src.modulus vLevel
  let fields : List (String × Json) := match i with
    | .relin _ a | .keySwitch _ a =>
      match get a with
      | some (x, _) =>
        let e := toArr K (centered (ofInt Q (ofArr (N := N) d.Z) - ofInt Q (ofArr x.Z)))
        let nrm := normA N e
        let dv := dvdA N P.src.t e
        [("measured", natJ nrm), ("bound", natJ E.keySwitch), ("tDivides", boolJ dv),
         ("measuredBits", bitsJ nrm), ("boundBits", bitsJ E.keySwitch)]
      | none => []
    | .modSwitch _ a =>
      match get a with
      | some (x, parts) =>
        match P.src.qs[x.level - 1]? with
        | some q =>
          let δ := toArr K ((q : Int) • ofArr (N := N) d.Φ - ofArr x.Φ)
          let nrm := normA N δ
          let dv := dvdA N P.src.t δ
          let Eb := mt.msBudgetM E parts
          [("measured", natJ nrm), ("bound", natJ (q * Eb)), ("tDivides", boolJ dv), ("q", natJ q),
           ("measuredOverQ", natJ ((nrm + q - 1) / q)), ("budget", natJ Eb),
           ("measuredOverQBits", bitsJ ((nrm + q - 1) / q)), ("budgetBits", bitsJ Eb),
           ("operandParts", Json.num parts),
           ("exceeds2PartBudget", boolJ (decide (nrm > q * E.modSwitch)))]
        | none => []
      | none => []
    | _ => []
  pure ⟨ok, fields⟩

/-- The lines of one variable that has ciphertext data. Returns whether the message agrees with
the textbook decryption. -/
def reportVar (x : Cx) (name op : String) (r : VarRec) (ph : Ph)
    (msg : Array (ZMod x.P.src.t)) (β : Option Nat) (arbitrary msgFromDecrypt : Bool)
    (objId : Option String) : IO Bool := do
  let P := x.P
  let N := x.N
  let Q := P.src.modulus r.level
  let common : List (String × Json) :=
    [("level", Json.num r.level), ("parts", Json.num r.parts), ("key", Json.num r.key),
     ("depth", Json.num r.depth), ("synthetic", boolJ r.synthetic)]
  let dec := decryptOfPhaseA N x.K P.src.t ph.Φ
  let msgOK := dec == msg
  let wrapWhy := "the reference analysis does not exclude a phase wrap here (2·β ≥ Q at this variable or an ancestor)"
  let premiseWhy := "an input this value depends on exceeds its bound β₀ (the premise InputsOK/BoundsOK of the analysis is false in this run; see the f.bound line of the input)"
  let excused := r.tainted || (r.premiseBad && op != "input")
  let wrapWhy := if r.tainted then wrapWhy else premiseWhy
  x.emit "b.msg" name op (if msgOK then some true else if excused then none else some false) "forced"
    (common ++ [("mismatches", Json.num (diffCount dec msg)), ("msgFromDecrypt", boolJ msgFromDecrypt)] ++
      (if msgOK then [] else [("why", Json.str (if excused then wrapWhy else
        "Source.step's message differs from Spec.Scheme.bgvDecrypt of OpenFHE's ciphertext although the reference bound is below Q/2"))]))
  let measured := normA N ph.Φ
  -- OpenFHE's own decryption
  let decObj : Option Json := do
    let id ← objId
    let o ← x.c.object? id
    jObj? o "decrypt"
  let obj : Option Json := objId.bind x.c.object?
  if let some dj := decObj then
    if r.key == 1 then
      if let some rawName := jStr? dj "raw" then
        let raw ← x.rawPoly rawName P.src.t
        let pred := valsOf (toArr x.K (x.mt.decScaleM P.src r.level • (ofArr msg : Poly P.src.t P.src.N)))
        x.emit "b.raw" name op (if pred == raw then some true else if excused then none else some false) "forced"
          (common ++ [("mismatches", Json.num (diffCount pred raw))] ++
            (if pred == raw then [] else [("why", Json.str (if excused then wrapWhy else
              "decScale · (message of Source.step) differs from OpenFHE's Decrypt"))]))
    else
      x.emit "b.shape" name op (some false) "forced"
        (common ++ [("why", Json.str "OpenFHE decrypts this object but the program records it under a key other than s")])
  -- scaling factors (glue bookkeeping, as extract.py does)
  if let (some o, some sc) := (obj, r.scale) then
    if jStr? o "kind" == some "ct" then
      let objSf := jNat? o "sf"
      let t := P.src.t
      let predDec := (sc * (x.mt.decScaleM P.src r.level).val) % t
      let decSf := decObj.bind (jNat? · "sf")
      if op == "mulPlain" then
        x.emit "b.sf" name op none "glue"
          (common ++ [("why", Json.str "LeveledSHERNS::EvalMultInPlace leaves scalingFactorInt stale; the BGV wrapper sets it on the following copy (harness/frontend/README.md)"),
            ("tracked", natJ sc), ("objectSf", match objSf with | some n => natJ n | none => Json.null)])
      else
        let ok1 := match objSf with | some n => n % t == sc % t | none => true
        let ok2 := match decSf with | some n => r.key != 1 || n % t == predDec | none => true
        x.emit "b.sf" name op (some (ok1 && ok2)) "glue"
          (common ++ [("tracked", natJ sc), ("objectSf", match objSf with | some n => natJ n | none => Json.null),
            ("predictedDecryptSf", natJ predDec), ("decryptSf", match decSf with | some n => natJ n | none => Json.null)])
  -- f: the reference bound against the measured phase
  match β with
  | none =>
    x.emit "f.bound" name op none "forced" (common ++ [("why", Json.str "refBound gives no bound (an operand has none)")])
  | some b =>
    let guardOK := decide (2 * b < Q)
    let why := if arbitrary then "inputsArbitrary: the input-noise premise of the analysis does not hold in this case"
      else if r.premiseBad && op != "input" then premiseWhy
      else if !msgOK then "wrapped: the measured phase does not decrypt to the predicted message, so it is not the phase the bound is about"
      else ""
    x.emit "f.bound" name op
      (if arbitrary || !msgOK || (r.premiseBad && op != "input") then none else some (decide (measured ≤ b))) "forced"
      (common ++ [("measured", natJ measured), ("bound", natJ b), ("halfQ", natJ (Q / 2)), ("premiseBad", boolJ r.premiseBad),
        ("measuredBits", bitsJ measured), ("boundBits", bitsJ b), ("halfQBits", bitsJ (Q / 2)),
        ("wrapped", boolJ (!msgOK)), ("guardOK", boolJ guardOK), ("tainted", boolJ r.tainted)] ++
        (if why.isEmpty then [] else [("why", Json.str why)]))
    if decObj.isSome && r.key == 1 then
      let qsℓ := P.src.qs.take r.level
      let sw := switchedPhaseA N x.K x.mt P.src.t qsℓ ph.Φ
      let nsw := normA N sw
      let dB := Decrypt.decBound P.src r.level b
      x.emit "f.decrypt" name op
        (if arbitrary || !msgOK || r.premiseBad then none else some (decide (nsw ≤ dB))) "forced"
        (common ++ [("measured", natJ nsw), ("bound", natJ dB), ("q0Half", natJ (P.src.qs.headD 0 / 2)),
          ("measuredBits", bitsJ nsw), ("boundBits", bitsJ dB),
          ("decryptOK", boolJ (Decrypt.decryptOK? P.src r.level b))] ++
          (if why.isEmpty then [] else [("why", Json.str why)]))
  -- the literal trusted phase
  if x.literal r.parts then
    let lit := toArr x.K (centered (Trace.phaseAt P Q r.key (ofArr x.s) (ph.comps.map ofArr)))
    x.emit "e.phase.literal-vs-forced" name "phaseAt" (some (lit == ph.Φ)) "literal+forced" common
  return msgOK

/-- b, e, f for the extracted program. Returns what it recorded per variable (for `b.user.*`). -/
def checkProg (x : Cx) (inp : FHE.Check.Input) (lay : Budget.KSLayout) : IO (Std.HashMap Var VarRec) := do
  let P := x.P
  let N := x.N
  let t := P.src.t
  let prog := inp.prog
  let E := Budget.certified P lay
  let layC : Budget.KSLayout := { lay with canonical := false }
  let arbitrary := jBool x.c.pin "inputsArbitrary"
  let inputsJ := jArr ((jObj? x.c.progJson "program").getD Json.null) "inputs"
  let originOf : Var → Option String := fun v =>
    inputsJ.findSome? fun d =>
      if jStr? d "name" == some v then (jObj? d "origin").bind (jStr? · "openfhe") else none
  let bodyJ := jArr ((jObj? x.c.progJson "program").getD Json.null) "body"
  let isNegate : Nat → Bool := fun k =>
    bodyJ.size == prog.body.length && (bodyJ[k]?.bind (jStr? · "op")) == some "negate"
  -- the OpenFHE object of a program variable: its own id, or, for a variable `id#k` (the
  -- extractor's name for a later definition with the same content-hash id), the object `id`
  let objOf : Var → Option String := fun v =>
    if (x.c.object? v).isSome then some v else
      match v.splitOn "#" with
      | [base, k] => if k.all Char.isDigit && !k.isEmpty && (x.c.object? base).isSome then some base else none
      | _ => none
  let mut msgTab : Std.HashMap Var (Array (ZMod P.src.t)) := {}
  let mut recs : Std.HashMap Var VarRec := {}
  let mut β : Std.HashMap Var Nat := {}
  x.emit "f.budget" "E" "certified" none "literal"
    [("why", Json.str "information: the budget Spec.Budget.certified P lay"),
     ("keySwitch", natJ E.keySwitch), ("modSwitch", natJ E.modSwitch), ("modSwitchOne", natJ E.modSwitchOne),
     ("modSwitchMany", Json.mkObj ((List.range 4).map fun k => (toString (k + 3), natJ (E.modSwitchMany (k + 3))))),
     ("modSwitchAt", Json.mkObj ((List.range 6).map fun k => (toString (k + 1), natJ (E.modSwitchAt (k + 1))))),
     ("inputNoise", natJ P.inputNoise), ("keyNoise", natJ P.keyNoise),
     ("canonical", boolJ lay.canonical)]
  x.emit "b.decls" "inputs" "Decl.ok" (some (prog.inputs.all fun d => d.ok P.src)) "literal"
  -- inputs
  let mut pendingInputs : Array (Decl × Ph × VarRec × Bool × String) := #[]
  for d in prog.inputs do
    try
      let origin := originOf d.name
      let ptId : Option String := origin.bind fun o =>
        match x.c.object? o with
        | some oj => if jStr? oj "kind" == some "pt" then some o else none
        | none => none
      let objId := if (x.c.object? d.name).isSome then d.name else (ptId.getD d.name)
      let (comps, towers) ← x.objComps objId
      let objParts := match x.c.object? objId with
        | some oj => if jStr? oj "kind" == some "pt" then 1 else (jNat? oj "parts").getD 0
        | none => 0
      x.emit "b.shape" d.name "input" (some (towers == d.level && objParts == d.parts && comps.length == d.parts)) "literal"
        [("level", Json.num d.level), ("towers", Json.num towers), ("parts", Json.num d.parts),
         ("objectParts", Json.num objParts), ("object", Json.str objId)]
      if towers != d.level then throw (IO.userError s!"declared at level {d.level}, object has {towers} towers")
      let ph ← x.mkPh comps d.level d.key
      let (msg, fromDec) ← match ptId with
        | some p =>
          let some pj := x.c.object? p | throw (IO.userError "pt object")
          let some pn := jStr? pj "poly" | throw (IO.userError "pt poly")
          let (pm, v) ← liftExcept (x.c.rnsPolyAny pn)
          -- the message of a plaintext: textbook decryption of the one-component value [p]
          let vc := centredA N x.K .none (pm.foldl (· * ·) 1) v
          pure (toArr x.K (ofInt P.src.t (ofArr (N := N) vc)), false)
        | none => pure (decryptOfPhaseA N x.K P.src.t ph.Φ, true)
      msgTab := msgTab.insert d.name msg
      let b0 := match prog.boundOf d.name with
        | some b => min b P.inputNoise
        | none => P.inputNoise
      β := β.insert d.name b0
      let sc := (x.c.object? objId).bind (jNat? · "sf")
      let r : VarRec := { ph := some ph, parts := d.parts, level := d.level, key := d.key, scale := sc,
                          tainted := !decide (2 * b0 < P.src.modulus d.level),
                          premiseBad := decide (normA N ph.Φ > b0) }
      recs := recs.insert d.name r
      pendingInputs := pendingInputs.push (d, ph, r, fromDec, objId)
    catch e =>
      x.emit "b.error" d.name "input" (some false) "forced" [("why", Json.str s!"{e}")]
      β := β.insert d.name P.inputNoise
  for (d, ph, r, fromDec, objId) in pendingInputs do
    let _ ← reportVar x d.name "input" r ph (msgTab[d.name]?.getD #[]) β[d.name]? arbitrary fromDec
      (if (x.c.object? d.name).isSome then some objId else none)
  let tab := msgTab
  let msgs : Var → Msg P.src.t P.src.N := fun v =>
    match tab[v]? with
    | some a => .exact (ofArr a)
    | none => .exact 0
  let mut ρ : Env P.src := initEnv P.src prog msgs
  let mut fmsg : Std.HashMap Var (Array (ZMod P.src.t)) := msgTab
  let mut idx : Nat := 0
  let mut firstOverflow : Option Nat := none
  let mut stepFailed := false
  for i in prog.body do
    let d := Trace.dst i
    let op := opName i
    let some ρ' := stepA x.K x.mt P.src ρ i
      | do
        x.emit "b.step" d op (some false) "forced"
          [("index", Json.num idx),
           ("why", Json.str s!"Spec.Source.step rejects instruction {idx} ({op}) of the extracted program")]
        stepFailed := true
        break
    let βm := β
    let bnd := Challenge.Headline.refBound P E ρ (fun y => βm[y]?) i
    let some v := ρ' d | break
    let msgArr : Array (ZMod P.src.t) := match v.msg with
      | .exact m => toArr x.K m
    fmsg := fmsg.insert d msgArr
    let ors := (operands i).map fun a => (recs[a]?).getD {}
    let depth := ors.foldl (fun acc r => max acc r.depth) 0 +
      (match i with | .mul .. | .square .. => 1 | _ => 0)
    let cost := match i with
      | .mul .. | .mulPlain .. | .square .. => N * (ors.foldl (fun acc r => acc + r.cost) 0) * (match i with | .square .. => 2 | _ => 1)
      | .automorph .. => N * (ors.foldl (fun acc r => acc + r.cost) 0)
      | _ => ors.foldl (fun acc r => acc + r.cost) 0
    let guardOK := match bnd with
      | some b => decide (2 * b < P.src.modulus v.level)
      | none => false
    if !guardOK && firstOverflow.isNone then firstOverflow := some idx
    let tainted := !guardOK || ors.any (·.tainted)
    let premiseBad := ors.any (·.premiseBad)
    let sa := ors.head?.bind (·.scale)
    let sb := (ors.drop 1).head?.bind (·.scale)
    let scale : Option Nat := match i with
      | .mul .. | .mulPlain .. => do let a ← sa; let b ← sb; pure (a * b % t)
      | .square .. => sa.map fun a => a * a % t
      | .mulConst _ _ c =>
        -- the extractor's `negate` (decoded as `mulConst −1`) negates the user's message and
        -- keeps OpenFHE's scalingFactorInt (extract.py `replay`)
        if isNegate idx then sa else sa.map fun a => ((a : Int) * c % (t : Int)).toNat
      | .modSwitch .. => do
        let a ← sa
        let q ← P.src.qs[v.level]?
        pure (a * ((q : ZMod t)⁻¹).val % t)
      | _ => sa
    let mut r : VarRec := { parts := v.parts, level := v.level, key := v.key, depth, tainted, premiseBad, scale, cost }
    let common : List (String × Json) := [("index", Json.num idx), ("level", Json.num v.level), ("parts", Json.num v.parts)]
    try
      let oid := objOf d
      let hasObj := oid.isSome
      if let some od := oid then
        let (comps, towers) ← x.objComps od
        let decrypted := ((x.c.object? od).bind (jObj? · "decrypt")).isSome
        let shapeOK := towers == v.level && comps.length == v.parts && (!decrypted || v.key == 1)
        x.emit "b.shape" d op (some shapeOK) "literal"
          (common ++ [("towers", Json.num towers), ("objectParts", Json.num comps.length), ("key", Json.num v.key)])
        if towers == v.level then
          r := { r with ph := some (← x.mkPh comps v.level v.key) }
      else
        match i with
        | .automorph _ a g =>
          if let some pa := (recs[a]?).bind (·.ph) then
            -- no OpenFHE object: the trusted automorphism applied to each component of the operand
            let comps := pa.comps.map (autoA N x.K x.mt g)
            r := { r with ph := some (← x.mkPh comps v.level v.key), synthetic := true }
        | .modSwitch _ a =>
          let ra := (recs[a]?).getD {}
          let q := P.src.qs[v.level]?.getD 0
          r := { r with pend := match ra.ph, ra.pend with
            | some _, _ => some (a, [q])
            | none, some (root, qsD) => some (root, qsD ++ [q])
            | none, none => none }
        | _ => pure ()
      match r.ph with
      | none =>
        if !(match i with | .modSwitch .. => r.pend.isSome | _ => false) then
          x.emit "e.step" d op none "forced"
            (common ++ [("why", Json.str "the destination has no OpenFHE object and cannot be synthesised")])
      | some ph =>
        let _ ← reportVar x d op r ph msgArr bnd arbitrary false oid
        let recsNow := recs
        let get : Var → Option (Ph × Nat) := fun a => do
          let ra ← recsNow[a]?
          let p ← ra.ph
          pure (p, ra.parts)
        -- composite modulus switch through object-less intermediates
        let composite : Option (Var × List Nat) := match i with
          | .modSwitch _ a =>
            match (recs[a]?).bind (·.ph), (recs[a]?).bind (·.pend) with
            | none, some (root, qsD) => some (root, qsD ++ [P.src.qs[v.level]?.getD 0])
            | _, _ => none
          | _ => none
        let ksExtra : List (String × Json) := match i with
          | .relin _ a | .keySwitch _ a =>
            let la := ((recs[a]?).getD {}).level
            [("ksBoundAt", natJ (Budget.ksBoundAt P lay la)),
             ("ksBoundAtCentred", natJ (Budget.ksBoundAt P layC la)),
             ("ksBoundAtBits", bitsJ (Budget.ksBoundAt P lay la)),
             ("ksBudget", natJ E.keySwitch), ("operandLevel", Json.num la)]
          | _ => []
        match composite with
        | some (root, qsD) =>
          match get root with
          | none => x.emit "e.step" d op none "forced" (common ++ [("why", Json.str "composite modSwitch: the root has no data")])
          | some (pr, parts) =>
            let qprod := qsD.foldl (· * ·) 1
            let δ := toArr x.K (((qprod : Nat) : Int) • ofArr (N := N) ph.Φ - ofArr pr.Φ)
            let nrm := normA N δ
            let dv := dvdA N t δ
            let Eb := x.mt.msBudgetM E parts
            let bound := (List.range qsD.length).foldl
              (fun acc j => acc + (qsD.take (j + 1)).foldl (· * ·) 1 * Eb) 0
            x.emit "e.step" d op (some (decide (nrm ≤ bound) && dv)) "forced"
              (common ++ [("composite", boolJ true), ("root", Json.str root), ("measured", natJ nrm),
                ("bound", natJ bound), ("tDivides", boolJ dv), ("q", natJ qprod),
                ("measuredOverQ", natJ ((nrm + qprod - 1) / qprod)), ("budget", natJ Eb),
                ("operandParts", Json.num parts)])
        | none =>
          match stepCheck P E x.K x.mt i v.level ph get with
          | none =>
            x.emit "e.step" d op none "forced" (common ++ [("why", Json.str "an operand has no ciphertext data")])
          | some res =>
            let partsOK := ph.comps.length == v.parts
            x.emit "e.step" d op (some (res.ok && partsOK)) "forced"
              (common ++ [("synthetic", boolJ r.synthetic), ("depth", Json.num depth), ("partsOK", boolJ partsOK)] ++
                res.fields ++ ksExtra)
    catch e =>
      x.emit "b.error" d op (some false) "forced" (common ++ [("why", Json.str s!"{e}")])
    β := match bnd with
      | some b => β.insert d b
      | none => β.erase d
    recs := recs.insert d r
    ρ := ρ'
    idx := idx + 1
  if !stepFailed then
    x.emit "b.outputs" "outputs" "eval" (some (prog.outputs.all fun o => (ρ o).isSome)) "forced"
  -- the literal Source.eval on the whole program
  if x.o.mu = .none && N ≤ x.o.litMaxN then
    match Source.eval P.src prog msgs with
    | none =>
      x.emit "b.eval" "program" "eval" (some false) "literal"
        [("why", Json.str "Spec.Source.eval rejects the extracted program"), ("forcedAlsoRejects", boolJ stepFailed)]
    | some ρL =>
      x.emit "b.eval" "program" "eval" (some (!stepFailed)) "literal" [("forcedAlsoAccepts", boolJ (!stepFailed))]
      for (name, r) in recs.toList do
        if r.cost * N > x.o.litCost then
          x.emit "b.literal-vs-forced" name "eval" none "literal+forced"
            [("why", Json.str s!"literal (unmemoised) message would cost about {r.cost * N} coefficient accesses (limit {x.o.litCost})")]
        else
          match ρL name, fmsg[name]? with
          | some vL, some fm =>
            match vL.msg with
            | .exact m =>
              let lit := toArr x.K m
              x.emit "b.literal-vs-forced" name "eval"
                (some (lit == fm && vL.level == r.level && vL.parts == r.parts && vL.key == r.key)) "literal+forced"
          | _, _ => x.emit "b.literal-vs-forced" name "eval" (some false) "literal+forced" [("why", Json.str "variable missing")]
  -- the locked reference analyzer on the whole program
  if x.o.mu = .none then
    let ra := Challenge.Headline.refAnalyze P E prog
    x.emit "f.refAnalyze" "program" "refAnalyze" none "literal"
      [("why", Json.str "information: verdict of Challenge.Headline.refAnalyze at the certified budget"),
       ("accepts", boolJ ra.isSome), ("bound", match ra with | some b => natJ b | none => Json.null),
       ("firstOverflowIndex", match firstOverflow with | some k => Json.num k | none => Json.null),
       ("stepFailed", boolJ stepFailed),
       ("consistent", boolJ (ra.isSome == (firstOverflow.isNone && !stepFailed
          && (prog.inputs.all fun d => d.ok P.src) && (prog.outputs.all fun o => (ρ o).isSome)
          && (prog.outputs.all fun o => (β[o]?).isSome))))]
  return recs

end FHE.Pin
