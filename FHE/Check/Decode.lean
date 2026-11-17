import FHE.Check.Ops
import Spec.Params
import Spec.Scaling
import Std.Data.HashSet

set_option autoImplicit false

/-!
# FHE.Check.Decode — `fhe-check/v1` JSON → `FullParams`, `Source.Program`, digit layout   (UNTRUSTED glue)

The decoder only *transcribes*: it never reads a bound, a root of unity, a budget or an
"expected" value as a fact. What it produces is checked downstream by verified definitions
(`schemeParamsOK?`, `Source.step` inside `Challenge.Headline.refAnalyze`), except the inputs that are
declared assumptions of the certificate (`inputNoise`, `keyNoise`, `secretBound`, the
key-switching variant and digit layout, the modulus-switching method), which the report prints.
-/

namespace FHE.Check
open Lean Spec Spec.Source

/-- Which proved hybrid key-switching algorithm the library's key switching is assumed to match. -/
inductive KsVariant
  /-- Centred ModUp and ModDown (`FHE.KeySwitch.keySwitchBGV_spec`). -/
  | centred
  /-- Canonical ModUp, OpenFHE's BGV ModDown (`FHE.KeySwitch.keySwitchBGVOpenFHE_spec`). The bound
  is the canonical one; the variant only names the proved OpenFHE algorithm in the report. -/
  | openfhe
  /-- Canonical representatives, no particular library algorithm named (the conservative
  choice: `Challenge.Budget.ksBoundAt_le_canonical`). Used for Lattigo. -/
  | canonical
  deriving BEq, Repr

def KsVariant.name : KsVariant → String
  | .centred => "centred" | .openfhe => "openfhe"
  | .canonical => "canonical"

def KsVariant.theorem : KsVariant → String
  | .centred => "FHE.KeySwitch.keySwitchBGV_spec"
  | .openfhe => "FHE.KeySwitch.keySwitchBGVOpenFHE_spec"
  | .canonical => "Spec.Budget.ksBoundAt (canonical layout)"

/-- How the ciphertext limbs at a level are grouped into key-switching digits. -/
inductive DigitSpec
  /-- Consecutive groups of `α` limbs (OpenFHE `numPartQ` layout, Lattigo groups of `|P|`). At
  level `ℓ` the digits are the groups of the first `ℓ` limbs, the last one possibly shorter. -/
  | consecutive (α : Nat)
  /-- Per level, the digits as lists of limb indices. -/
  | explicit (perLevel : List (Nat × List (List Nat)))
  deriving Repr

structure KsConfig where
  variant : KsVariant
  digits : DigitSpec

/-- One `expect` annotation: the frontend's own level/parts for the destination of body
instruction `idx`. Compared with `Source.step`, never trusted. -/
structure Expect where
  idx : Nat
  dst : Var
  level : Option Nat
  parts : Option Nat

/-- Which decryption the frontend says the library performs on the outputs. -/
inductive DecMethod
  /-- Textbook decryption modulo the output's own level (`Spec.Scheme.bgvDecrypt`). -/
  | atOutputLevel
  /-- The phase is switched down to one limb first (`Spec.Decrypt.bgvDecryptSwitched`; OpenFHE's
  `PKEBGVRNS::Decrypt`). -/
  | switched
  deriving BEq, Repr

def DecMethod.name : DecMethod → String
  | .atOutputLevel => "at-output-level" | .switched => "switch-to-one-limb"

/-- The optional `ℓ₂` description of fresh encryptions (`freshEncryption.l2`, used by
`--kappa K --l2`; `Challenge.FreshNoiseL2`). Each field the input gives is an ASSUMPTION about the
fixed key or the samplers; a missing field is computed by the tool from the support bounds
(`FHE.Check.l2Values`). -/
structure L2Decl where
  /-- `‖e_pk‖₂² ≤ keyErrorSq`. -/
  keyErrorSq : Option Nat := none
  /-- `‖s‖₂² ≤ secretSq`. -/
  secretSq : Option Nat := none
  /-- Sub-Gaussian variance proxies of the coefficients of `u`, `e₁`, `e₂`. -/
  uProxy : Option Nat := none
  e1Proxy : Option Nat := none
  e2Proxy : Option Nat := none
  /-- The frontend's account of the values (printed). -/
  source : String := ""

/-- The frontend's description of fresh public-key encryptions (`Spec.Encrypt`): which inputs
they are, and the sampler bounds. ASSUMPTIONS of the probabilistic certificate (`--kappa`). -/
structure FreshModel where
  inputs : List Var
  /-- `‖e_pk‖∞ ≤ keyError`: the error of the public key. -/
  keyError : Nat
  /-- `|u_i| ≤ u`. -/
  u : Nat
  /-- `|e₁,i| ≤ e1`, `|e₂,i| ≤ e2`. -/
  e1 : Nat
  e2 : Nat
  source : String
  /-- `freshEncryption.l2`, if present. -/
  l2 : Option L2Decl := none
  /-- `freshEncryption.plaintextBound`: the declared bound on the norm of the stored plaintext
  polynomial of a fresh encryption (`Spec.Encrypt`). Absent: `t − 1` (a representative in
  `[0, t)`, as OpenFHE's packed encoding stores) is ASSUMED, and printed as such. -/
  plainBound : Option Nat := none
  /-- `freshEncryption.mean = {"num": mn, "den": md}`: every coefficient of the encryption
  randomness has mean at most `mn/md` in absolute value. Absent: mean zero (`0/1`) is ASSUMED,
  and printed as such. -/
  meanNum : Nat := 0
  meanDen : Nat := 1
  meanGiven : Bool := false

/-- The bound on the stored plaintext polynomial of a fresh encryption: the declared one, or
`t − 1`. -/
def FreshModel.bp (fm : FreshModel) (t : Nat) : Nat := fm.plainBound.getD (t - 1)

/-- A decoded input file. -/
structure Input where
  P : FullParams
  prog : Program
  /-- Per-input declared bounds (`program.inputs[].bound`), also in `prog.bounds`. -/
  bounds : List (Var × Nat)
  ks : KsConfig
  msMethod : String
  expects : List Expect
  /-- Body index → provenance text (tool op, trace line), printed only. -/
  provenance : List (Nat × String)
  sourceTool : String
  /-- The frontend's account of how it obtained `inputNoise` / `keyNoise` (printed, unchecked). -/
  noiseDerivation : Json
  /-- `$.decryption.method` (absent: textbook decryption at the output's level). -/
  decryption : DecMethod := .atOutputLevel
  /-- `$.freshEncryption` (absent: `--kappa` is not available for this file). -/
  fresh : Option FreshModel := none
  /-- `$.scaling`: the library's scaling-factor bookkeeping (`Spec.Scaling.ScaleData`; marks from
  `$.scaling.adjustments`). Absent: user-level decryption is not covered. -/
  scaling : Option Spec.Scaling.ScaleData := none
  /-- `$.source.idealised = true`: the frontend declares an IDEALISED algorithm instead of what the
  library runs (`extract_bfv.py --idealised`); the verdict is labelled as such. -/
  idealised : Bool := false

inductive Decoded
  | ok (inp : Input)
  /-- An operation, scheme or method outside what is certified. `idx` is the body index if any. -/
  | unsupported (what : String) (idx : Option Nat) (why : String)

def formatV1 : String := "fhe-check/v1"

/-- **Strict schema.** Every key of the object `j` (at path `ctx`) must be one of `allowed`: a
misspelt or unknown field is INVALID INPUT instead of being ignored (an ignored optional field
would silently take its default). Objects whose content is printed only (`source`,
`noiseDerivation`, `crossCheck`, `provenance[]`, `program.inputs[].origin`, `bfv.encryption`) are
not checked (nor is `recommendation`, which `fhe_check recommend --emit` writes); every object the
decoder reads a value from is. A non-object is left to the field
accessors, which say what they expected. -/
def onlyKeys (ctx : String) (j : Json) (allowed : List String) : DecodeM Unit :=
  match j with
  | .obj kvs => do
    for (k, _) in kvs.toArray do
      unless allowed.contains k do
        throw s!"{ctx}.{k}: unknown field (fhe-check/v1 allows here: {", ".intercalate allowed}); a misspelt field would otherwise be ignored"
  | _ => pure ()

/-- The top-level fields of `fhe-check/v1` (`decode` takes the scheme's extra ones, e.g. `bfv`). -/
def topKeys : List String :=
  ["format", "source", "params", "noiseDerivation", "keySwitching", "modSwitch", "decryption",
   "freshEncryption", "program", "provenance", "crossCheck", "scaling",
   -- printed only: written by `fhe_check recommend --emit` (`FHE.Check.Recommend`)
   "recommendation"]

def decodeLimb (ctx : String) (j : Json) : DecodeM Layout.LimbParams := do
  match j with
  | .str _ | .num _ => return ⟨← asNat ctx j, 0⟩
  | _ =>
    onlyKeys ctx j ["q", "psi"]
    let q ← natField ctx j "q"
    -- `psi` is a storage-level datum; the noise verdict never reads it.
    let ψ ← match field? j "psi" with
      | some v => asNat s!"{ctx}.psi" v
      | none => pure 0
    return ⟨q, ψ⟩

def decodeDigits (ctx : String) (j : Json) : DecodeM DigitSpec := do
  onlyKeys ctx j ["kind", "towersPerDigit", "dnum", "perLevel"]
  match ← strField ctx j "kind" with
  | "consecutive" => return .consecutive (← natField ctx j "towersPerDigit")
  | "explicit" =>
    let pl ← field ctx j "perLevel"
    let obj ← match pl with
      | .obj o => pure o
      | _ => throw s!"{ctx}.perLevel: expected an object level -> digits"
    let mut out := #[]
    for (k, v) in obj.toArray do
      let lvl ← asNat s!"{ctx}.perLevel key" (Json.str k)
      let ds ← asArr s!"{ctx}.perLevel.{k}" v
      let ds ← ds.toList.mapM fun d => do
        (← asArr s!"{ctx}.perLevel.{k}[]" d).toList.mapM (asNat s!"{ctx}.perLevel.{k}[][]")
      out := out.push (lvl, ds)
    return .explicit out.toList
  | k => throw s!"{ctx}.kind: unknown digit layout \"{k}\" (consecutive | explicit)"

def decodeDecl (ctx : String) (j : Json) : DecodeM (Decl × Option Nat) := do
  onlyKeys ctx j ["name", "parts", "level", "key", "bound", "origin", "scale"]
  -- `scale` is not read (every declaration has message scale 1; BGV scale factors are `$.scaling`):
  -- accepted only as 1, so that a file meaning something else is not silently read as 1
  if let some v := field? j "scale" then
    unless (← asNat s!"{ctx}.scale" v) == 1 do
      throw s!"{ctx}.scale: only 1 is accepted (the declared message scale is 1; a BGV scale factor goes in $.scaling.inputFactors)"
  let name ← strField ctx j "name"
  let parts ← natField ctx j "parts"
  let level ← natField ctx j "level"
  let key ← match field? j "key" with
    | some v => asNat s!"{ctx}.key" v
    | none => pure 1
  let bound ← match field? j "bound" with
    | some v => some <$> asNat s!"{ctx}.bound" v
    | none => pure none
  return ({ name, parts, level, scale := 1, key }, bound)

/-- Decode a whole `fhe-check/v1` document. -/
def decode (j : Json) (extraTop : List String := []) : DecodeM Decoded := do
  let fmt ← strField "$" j "format"
  if fmt == "fhe-check/v0" then
    throw "format fhe-check/v0 is the superseded draft; regenerate the file with the v1 extractors in harness/frontend/"
  unless fmt == formatV1 do throw s!"$.format: \"{fmt}\" is not {formatV1}"
  if let some e := field? j "error" then
    throw s!"the frontend reported an extraction failure: {e.compress}"
  onlyKeys "$" j (topKeys ++ extraTop)
  let p ← field "$" j "params"
  onlyKeys "$.params" p ["scheme", "N", "t", "limbs", "special", "secretBound", "inputNoise", "keyNoise"]
  let scheme ← strField "$.params" p "scheme"
  unless scheme == "BGV" do
    -- A BFV file never reaches this decoder in a plain check (FheCheck.lean hands it to
    -- FHE.Check.BFVReport first); it does in `fhe_check recommend`, which has no BFV mode.
    return .unsupported s!"scheme {scheme}" none
      (if scheme == "BFV" then
        "this command handles BGV programs only: a BFV program is certified by a plain `fhe_check FILE`; `fhe_check recommend` has no BFV mode"
      else "fhe_check certifies BGV and BFV programs only")
  let N ← natField "$.params" p "N"
  let t ← natField "$.params" p "t"
  let limbs ← (← asArr "$.params.limbs" (← field "$.params" p "limbs")).toList.mapIdxM
    fun i l => decodeLimb s!"$.params.limbs[{i}]" l
  let special ← (← asArr "$.params.special" (← field "$.params" p "special")).toList.mapIdxM
    fun i l => decodeLimb s!"$.params.special[{i}]" l
  let secretBound ← natField "$.params" p "secretBound"
  let inputNoise ← natField "$.params" p "inputNoise"
  let keyNoise ← natField "$.params" p "keyNoise"
  let P : FullParams :=
    { src := { kind := .bgv, N, qs := limbs.map (·.q), t }
      -- `store` is not read by the scheme-level check or the noise analyzer.
      store := { W := N, limbs, special }
      secretBound, inputNoise, keyNoise, outputNoise := 0 }
  -- key switching
  let ksj ← field "$" j "keySwitching"
  onlyKeys "$.keySwitching" ksj ["method", "variant", "digits", "source", "technique"]
  let method ← strField "$.keySwitching" ksj "method"
  unless method == "hybrid" do
    return (.unsupported s!"key-switching method {method}" none
      "only hybrid (RNS digit) key switching has a proved bound")
  let variant ← match ← strField "$.keySwitching" ksj "variant" with
    | "centred" => pure KsVariant.centred
    | "openfhe" => pure .openfhe
    | "canonical" => pure .canonical
    | v => return (.unsupported s!"key-switching variant {v}" none
        "no proved key-switching bound for this variant (centred | canonical | openfhe)")
  let digits ← decodeDigits "$.keySwitching.digits" (← field "$.keySwitching" ksj "digits")
  let msj ← field "$" j "modSwitch"
  onlyKeys "$.modSwitch" msj ["method", "source"]
  let msMethod ← strField "$.modSwitch" msj "method"
  -- program
  let pj ← field "$" j "program"
  onlyKeys "$.program" pj ["inputs", "body", "outputs"]
  let decls ← (← asArr "$.program.inputs" (← field "$.program" pj "inputs")).toList.mapIdxM
    fun i d => decodeDecl s!"$.program.inputs[{i}]" d
  let bodyJ ← asArr "$.program.body" (← field "$.program" pj "body")
  let mut body := #[]
  let mut expects := #[]
  for h : i in [:bodyJ.size] do
    let ij := bodyJ[i]
    match ← decodeInstr s!"$.program.body[{i}]" ij with
    | .unsupported op why => return .unsupported s!"operation {op}" (some i) why
    | .ok ins =>
      onlyKeys s!"$.program.body[{i}]" ij ["op", "dst", "a", "b", "c", "g", "k", "p", "expect"]
      body := body.push ins
      if let some e := field? ij "expect" then
        onlyKeys s!"$.program.body[{i}].expect" e ["level", "parts"]
        let lv ← (field? e "level").mapM (asNat s!"$.program.body[{i}].expect.level")
        let pt ← (field? e "parts").mapM (asNat s!"$.program.body[{i}].expect.parts")
        expects := expects.push { idx := i, dst := ← strField "" ij "dst", level := lv, parts := pt }
  let outputs ← (← asArr "$.program.outputs" (← field "$.program" pj "outputs")).toList.mapIdxM
    fun i o => asStr s!"$.program.outputs[{i}]" o
  if outputs.isEmpty then throw "$.program.outputs: no outputs (nothing to certify)"
  -- Names are unique. (`Source` reads the FIRST declaration of a name and ignores the others; a
  -- file that declares a name twice, with different shapes or bounds, is not a program any
  -- frontend meant. The same output listed twice would only repeat a line, but is refused too.)
  let dupOf := fun (l : List String) => Id.run do
    let mut seen : Std.HashSet String := {}
    for x in l do
      if seen.contains x then return some x
      seen := seen.insert x
    return none
  if let some x := dupOf (decls.map (·.1.name)) then
    throw s!"$.program.inputs: the input \"{x}\" is declared more than once"
  if let some x := dupOf outputs then
    throw s!"$.program.outputs: the output \"{x}\" is listed more than once"
  -- SWITCH-OVER POINT 2b (done): declared per-input bounds go to `Program.bounds`.
  let bounds := decls.filterMap fun (d, b) => b.map (d.name, ·)
  let prog : Program := { inputs := decls.map (·.1), body := body.toList, outputs, bounds }
  let prov := match field? j "provenance" with
    | some (.arr a) => a.toList.filterMap fun e =>
        match (e.getObjValAs? Nat "index") with
        | .ok k => some (k, match e with
          | .obj kvs => (Json.obj (kvs.erase "index")).compress
          | _ => e.compress)
        | .error _ => none
    | _ => []
  let decryption ← match field? j "decryption" with
    | none => pure DecMethod.atOutputLevel
    | some dj =>
      onlyKeys "$.decryption" dj ["method", "source"]
      match ← strField "$.decryption" dj "method" with
      | "at-output-level" => pure DecMethod.atOutputLevel
      | "switch-to-one-limb" => pure DecMethod.switched
      | m => return (.unsupported s!"decryption method {m}" none
          "no proved statement for this decryption (at-output-level | switch-to-one-limb)")
  let fresh ← match field? j "freshEncryption" with
    | none => pure none
    | some fj =>
      onlyKeys "$.freshEncryption" fj ["inputs", "keyError", "u", "e1", "e2", "source", "mean", "plaintextBound", "l2"]
      let ins ← (← asArr "$.freshEncryption.inputs" (← field "$.freshEncryption" fj "inputs")).toList.mapIdxM
        fun i o => asStr s!"$.freshEncryption.inputs[{i}]" o
      let l2 ← match field? fj "l2" with
        | none => pure none
        | some lj =>
          onlyKeys "$.freshEncryption.l2" lj ["keyErrorSq", "secretSq", "uProxy", "e1Proxy", "e2Proxy", "source"]
          let opt := fun (k : String) => (field? lj k).mapM (asNat s!"$.freshEncryption.l2.{k}")
          pure (some ({ keyErrorSq := ← opt "keyErrorSq", secretSq := ← opt "secretSq",
                        uProxy := ← opt "uProxy", e1Proxy := ← opt "e1Proxy", e2Proxy := ← opt "e2Proxy",
                        source := match lj.getObjValAs? String "source" with
                          | .ok s => s
                          | .error _ => "" } : L2Decl))
      let plainBound ← (field? fj "plaintextBound").mapM (asNat "$.freshEncryption.plaintextBound")
      let mean ← match field? fj "mean" with
        | none => pure none
        | some mj =>
          onlyKeys "$.freshEncryption.mean" mj ["num", "den", "source"]
          let mn ← natField "$.freshEncryption.mean" mj "num"
          let md ← natField "$.freshEncryption.mean" mj "den"
          if md == 0 then throw "$.freshEncryption.mean.den: must be positive"
          pure (some (mn, md))
      pure (some { inputs := ins
                   l2
                   plainBound
                   meanNum := (mean.map (·.1)).getD 0
                   meanDen := (mean.map (·.2)).getD 1
                   meanGiven := mean.isSome
                   keyError := ← natField "$.freshEncryption" fj "keyError"
                   u := ← natField "$.freshEncryption" fj "u"
                   e1 := ← natField "$.freshEncryption" fj "e1"
                   e2 := ← natField "$.freshEncryption" fj "e2"
                   source := match fj.getObjValAs? String "source" with
                     | .ok s => s
                     | .error _ => "" : FreshModel })
  if let some fm := fresh then
    if let some x := dupOf fm.inputs then
      throw s!"$.freshEncryption.inputs: \"{x}\" is listed more than once"
    let declared : Std.HashSet String := decls.foldl (fun s d => s.insert d.1.name) {}
    if let some x := fm.inputs.find? fun x => !declared.contains x then
      throw s!"$.freshEncryption.inputs: \"{x}\" is not a declared input of the program"
  let scaling ← match field? j "scaling" with
    | none => pure none
    | some sj =>
      onlyKeys "$.scaling" sj ["tracks", "inputFactors", "adjustments"]
      let tracks ← match field? sj "tracks" with
        | some (.bool b) => pure b
        | _ => throw "$.scaling.tracks: expected true or false"
      let fs ← (← asArr "$.scaling.inputFactors" (← field "$.scaling" sj "inputFactors")).toList.mapIdxM
        fun i e => do
          onlyKeys s!"$.scaling.inputFactors[{i}]" e ["name", "factor"]
          pure ((← strField s!"$.scaling.inputFactors[{i}]" e "name"),
                (← natField s!"$.scaling.inputFactors[{i}]" e "factor"))
      if let some x := dupOf (fs.map (·.1)) then
        throw s!"$.scaling.inputFactors: \"{x}\" is listed more than once"
      let adj ← match field? sj "adjustments" with
        | none => pure []
        | some aj => do
            let a ← asArr "$.scaling.adjustments" aj
            a.toList.mapIdxM fun i k => asNat s!"$.scaling.adjustments[{i}]" k
      if let some k := adj.find? (· ≥ body.size) then
        throw s!"$.scaling.adjustments: {k} is not an index of $.program.body"
      if let some k := adj.find? fun k => !(match body[k]? with
          | some (.mulConst ..) => true | _ => false) then
        throw s!"$.scaling.adjustments: body[{k}] is not a mulConst (only a constant multiplication can be a scale adjustment)"
      -- a boolean array instead of `adj.contains` per body index (that was quadratic)
      let marked : Array Bool := adj.foldl (fun m k => m.set! k true) (Array.replicate body.size false)
      pure (some ({ factors := fs, marks := marked.toList,
                    tracks } : Spec.Scaling.ScaleData))
  let tool := match field? j "source" with
    | some s => match s.getObjValAs? String "tool" with
      | .ok t => t
      | .error _ => "unknown"
    | none => "unknown"
  let idealised ← match field? j "source" with
    | some s => match field? s "idealised" with
      | some (.bool b) => pure b
      | some _ => throw "$.source.idealised: expected true or false"
      | none => pure false
    | none => pure false
  -- The build options an OpenFHE extractor records (`$.noiseDerivation.build`, from the tracer's
  -- params.json): the transcriptions of the key switching and of the noise estimates cover the
  -- default build only (WITH_REDUCED_NOISE off, 64-bit native integers, HAVE_INT128). A file that
  -- records another build is outside what the proof covers.
  if let some nd := field? j "noiseDerivation" then
    if let some b@(.obj _) := field? nd "build" then
      let off (k : String) := match field? b k with | some (.bool true) => true | _ => false
      if off "WITH_REDUCED_NOISE" then
        return .unsupported "build option WITH_REDUCED_NOISE" none
          "$.noiseDerivation.build records WITH_REDUCED_NOISE = true; the transcriptions cover OpenFHE built with WITH_REDUCED_NOISE = OFF (the default) only. Re-extract from a default build"
      if (match field? b "HAVE_INT128" with | some (.bool false) => true | _ => false) then
        return .unsupported "build option HAVE_INT128" none
          "$.noiseDerivation.build records HAVE_INT128 = false; the transcriptions cover the default build (HAVE_INT128) only. Re-extract from a default build"
      if (match field? b "NATIVEINT" with
          | some (.num n) => n != 64
          | some _ => true
          | none => false) then
        return .unsupported "build option NATIVEINT" none
          "$.noiseDerivation.build records a NATIVEINT other than 64; the transcriptions cover the default 64-bit build only. Re-extract from a default build"
  return .ok { P, prog, bounds, idealised,
               ks := { variant, digits }, msMethod, expects := expects.toList,
               provenance := prov, sourceTool := tool,
               noiseDerivation := (field? j "noiseDerivation").getD Json.null,
               decryption, fresh, scaling }

/-- The build configuration the transcriptions assume, with what the file records about it, for the
assumptions list of an OpenFHE file (`none` for another source). -/
def Input.buildAssumption (inp : Input) : Option String :=
  if inp.sourceTool != "openfhe" then none else
  let rec_ := match field? inp.noiseDerivation "build" with
    | some (b@(.obj _)) => s!"the file records {b.compress}"
    | some (.str t) => s!"the file states: {t}"
    | _ => "the file records no build"
  some s!"OpenFHE built with WITH_REDUCED_NOISE=OFF, NATIVEINT=64 and HAVE_INT128 (the default build; the transcriptions cover no other); {rec_}"

end FHE.Check
