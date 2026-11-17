import FHE.Check.Report
import FHE.Check.BFVReport  -- BFV
import FHE.Check.Recommend
import FHE.Check.Profile

set_option autoImplicit false

/-!
# fhe_check — is this BGV program guaranteed to decrypt correctly?   (UNTRUSTED glue around verified definitions)

    fhe_check [--kappa K [--l2]] [--json] [--steps] [--dump-program] [--no-suggest] [--max-instructions N] FILE.fhecheck.json
    fhe_check --profile PROFILE.json [--json] [--max-instructions N] FILE.fhecheck.json
    fhe_check --emit-profile FILE.fhecheck.json
    fhe_check recommend [--target openfhe|heir|neutral] [--ring-dim N] [--security 128|192|256]
                        [--digits keep|any|D] [--kappa K] [--margin BITS] [--emit OUT.json] [--json]
                        FILE.fhecheck.json
    fhe_check --help

Reads the neutral `fhe-check/v1` JSON (produced from OpenFHE or HEIR by the extractors in
`harness/frontend/`), runs the verified pipeline of `FHE.Check.Report.runCheck`, and prints the
verdict with the proved bounds and a fixed statement of what the certificate means.

Exit codes: 0 CERTIFIED, 1 NOT CERTIFIED (also: a certificate of the idealised algorithm only, printed NOT CERTIFIED FOR THE LIBRARY), 2 UNSUPPORTED, 3 INVALID INPUT, 4 usage error.
`recommend` (`FHE.Check.Recommend`): 0 certified parameters found (the plain check of the emitted
file is CERTIFIED), 1 none found within the constraints, 2 unsupported, 3 invalid input, 4 usage.
-/

open Lean FHE.Check

def usage : String :=
  "usage: fhe_check [--kappa K [--l2]] [--json] [--steps] [--dump-program] [--no-suggest] [--time]\n" ++
  "                 [--max-instructions N] FILE.fhecheck.json\n\n" ++
  -- BEGIN BFV (usage text: "BGV" -> "BGV or BFV"; one added line below)
  "Answers, backed by a machine-checked Lean theorem, whether a BGV or BFV program with its parameters\n" ++
  "is guaranteed (worst case) to decrypt correctly. Input: the neutral fhe-check/v1 JSON made by\n" ++
  "harness/frontend/{openfhe,heir} extractors.\n" ++
  "BFV (params.scheme = \"BFV\"): with a freshEncryption section the input noise is computed from the key and\n" ++
  "  sampler bounds (Challenge.BFVEncrypt.certifyBFVFresh?) and --kappa K [--l2] is available; without one, worst\n" ++
  "  case at the declared input noise (--kappa is refused); see harness/frontend/README.md.\n\n" ++
  -- END BFV
  "  --kappa K       bound the noise of the fresh encryptions with probability >= 1 - 2^-K over\n" ++
  "                  the encryption randomness (Hoeffding; Challenge.FreshNoise), keeping the\n" ++
  "                  evaluation worst-case. Default: worst case throughout. Needs a file whose\n" ++
  "                  frontend supplied freshEncryption (OpenFHE extractor). K >= 1; a report\n" ++
  s!"                  with K < {kappaFloor} carries a warning (2^-K is then not negligible).\n" ++
  "  --l2            with --kappa K: describe the fresh encryptions in l2 (Challenge.FreshNoiseL2):\n" ++
  "                  ||e_pk||_2^2 <= E2, ||s||_2^2 <= S2, sub-Gaussian proxies Vu, V1, V2, from the\n" ++
  "                  file's freshEncryption.l2 (ASSUMPTIONS) or computed from the support bounds\n" ++
  "  --no-suggest    on NOT CERTIFIED, do not search for the smallest change that would certify\n" ++
  "  --json          machine-readable report\n" ++
  "  --steps         also print the bound after every instruction (diagnostic)\n" ++
  "  --dump-program  print the decoded Source.Program the certificate is about\n" ++
  "  --time          print the wall-clock time of each phase (read, parse, decode, check) to stderr\n" ++
  "  --profile P     PROFILE MODE: certify against the implementation profile declared in P\n" ++
  "                  (fhe-check-profile/v1: the budget every operation is claimed to meet), with no\n" ++
  "                  library table: CERTIFIED exactly when Challenge.Profile.certifyProfile? (BGV) or\n" ++
  "                  certifyBFVProfile? (BFV) accepts at it; the report says whether the proved algorithm\n" ++
  "                  families are known to meet it (coverage). Not with --kappa. See harness/frontend/README.md\n" ++
  "  --emit-profile  print the profile the OpenFHE-table mode computes for FILE, in the same format\n" ++
  s!"  --max-instructions N  answer UNSUPPORTED for a program of more than N instructions (default\n" ++
  s!"                  {defaultMaxInstructions}; 0 = no limit). A resource guard, for BGV and BFV: time and memory are\n" ++
  "                  proportional to the program length; the refusal states the estimate.\n\n" ++
  s!"Certified operations: {supportedOps}\n" ++
  (if pendingOps.isEmpty then "\n" else s!"Recognised but not yet certified: {pendingOps}\n\n") ++
  "Exit codes: 0 CERTIFIED, 1 NOT CERTIFIED (also: a certificate of the idealised algorithm only, printed NOT CERTIFIED FOR THE LIBRARY), 2 UNSUPPORTED, 3 INVALID INPUT, 4 usage error.\n\n" ++
  "fhe_check recommend [options] FILE   finds certified parameters for the program in FILE\n" ++
  "                                     (fhe_check recommend --help)"

def emit (json : Bool) (path : String) (r : Result) (steps : Bool) : IO Unit :=
  if json then IO.println (renderJson path r).pretty
  else IO.println (renderHuman path r steps)

def recommendUsage : String :=
  "usage: fhe_check recommend [--target openfhe|heir|neutral] [--ring-dim N] [--security 128|192|256]\n" ++
  "                           [--digits keep|any|D] [--objective time|size] [--kappa K] [--margin BITS] [--emit OUT.json] [--json] FILE.fhecheck.json\n\n" ++
  "Keeps the program of FILE and searches for a modulus chain (actual primes, generated as the target\n" ++
  "library generates them) that the verified pipeline certifies, within a security cap on log2(Q*P)\n" ++
  "taken from the HomomorphicEncryption.org standard table (an INPUT ASSUMPTION). The verdict printed\n" ++
  "is fhe_check's plain check of the emitted parameters; optimality is not claimed.\n\n" ++
  "  --target T      prime rule and configuration output: openfhe (FIXEDMANUAL), heir (Lattigo backend),\n" ++
  "                  neutral. Default: from the file's source.tool\n" ++
  "  --ring-dim N    fixed ring dimension (default: the smallest N meeting the security level)\n" ++
  "  --security S    128 (default), 192 or 256 bits, classical, ternary secret\n" ++
  "  --digits D      key-switching digits: keep (default, the file's), any (searched), or a count\n" ++
  "                  (OpenFHE: dnum; HEIR/neutral: number of special primes = limbs per digit)\n" ++
  "  --objective O   time (default): the least predicted evaluation time (a fitted MODEL; the file's digit\n" ++
  "                  count is kept unless another is predicted faster by more than the model's error);\n" ++
  "                  size: the least log2(Q*P). Either way the verdict is the plain check's\n" ++
  "  --kappa K       probabilistic fresh noise, as in a plain check\n" ++
  "  --margin BITS   require at least BITS bits of margin on every output (default 0)\n" ++
  "  --sizes F,S     no search: evaluate these sizes (OpenFHE: SetFirstModSize F, SetScalingModSize S;\n" ++
  "                  HEIR/neutral: F,S or one size per limb), with --special-size P (HEIR/neutral),\n" ++
  "                  --ring-dim (default: the file's N) and --digits; prints the primes the library\n" ++
  "                  would generate and fhe_check's verdict on them\n" ++
  "  --emit OUT      write the recommended parameters as an fhe-check/v1 file (check it with fhe_check OUT,\n" ++
  "                  or fhe_check --kappa K OUT if --kappa K was given)\n" ++
  "  --json          machine-readable output\n" ++
  s!"  --max-instructions N  UNSUPPORTED above N instructions (default {defaultMaxInstructions}; 0 = no limit)\n\n" ++
  "Exit codes: 0 certified parameters found, 1 none found, 2 UNSUPPORTED, 3 INVALID INPUT, 4 usage error."

/-- Options of `fhe_check recommend`. -/
structure RecArgs where
  opts : Rec.Opts := {}
  emit : Option String := none
  json : Bool := false
  maxInstr : Nat := defaultMaxInstructions
  files : List String := []

def parseRecArgs : List String → RecArgs → Except String RecArgs
  | [], r => .ok { r with files := r.files.reverse }
  | "--json" :: rest, r => parseRecArgs rest { r with json := true }
  | "--target" :: v :: rest, r =>
    match v with
    | "openfhe" => parseRecArgs rest { r with opts.target := some .openfhe }
    | "heir" => parseRecArgs rest { r with opts.target := some .heir }
    | "neutral" => parseRecArgs rest { r with opts.target := some .neutral }
    | _ => .error s!"--target {v}: expected openfhe, heir or neutral"
  | "--ring-dim" :: v :: rest, r =>
    if v == "auto" then parseRecArgs rest { r with opts.ringDim := none }
    else if !v.isEmpty && v.length < 8 && v.all Char.isDigit && Rec.ringDims.contains v.toNat! then
      parseRecArgs rest { r with opts.ringDim := some v.toNat! }
    else .error s!"--ring-dim {v}: expected auto or one of {Rec.ringDims}"
  | "--security" :: v :: rest, r =>
    if v == "128" || v == "192" || v == "256" then parseRecArgs rest { r with opts.security := v.toNat! }
    else .error s!"--security {v}: expected 128, 192 or 256"
  | "--digits" :: v :: rest, r =>
    if v == "keep" then parseRecArgs rest { r with opts.digits := .keep }
    else if v == "any" then parseRecArgs rest { r with opts.digits := .any }
    else if !v.isEmpty && v.length < 4 && v.all Char.isDigit then
      parseRecArgs rest { r with opts.digits := .fixed v.toNat! }
    else .error s!"--digits {v}: expected keep, any or a count"
  | "--objective" :: v :: rest, r =>
    match v with
    | "time" => parseRecArgs rest { r with opts.objective := .time }
    | "size" => parseRecArgs rest { r with opts.objective := .size }
    | _ => .error s!"--objective {v}: expected time or size"
  | "--kappa" :: v :: rest, r =>
    if v.isEmpty || !v.all Char.isDigit || v.length > 7 || v.toNat! == 0 || v.toNat! > maxKappa then
      .error s!"--kappa {v}: K must be a natural number in 1..{maxKappa}"
    else parseRecArgs rest { r with opts.kappa := some v.toNat! }
  | "--emit" :: v :: rest, r => parseRecArgs rest { r with emit := some v }
  | "--max-instructions" :: v :: rest, r =>
    if !v.isEmpty && v.length ≤ 12 && v.all Char.isDigit then parseRecArgs rest { r with maxInstr := v.toNat! }
    else .error s!"--max-instructions {v}: expected a number of instructions (0 = no limit)"
  | "--sizes" :: v :: rest, r =>
    let parts := v.splitOn ","
    if parts.all (fun x => !x.isEmpty && x.length < 4 && x.all Char.isDigit) && parts.length ≤ 64 then
      parseRecArgs rest { r with opts.sizes := some (parts.map String.toNat!) }
    else .error s!"--sizes {v}: expected comma-separated bit sizes"
  | "--special-size" :: v :: rest, r =>
    if !v.isEmpty && v.length < 4 && v.all Char.isDigit then parseRecArgs rest { r with opts.specialSize := some v.toNat! }
    else .error s!"--special-size {v}: expected a bit size"
  | "--margin" :: v :: rest, r =>
    if !v.isEmpty && v.length < 4 && v.all Char.isDigit then parseRecArgs rest { r with opts.margin := v.toNat! }
    else .error s!"--margin {v}: expected a number of bits"
  | a :: rest, r =>
    if a.startsWith "--" then .error s!"{a}: unknown option, or missing value"
    else parseRecArgs rest { r with files := a :: r.files }

/-- `fhe_check recommend …` -/
def mainRecommend (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println recommendUsage; return 0
  let ra ← match parseRecArgs args {} with
    | .ok r => pure r
    | .error e => IO.eprintln s!"fhe_check recommend: {e}"; IO.eprintln recommendUsage; return 4
  let [path] := ra.files | IO.eprintln recommendUsage; return 4
  let text ← try IO.FS.readFile path catch e =>
    IO.eprintln s!"fhe_check recommend: cannot read {path}: {e}"; return 4
  let report := fun (r : Rec.Report) => do
    if ra.json then
      let j := if r.json.isNull then
        Json.mkObj [("tool", "fhe_check"), ("format", "fhe-check-recommend/v1"), ("input", Json.str path),
                    ("verdict", Json.str r.verdict.label), ("summary", Json.str r.headline),
                    ("notes", toJson r.lines)] else r.json
      IO.println j.pretty
    else
      IO.println s!"fhe_check recommend: {path}"
      IO.println s!"RECOMMENDATION: {r.verdict.label}: {r.headline}"
      unless r.lines.isEmpty do
        IO.println ""
        for l in r.lines do IO.println l
    if let (some out, some ej) := (ra.emit, r.emitted) then
      if r.verdict == .certified then IO.FS.writeFile out (ej.pretty ++ "\n")
    return r.verdict.exitCode
  if let .error e := lexCheck text then
    return (← report { verdict := .invalid, headline := s!"refused before parsing: {e}" })
  let j ← match Json.parse text with
    | .ok j => pure j
    | .error e => return (← report { verdict := .invalid, headline := s!"malformed JSON: {e}" })
  -- BEGIN BFV: no parameter search for BFV (harness/frontend/README.md, BFV section)
  if BFV.isBFV j then
    let why := "fhe_check recommend has no BFV mode: a BFV parameter search would have to model OpenFHE's BFV parameter generation (ring dimension, the auxiliary bases of the multiplication technique) and, for the default HPSPOVERQLEVELED, the internal drops of the hypothetical context (FindLevelsToDrop, which fhe_check does not model; the drops are an input assumption the extractor reads from a run). Re-generate the context, re-run and re-extract, and check the new file: harness/eval/frontier/frontier.py bfv searches OpenFHE's own BFV settings (multiplicative depth, scaling-mod size, digits, techniques) with the library in the loop, and harness/frontend/levelbfv/depth_table.py the depth alone for the chain program."
    return (← report { verdict := .unsupported, headline := why })
  -- END BFV
  match decode j with
  | .error e => report { verdict := .invalid, headline := e }
  | .ok (.unsupported what idx why) =>
    report { verdict := .unsupported,
             headline := s!"{what}{match idx with | some i => s!" (body[{i}])" | none => ""}: {why}" }
  | .ok (.ok inp) =>
    if ra.maxInstr != 0 && inp.prog.body.length > ra.maxInstr then
      report { verdict := .unsupported, headline := (tooLarge inp ra.maxInstr).headline ++
        " (fhe_check recommend runs the check once per candidate, so it takes many times longer.)" }
    else report (Rec.recommend path j inp ra.opts)

/-- Flush and exit at once with `code`. The check starts some of its parts in parallel tasks
(`Task.spawn` in `FHE.Check.Report.runCheck`, `FHE.Check.BFV.runCheck`); a task whose result a
refusal no longer needs may still be running, and the process must not wait for it. -/
def exitNow (code : UInt32) : IO UInt32 := do
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8

def mainCheck (args : List String) : IO UInt32 := do
  if args.head? == some "recommend" then return (← mainRecommend args.tail)
  if args.contains "--help" || args.contains "-h" then
    IO.println usage; return 0
  let json := args.contains "--json"
  let steps := args.contains "--steps"
  let dump := args.contains "--dump-program"
  let time := args.contains "--time"
  let suggest := !args.contains "--no-suggest"
  let l2 := args.contains "--l2"
  -- `--kappa K` and `--max-instructions N` take a value; everything else not starting with `--`
  -- is the input file
  let rec split : List String → Option Nat × Nat → List String →
      Except String ((Option Nat × Nat) × List String)
    | [], k, fs => .ok (k, fs.reverse)
    | "--kappa" :: v :: rest, (_, m), fs =>
      if v.isEmpty || !v.all Char.isDigit then .error s!"--kappa: \"{v}\" is not a natural number"
      else if v.length > 7 || v.toNat! > maxKappa then
        .error s!"--kappa {v}: K is at most {maxKappa} (a larger K only falls back to the worst case)"
      else if v.toNat! == 0 then
        .error "--kappa 0: a failure probability of at most 2^-0 = 1 says nothing; K must be at least 1"
      else split rest (some v.toNat!, m) fs
    | ["--kappa"], _, _ => .error "--kappa needs a value"
    | "--max-instructions" :: v :: rest, (k, _), fs =>
      if v.isEmpty || !v.all Char.isDigit || v.length > 12 then
        .error s!"--max-instructions: \"{v}\" is not a natural number (0 = no limit)"
      else split rest (k, v.toNat!) fs
    | ["--max-instructions"], _, _ => .error "--max-instructions needs a value (0 = no limit)"
    | a :: rest, k, fs => if a.startsWith "--" then split rest k fs else split rest k (a :: fs)
  -- `--profile P` takes a value (the profile file)
  let rec takeProfile : List String → Option String → List String →
      Except String (Option String × List String)
    | [], p, acc => .ok (p, acc.reverse)
    | "--profile" :: v :: rest, none, acc =>
      if v.startsWith "--" then .error "--profile needs a profile file" else takeProfile rest (some v) acc
    | "--profile" :: _ :: _, some _, _ => .error "--profile given twice"
    | ["--profile"], _, _ => .error "--profile needs a profile file"
    | a :: rest, p, acc => takeProfile rest p (a :: acc)
  let (profile, args) ← match takeProfile args none [] with
    | .ok r => pure r
    | .error e => IO.eprintln s!"fhe_check: {e}"; IO.eprintln usage; return 4
  let emitProfile := args.contains "--emit-profile"
  let ((kappa, maxInstr), files) ← match split args (none, defaultMaxInstructions) [] with
    | .ok r => pure r
    | .error e => IO.eprintln s!"fhe_check: {e}"; IO.eprintln usage; return 4
  let some path := files.head? | IO.eprintln usage; return 4
  unless files.length == 1 do IO.eprintln usage; return 4
  if l2 && kappa.isNone then
    IO.eprintln "fhe_check: --l2 selects the l2 description of the fresh encryptions and needs --kappa K"
    IO.eprintln usage; return 4
  if (profile.isSome || emitProfile) && (kappa.isSome || l2) then
    IO.eprintln "fhe_check: --profile and --emit-profile are worst-case modes at the declared inputNoise; --kappa and --l2 do not apply"
    IO.eprintln usage; return 4
  if profile.isSome && emitProfile then
    IO.eprintln "fhe_check: --profile checks a profile, --emit-profile writes one: give one of them"
    IO.eprintln usage; return 4
  let t0 ← IO.monoNanosNow
  let ms := fun (a b : Nat) => s!"{(b - a) / 1000000} ms"
  let invalid := fun (msg : String) => do
    let r : Result := { verdict := .invalid, headline := msg }
    emit json path r false
    return Verdict.invalid.exitCode
  -- the size limit, before the file is read
  let size ← try pure (some (← System.FilePath.metadata path).byteSize) catch _ => pure none
  if let some sz := size then
    if sz.toNat > maxInputBytes then
      return (← invalid s!"refused before parsing: the input is larger than {maxInputBytes} bytes ({sz.toNat} bytes)")
  let text ← try IO.FS.readFile path catch e =>
    IO.eprintln s!"fhe_check: cannot read {path}: {e}"; return 4
  let tFile ← IO.monoNanosNow
  if let .error e := lexCheck text then return (← invalid s!"refused before parsing: {e}")
  let tRead ← IO.monoNanosNow
  let j ← match Json.parse text with
    | .ok j => pure j
    | .error e => return (← invalid s!"malformed JSON: {e}")
  -- PROFILE MODE (`FHE.Check.Profile`): the verdict is the locked profile decision at the declared
  -- budget, computed by the holes `FHE.Holes.certifyProfileFast`, `certifyBFVProfileFast`
  if emitProfile then
    match Profile.emit j with
    | .ok pj => IO.println pj.pretty; return (← exitNow 0)
    | .error e => IO.eprintln s!"fhe_check --emit-profile: {path}: {e}"; return (← exitNow 3)
  if let some pp := profile then
    let invalidP := fun (msg : String) => do
      let r : Profile.Res := { verdict := .invalid, headline := msg }
      if json then IO.println (Profile.renderJson path pp r).pretty
      else IO.println (Profile.renderHuman path pp r)
      return Verdict.invalid.exitCode
    let psize ← try pure (some (← System.FilePath.metadata pp).byteSize) catch _ => pure none
    if let some sz := psize then
      if sz.toNat > maxInputBytes then
        return (← invalidP s!"profile: refused before parsing: larger than {maxInputBytes} bytes")
    let ptext ← try IO.FS.readFile pp catch e =>
      IO.eprintln s!"fhe_check: cannot read {pp}: {e}"; return 4
    if let .error e := lexCheck ptext then return (← invalidP s!"profile: refused before parsing: {e}")
    let pj ← match Json.parse ptext with
      | .ok v => pure v
      | .error e => return (← invalidP s!"profile: malformed JSON: {e}")
    let tP ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => Profile.check j pj maxInstr
    let tC ← IO.monoNanosNow
    let out := if json then (Profile.renderJson path pp r).pretty else Profile.renderHuman path pp r
    IO.println out
    if time then
      IO.eprintln s!"fhe_check: read+parse {ms t0 tP}, profile check (decode + decision + coverage) {ms tP tC}; verdict {r.verdict.label}"
    return (← exitNow r.verdict.exitCode)
  -- BEGIN BFV: `params.scheme = "BFV"` is checked by the BFV pipeline (FHE.Check.BFVReport);
  -- every other input takes the path below, unchanged.
  if BFV.isBFV j then
    if time then
      -- the phases of the BFV check, timed one by one (diagnostic only: the verdict printed
      -- below is `BFV.check`'s; these evaluations only measure)
      let tParse ← IO.monoNanosNow
      IO.eprintln s!"fhe_check: read {ms t0 tFile}, lex {ms tFile tRead}, JSON parse {ms tRead tParse}"
      let d ← IO.lazyPure fun _ => BFV.decode j
      let tDec ← IO.monoNanosNow
      if let .ok (.ok inp) := d then
        IO.eprintln s!"fhe_check: decode {ms tParse tDec} ({inp.base.prog.body.length} instructions)"
        let br ← IO.lazyPure fun _ => BFV.computeBudget inp
        let tB ← IO.monoNanosNow
        IO.eprintln s!"fhe_check:   budget (computeBudget) {ms tDec tB}"
        if let .ok br := br then
          let P := inp.base.P
          let prog := inp.base.prog
          let st ← IO.lazyPure fun _ => BFV.replay P br.E prog
          let tR ← IO.monoNanosNow
          IO.eprintln s!"fhe_check:   diagnostic replay {ms tB tR} ({st.size} steps)"
          let a ← IO.lazyPure fun _ => BFV.analyzer P br.E prog
          let tA ← IO.monoNanosNow
          IO.eprintln s!"fhe_check:   analysis (analyzeBFVFast) {ms tR tA} ({a.isSome})"
          let c ← IO.lazyPure fun _ => FHE.Holes.certifyBFVFast br.x
          let tC ← IO.monoNanosNow
          IO.eprintln s!"fhe_check:   decision (certifyBFVFast, worst-case mode) {ms tA tC} ({c.isSome})"
      let tS ← IO.monoNanosNow
      let r ← IO.lazyPure fun _ => BFV.check j { kappa, suggest, l2, maxInstr }
      let tK ← IO.monoNanosNow
      IO.eprintln s!"fhe_check: whole check (decode + all of the above + report data) {ms tS tK}; verdict {r.verdict.label}"
      let out := if json then (BFV.renderJson path r).pretty else BFV.renderHuman path r steps
      let tO ← IO.monoNanosNow
      IO.eprintln s!"fhe_check: render {ms tK tO} ({out.length} characters)"
      IO.println out
      IO.eprintln s!"fhe_check: total {ms t0 tO}"
      return (← exitNow r.verdict.exitCode)
    let r := BFV.check j { kappa, suggest, l2, maxInstr }
    if dump then
      if let some inp := r.input then IO.eprintln (repr inp.base.prog).pretty
    let out := if json then (BFV.renderJson path r).pretty else BFV.renderHuman path r steps
    let t1 ← IO.monoNanosNow
    IO.println out
    if time then IO.eprintln s!"fhe_check: checked in {ms t0 t1}"
    return (← exitNow r.verdict.exitCode)
  -- END BFV
  let tParse ← IO.monoNanosNow
  let mut tDecode := tParse
  let r ← match decode j with
    | .error e => return (← invalid e)
    | .ok (.unsupported what idx why) =>
      pure ({ verdict := .unsupported,
              headline := s!"{what}{match idx with | some i => s!" (body[{i}])" | none => ""}: {why}" } : Result)
    | .ok (.ok inp) =>
      tDecode ← IO.monoNanosNow
      if time then IO.eprintln s!"fhe_check: read {ms t0 tFile}, lex {ms tFile tRead}, JSON parse {ms tRead tParse}, decode {ms tParse tDecode} ({inp.prog.body.length} instructions)"
      let n := inp.prog.body.length
      if maxInstr != 0 && n > maxInstr then
        pure (tooLarge inp maxInstr)
      else
        if dump then IO.eprintln (repr inp.prog).pretty
        -- evaluated here (not where the report first reads it), so that `--time` splits the
        -- check from the rendering
        IO.lazyPure fun _ => runCheck inp { kappa, suggest, l2 }
  let tCheck ← IO.monoNanosNow
  -- force the result before stopping the clock
  let out := if json then (renderJson path r).pretty else renderHuman path r steps
  let t1 ← IO.monoNanosNow
  IO.println out
  if time then
    IO.eprintln s!"fhe_check: check {ms tDecode tCheck} (verdict {r.verdict.label}), render {ms tCheck t1} ({out.length} characters); total {ms t0 t1}"
  return (← exitNow r.verdict.exitCode)

/-- The entry point. If the reader of standard output has gone away (a closed pipe: `fhe_check … |
head -1`), writing the report fails with a broken-pipe error; exit quietly with 141 (128 + SIGPIPE,
the status a process killed by that signal reports), which is none of the verdict codes 0 to 4.
Every other error is raised as before. -/
def main (args : List String) : IO UInt32 := do
  try mainCheck args
  catch
    | .resourceVanished _ _ => IO.Process.exit 141
    | e => throw e
