import FHE.Check.Budget
import FHE.Check.Security
import Challenge.Headline.Defs
import Challenge.Certify.Defs
import FHE.Holes
import FHE.Noise.FastScaling
import Spec.Decrypt
import Spec.Encrypt
import Spec.Scaling
import Challenge.Word

set_option autoImplicit false

/-!
# FHE.Check.Report — the `fhe_check` pipeline and its report   (UNTRUSTED glue)

**The verdict CERTIFIED is issued in one place only: where the locked function
`Challenge.Certify.certify?` returns a certificate** for the decoded data (`certificate?` below;
`runCheck`, "THE VERDICT"). `certify?` performs every check listed here itself, and the locked
statements `Challenge.Certify.*` are of the form `certify? x = some c → …`, so this file composes
nothing: it decodes, calls `certify?`, and prints the certificate. Everything else in `runCheck`
only explains refusals (and can refuse more: a modulus-switching method other than the centred
t-corrected one, a disagreement with the frontend's `expect` annotations, a printed figure that
is not the certificate's).

**What `certify?` evaluates** (compiled code; `Challenge.Certify.Defs`):

1. the mode: worst case at the declared input noise; or `--kappa κ`: `Spec.Encrypt.freshOK?` on
   the inputs and the input noise **replaced** by `Spec.Encrypt.freshNoise t ε`, with
   `ε = Spec.Encrypt.epsFor …` (failure probability at most `2^(−κ)`), or `worstError` (no
   probability) when the former is not smaller; or `--kappa κ --l2`: the same with the `ℓ₂`
   variance proxy `Spec.Encrypt.varProxyL2` (no fallback);
2. `Spec.schemeParamsOK?` and `Spec.Budget.specialOK?`; the key-switching layout at every level;
3. `Challenge.Headline.refAnalyze` on the program at the budget `Spec.Budget.certified P lay`
   (`FHE.Check.Budget`), and on each output alone;
4. `Spec.Encrypt.certOK?` on each output with its own bound (under the secret key itself; the
   switched decryption exact, if the frontend declares it).

**Each verdict CERTIFIED instantiates exactly one locked statement** (`Challenge.Certify`):
`worst_certified` (worst case), `fresh_kappa_certified` (`--kappa`), `fresh_worst_certified`
(`--kappa` falling back to the worst case of a fresh encryption), `fresh_l2_certified`
(`--kappa --l2`); each is about all outputs jointly, each with its own bound.

Per-output bounds are the certificate's. On a refusal the diagnostic replay explains it; the first failing instruction is confirmed by `refAnalyze` on the prefixes around
it. Everything else here is *diagnostic* (which clause failed, how large the overflowing bound
was) and labelled so in the output; it never turns a rejection into an acceptance.
-/

namespace FHE.Check
open Lean Spec Spec.Source Challenge.Headline

/-- The analyzer `fhe_check` runs: `FHE.Holes.analyzeFast` (`FHE/Noise/Fast.lean`: environments
in search trees, near-linear), which the locked statement `Challenge.Fast.analyzeFast_eq` proves
equal, on every input, to the reference analyzer `refAnalyze` the cited theorems are about. -/
def analyzer : NoiseAnalyzer := FHE.Holes.analyzeFast

def analyzerName : String := "Challenge.Headline.refAnalyze"

/-- Largest `--kappa` accepted, and the floor below which a report carries a warning: a failure
probability of `2^-K` with `K < 40` (one in a trillion) is not negligible for a statement meant
to hold over every encryption a deployment ever makes. -/
def maxKappa : Nat := 1000000
def kappaFloor : Nat := 40

/-- Default limit on the number of instructions (`--max-instructions N`, 0 = no limit), for both
schemes. The check is near-linear in the program length (`FHE/Noise/Fast.lean`); the limit is a
resource guard, not a time-out for a quadratic analysis. Measured
(`harness/eval/analyzer-speed/RESULTS.md`): about 15 to 80 microseconds and 0.7 to 1.8 kB of peak
memory per instruction, so a program at the limit takes 30 s (BGV) to 2.5 min (BFV) and up to 3.5 GB. -/
def defaultMaxInstructions : Nat := 2000000

/-! ### Verdicts -/

inductive Verdict
  | certified | notCertified | unsupported | invalid
  deriving BEq

def Verdict.label : Verdict → String
  | .certified => "CERTIFIED" | .notCertified => "NOT CERTIFIED"
  | .unsupported => "UNSUPPORTED" | .invalid => "INVALID INPUT"

def Verdict.exitCode : Verdict → UInt32
  | .certified => 0 | .notCertified => 1 | .unsupported => 2 | .invalid => 3

/-! ### Instruction printing -/

def instrOp : Instr → String
  | .add .. => "add" | .sub .. => "sub" | .mul .. => "mul" | .square .. => "square"
  | .mulConst .. => "mulConst" | .copy .. => "copy" | .toEval .. => "toEval"
  | .toCoeff .. => "toCoeff" | .relin .. => "relin" | .keySwitch .. => "keySwitch"
  | .automorph .. => "automorph" | .modSwitch .. => "modSwitch"
  | .addPlain .. => "addPlain" | .subPlain .. => "subPlain" | .mulPlain .. => "mulPlain"
  | .dropLimbs .. => "dropLimbs"

def instrStr : Instr → String
  | .add d a b => s!"{d} = add {a} {b}" | .sub d a b => s!"{d} = sub {a} {b}"
  | .mul d a b => s!"{d} = mul {a} {b}" | .square d a => s!"{d} = square {a}"
  | .mulConst d a c => s!"{d} = mulConst {a} {c}" | .copy d a => s!"{d} = copy {a}"
  | .toEval d a => s!"{d} = toEval {a}" | .toCoeff d a => s!"{d} = toCoeff {a}"
  | .relin d a => s!"{d} = relin {a}" | .keySwitch d a => s!"{d} = keySwitch {a}"
  | .automorph d a g => s!"{d} = automorph {a} {g}" | .modSwitch d a => s!"{d} = modSwitch {a}"
  | .addPlain d a p => s!"{d} = addPlain {a} {p}" | .subPlain d a p => s!"{d} = subPlain {a} {p}"
  | .mulPlain d a p => s!"{d} = mulPlain {a} {p}" | .dropLimbs d a k => s!"{d} = dropLimbs {a} {k}"

/-! ### Diagnostics (unverified; never decide the verdict) -/

/-- The first clause of `SchemeParamsOK` that fails, as text (diagnostic mirror of
`Spec.schemeParamsOK?`). `chain` names what `qs` is. -/
def paramsClause (P : FullParams) (chain : String) : String := Id.run do
  let s := P.src
  if s.N ≠ 2 ^ Nat.log2 s.N then return s!"N_pow2: N = {s.N} is not a power of two"
  if s.qs.isEmpty then return "qs_nonempty: the modulus chain is empty"
  for h : i in [:s.qs.length] do
    let q := s.qs[i]
    if !primeOK? q then
      return s!"prime: {chain}[{i}] = {q} is not accepted as prime by Spec.primeOK? (composite, even, or without a quadratic non-residue below 64)"
  if !s.qs.Nodup then return s!"distinct: a prime occurs twice in {chain}"
  if s.t < 2 then return s!"plaintext: t = {s.t} < 2"
  for h : i in [:s.qs.length] do
    if Nat.gcd s.t s.qs[i] ≠ 1 then
      return s!"plaintext: t = {s.t} is not coprime to {chain}[{i}] = {s.qs[i]}"
  if s.t / 2 > P.inputNoise then
    return s!"msgRange: inputNoise = {P.inputNoise} < t/2 = {s.t / 2} (the bound would exclude some messages)"
  return "(no failing clause found by the diagnostic mirror)"

/-- Why `Source.step` rejects an instruction (diagnostic). -/
def stepWhy (P : Params) (ρ : Env P) (i : Instr) : String :=
  let undef := fun (x : Var) => (ρ x).isNone
  let operands : List Var := match i with
    | .add _ a b | .sub _ a b | .mul _ a b => [a, b]
    | .square _ a | .mulConst _ a _ | .copy _ a | .toEval _ a | .toCoeff _ a | .relin _ a
    | .keySwitch _ a | .automorph _ a _ | .modSwitch _ a | .dropLimbs _ a _ => [a]
    | .addPlain _ a p | .subPlain _ a p | .mulPlain _ a p => [a, p]
  match operands.find? undef with
  | some x => s!"operand {x} is not defined at this point"
  | none =>
    let v := fun x => (ρ x).getD { msg := .exact 0, parts := 0, level := 0, key := 0, scale := 0 }
    match i with
    | .add _ a b | .sub _ a b | .mul _ a b =>
      if (v a).level ≠ (v b).level then s!"operands at different levels ({(v a).level} and {(v b).level})"
      else if (v a).key ≠ (v b).key then s!"operands under different keys (Galois {(v a).key} and {(v b).key}); key-switch first"
      else "operands do not fit (parts)"
    | .relin _ a => s!"relin needs a 3-part ciphertext under s; {a} has {(v a).parts} parts under Galois key {(v a).key}"
    | .keySwitch _ a => s!"keySwitch needs a 2-part ciphertext; {a} has {(v a).parts} parts"
    | .automorph _ _ g => s!"Galois element {g} is even"
    | .modSwitch _ a => s!"modSwitch needs level >= 2 inside the chain; {a} is at level {(v a).level}"
    | .addPlain _ a p | .subPlain _ a p | .mulPlain _ a p =>
      if (v p).parts ≠ 1 then s!"plaintext operand {p} has {(v p).parts} parts (must be 1)"
      else s!"operands at different levels ({a}: {(v a).level}, {p}: {(v p).level})"
    | .dropLimbs _ a k => s!"dropLimbs {k} must leave at least one limb; {a} is at level {(v a).level}"
    | _ => "ill-formed instruction"

/-- One step of the diagnostic replay. -/
structure StepInfo where
  idx : Nat
  instr : Instr
  /-- `none`: `Source.step` rejected the instruction (with the reason). -/
  ill : Option String
  level : Nat
  parts : Nat
  bound : Nat
  /-- `P.src.modulus level`. -/
  Q : Nat
  /-- The Galois element of the key the destination is under (diagnostic). -/
  key : Nat := 1

/-- Replay of `refRun` that records every step up to and including the first ill-formed or
overflowing one (diagnostic; the locked `refBound` and `Source.step` give the numbers). The
environments are search trees (`ZEnv`; the locked functions are called on lookups backed by
them), so the replay is near-linear in the program length. Also returns `(level, key)` of every variable in
the final environment. -/
def replay (P : FullParams) (E : Trace.Budget) (prog : Program) :
    Array StepInfo × Std.HashMap Var (Nat × Nat) := Id.run do
  -- the moduli of the levels, computed once (`FHE.Noise.Fast.modsOf`)
  let Qt := FHE.Noise.Fast.modAt P (FHE.Noise.Fast.modsOf P)
  let mut ρ := ZEnv.init P.src prog
  -- initial bounds as in `refAnalyze`: the declared bound if smaller than `inputNoise`
  -- (`FHE.Noise.Fast.initBoundMap`; `Validation.Fast.Aux.initBoundMap_get`)
  let mut β : Std.TreeMap Var Nat := FHE.Noise.Fast.initBoundMap P prog
  let mut out := #[]
  let mut idx := 0
  for i in prog.body do
    let bm := β
    match ρ.step i, refBound P E ρ.get (fun x => bm[x]?) i with
    | some ρ', some b =>
      let v := (ρ'.get (Trace.dst i)).getD { msg := .exact 0, parts := 0, level := 0, key := 0, scale := 0 }
      out := out.push { idx, instr := i, ill := none, level := v.level, parts := v.parts, bound := b,
                        Q := Qt v.level, key := v.key }
      ρ := ρ'
      -- stop at the first overflow, as the verified analyzer does (past it, bounds square at
      -- every multiplication and their size grows exponentially)
      if 2 * b ≥ Qt v.level then break
      β := β.insert (Trace.dst i) b
    | _, _ =>
      out := out.push { idx, instr := i, ill := some (stepWhy P.src ρ.get i), level := 0, parts := 0,
                        bound := 0, Q := 0 }
      break
    idx := idx + 1
  return (out, ρ.m.foldl (init := {}) fun acc x v => acc.insert x (v.level, v.key))

/-! ### The result of a check -/

structure OutputInfo where
  name : Var
  level : Nat
  bound : Nat
  Q : Nat
  /-- The Galois element of the key the output is under (`Spec.Encrypt.outputKey?`); the
  certificate needs `some 1`. -/
  key : Option Nat := none
  /-- Switched decryption only: `Spec.Decrypt.decBound` at the output's level, and whether
  `Spec.Decrypt.decryptAllOK?` accepted this output. -/
  decBound : Option Nat := none
  decOK : Bool := true

/-- The five numbers of the `ℓ₂` mode, and which of them the input supplied (an ASSUMPTION) rather
than the tool computing it from the support bounds. -/
structure L2Vals where
  E2 : Nat
  S2 : Nat
  Vu : Nat
  V1 : Nat
  V2 : Nat
  /-- Supplied by the input: `(E2, S2, Vu, V1, V2)`. -/
  given : Bool × Bool × Bool × Bool × Bool
  source : String := ""

/-- The `ℓ₂` numbers for a file: each field of `freshEncryption.l2` the input gives (an
ASSUMPTION), otherwise computed from the declared support bounds: `‖e_pk‖₂² ≤ N·Bk²`,
`‖s‖₂² ≤ N·Bs²` (`Challenge.FreshNoiseL2.normSq_le`: always true within the support bounds), and
the squared support bounds as variance proxies (bounded coefficients are, about their means, sub-Gaussian
with that proxy: Hoeffding's lemma, `subGaussSamplerOK_of_samplerOK`). With nothing supplied the
`ℓ₂` variance proxy equals the support one (`varProxyL2_support`). -/
def l2Values (P : FullParams) (fm : FreshModel) : L2Vals :=
  let d : L2Decl := fm.l2.getD {}
  let N := P.src.N
  { E2 := d.keyErrorSq.getD (N * fm.keyError ^ 2), S2 := d.secretSq.getD (N * P.secretBound ^ 2),
    Vu := d.uProxy.getD (fm.u ^ 2), V1 := d.e1Proxy.getD (fm.e1 ^ 2), V2 := d.e2Proxy.getD (fm.e2 ^ 2),
    given := (d.keyErrorSq.isSome, d.secretSq.isSome, d.uProxy.isSome, d.e1Proxy.isSome, d.e2Proxy.isSome),
    source := d.source }

/-- The probabilistic mode (`--kappa`): everything `Challenge.FreshNoise.fresh_certified_kappa`
is instantiated with. -/
structure KappaInfo where
  kappa : Nat
  /-- Number of fresh encryptions. -/
  n : Nat
  varProxy : Nat
  /-- Events in the union bound: `n · 2N`. -/
  count : Nat
  /-- The error bound used: `Spec.Encrypt.epsFor varProxy count kappa`, or `worst` if that is not
  smaller (`deterministic`). -/
  eps : Nat
  /-- `Spec.Encrypt.epsFor varProxy count kappa` (whether used or not). -/
  epsKappa : Nat
  /-- The worst case of the fresh error was used: no probability
  (`Challenge.FreshNoise.fresh_worst_decrypts`). -/
  deterministic : Bool
  /-- `Spec.Encrypt.worstError`, for comparison. -/
  worst : Nat
  /-- `Spec.Encrypt.freshNoise t Bp eps`: the input noise the analyzer was run at. -/
  inputNoise : Nat
  /-- `Bp`: the bound on the stored plaintext polynomials (`FreshModel.bp`). -/
  plainBound : Nat
  /-- The mean drift contained in `epsKappa` (`Spec.Encrypt.meanDrift`; `0` for mean bound 0). -/
  drift : Nat := 0
  /-- The frontend's worst-case input noise (not used in this mode). -/
  suppliedNoise : Nat
  model : FreshModel
  /-- `--l2`: the `ℓ₂` description used (`Challenge.FreshNoiseL2`). -/
  l2 : Option L2Vals := none

/-- Command-line options that change what is computed. -/
structure Options where
  kappa : Option Nat := none
  /-- The instruction limit (`--max-instructions`; 0 = none). Enforced by the caller for BGV
  (`FheCheck.lean`) and by `BFV.check` for BFV, after decoding and before any analysis. -/
  maxInstr : Nat := 0
  /-- With `kappa`: the `ℓ₂` description of the fresh encryptions (`--l2`). -/
  l2 : Bool := false
  suggest : Bool := true

structure Failure where
  /-- What failed, in words. -/
  what : String
  step : Option StepInfo := none
  /-- Whether `refAnalyze` on the prefixes confirmed the location. -/
  confirmed : Bool := false
  /-- A noise or decryption-bound overflow (as opposed to an ill-formed input): the kind of
  failure a parameter change can fix. -/
  overflow : Bool := false

structure Result where
  verdict : Verdict
  headline : String
  input : Option Input := none
  schemeOK : Option Bool := none
  specialOK : Option Bool := none
  budget : Option BudgetReport := none
  /-- The value `refAnalyze` returned (max over outputs). -/
  analyzed : Option Nat := none
  outputs : List OutputInfo := []
  failure : Option Failure := none
  steps : Array StepInfo := #[]
  warnings : List String := []
  /-- `some` iff the verdict was computed in the probabilistic mode. -/
  kappa : Option KappaInfo := none
  /-- "Smallest fix" suggestions (searches with the verified analyzer; not theorems). -/
  suggestions : List String := []
  /-- CERTIFIED at phase level only: user-level decryption (`userDecryption`) is not covered, for
  an input that is not extracted from a library (printed as `CERTIFIED AT PHASE LEVEL`, never as
  the plain CERTIFIED; for a library-extracted input the verdict is withheld instead). -/
  phaseOnly : Bool := false
  /-- `userDecryption` of the input, as `runCheck` computed it for a CERTIFIED verdict (the
  rendering reads it instead of evaluating the scaling check again). -/
  userDec : Option (Bool × String) := none

/-- The verdict as printed (`phaseOnly`: `CERTIFIED AT PHASE LEVEL`). -/
def Result.label (r : Result) : String :=
  if r.verdict == .certified && r.phaseOnly then "CERTIFIED AT PHASE LEVEL" else r.verdict.label

/-- The refusal of a program of `n` instructions above the instruction limit (no analysis is
run). -/
def tooLargeHeadline (n limit : Nat) : String :=
  s!"program too large: {n} instructions, above the limit of {limit} (--max-instructions N; 0 = no limit). The limit is a resource guard: the check takes time and memory proportional to the program length (measured on one machine, harness/eval/analyzer-speed/RESULTS.md: about 15 to 80 microseconds and 0.7 to 1.8 kB per instruction, so up to about {(n * 80 + 500000) / 1000000} s and {n * 18 / 10000 + 80} MB for this program). Re-run with --max-instructions 0 to check it anyway."

/-- The answer for a program above the instruction limit (no analysis is run). -/
def tooLarge (inp : Input) (limit : Nat) : Result :=
  { verdict := .unsupported, headline := tooLargeHeadline inp.prog.body.length limit }

/-- Which clause of `Spec.Budget.SpecialOK` fails (diagnostic mirror of `specialOK?`). -/
def specialClause (P : FullParams) : String := Id.run do
  let ps := P.store.special.map (·.q)
  for h : i in [:ps.length] do
    if ps[i] < 2 then return s!"special[{i}] = {ps[i]} < 2"
    if ps[i] % 2 ≠ 1 then return s!"special[{i}] = {ps[i]} is even (special primes must be odd)"
  for h : i in [:ps.length] do
    for h2 : j in [i+1:ps.length] do
      if Nat.gcd ps[i] ps[j] ≠ 1 then return s!"special[{i}] and special[{j}] are not coprime"
  for h : i in [:ps.length] do
    for q in P.src.qs do
      if Nat.gcd ps[i] q ≠ 1 then return s!"special[{i}] = {ps[i]} is not coprime to the ciphertext prime {q}"
    if Nat.gcd P.src.t ps[i] ≠ 1 then return s!"special[{i}] = {ps[i]} is not coprime to t = {P.src.t}"
  return "(no failing clause found by the diagnostic mirror)"

/-- Analyze one prefix of the body with one output (used to localise a failure with the
verified analyzer). -/
def analyzeAt (P : FullParams) (E : Trace.Budget) (prog : Program) (k : Nat) : Option Nat :=
  match prog.body[k]? with
  | some i => analyzer P E { prog with body := prog.body.take (k + 1), outputs := [Trace.dst i] }
  | none => none

def chainName : String := "limbs"

/-- Where the bound on the stored plaintext polynomials comes from (printed). -/
def bpSource (fm : FreshModel) (t : Nat) : String :=
  match fm.plainBound with
  | some _ => "declared by the input, freshEncryption.plaintextBound; an ASSUMPTION about the encoder"
  | none => s!"ASSUMED, not declared by the input: t - 1 = {t - 1}, a representative in [0, t), as a packed encoding stores"

/-- Where the mean bound of the samplers comes from (printed). -/
def meanSource (fm : FreshModel) : String :=
  if fm.meanGiven then "declared by the input, freshEncryption.mean; an ASSUMPTION about the samplers"
  else "ASSUMED, not declared by the input: mean zero"

/-! ### The verdict: `Challenge.Certify.certify?` -/

/-- The mode of `certify?` for the probabilistic modes. -/
def certMode (i : KappaInfo) : Spec.Certify.Mode :=
  match i.l2 with
  | none => .fresh i.model.inputs i.plainBound i.model.keyError i.model.u i.model.e1 i.model.e2
      i.model.meanNum i.model.meanDen i.kappa
  | some v => .freshL2 i.model.inputs i.plainBound v.E2 v.S2 v.Vu v.V1 v.V2
      i.model.meanNum i.model.meanDen i.kappa

/-- The declared modulus-switching method, as `certify?` takes it. -/
def msMethodOf (m : String) : Spec.Certify.MSMethod :=
  if m == "t-corrected-centred" then .centred
  else if m == "t-corrected-canonical" then .canonical else .other

/-- **The one decision.** `some c` iff the locked `certify?` certifies the decoded data, computed
by `FHE.Holes.certifyFast` (`FHE/Noise/Fast.lean`), which is equal to `certify?` on every input
(the locked statement `Challenge.Fast.certifyFast_eq`, proved in `Validation/Fast.lean`): the
DECLARED parameters (in the fresh modes `certify?` replaces the input noise itself), the layout,
the program, the decryption, the mode, the declared modulus-switching method. -/
def certificate? (P : FullParams) (lay : Budget.KSLayout) (prog : Program) (dec : DecMethod)
    (ki : Option KappaInfo) (ms : String := "t-corrected-centred") :
    Option Spec.Certify.Certificate :=
  FHE.Holes.certifyFast { P, lay, prog, switched := dec == .switched,
                          mode := match ki with | none => .worstCase | some i => certMode i,
                          msMethod := msMethodOf ms }

/-! ### Hypothetical acceptance (suggestions only; never a verdict) -/

/-- Whether `refAnalyze` at the certified budget and `Spec.Encrypt.certOK?` on every output
would accept `prog` at the (possibly hypothetical, non-prime) parameters `P`. It does NOT check
the parameters, so it is not `certify?` and decides no verdict: it is used only by the "smallest
fix" suggestions, whose output is labelled as not a theorem. -/
def accepts (P : FullParams) (lay : Budget.KSLayout) (prog : Program) (dec : DecMethod) : Bool :=
  let E := Budget.certified P lay
  match analyzer P E prog with
  | none => false
  | some B =>
    -- with one output, `{ prog with outputs := [o] }` is `prog` itself: reuse its bound
    if prog.outputs.length == 1 then Encrypt.certOK? P prog B (dec == .switched) else
    prog.outputs.all fun o =>
      match analyzer P E { prog with outputs := [o] } with
      | some b => Encrypt.certOK? P { prog with outputs := [o] } b (dec == .switched)
      | none => false

/-- DIAGNOSTIC MIRROR of the mode selection inside `certify?` (`Spec.Certify.freshEps`), used to
explain refusals and to print; on CERTIFIED, `runCheck` checks that these figures are the
certificate's. The parameters of the fresh-encryption mode at exponent `κ`: the input noise is
`freshNoise t Bp ε` with `ε = epsFor V (n·2N) κ + meanDrift …`, or `ε = worstError` if that is not
larger (then nothing is probabilistic). `none` if the variance proxy is zero. -/
def kappaInfo (P : FullParams) (fm : FreshModel) (κ : Nat) : Option KappaInfo :=
  let V := Encrypt.varProxy P.src.N P.secretBound fm.keyError fm.u fm.e1 fm.e2
  let n := fm.inputs.length
  let count := n * (2 * P.src.N)
  let drift := Spec.Certify.freshDrift P fm.keyError fm.meanNum fm.meanDen
  let epsKappa := Encrypt.epsFor V count κ + drift
  let worst := Encrypt.worstError P.src.N P.secretBound fm.keyError fm.u fm.e1 fm.e2
  let deterministic := decide (worst ≤ epsKappa)
  let eps := if deterministic then worst else epsKappa
  let Bp := fm.bp P.src.t
  if V = 0 then none else
  some { kappa := κ, n, varProxy := V, count, eps, epsKappa, deterministic, worst,
         inputNoise := Encrypt.freshNoise P.src.t Bp eps, suppliedNoise := P.inputNoise,
         model := fm, plainBound := Bp, drift := if deterministic then 0 else drift }

/-- The same for the `ℓ₂` mode (`--l2`): `ε = epsFor (varProxyL2 E2 S2 Vu V1 V2) (n·2N) κ +
meanDrift (E2 + 1 + S2) mn md`, no fallback to the worst case (`certify?`, mode `freshL2`). -/
def kappaInfoL2 (P : FullParams) (fm : FreshModel) (κ : Nat) : Option KappaInfo :=
  let v := l2Values P fm
  let V := Encrypt.varProxyL2 v.E2 v.S2 v.Vu v.V1 v.V2
  let n := fm.inputs.length
  let count := n * (2 * P.src.N)
  let drift := Encrypt.meanDrift (v.E2 + 1 + v.S2) fm.meanNum fm.meanDen
  let eps := Encrypt.epsFor V count κ + drift
  let worst := Encrypt.worstError P.src.N P.secretBound fm.keyError fm.u fm.e1 fm.e2
  let Bp := fm.bp P.src.t
  if V = 0 then none else
  some { kappa := κ, n, varProxy := V, count, eps, epsKappa := eps, deterministic := false, worst,
         inputNoise := Encrypt.freshNoise P.src.t Bp eps, suppliedNoise := P.inputNoise,
         model := fm, l2 := some v, plainBound := Bp, drift }

/-- The mode's figures at exponent `κ` (`ℓ₂` if `l2`). -/
def kappaInfoAt (P : FullParams) (fm : FreshModel) (l2 : Bool) (κ : Nat) : Option KappaInfo :=
  if l2 then kappaInfoL2 P fm κ else kappaInfo P fm κ

/-- Whether the fresh-encryption mode at `κ` certifies: `Challenge.Certify.certify?`. -/
def acceptsKappa (P : FullParams) (lay : Budget.KSLayout) (prog : Program) (dec : DecMethod)
    (fm : FreshModel) (l2 : Bool) (κ : Nat) : Bool :=
  match kappaInfoAt P fm l2 κ with
  | none => false
  | some ki => (certificate? P lay prog dec (some ki)).isSome

/-- Largest `k ∈ [lo, hi]` with `f k`, by bisection (exact if `f` is antitone; in any case the
returned `k` satisfies `f k`). -/
def greatestTrue (f : Nat → Bool) (lo hi : Nat) : Option Nat := Id.run do
  if !f lo then return none
  let mut a := lo
  let mut b := hi
  if f hi then return some hi
  -- invariant: f a, ¬ f b
  for _ in [0:64] do
    if b - a ≤ 1 then break
    let m := (a + b) / 2
    if f m then a := m else b := m
  return some a

/-- Smallest `k ∈ [lo, hi]` with `f k`, by bisection (exact if `f` is monotone; in any case the
returned `k` satisfies `f k`). -/
def leastTrue (f : Nat → Bool) (lo hi : Nat) : Option Nat := Id.run do
  if !f hi then return none
  if f lo then return some lo
  let mut a := lo
  let mut b := hi
  -- invariant: ¬ f a, f b
  for _ in [0:64] do
    if b - a ≤ 1 then break
    let m := (a + b) / 2
    if f m then b := m else a := m
  return some b

/-- The hypothetical parameters with every ciphertext and special modulus multiplied by `2^k`
(sizes only: the results are not primes; used by the suggestions, never for a verdict). -/
def growParams (P : FullParams) (k : Nat) : FullParams :=
  let f := fun (lp : Layout.LimbParams) => { lp with q := lp.q * 2 ^ k }
  { P with src := { P.src with qs := P.src.qs.map (· * 2 ^ k) },
           store := { P.store with limbs := P.store.limbs.map f, special := P.store.special.map f } }

/-- The "smallest fix" at twice the ring dimension, for when the uniform increase at the file's `N`
exceeds the 128-bit cap: the same program (Galois elements moved, `remapProg`), the same moduli
sizes, the input noise recomputed at `2N` from the file's `freshEncryption` bounds
(`freshNoiseAt`; in `--kappa` mode `kappaInfo` at `2N`), and the smallest uniform increase
`k ∈ [0, 64]` that the verified pipeline accepts. A search on hypothetical parameters, not a
theorem (UNVERIFIED GLUE: the input noise and the rotations at `2N`). -/
def suggestAt2N (inp : Input) (lay : Budget.KSLayout) (ki : Option KappaInfo) : String := Id.run do
  let P := inp.P
  let N := P.src.N
  let N2 := 2 * N
  let pre := s!"larger moduli at 2N = {N2} (a search on hypothetical parameters, NOT a theorem): "
  let some fm := inp.fresh
    | return pre ++ s!"cannot be computed by this tool: the file has no freshEncryption section (HEIR/Lattigo, neutral or hand-written files), so its input noise is not known at another ring dimension. fhe_check recommend FILE searches other chains and ring dimensions{if inp.sourceTool == "heir" then " (for HEIR files with the Lattigo formula of extract_bgv.py)" else ""}."
  let some prog2 := remapProg inp.prog N N2
    | return pre ++ "cannot be computed: a Galois element of the program is not of the form +-5^e mod 2N, so its rotations cannot be moved to 2N."
  let some noise2 := freshNoiseAt inp N2
    | return pre ++ "cannot be computed: no input noise at 2N."
  let P2 : FullParams := { P with src := { P.src with N := N2 }, store := { P.store with W := N2 },
                                  inputNoise := noise2 }
  -- in `--kappa` mode, the fresh noise at 2N (the variance proxy and the union count depend on N)
  let k2? : Option KappaInfo := ki.bind fun i => kappaInfoAt P2 fm i.l2.isSome i.kappa
  if ki.isSome && k2?.isNone then
    return pre ++ "cannot be computed: no --kappa error bound at 2N."
  let P2 := match k2? with | some i => { P2 with inputNoise := i.inputNoise } | none => P2
  let ok := fun (k : Nat) =>
    let Pk := growParams P2 k
    (match k2? with
      | some i => FHE.Noise.Fast.freshOK Pk prog2 i.model.inputs
      | none => true) && accepts Pk lay prog2 inp.decryption
  let how := s!"the same program with its rotations moved to 2N (+-5^e), the same digits, every ciphertext and special modulus multiplied by 2^k, input noise {match k2? with | some i => s!"Bp + t*eps at --kappa {i.kappa} and 2N" | none => s!"{pow2 noise2}"} recomputed at 2N from the file's freshEncryption bounds (UNVERIFIED GLUE)"
  match leastTrue ok 0 64 with
  | some k =>
    let qp := qpOf (growParams P2 k)
    return pre ++ s!"with {how}, the analyzer accepts for k = {k} (the smallest found by bisection over 0..64): {capText128 N2 qp}. Regenerate the parameters at N = {N2} with the library and re-run fhe_check; fhe_check recommend FILE gives actual primes."
  | none =>
    return pre ++ s!"with {how}, no k in 0..64 makes the analyzer accept."

/-- "Smallest fix" suggestions for a noise or decryption overflow. Each is found by running the
verified analyzer on hypothetical inputs; none is a theorem, none is proved minimal. -/
def suggest (inp : Input) (lay : Budget.KSLayout) (ki : Option KappaInfo) : List String := Id.run do
  if inp.prog.body.length > 3000 then
    return ["(no suggestions computed: the program has more than 3000 instructions)"]
  let P := inp.P
  let mut out : List String := []
  -- (a) the largest security exponent at which the probabilistic mode certifies
  if let some fm := inp.fresh then
    let hi := match ki with | some k => k.kappa | none => 512
    let l2 := ki.any (·.l2.isSome)
    let flag := if l2 then " --l2" else ""
    match greatestTrue (acceptsKappa P lay inp.prog inp.decryption fm l2) 1 hi with
    | some k =>
      out := out ++ [s!"probabilistic fresh noise: `fhe_check --kappa K{flag}` certifies this same program and parameters for K = {k}" ++
        (if k == hi && ki.isNone then " (the largest K tried)" else s!" (largest K found by bisection over 1..{hi})") ++
        s!": failure probability at most 2^-{k} over the encryption randomness, evaluation worst-case. Smaller K also certify." ++
        (if k < kappaFloor then s!" NOTE: K = {k} is below {kappaFloor}; a failure probability of 2^-{k} is not negligible, so this is not a meaningful guarantee." else "")]
    | none =>
      out := out ++ [s!"probabilistic fresh noise: no K in 1..{hi} certifies with --kappa K{flag} (even at K = 1 the bound overflows, or the inputs are not all fresh encryptions)."]
  -- (b) the smallest uniform growth of the moduli
  let P0 := match ki with | some k => { P with inputNoise := k.inputNoise } | none => P
  let grows := fun (k : Nat) =>
    let Pk := growParams P0 k
    let layk := lay
    (match ki with
      | some i => FHE.Noise.Fast.freshOK Pk inp.prog i.model.inputs
      | none => true) && accepts Pk layk inp.prog inp.decryption
  match leastTrue grows 1 64 with
  | some k =>
    let qpK := qpOf (growParams P0 k)
    let N := P.src.N
    let capNote := match capOf 128 N with
      | some cap =>
        if qpK < 2 ^ cap then
          s!" Security (INPUT ASSUMPTION, not proved here; {secCitation}): log2(Q*P) after the fix = {fmt2 (log2F qpK)} <= {cap}, the 128-bit cap at this N."
        else
          s!" SECURITY: this fix exceeds the 128-bit cap at this N (log2 QP after the fix = {fmt2 (log2F qpK)} > cap {cap}, at N = {N}; {secCitation}, an INPUT ASSUMPTION). A uniform increase is one family of chains only: other chains at this N may certify within the cap (fhe_check recommend FILE searches them); for the same program at 2N see the next suggestion."
      | none => s!" Security: log2(Q*P) after the fix = {fmt2 (log2F qpK)}; the security table has {(secNoEntry N).getD "no entry"}."
    out := out ++ [s!"larger moduli: with every ciphertext and special modulus {k} bit(s) larger (hypothetical chain: each modulus multiplied by 2^{k}; same number of limbs, same digits, same program" ++
      (match ki with | some i => s!", same --kappa {i.kappa}" | none => ", worst-case mode") ++
      s!") the analyzer accepts; {k} is the smallest such increase found by bisection over 1..64. The hypothetical moduli are not primes: regenerate the parameters with the library (for OpenFHE FIXEDMANUAL: SetScalingModSize and SetFirstModSize) and re-run fhe_check on them. For actual primes that ARE certified, and the library settings that produce them: fhe_check recommend FILE (OpenFHE: FIXEDMANUAL programs only)." ++ capNote]
    if let some cap := capOf 128 N then
      if qpK ≥ 2 ^ cap then
        out := out ++ [suggestAt2N inp lay ki]
  | none =>
    out := out ++ ["larger moduli: no uniform increase of 1..64 bits of every ciphertext and special modulus makes the analyzer accept this program (fhe_check recommend FILE searches other chains and ring dimensions)."]
  return out

/-- Which clause of `Spec.Encrypt.freshOK?` fails (diagnostic mirror). -/
def freshClause (P : FullParams) (prog : Program) (fresh : List Var) : String := Id.run do
  if fresh.isEmpty then
    return "no input is a fresh encryption (freshEncryption.inputs is empty), so there is nothing probabilistic to certify; run without --kappa for the worst-case certificate"
  -- (sets and a tree for the lookups: list searches here are quadratic in the number of inputs)
  let names : Std.HashSet String := prog.inputs.foldl (fun s d => s.insert d.name) {}
  let fs : Std.HashSet String := fresh.foldl (fun s x => s.insert x) {}
  let bm := FHE.Noise.Fast.boundMap prog
  for x in fresh do
    if !names.contains x then return s!"fresh input {x} is not a declared input"
  for d in prog.inputs do
    if fs.contains d.name then
      if d.parts != 2 then return s!"fresh input {d.name} is declared with {d.parts} parts (must be 2)"
      if d.key != 1 then return s!"fresh input {d.name} is declared under Galois key {d.key} (must be 1)"
      if let some b := bm[d.name]? then
        return s!"fresh input {d.name} also declares a bound ({b}): a bound on a fresh encryption would be an extra assumption on the encryption itself (the analysis would start it at that bound instead of at the noise of an encryption), so the certificate would not be about fresh encryptions; remove the bound, or remove {d.name} from freshEncryption.inputs and use the worst-case mode"
      if 2 * P.inputNoise ≥ P.src.modulus d.level then
        return s!"fresh input {d.name}: twice the input noise {pow2 P.inputNoise} is not below the modulus at its level {d.level}"
    else
      if d.parts != 1 then
        return s!"input {d.name} is not a fresh encryption (freshEncryption.inputs) and has {d.parts} parts: the fresh-encryption certificate covers only fresh public-key encryptions and 1-part plaintext operands with declared bounds"
      match bm[d.name]? with
      | some b => if b > P.inputNoise then return s!"input {d.name} declares a bound {b} above the fresh input noise {P.inputNoise}"
      | none => return s!"input {d.name} is not a fresh encryption (freshEncryption.inputs) and declares no bound: the fresh-encryption certificate covers only fresh public-key encryptions and plaintext operands with declared bounds"
  return "(no failing clause found by the diagnostic mirror)"

/-! ### The security note (NOT part of the verdict) -/

/-- The security note's lines: `log₂(Q·P)` of the file against the standard's table for its `N`
(an INPUT ASSUMPTION; never part of the verdict). -/
def securityLines (P : FullParams) : List String :=
  let N := P.src.N
  let qp := qpOf P
  let head := s!"  log2(Q*P) = {fmt2 (log2F qp)} ({P.src.qs.length} ciphertext limbs, all of them, including any extra limb, and {P.store.special.length} special primes)"
  match secNoEntry N with
  | some why => [head, s!"  table: {secCitation}: {why}"]
  | none =>
    let c := fun (sec : Nat) => (capOf sec N).getD 0
    let meets := fun (sec : Nat) => decide (qp < 2 ^ c sec)
    let ext := if secRowIsExtension N then s!" (the row N = {N} is OpenFHE's extension of the table, stdlatticeparms.cpp:187-192, NOT in the 2018 standard)" else ""
    let verdictTxt :=
      if meets 256 then "within the 128-, 192- and 256-bit caps"
      else if meets 192 then "within the 128- and 192-bit caps; above the 256-bit cap"
      else if meets 128 then "within the 128-bit cap; above the 192- and 256-bit caps"
      else s!"ABOVE the 128-bit cap ({fmt2 (log2F qp)} > {c 128}): below 128-bit security per the standard"
    [head,
     s!"  caps on log2(Q*P) at N = {N} (ASSUMED, from the {secCitation}){ext}: {c 128} (128-bit), {c 192} (192-bit), {c 256} (256-bit)",
     s!"  these parameters: {verdictTxt}"]

/-- The warning printed under the verdict when `log₂(Q·P)` exceeds the 128-bit cap at `N`, or `N`
is below the table. -/
def securityWarning (P : FullParams) : Option String :=
  let N := P.src.N
  let qp := qpOf P
  match capOf 128 N with
  | some cap =>
    if qp < 2 ^ cap then none else
    some s!"SECURITY (not part of the verdict): log2(Q*P) = {fmt2 (log2F qp)} EXCEEDS the 128-bit classical cap of {cap} bits at N = {N}{if secRowIsExtension N then " (OpenFHE's extension row, not the 2018 standard)" else ""} ({secCitation}; an INPUT ASSUMPTION, not proved here). These parameters are below 128-bit security per the standard; the verdict is about correctness only."
  | none =>
    if N < 1024 && N = 2 ^ Nat.log2 N then
      some s!"SECURITY (not part of the verdict): N = {N} is below the smallest ring dimension of the security standard (1024); NOT secure per the standard ({secCitation}). The verdict is about correctness only."
    else none

def certifiesLine : String :=
  "NOTE: what is certified is correctness (exact decryption), not security; see \"Security note\" below."

/-- **User-level decryption** (what the library's user reads after `Decode`): covered exactly when
the input carries the library's scaling data, declares the switched decryption, and the trusted
check `Spec.Scaling.scaleOK?` accepts; then `Challenge.Scaling.certify?_user` applies to the
certificate. Returns whether it is covered and the one line the report prints. The reasons are
diagnostic (they never turn a failed check into a covered one). -/
def userDecryption (inp : Input) : Bool × String :=
  let no := fun (why : String) => (false, s!"user-level decryption not covered: {why}")
  match inp.scaling with
  | none => no "no scaling data in the input (the library's scaling-factor bookkeeping, $.scaling, is needed)"
  | some sd =>
    if inp.decryption != .switched then
      no "the input declares textbook decryption at the output's level; Challenge.Scaling.certify?_user is about the library's switched decryption"
    -- `Spec.Scaling.scaleOK?`, computed with the factors in a tree (the locked one keeps them in
    -- closures and is quadratic in the program length): `FHE.Noise.FastScaling.scaleOK`, equal to
    -- it on every input (`Validation.FastScaling.scaleOK_eq`; the factors: `factors_eq`)
    else if FHE.Noise.FastScaling.scaleOK inp.P.src inp.prog sd then
      (true, "user-level decryption covered (Challenge.Scaling.certify?_user)")
    else
      match FHE.Noise.FastScaling.factors inp.P.src inp.prog sd with
      | none => no "Spec.Scaling.scaleOK? failed: the factors cannot be computed (an input without a declared factor, or an addition or subtraction of operands whose true factors differ)"
      | some m =>
        let bad := inp.prog.outputs.findSome? fun o =>
          match m[o]? with
          | none => some s!"output {o} has no factor"
          | some x =>
            let d := Spec.Scaling.decodeFactor inp.P.src sd.tracks x
            let want := x.phi * Spec.Decrypt.decScale inp.P.src x.level
            if d != want then
              some s!"output {o}: the factor the library hands to Decode ({d.val}) is not the true factor times decScale ({want.val})"
            else if d * d⁻¹ != 1 then
              some s!"output {o}: the decode factor {d.val} is not invertible modulo t"
            else none
        no s!"Spec.Scaling.scaleOK? failed: {bad.getD "an output fails"}"

/-- OpenFHE's 64-bit word arithmetic on the moduli of this file (`Challenge.Word.ksWordOK?`):
every ciphertext and special modulus below `2⁶⁰` (its Barrett and Shoup
routines) and the unreduced 128-bit sums of the hybrid key switch's base conversions below `2¹²⁸`
(`Challenge.Word.modUp_acc_no_overflow`, `modDown_acc_no_overflow`). Checked for files whose
frontend is OpenFHE's (`source.tool = "openfhe"`); `none` when it holds. -/
def openfheWordRefusal? (tool : String) (P : FullParams) : Option String :=
  let qs := P.src.qs
  let ps := P.store.special.map (·.q)
  if tool != "openfhe" || Challenge.Word.ksWordOK? qs ps then none else
  let big := (qs ++ ps).filter fun m => !(decide (2 ≤ m) && decide (m < 2 ^ 60))
  let why := match big.head? with
    | some m => s!"the modulus {m} ({pow2 m}) is not in [2, 2^60): the word-arithmetic model of the proof (Challenge.Word: Barrett and Shoup reduction with a precomputed constant that must fit a 64-bit word, and the NTT tables built on it) covers moduli below 2^60 only"
    | none => s!"the unreduced 128-bit sums of the hybrid key switch's base conversions (ApproxSwitchCRTBasis, dcrtpoly-impl.h:957-965) may not fit 128 bits: with {qs.length} ciphertext and {ps.length} special moduli the worst-case sum over a source basis exceeds 2^128 (the proved bound covers about 256 moduli of 60 bits at most)"
  some s!"Challenge.Word.ksWordOK? = false: {why}. The certificate's statements model the library's word arithmetic as exact modular arithmetic, and the proof of that model covers only moduli and limb counts meeting this condition; to certify, use moduli and a number of limbs that meet it."

/-- A declared input bound above `inputNoise`. For BGV the analysis starts every input (plaintext
operands included) at min(declared bound, inputNoise) (`Challenge.Headline.refAnalyze`,
`Spec.InputsOK`), so the theorem's hypothesis on such an input is `inputNoise`, not the declared
bound: a certificate would be about a stronger input assumption than the file states. -/
def declaredBoundRefusal? (P : FullParams) (prog : Program) : Option (Var × Nat) :=
  prog.bounds.find? (fun (_, b) => b > P.inputNoise)

set_option maxHeartbeats 400000 in
/-- **The pipeline.** -/
def runCheck (inp0 : Input) (opts : Options := {}) : Result := Id.run do
  let base : Result := { verdict := .notCertified, headline := "", input := some inp0 }
  let mut warnings : List String := []
  -- 0. the mode: worst case (the frontend's inputNoise), or `--kappa`
  let mut ki : Option KappaInfo := none
  if let some κ := opts.kappa then
    let some fm := inp0.fresh
      | return { base with verdict := .unsupported,
                           headline := "--kappa: the input file has no freshEncryption section (which inputs are fresh public-key encryptions, and the sampler bounds), so no probabilistic statement is available for it" }
    let some i := kappaInfoAt inp0.P fm opts.l2 κ
      | return { base with verdict := .unsupported,
                           headline := "--kappa: the variance proxy is zero (all sampler bounds are zero); use the worst-case mode" }
    if i.deterministic then
      warnings := warnings ++ [s!"--kappa {κ}: the high-probability error bound epsFor = {i.epsKappa} ({pow2 i.epsKappa}) is not below the worst case of a fresh encryption's error, Spec.Encrypt.worstError = {i.worst} ({pow2 i.worst}); the worst case was used instead (no probability: the stronger statement, Challenge.FreshNoise.fresh_worst_decrypts)"]
    else if κ < kappaFloor then
      warnings := warnings ++ [s!"--kappa {κ} IS BELOW {kappaFloor}: a failure probability of up to 2^-{κ} per set of encryptions is NOT negligible. A CERTIFIED verdict at this K is a weak statement; do not read it as \"decrypts correctly\"."]
    let w := Encrypt.freshNoise inp0.P.src.t i.plainBound i.worst
    if inp0.P.inputNoise < w then
      warnings := warnings ++ [s!"the frontend's inputNoise = {inp0.P.inputNoise} ({pow2 inp0.P.inputNoise}) is BELOW the worst case of a fresh encryption with the sampler bounds this same file declares ({pow2 w}). It is not used in this mode (the input noise is computed from the sampler bounds: {pow2 i.inputNoise}), but a worst-case run (without --kappa) of this file rests on it."]
    ki := some i
  else if let some fm := inp0.fresh then
    -- worst-case mode on a file that describes its fresh encryptions: compare the frontend's
    -- inputNoise with the verified worst case of such an encryption
    let w := Encrypt.freshNoise inp0.P.src.t (fm.bp inp0.P.src.t)
      (Encrypt.worstError inp0.P.src.N inp0.P.secretBound fm.keyError fm.u fm.e1 fm.e2)
    if inp0.P.inputNoise < w then
      warnings := warnings ++ [s!"ASSUMPTION NOT COVERED BY THE FILE'S OWN SAMPLER BOUNDS: the frontend's inputNoise = {inp0.P.inputNoise} ({pow2 inp0.P.inputNoise}) is BELOW the worst case of a fresh encryption with the sampler bounds this same file declares, Spec.Encrypt.freshNoise t Bp (worstError ...) = {w} ({pow2 w}; Challenge.FreshNoise.freshError_worst_attained). The verdict below assumes every input ciphertext has noise at most inputNoise; fresh encryptions with those sampler bounds need not. Use --kappa K for a certificate about fresh encryptions."]
  let inp : Input := match ki with
    | some i => { inp0 with P := { inp0.P with inputNoise := i.inputNoise } }
    | none => inp0
  let P := inp.P
  warnings := warnings ++ (securityWarning inp0.P).toList
  let base : Result := { base with input := some inp, kappa := ki, warnings }
  -- 1. parameters (verified: `schemeParamsOK?`)
  let ok1 := schemeParamsOK? P
  if !ok1 then
    return { base with schemeOK := some false, headline := "the parameters are rejected",
                       failure := some { what := s!"Spec.schemeParamsOK? = false. First failing clause (diagnostic): {paramsClause P chainName}" } }
  let ok2 := Budget.specialOK? P
  if !ok2 then
    return { base with schemeOK := some true, specialOK := some false,
                       headline := "the special (key-switching) primes are rejected",
                       failure := some { what := s!"Spec.Budget.specialOK? = false: {specialClause P}" } }
  let base := { base with schemeOK := some true, specialOK := some true }
  -- 1a. OpenFHE's word arithmetic is exact on these moduli (`Challenge.Word.ksWordOK?`)
  if let some why := openfheWordRefusal? inp.sourceTool P then
    return { base with verdict := .unsupported,
                       headline := "OpenFHE's 64-bit word arithmetic is not shown to be exact on these moduli",
                       failure := some { what := why } }
  -- 1a'. OpenFHE's packed encoder (the same code as BFV's) stores a coefficient
  -- x in [0, t) in limb 0 and x - q0 in the other limbs when x > floor(q0/2): t - 1 <= floor(q0/2)
  -- keeps every stored coefficient one integer. OpenFHE's BGV parameter
  -- generation meets it (q0 = 1 mod 2N*t, or q0 >= 2t*V - t); checked here so that it is not assumed.
  if inp.sourceTool == "openfhe" && !decide (P.src.t - 1 ≤ P.src.qs.headD 0 / 2) then
    return { base with verdict := .unsupported,
                       headline := "the plaintext modulus is outside the condition t - 1 <= floor(q0/2) on the first ciphertext prime, under which the input contract describes the packed plaintexts of an OpenFHE file",
                       failure := some { what := s!"t - 1 <= floor(q0/2) fails (t = {P.src.t}, q0 = {P.src.qs.headD 0}): the plaintext modulus is outside the packed-encoding window t - 1 <= floor(q0/2) (and t <= every limb) under which the packed-encoding model of the input contract holds; use a larger first ciphertext prime or a smaller t" } }
  -- 1a''. a declared input bound above `inputNoise` (`declaredBoundRefusal?`)
  if let some (x, b) := declaredBoundRefusal? P inp.prog then
    return { base with verdict := .unsupported,
                       headline := s!"input {x} declares the bound {b} ({pow2 b}), above the input noise {P.inputNoise} ({pow2 P.inputNoise}) that the theorem assumes for every input (the analysis would start it at {P.inputNoise}), so no certificate is given for the declared bound",
                       failure := some { what := s!"declared input bound {b} > inputNoise = {P.inputNoise} for input {x} (every BGV input, plaintext operands included, is analysed at min(declared bound, inputNoise)): lower the declared bound to at most {P.inputNoise}, or raise params.inputNoise to at least {b} (which then applies to every input ciphertext)" } }
  -- 1b. probabilistic mode: the inputs (verified: `freshOK?`)
  if let some i := ki then
    -- `Spec.Encrypt.freshOK?` with the name lookups in trees (the locked one searches lists,
    -- quadratic in the number of fresh inputs): equal to it, `Validation.Fast.Aux.freshOK_eq`
    if !FHE.Noise.Fast.freshOK P inp.prog i.model.inputs then
      return { base with verdict := .unsupported,
                         headline := s!"--kappa: Spec.Encrypt.freshOK? = false: {freshClause P inp.prog i.model.inputs}",
                         failure := some { what := "Spec.Encrypt.freshOK? = false" } }
  -- 2. budget
  let br ← match computeBudget inp with
    | .ok b => pure b
    | .error (.invalid m) => return { base with verdict := .invalid, headline := m }
    | .error (.unsupported what idx why) =>
      return { base with verdict := .unsupported,
                         headline := s!"{what}{match idx with | some i => s!" (body[{i}])" | none => ""}: {why}" }
  let base := { base with budget := some br }
  -- 2b. the layout serves every level from one top-level key set (verified: `layoutOK?`,
  -- `keysRestrict?`, both checked again inside `certify?`; this only words the refusal)
  if !Spec.Certify.layoutOK? P br.layout then
    return { base with budget := none, verdict := .unsupported,
                       headline := "the key-switching digit layout does not restrict from the top level: at some level its digits are not the top-level digits cut down to that level's limbs, so keys generated once at the top level are not shown to be keys there (Spec.Certify.layoutOK? = false; Challenge.Budget.gadgetKeys_restrict_needs_restrictsTo)",
                       failure := some { what := "Spec.Certify.layoutOK? = false" } }
  if !Spec.Certify.keysRestrict? P then
    return { base with headline := s!"the key noise is too large for a top-level key-switching key to remain a key at level 1: 2*floor(keyNoise/t)*t = {2 * (P.keyNoise / P.src.t * P.src.t)} is not below q0*P = {P.src.modulus 1 * Budget.specialProd P} (Spec.Certify.keysRestrict? = false; Challenge.Budget.gadgetKeys_restrict_needs_size_bgv)",
                       failure := some { what := "Spec.Certify.keysRestrict? = false" } }
  -- THE DECISION (read below): started in a task of its own, so that it runs while the
  -- diagnostic replay is computed (parallelism only; the same call, the same value)
  let certT := Task.spawn fun _ =>
    certificate? inp0.P br.layout inp0.prog inp0.decryption ki inp0.msMethod
  let (steps, zenv) := replay P br.E inp.prog
  let base := { base with steps }
  let withSuggestions := fun (r : Result) =>
    if opts.suggest then { r with suggestions := suggest inp0 br.layout ki } else r
  let switched := inp.decryption == .switched
  -- frontend cross-check (never trusted; a disagreement withholds the certificate)
  let mism := inp.expects.filterMap fun e =>
    match steps[e.idx]? with
    | some s =>
      if (e.level.isSome && e.level != some s.level) || (e.parts.isSome && e.parts != some s.parts) then
        some s!"body[{e.idx}] ({e.dst}): the frontend says level {e.level.getD 0}, parts {e.parts.getD 0}; Source.step gives level {s.level}, parts {s.parts}"
      else none
    | none => none
  -- THE VERDICT. The locked `Challenge.Certify.certify?` on the decoded data (the declared
  -- parameters `inp0.P`: in the fresh modes `certify?` replaces the input noise itself). This is
  -- the only place a certificate is issued; everything below explains refusals.
  if let some c := certT.get then
    if !mism.isEmpty then
      -- no per-output bounds are shown: the certificate is withheld
      return { base with analyzed := some c.bound,
                         headline := "the frontend and the verified semantics disagree on the program's shape, so the certificate is withheld",
                         failure := some { what := String.intercalate "\n" mism } }
    -- the outputs, with the certificate's bounds; level and key from the diagnostic replay
    -- (`Source.step` on zero messages, as `Decrypt.outputLevel?` and `Encrypt.outputKey?` compute
    -- them), the switched-phase bound from `Spec.Decrypt.decBound` at the certificate's bound
    let outs := c.outputs.map fun (o, b) =>
      let v := zenv[o]?
      let lvl := (v.map (·.1)).getD 0
      let o1 : OutputInfo := { name := o, level := lvl, bound := b, Q := c.params.src.modulus lvl,
                               key := v.map (·.2) }
      if switched then { o1 with decBound := some (Decrypt.decBound c.params.src lvl b) } else o1
    -- What is printed is the certificate: a printed figure that is not the certificate's
    -- withholds it.
    let agree := c.params.inputNoise == P.inputNoise && c.params.src.N == P.src.N &&
      c.params.src.qs == P.src.qs && c.outputs.map (·.1) == inp.prog.outputs &&
      c.budget.keySwitch == br.E.keySwitch && c.budget.modSwitch == br.E.modSwitch &&
      c.budget.modSwitchOne == br.E.modSwitchOne &&
      br.msManyParts.all (fun k => c.budget.modSwitchAt k == br.E.modSwitchAt k) &&
      outs.all (fun o => o.key == some 1) &&
      (match ki with
       | none => c.used == .declared
       | some i => c.eps == i.eps && c.drift == i.drift &&
           c.used == (if i.l2.isSome then .freshKappaL2 else if i.deterministic then .freshWorst else .freshKappa))
    unless agree do
      return { base with analyzed := some c.bound,
                         headline := "internal disagreement between the figures of this report and the certificate of Challenge.Certify.certify?; no certificate",
                         failure := some { what := "report figures differ from the certificate" } }
    -- POLICY: the plain CERTIFIED headline only when the statement covers what the user reads
    -- (user-level decryption, `userDecryption`). Not covered: a library-extracted input (OpenFHE)
    -- is NOT CERTIFIED; any other input is CERTIFIED AT PHASE LEVEL (`Result.phaseOnly`).
    let (udCov, udLine) := userDecryption inp
    if !udCov && inp.sourceTool == "openfhe" then
      return { base with analyzed := some c.bound, outputs := outs,
                         headline := s!"the phase-level certificate holds, but what the user reads is not covered ({udLine}); for a program extracted from a library the certificate is withheld",
                         failure := some { what := udLine } }
    let h := match ki with
      | some i =>
        if i.deterministic then "every output decrypts correctly for every fresh encryption within the sampler bounds (worst case, no probability), under the assumptions below"
        else s!"fresh-noise failure probability at most 2^-{i.kappa}{if i.l2.isSome then " (l2 description of the key and samplers)" else ""}; evaluation worst-case"
      | none => "every output decrypts correctly, in the worst case, under the assumptions below"
    return { base with verdict := .certified, analyzed := some c.bound, outputs := outs, phaseOnly := !udCov,
                       userDec := some (udCov, udLine),
                       headline := if udCov then h else
                         s!"{h.replace "every output decrypts correctly" "the raw (phase-level) decryption of every output is correct"}; user-level decryption depends on the backend and is NOT covered" }
  -- 3. no certificate: explain why (the verified analyzer and certOK?, for the diagnosis)
  match analyzer P br.E inp.prog with
  | some B =>
    -- Per output: the bound of `refAnalyze` on the program with this output alone (with one
    -- output that program is `inp.prog` itself, whose bound `B` was just computed), and
    -- `Spec.Encrypt.certOK?` with that bound, each evaluated once.
    -- Computed from the final environments of one run of the body (`FHE.Noise.Fast.run`,
    -- `outBound`, `certOK`): the values of `refAnalyze` and `certOK?` on the one-output program
    -- (`Validation.Fast.Aux.refAnalyze_eq`, `certOK?_eq`), without running the body per output.
    let single := inp.prog.outputs.length == 1
    let r? := FHE.Noise.Fast.run P br.E inp.prog
    let certs : List (Var × Option Nat × Bool) := inp.prog.outputs.map fun o =>
      let b? := if single then some B else r?.bind fun r => FHE.Noise.Fast.outBound r [o]
      (o, b?, match b?, r? with
        | some b, some r => FHE.Noise.Fast.certOK P r o b switched
        | _, _ => false)
    let outs := certs.filterMap fun (o, b?, c) =>
      b?.map fun b =>
        -- level and key: the diagnostic replay (`Source.step` on zero messages, as
        -- `Decrypt.outputLevel?` and `Encrypt.outputKey?` compute them)
        let v := zenv[o]?
        let lvl := (v.map (·.1)).getD 0
        let o1 : OutputInfo := { name := o, level := lvl, bound := b, Q := P.src.modulus lvl,
                                 key := v.map (·.2) }
        -- 4. switched decryption (verified: `decryptOK?` at the output's level, which is what
        -- `decryptAllOK?` on the one-output program evaluates; implied by `certOK?`, so
        -- evaluated separately only when that failed)
        if switched then
          { o1 with decBound := some (Decrypt.decBound P.src lvl b),
                    decOK := c || (v.isSome && Decrypt.decryptOK? P.src lvl b) }
        else o1
    if !mism.isEmpty then
      -- no per-output bounds are shown: the certificate is withheld
      return { base with analyzed := some B,
                         headline := "the frontend and the verified semantics disagree on the program's shape, so the certificate is withheld",
                         failure := some { what := String.intercalate "\n" mism } }
    -- 4a. every output under the secret key itself (verified: `outputsUnderS?`, part of `certOK?`)
    -- (`certOK?` = `outputsUnderS?` && …, so only the outputs it rejected are examined)
    -- (the key an output is under: the final environment of the replay, which is what
    -- `Spec.Encrypt.outputKey?` computes)
    if let some (o, _, _) := certs.find? fun (o, _, c) =>
        !c && (zenv[o]?).map (·.2) != some 1 then
      let k := (zenv[o]?).map (·.2)
      let kd := match k with | some g => toString g | none => "?"
      return { base with
        analyzed := some B, outputs := outs,
        headline := s!"output {o} is left under the rotated key sigma_{kd}(s) (Galois element {kd}), not under the secret key s: the noise bound holds, but decryption with s does not return its message",
        failure := some { what := s!"Spec.Encrypt.outputsUnderS? = false: output {o} is recorded under the Galois element {kd} (Spec.Encrypt.outputKey?). The noise theorems speak of decryption under sigma_{kd}(s); a library decrypts with s. Key-switch {o} back to s (keySwitch after the automorphism) before it is output, or declare the input under key 1." } }
    if let some o := outs.find? (!·.decOK) then
      let q0 := P.src.qs.headD 0
      let db := o.decBound.getD 0
      let r : Result := { base with
        analyzed := some B, outputs := outs,
        headline := s!"the noise bounds hold at every level, but the library's decryption (phase switched to one limb) is not shown exact for output {o.name}",
        failure := some { overflow := true, what := s!"decryption with the phase switched to one limb: output {o.name} (level {o.level}, noise <= {pow2 o.bound}) has switched-phase bound Spec.Decrypt.decBound = {pow2 db}, not below q0/2 = {pow2 (q0 / 2)} (over by {fmt2 (log2F (2 * db) - log2F q0)} bits)" } }
      return withSuggestions r
    return { base with analyzed := some B, outputs := outs,
                       headline := "internal disagreement: the diagnostic checks found no failure, but Challenge.Certify.certify? refuses; no certificate",
                       failure := some { what := "Challenge.Certify.certify? = none" } }
  | none =>
    -- localise the failure
    if let some d := inp.prog.inputs.find? (fun d => !d.ok P.src) then
      return { base with headline := "the program is ill-formed",
                         failure := some { what := s!"input {d.name} is ill-formed (Source.Decl.ok): parts {d.parts}, level {d.level} (chain has {P.src.qs.length} limbs), key {d.key} (must be odd and < 2N)" } }
    match steps.find? (fun s => s.ill.isSome || 2 * s.bound ≥ s.Q) with
    | some s =>
      -- the two prefix runs are independent: in parallel
      let atT := Task.spawn fun _ => analyzeAt P br.E inp.prog s.idx
      let beforeT := Task.spawn fun _ => s.idx == 0 || (analyzeAt P br.E inp.prog (s.idx - 1)).isSome
      let confirmed := atT.get == none && beforeT.get
      match s.ill with
      | some why =>
        return { base with headline := s!"the program is ill-formed at body[{s.idx}]",
                           failure := some { what := why, step := some s, confirmed } }
      | none =>
        let kind := match ki with
          | some i => if i.deterministic then "worst-case noise bound (fresh encryptions at their worst case)"
                      else "noise bound (fresh noise with high probability, evaluation worst-case)"
          | none => "worst-case noise bound"
        let r : Result := { base with
          headline := s!"the {kind} overflows at body[{s.idx}]",
          failure := some { what := "noise overflow", step := some s, confirmed, overflow := true } }
        return withSuggestions r
    | none =>
      let missing := inp.prog.outputs.filter fun o =>
        !(steps.any (Trace.dst ·.instr == o) || inp.prog.inputs.any (·.name == o))
      return { base with headline := "the program is ill-formed",
                         failure := some { what := s!"output(s) never defined: {missing}" } }

/-! ### The fixed statement of what a certificate means -/

/-- The one locked statement a CERTIFIED verdict instantiates. -/
def certificateTheorem (ki : Option KappaInfo) : String :=
  match ki with
  | none => "Challenge.Certify.worst_certified"
  | some i => if i.l2.isSome then "Challenge.Certify.fresh_l2_certified"
              else if i.deterministic then "Challenge.Certify.fresh_worst_certified"
              else "Challenge.Certify.fresh_kappa_certified"

def theoremsCited (inp : Input) (ki : Option KappaInfo) : List (String × String) :=
  (match ki with
   | none =>
    [("Challenge.Certify.worst_certified",
      "THE CERTIFICATE (worst case): if Challenge.Certify.certify? returns a certificate c in the worst-case mode, then for every secret s (no bound on s assumed; a run within the budget exists for s within secretBound) and all inputs within inputNoise and their declared bounds, every output of every run meeting the Spec.Trace contracts at the budget Spec.Budget.certified decrypts WITH s to the value the program computes and has noise at most its own bound in c (all outputs jointly)"),
     ("Challenge.FreshNoise.certified_decrypts", "the same for one program with one bound (used in the proof, per output)")]
   | some i =>
    if i.l2.isSome then
    [("Challenge.Certify.fresh_l2_certified",
      "THE CERTIFICATE (fresh encryptions, l2 description, probabilistic): if Challenge.Certify.certify? returns a certificate c in the mode freshL2 fresh E2 S2 Vu V1 V2 kappa, then for every key with ||s||_2^2 <= S2 and ||e_pk||_2^2 <= E2 (hypotheses on the fixed key) and SubGaussSamplerOK encryption randomness with proxies Vu, V1, V2, the probability that there exist messages for which SOME output of some run does not decrypt WITH s, or exceeds its own noise bound in c, is at most 2^-kappa: one event for all outputs"),
     ("Challenge.Certify.fresh_l2_decrypts", "the same with the failure event of Challenge.FreshNoise (decryption alone)"),
     ("Challenge.Certify.certify?_freshL2", "in the freshL2 mode the analysed input noise is freshNoise t (epsFor (varProxyL2 E2 S2 Vu V1 V2) (n*2N) kappa)"),
     ("Challenge.Certify.fresh_l2_run_exists", "a run exists at the certified budget on the event that every fresh error is at most c.eps"),
     ("Challenge.FreshNoiseL2.normSq_le", "||a||_2^2 <= N*||a||_inf^2: the support bounds discharge the l2 hypotheses on the key"),
     ("Challenge.FreshNoiseL2.subGaussSamplerOK_of_samplerOK", "bounded coefficients are sub-Gaussian about their means with the square of the bound as proxy (Hoeffding's lemma)"),
     ("Challenge.FreshNoise.epsFor_spec", "count * exp(-epsFor(V,count,kappa)^2 / (2V)) <= 2^-kappa"),
     ("Challenge.FreshNoise.phase_encrypt", "the phase of Spec.Encrypt.encrypt is m + t*(e_pk*u + e1 + e2*s)")]
    else if i.deterministic then
    [("Challenge.Certify.fresh_worst_certified",
      "THE CERTIFICATE (fresh encryptions, worst case, no probability): if Challenge.Certify.certify? returns a certificate c in the fresh mode with c.used = freshWorst (analysed at input noise freshNoise t Bp (worstError ...)), then for every key and all encryption randomness within the bounds, every output of every run decrypts WITH s and has noise at most its own bound in c"),
     ("Challenge.FreshNoise.fresh_worst_decrypts", "the same for one program with one bound"),
     ("Challenge.FreshNoise.freshError_worst", "the error e_pk*u + e1 + e2*s of a fresh encryption is at most worstError"),
     ("Challenge.FreshNoise.phase_encrypt", "the phase of Spec.Encrypt.encrypt is m + t*(e_pk*u + e1 + e2*s)")]
    else
    [("Challenge.Certify.fresh_kappa_certified",
      "THE CERTIFICATE (fresh encryptions, probabilistic): if Challenge.Certify.certify? returns a certificate c in the fresh mode with exponent kappa, then for a fixed key and SamplerOK encryption randomness, the probability that there exist messages for which SOME output of some run does not decrypt WITH s to the value the program computes, or exceeds its own noise bound in c, is at most 2^-kappa: one event for all outputs (the parameters are c.params: input noise freshNoise t c.eps)"),
     ("Challenge.Certify.fresh_kappa_decrypts", "the same with the failure event of Challenge.FreshNoise (decryption alone)"),
     ("Challenge.FreshNoise.fresh_kappa_decrypts", "the statement for one program with one bound (not used per output: that would cost a factor #outputs)"),
     ("Challenge.FreshNoise.fresh_certified_kappa", "the same for the noise bound (Encrypts) instead of decryption"),
     ("Challenge.FreshNoise.fresh_certified", "the same with an explicit error bound eps: failure probability <= n * 2N * exp(-eps^2 / (2V))"),
     ("Challenge.FreshNoise.freshError_tail", "Hoeffding tail bound for the error e_pk*u + e1 + e2*s of one fresh encryption"),
     ("Challenge.FreshNoise.epsFor_spec", "count * exp(-epsFor(V,count,kappa)^2 / (2V)) <= 2^-kappa"),
     ("Challenge.FreshNoise.phase_encrypt", "the phase of Spec.Encrypt.encrypt is m + t*(e_pk*u + e1 + e2*s)"),
     ("Challenge.FreshNoise.samplerOK_rademacher", "the sampler hypothesis SamplerOK is satisfiable (explicit product measure)")]) ++
  (match ki with
   | some _ => [("Challenge.FreshNoise.freshOK?_spec", "freshOK? implies: there is a fresh input, each is a declared input, and none declares a bound of its own")]
   | none => []) ++
  [("Challenge.Certify.certify?_sound", "the BGV headline (= Challenge.Certify.certified_sound): for inputs within the analysed input noise c.params.inputNoise, in any mode, every output of every run within c.budget is under s, decrypts with s and has noise at most its own bound"),
   ("Challenge.Certify.certify?_spec", "what the fields of the certificate are, and that every check (schemeParamsOK?, specialOK?, the layout at every level, refAnalyze on the whole program and on each output alone, certOK? per output) was made at the analysed parameters"),
   ("Challenge.Certify.certify?_paramsOK", "certify? = some c implies SchemeParamsOK, BGV, SpecialOK and the layout usable at every level 1..L"),
   ("Challenge.Certify.certified_run_exists", "a certified program has a run at the certified budget from every valid input (the textbook algorithms): the certificate is not about no runs"),
   ("Challenge.FreshNoise.outputKey?_eq", "the key an output is under does not depend on the messages"),
   ("Challenge.Budget.certified_sound",
    "the noise bound of refAnalyze at E = Spec.Budget.certified P lay holds for every run meeting the Spec.Trace contracts"),
   ("Challenge.Params.schemeParamsOK?_sound", "schemeParamsOK? P = true implies SchemeParamsOK P"),
   ("Challenge.Budget.specialOK?_sound", "specialOK? P = true implies SpecialOK P (special primes)"),
   ("Challenge.Budget.relin_realizable",
    "relinearization can be done within ksBoundAt at every level (keys with noise <= keyNoise; no prime-size condition)"),
   ("Challenge.Budget.keySwitch_realizable", "the same for key switching after an automorphism"),
   ("Challenge.Budget.modSwitch_realizable_parts", "modulus switching of a value with k parts can be done within msBudgetAt P k = ceil(t*sum_{i<k}(N*secretBound)^i/2), for every k"),
   ("Challenge.Budget.modSwitch_realizable", "modulus switching of a 2-part ciphertext can be done within msBudget"),
   ("Challenge.Budget.modSwitch_realizable_one",
    "modulus switching of a 1-part value (a plaintext operand) can be done within msBudgetOne = ceil(t/2)"),
   ("Challenge.Budget.ksBoundAt_le_ksBudget", "ksBudget covers every level of the chain")] ++
  (if inp.decryption == .switched then
    [("Challenge.Decrypt.decrypt_switched",
      "a ciphertext that Encrypts v with noise <= B and passes decryptOK? decrypts by bgvDecryptSwitched to decScale * message"),
     ("Challenge.Decrypt.outputLevel?_eq", "the level of an output does not depend on the messages")]
   else []) ++
  [("Challenge.Fast.certifyFast_eq",
    "the function fhe_check runs, FHE.Holes.certifyFast, returns exactly what Challenge.Certify.certify? returns, on every input (all modes)"),
   ("Challenge.Fast.analyzeFast_eq",
    "the analyzer fhe_check runs, FHE.Holes.analyzeFast, returns exactly what Challenge.Headline.refAnalyze returns, on every input"),
   ("Challenge.Trace.encrypts_bgv_decrypts",
    "a ciphertext that Encrypts a value decrypts to its message exactly by textbook decryption at its own level, under the key it is recorded under")]

/-- How the verdict was computed: the fast path, and the locked statements that make its result
the value of the locked decision. -/
def computedByText : List String := [
  "",
  "HOW THE VERDICT WAS COMPUTED: by FHE.Holes.certifyFast, which makes the checks of",
  "Challenge.Certify.certify? with the environments of the analysis in search trees and one pass",
  "over the program (FHE/Noise/Fast.lean; near-linear instead of quadratic in the program length).",
  "The locked statement Challenge.Fast.certifyFast_eq, proved and kernel-checked in this",
  "repository, says that it returns exactly what certify? returns, on every input; so a",
  "certificate printed here is the value of certify?, and the theorems cited are about it. The",
  "bounds shown without a certificate are those of Challenge.Headline.refAnalyze, computed by",
  "FHE.Holes.analyzeFast (Challenge.Fast.analyzeFast_eq: equal on every input)."]

/-- What is said about decryption, depending on the decryption the frontend declared. -/
def decryptionText (inp : Input) : List String :=
  match inp.decryption with
  | .atOutputLevel => [
    "DECRYPTION COVERED: textbook decryption WITH THE SECRET KEY s modulo the output's own level,",
    "  [[<ct, s>]_Q]_t (Spec.Scheme.bgvDecrypt). certify? evaluates Spec.Encrypt.certOK?: every",
    "  output is under s itself (Galois element 1; an output left under a rotated key is refused).",
    "  NOT covered: a decryption",
    "  that first switches the ciphertext or its phase to fewer limbs (OpenFHE's Decrypt does; its",
    "  extractor declares that, and this file does not)."]
  | .switched => [
    "DECRYPTION COVERED: decryption with the PHASE switched to one limb, as OpenFHE's",
    "  PKEBGVRNS::Decrypt does for a ciphertext in EVALUATION format (bgvrns-pke.cpp:52-71): compute",
    "  <ct, s> modulo the output's level, switch that one polynomial down to q0 by the centred",
    "  t-corrected switch, read it modulo q0 (centred) and modulo t. This is",
    "  Spec.Decrypt.bgvDecryptSwitched, WITH THE SECRET KEY s. certify? evaluates",
    "  Spec.Encrypt.certOK? on every output with its bound: the output is under s itself (Galois",
    "  element 1; an output left under a rotated key sigma_g(s) is refused), and",
    "  Spec.Decrypt.decryptAllOK? holds: the switched-phase bound decBound (shown per output; each",
    "  dropped limb q maps B to floor((B + t*floor(q/2))/q), no secret-dependent term) is below",
    "  q0/2. By the certificate theorem each output then decrypts to its message times",
    "  decScale = (q_1*...*q_(l-1))^-1 mod t, the factor the library keeps in the ciphertext's",
    "  scaling factor and removes when decoding (see the line \"user-level decryption ...\": covered",
    "  when Spec.Scaling.scaleOK? accepts the input's scaling data, Challenge.Scaling.certify?_user;",
    "  that the library tracks its factor as Spec.Scaling.facStep says is an assumption).",
    "  Textbook decryption with s at the output's level is covered too (same theorem).",
    "  NOT covered: the COEFFICIENT-format branch of Decrypt, which switches",
    "  every ciphertext component instead of the phase."]

def meaningText (inp : Input) (v : Verdict) (ki : Option KappaInfo := none) : List String :=
  let P := inp.P
  let canon := inp.ks.variant != .centred
  let boundsLine :=
    s!"{inp.bounds.length} input(s) declare their own bound ({boundsList inp.bounds}); the theorem covers only inputs that meet it."
  let header := match v, ki with
    | .certified, none => [
      "WHAT \"CERTIFIED\" MEANS",
      "fhe_check computed the value of the locked Lean function Challenge.Certify.certify? on the decoded",
      "parameters, key-switching layout, program and decryption method, and it returned a",
      "certificate. certify? itself runs Spec.schemeParamsOK?, Spec.Budget.specialOK?, the layout",
      s!"check at every level, {analyzerName} (the reference worst-case BGV",
      "noise analysis; the hole FHE.Holes.analyze of the headline theorem is defined as this same",
      "function today) with the budget Spec.Budget.certified, which returned the bound shown for each",
      "output, and Spec.Encrypt.certOK? on each output with that bound",
      "(Challenge.Certify.certify?_spec). The Lean theorem Challenge.Certify.worst_certified,",
      "proved and kernel-checked in this repository, then states, from certify? = some c alone:",
      "for every secret key s (no bound on s is assumed here; that an execution within the budget",
      "exists, and that the reference algorithms stay within it, is proved for s within secretBound:",
      "Challenge.Certify.certified_run_exists, Challenge.Budget.relin_realizable), all input messages, and",
      "all input ciphertexts with noise at most inputNoise (and at most their declared bound, for",
      "inputs that declare one), in EVERY execution of the program in which each operation meets its",
      "phase contract (Spec.Trace) with the budgets above, each output is a ciphertext under s itself",
      "that decrypts WITH s exactly to the value the program computes on the messages (see",
      "DECRYPTION COVERED), with noise at most the bound shown (Challenge.Budget.certified_sound)."]
    | .certified, some i => if i.deterministic then [
      "WHAT \"CERTIFIED\" MEANS",
      "CERTIFIED (fresh encryptions at the worst case of their error; no probability; evaluation",
      s!"worst-case). --kappa {i.kappa} was requested, but the high-probability error bound is not below the",
      "worst case, so the worst case was used (by the locked Challenge.Certify.certify?, which made",
      "every check itself). The Lean theorem instantiated is",
      "Challenge.Certify.fresh_worst_certified (proved and kernel-checked in this repository), at:",
      s!"  n = {i.n} fresh encryptions ({String.intercalate ", " i.model.inputs});",
      s!"  bounds: |s_i| <= secretBound = {P.secretBound}, public-key error |e_pk,i| <= {i.model.keyError},",
      s!"    encryption randomness |u_i| <= {i.model.u}, |e1_i| <= {i.model.e1}, |e2_i| <= {i.model.e2};",
      s!"  stored plaintext polynomials of norm at most Bp = {i.plainBound} ({bpSource i.model P.src.t});",
      s!"  eps = Spec.Encrypt.worstError = N*Bk*Bu + B1 + N*B2*Bs = {i.worst} ({pow2 i.worst})",
      s!"    (Spec.Encrypt.epsFor at kappa = {i.kappa}, plus the mean drift, is {i.epsKappa}, not smaller);",
      s!"  input noise used by the analyzer: freshNoise = Bp + t*eps = {i.inputNoise} ({pow2 i.inputNoise})",
      s!"    (the frontend's inputNoise {pow2 i.suppliedNoise} was NOT used);",
      "  Spec.Encrypt.freshOK? = true: every input is one of these fresh 2-part encryptions under s",
      "    (its modulus exceeds twice the input noise, and it declares NO bound of its own) or a",
      "    1-part plaintext operand with a declared bound; Spec.Encrypt.certOK? = true.",
      s!"The analysis is {analyzerName} (the reference analyzer; computed as stated below).",
      "Precisely: for any secret key s and public key (b, a) with b + a*s = t*e_pk modulo the full",
      "chain, within the bounds above, ALL encryption randomness (u, e1, e2) within its bounds, and all",
      "messages (and plaintext operands within their declared bounds): with the fresh inputs being",
      "Spec.Encrypt.encrypt of those messages, every output of every execution meeting the Spec.Trace",
      "contracts is under s and decrypts with s to the value the program computes."]
     else if let some l := i.l2 then
      let src := fun (g : Bool) => if g then "ASSUMED: supplied by the input" else "computed by fhe_check from the support bounds"
      let (gE, gS, gU, g1, g2) := l.given
      [
      "WHAT \"CERTIFIED\" MEANS",
      s!"CERTIFIED (fresh-noise failure probability at most 2^-{i.kappa}, l2 description of the key and the",
      s!"samplers; evaluation worst-case). For the fixed key, if ||s||_2^2 <= S2 and ||e_pk||_2^2 <= E2, and",
      "if each encryption draws the 3N coefficients of (u, e1, e2) independently, with means within the",
      "stated bound and sub-Gaussian about their means with",
      s!"variance proxies Vu, V1, V2, then with probability at least 1 - 2^-{i.kappa} over the encryption",
      "randomness alone, every output of this program decrypts exactly, for all messages. Assumed, not",
      "verified: the key and the samplers meet that description; the library's operations meet the",
      "per-operation contracts. No probability over messages, keys or rounding. No security claim.",
      "PER EXECUTION: 2^-kappa bounds the failure of ONE execution of the program (a union bound over",
      "the n*2N coefficient tails of its fresh encryptions, for one fixed key). Over E executions, or",
      "against a party that can request E batches of fresh encryptions, the bound is E*2^-kappa: to",
      "keep 2^-K overall, use kappa = K + ceil(log2 E). No adaptive adversary is modelled.",
      "",
      "The ONE Lean theorem instantiated is Challenge.Certify.fresh_l2_certified: if the locked",
      "function Challenge.Certify.certify? returns a certificate in the mode freshL2 (it did; it makes",
      "every check itself), the failure probability for ALL outputs together is at most 2^-kappa",
      "(proved and kernel-checked in this repository, from Challenge.FreshNoiseL2), at:",
      s!"  kappa = {i.kappa}; n = {i.n} fresh encryptions ({String.intercalate ", " i.model.inputs});",
      s!"  E2 = {l.E2} (||e_pk||_2^2 bound; {src gE}{if gE then "" else s!": N*Bk^2, Bk = {i.model.keyError}, Challenge.FreshNoiseL2.normSq_le"});",
      s!"  S2 = {l.S2} (||s||_2^2 bound; {src gS}{if gS then "" else s!": N*Bs^2, Bs = {P.secretBound}, normSq_le"});",
      s!"  Vu = {l.Vu}, V1 = {l.V1}, V2 = {l.V2} (sub-Gaussian variance proxies of u, e1, e2; Vu {src gU}, V1 {src g1}, V2 {src g2};",
      "    a computed proxy is the squared support bound: subGaussSamplerOK_of_samplerOK);",
      s!"  V = Spec.Encrypt.varProxyL2 = Vu*E2 + V1 + V2*S2 = {i.varProxy};",
      s!"  means of the coefficients of (u, e1, e2) at most {i.model.meanNum}/{i.model.meanDen} in absolute value ({meanSource i.model});",
      s!"  stored plaintext polynomials of norm at most Bp = {i.plainBound} ({bpSource i.model P.src.t});",
      s!"  eps = Spec.Encrypt.epsFor V (n*2N) kappa + drift = {i.eps} ({pow2 i.eps}), drift = Spec.Encrypt.meanDrift (E2+1+S2) = {i.drift},",
      s!"    so that n*2N*exp(-(eps-drift)^2/(2V)) <= 2^-{i.kappa} (epsFor_spec, freshError_tail_l2);",
      s!"    no fallback to the worst case in this mode (worstError = {i.worst}, {pow2 i.worst});",
      s!"  input noise used by the analyzer: freshNoise = Bp + t*eps = {i.inputNoise} ({pow2 i.inputNoise})",
      s!"    (the frontend's inputNoise {pow2 i.suppliedNoise} was NOT used);",
      "  Spec.Encrypt.freshOK? = true; Spec.Encrypt.certOK? = true.",
      s!"The analysis is {analyzerName} (the reference analyzer; computed as stated below).",
      "Precisely: fix the parameters, the program, a secret key s and a public key (b, a) with",
      "b + a*s = t*e_pk modulo the full chain, with ||s||_2^2 <= S2 and ||e_pk||_2^2 <= E2 (hypotheses",
      "on the one fixed key: nothing proves that a generated key meets them unless they were computed",
      "from the support bounds). On ANY probability space carrying, for each fresh input, randomness",
      "(u, e1, e2) whose 3N coefficients are independent, of mean within the stated bound, and",
      "sub-Gaussian about their means with proxies Vu, V1, V2",
      "(Challenge.FreshNoiseL2.SubGaussSamplerOK), the probability that there EXIST messages for which",
      "some output of some execution meeting the Spec.Trace contracts is not under s, does not decrypt",
      s!"with s to the value the program computes, or exceeds its bound, is at most 2^-{i.kappa}.",
      "NOT proved here (an assumption whenever a proxy is below the squared support bound): that a",
      "centred discrete Gaussian of parameter sigma, truncated symmetrically, has proxy sigma^2",
      "(Micciancio-Peikert 2012, Lemma 2.8), or the uniform ternary distribution proxy 2/3.",
      s!"Source of the supplied values: {if l.source.isEmpty then "(none given)" else l.source}."]
     else [
      "WHAT \"CERTIFIED\" MEANS",
      s!"CERTIFIED (fresh-noise failure probability at most 2^-{i.kappa}; evaluation worst-case). For every",
      s!"secret and public key within the stated bounds and every choice of the {i.n} input messages: if each",
      "encryption draws its coefficients independently, within the sampler bounds and with means within",
      "the stated mean bound,",
      s!"then with probability at least 1 - 2^-{i.kappa} over the encryption randomness alone, every output of",
      "this program decrypts exactly. Assumed, not verified: the library's samplers meet that",
      "description; the library's operations meet the per-operation contracts. No probability is taken",
      "over messages, keys or rounding. No security claim.",
      "PER EXECUTION: 2^-kappa bounds the failure of ONE execution of the program (a union bound over",
      "the n*2N coefficient tails of its fresh encryptions, for one fixed key). Over E executions, or",
      "against a party that can request E batches of fresh encryptions, the bound is E*2^-kappa: to",
      "keep 2^-K overall, use kappa = K + ceil(log2 E). No adaptive adversary is modelled.",
      "",
      "The ONE Lean theorem instantiated is Challenge.Certify.fresh_kappa_certified: if the locked",
      "function Challenge.Certify.certify? returns a certificate (it did; it makes every check",
      "itself), the failure probability for ALL outputs together is at most 2^-kappa (it contains the",
      "noise analysis, the fresh-noise tail bound and the decryption; proved from",
      "freshError_tail, epsFor_spec, phase_encrypt and kernel-checked in this repository), at:",
      s!"  kappa = {i.kappa}; n = {i.n} fresh encryptions ({String.intercalate ", " i.model.inputs});",
      s!"  bounds: |s_i| <= secretBound = {P.secretBound}, public-key error |e_pk,i| <= {i.model.keyError},",
      s!"    encryption randomness |u_i| <= {i.model.u}, |e1_i| <= {i.model.e1}, |e2_i| <= {i.model.e2};",
      s!"  V = Spec.Encrypt.varProxy = N*(Bk*Bu)^2 + B1^2 + N*(B2*Bs)^2 = {i.varProxy};",
      s!"  means of the coefficients of (u, e1, e2) at most {i.model.meanNum}/{i.model.meanDen} in absolute value ({meanSource i.model});",
      s!"  stored plaintext polynomials of norm at most Bp = {i.plainBound} ({bpSource i.model P.src.t});",
      s!"  eps = Spec.Encrypt.epsFor V (n*2N) kappa + drift = {i.eps} ({pow2 i.eps}), computed by fhe_check, with",
      s!"    drift = Spec.Encrypt.meanDrift (N*Bk + 1 + N*Bs) = {i.drift}, so that",
      s!"    n*2N*exp(-(eps-drift)^2/(2V)) <= 2^-{i.kappa} (epsFor_spec, freshError_tail); the worst case of the",
      s!"    same error is Spec.Encrypt.worstError = {i.worst} ({pow2 i.worst});",
      s!"  input noise used by the analyzer: freshNoise = Bp + t*eps = {i.inputNoise} ({pow2 i.inputNoise})",
      s!"    (the frontend's inputNoise {pow2 i.suppliedNoise} was NOT used);",
      "  Spec.Encrypt.freshOK? = true: every input is one of these fresh 2-part encryptions under s",
      "    (its modulus exceeds twice the input noise, and it declares NO bound of its own) or a",
      "    1-part plaintext operand with a declared bound; Spec.Encrypt.certOK? = true.",
      s!"The analysis is {analyzerName} (the reference analyzer; computed as stated below).",
      "Precisely: fix the parameters, the program, any secret key s and any public key (b, a) with",
      "b + a*s = t*e_pk modulo the full chain, within the bounds above. On ANY probability space",
      "carrying, for each fresh input, randomness (u, e1, e2) whose 3N coefficients are independent,",
      "of mean within the stated mean bound and almost surely within their bounds (Challenge.FreshNoise.SamplerOK; the triples of",
      "different inputs need not be independent of each other), the probability of the event \"there",
      "EXIST messages (and plaintext operands within their declared bounds) such that, with the inputs",
      "being Spec.Encrypt.encrypt of those messages under (b, a) with that randomness, some output of",
      "some execution meeting the Spec.Trace contracts is not under s or does not decrypt with s to the",
      s!"value the program computes\" is at most 2^-{i.kappa}.",
      "What this says about chosen messages: the messages are quantified INSIDE the event, so the",
      "guarantee holds for all messages simultaneously, including messages chosen by an adversary",
      "(the error of a fresh encryption does not depend on its message). What it does NOT say:",
      "anything about randomness that is not as described (a biased, correlated or re-drawn sampler;",
      "an adversary who can make the encryptor re-encrypt or who selects among several encryptions);",
      "anything about ciphertexts that are not these fresh encryptions; any average over keys."]
    | _, _ => [
      "WHAT \"NOT CERTIFIED\" / \"UNSUPPORTED\" MEANS",
      "No theorem is claimed. This is not a proof that decryption fails: the analysis could not show",
      "it always succeeds (or the input is outside what is certified). Worst-case bounds are usually",
      "far above what is observed in practice."]
  let noiseAssumption := match ki with
    | none => [
      s!"  1. Noise of the inputs: every input ciphertext has centred phase m + t*e with",
      s!"     |m + t*e|inf <= inputNoise = {P.inputNoise} ({pow2 P.inputNoise}); every key-switching key",
      s!"     has error <= keyNoise = {P.keyNoise} ({pow2 P.keyNoise}), divisible by t; every secret-key",
      s!"     coefficient has |s_i| <= secretBound = {P.secretBound}. {boundsLine}",
      s!"     These values were supplied by the frontend",
      s!"     ({inp.sourceTool}) from the library's sampler constants and encodings (see \"noise",
      "     derivation\"); fhe_check did not derive or check them."]
    | some i =>
      if let some l := i.l2 then [
      s!"  1. The inputs: each of the {i.n} ciphertext inputs is a fresh public-key encryption of the form",
      s!"     (b*u + t*e1 + p, a*u + t*e2), p the stored plaintext polynomial of the message, |p| <= Bp = {i.plainBound}",
      "     (Spec.Encrypt.encrypt), whose randomness",
      s!"     has independent sub-Gaussian coefficients with variance proxies Vu = {l.Vu}, V1 = {l.V1}, V2 = {l.V2};",
      s!"     the fixed key has ||e_pk||_2^2 <= E2 = {l.E2} and ||s||_2^2 <= S2 = {l.S2} (values supplied by the",
      "     input are ASSUMPTIONS, see above; computed ones follow from the support bounds); every",
      s!"     key-switching key has error <= keyNoise = {P.keyNoise} ({pow2 P.keyNoise}), divisible by t; every",
      s!"     secret-key coefficient has |s_i| <= secretBound = {P.secretBound}. {boundsLine}",
      s!"     Which inputs are fresh encryptions, the bounds and any l2 values were supplied by the",
      s!"     frontend ({inp.sourceTool}: {i.model.source}); fhe_check did not check them, and no sampler",
      "     implementation was examined."]
      else [
      s!"  1. The inputs: each of the {i.n} ciphertext inputs is a fresh public-key encryption of the form",
      s!"     (b*u + t*e1 + p, a*u + t*e2), p the stored plaintext polynomial of the message, |p| <= Bp = {i.plainBound}",
      "     (Spec.Encrypt.encrypt), whose randomness",
      (if i.deterministic then "     is within its bounds (coefficients within the"
       else "     meets the sampler description above (independent coefficients, means within the stated bound, within the"),
      s!"     bounds {i.model.u}, {i.model.e1}, {i.model.e2}); the public key has error at most {i.model.keyError}; every",
      s!"     key-switching key has error <= keyNoise = {P.keyNoise} ({pow2 P.keyNoise}), divisible by t; every",
      s!"     secret-key coefficient has |s_i| <= secretBound = {P.secretBound}. {boundsLine}",
      s!"     Which inputs are fresh encryptions, and the bounds, were supplied by the frontend",
      s!"     ({inp.sourceTool}: {i.model.source}); fhe_check did not check them, and no sampler",
      "     implementation was examined."]
  header ++ computedByText ++ [
    "",
    "Where the budgets come from (Spec.Budget, locked pins in Challenge.Budget, proved):",
    s!"  key switching: E.keySwitch = ksBudget, the largest ksBoundAt over the levels of the chain, for",
    s!"    {if canon then "canonical" else "centred"} representatives and the declared digit layout. Challenge.Budget.relin_realizable",
    "    and keySwitch_realizable: at every level, RNS hybrid key switching with keys of noise at most",
    "    keyNoise (divisible by t) meets the relin/keySwitch contract within ksBoundAt, for any prime",
    "    sizes, given SpecialOK (checked here by Spec.Budget.specialOK?).",
    "  modulus switching: E.modSwitch = msBudget = ceil(t*(1+N*secretBound)/2) for a 2-part ciphertext",
    "    (Challenge.Budget.modSwitch_realizable) and E.modSwitchOne = msBudgetOne = ceil(t/2) for a",
    "    1-part value, i.e. a plaintext operand (Challenge.Budget.modSwitch_realizable_one); for a value",
    "    with k parts (a product not yet relinearized: k = 3), E.modSwitchAt k = msBudgetAt P k =",
    "    ceil(t*sum_{i<k}(N*secretBound)^i/2) (Challenge.Budget.modSwitch_realizable_parts): the centred",
    "    t-corrected switch of every part meets the modSwitch contract within them.",
    ""] ++ decryptionText inp ++ [
    "",
    "ASSUMPTIONS (inputs to the theorem, not proved by it):"] ++ noiseAssumption ++ [
    "  2. The library's operations meet the per-operation phase contracts of Spec.Trace with these",
    "     budgets, and its key switching uses the declared digit layout and representatives. That",
    "     the contracts are achievable is proved for the reference algorithms in this repository",
    "     (textbook add/multiply, RNS hybrid key switching, centred t-corrected modulus switching),",
    "     NOT for OpenFHE's C++ or Lattigo's Go code, whose agreement with them is assumed. The",
    "     frontend's translation of the library's program into the operations listed is untrusted;",
    "     so is its statement of which decryption the library performs.",
    (match ki with
     | none => "  3. Worst-case analysis (infinity norm, every coefficient at its extreme); no probabilistic or"
     | some _ => "  3. Evaluation is analysed in the worst case (infinity norm, every coefficient at its extreme);"),
    (match ki with
     | none => "     average-case statement."
     | some i => if i.deterministic then "     no probabilistic statement is made."
                 else "     the only probabilistic statement is the one above, about the encryption randomness."),
    "  4. BGV only. No security claim: the parameters are not checked for a security level.",
    "     (The \"Security note\" compares log2(Q*P) with the standard's table; it is not part of",
    "     the certificate.)",
    "  5. Each output is decrypted with the secret key s the inputs were encrypted under.",
    "  6. The executable is compiled by the Lean compiler from the verified definitions; the Lean",
    "     compiler and runtime, and this tool's (untrusted) JSON decoding and printing, are trusted.",
    "Neither OpenFHE, nor HEIR, nor Lattigo has been verified."]

/-! ### Human-readable rendering -/

def renderHuman (path : String) (r : Result) (showSteps : Bool) : String := Id.run do
  let mut L : Array String := #[]
  L := L.push s!"fhe_check: {path}"
  L := L.push s!"VERDICT: {r.label}: {r.headline}"
  for w in r.warnings do L := L.push s!"WARNING: {w}"
  if r.verdict == .certified then L := L.push certifiesLine
  let some inp := r.input | return "\n".intercalate L.toList
  if r.verdict == .certified then L := L.push (r.userDec.getD (userDecryption inp)).2
  let P := inp.P
  L := L.push ""
  let Qtop := P.src.modulus P.src.qs.length
  L := L.push s!"Parameters (BGV, from {inp.sourceTool}): N = {P.src.N}, t = {P.src.t}, {P.src.qs.length} ciphertext primes (log2 Q = {fmt2 (log2F Qtop)}), {P.store.special.length} special primes (log2 P = {fmt2 (log2F (P.store.special.map (·.q)).prod)})"
  L := L.push s!"  limb bits: {P.src.qs.map fun q => fmt2 (log2F q)}"
  match r.schemeOK with
  | some true => L := L.push "  Spec.schemeParamsOK? (chain): passed"
  | some false => L := L.push "  Spec.schemeParamsOK? (chain): FAILED"
  | none => pure ()
  match r.specialOK with
  | some true => L := L.push "  Spec.Budget.specialOK? (special primes): passed"
  | some false => L := L.push "  Spec.Budget.specialOK? (special primes): FAILED"
  | none => pure ()
  L := L.push ""
  L := L.push "Security note (NOT part of the verdict; the table is an INPUT ASSUMPTION, not proved here):"
  L := L ++ (securityLines P).toArray
  match r.kappa with
  | some i =>
    L := L.push ""
    if i.deterministic then
      L := L.push s!"Mode: fresh encryptions at the worst case of their error (no probability); evaluation worst-case (--kappa {i.kappa} gave no gain)"
      L := L.push s!"  error bound eps = Spec.Encrypt.worstError = {i.eps} ({pow2 i.eps}) for {i.n} fresh encryption(s); Spec.Encrypt.epsFor at kappa {i.kappa} is {i.epsKappa} ({pow2 i.epsKappa})"
    else
      L := L.push s!"Mode: fresh-encryption noise with probability >= 1 - 2^-{i.kappa}; evaluation worst-case (--kappa {i.kappa}{if i.l2.isSome then " --l2" else ""})"
      if let some l := i.l2 then
        let g := fun (b : Bool) => if b then "input" else "computed"
        let (gE, gS, gU, g1, g2) := l.given
        L := L.push s!"  l2 description: E2 = {l.E2} ({g gE}), S2 = {l.S2} ({g gS}), Vu = {l.Vu} ({g gU}), V1 = {l.V1} ({g g1}), V2 = {l.V2} ({g g2}); V = Spec.Encrypt.varProxyL2 = {i.varProxy}"
      L := L.push s!"  error bound eps = Spec.Encrypt.epsFor + drift = {i.eps} ({pow2 i.eps}) for {i.n} fresh encryption(s), drift {i.drift} for sampler means within {i.model.meanNum}/{i.model.meanDen} ({meanSource i.model}); worst case {i.worst} ({pow2 i.worst})"
    L := L.push s!"  input noise Bp + t*eps = {i.inputNoise} ({pow2 i.inputNoise}), Bp = {i.plainBound} ({bpSource i.model P.src.t}); the frontend's inputNoise ({pow2 i.suppliedNoise}) is not used"
    if r.failure.any (·.what == "Spec.Encrypt.freshOK? = false") then
      L := L.push "  Spec.Encrypt.freshOK? (inputs are unbounded fresh encryptions or bounded 1-part plaintexts): FAILED"
    else if r.schemeOK == some true && r.specialOK == some true then
      L := L.push "  Spec.Encrypt.freshOK? (inputs are unbounded fresh encryptions or bounded 1-part plaintexts): passed"
  | none =>
    L := L.push ""
    L := L.push s!"Mode: worst case (input noise {pow2 P.inputNoise}, supplied by the frontend){if inp.fresh.isSome then "; --kappa K is available for this file" else ""}"
  if let some br := r.budget then
    L := L.push ""
    L := L.push "Budgets (computed by fhe_check, not read from the input):"
    let lay := if br.layout.canonical then "canonical" else "centred"
    L := L.push s!"  E.keySwitch = Spec.Budget.ksBudget = {br.E.keySwitch} ({pow2 br.E.keySwitch}): max of ksBoundAt over levels 1..{inp.P.src.qs.length}, {lay} representatives (reference algorithm: {inp.ks.variant.theorem})"
    for k in br.ksLevels do
      if br.usedKsLevels.contains k.level || k.bound == br.E.keySwitch then
        L := L.push s!"    level {k.level}: ksBoundAt = {pow2 k.bound}; digits (limbs, log2 Q_j): {k.digits.map fun (l, Q) => (l, fmt2 (log2F Q))}{if br.usedKsLevels.contains k.level then "  [used]" else ""}"
    if !br.hasKs then L := L.push "    (the program does not key-switch; the budget is unused)"
    if br.hasMs then
      L := L.push s!"  E.modSwitch = Spec.Budget.msBudget = ceil(t*(1+N*secretBound)/2) = {br.E.modSwitch} ({pow2 br.E.modSwitch})"
    else L := L.push s!"  E.modSwitch = Spec.Budget.msBudget = {br.E.modSwitch} ({pow2 br.E.modSwitch}) (the program does not modulus-switch a {if br.msManyParts.isEmpty then "" else "2-part "}ciphertext)"
    if br.hasMsOne then
      L := L.push s!"  E.modSwitchOne = Spec.Budget.msBudgetOne = ceil(t/2) = {br.E.modSwitchOne} ({pow2 br.E.modSwitchOne}) (modulus switch of a 1-part value: a plaintext operand)"
    for k in br.msManyParts do
      L := L.push s!"  E.modSwitchAt {k} = Spec.Budget.msBudgetAt P {k} = ceil(t*sum_(i<{k}) (N*secretBound)^i / 2) = {br.E.modSwitchAt k} ({pow2 (br.E.modSwitchAt k)}) (modulus switch of a {k}-part value, not relinearized; Challenge.Budget.modSwitch_realizable_parts)"
  if !r.outputs.isEmpty then
    L := L.push ""
    L := L.push s!"Outputs (bound = {analyzerName} on the program with this output alone):"
    let q0 := P.src.qs.headD 0
    for o in r.outputs do
      L := L.push s!"  {o.name}: level {o.level}, noise <= {pow2 o.bound}, Q/2 = {pow2 (o.Q / 2)}, margin {fmt2 (log2F o.Q - 1 - log2F o.bound)} bits{match o.key with | some 1 => "" | some g => s!"  [UNDER THE ROTATED KEY sigma_{g}(s), NOT s]" | none => "  [key unknown]"}"
      if let some db := o.decBound then
        L := L.push s!"    decryption (phase switched to one limb): Spec.Decrypt.decBound = {pow2 db}, q0/2 = {pow2 (q0 / 2)}, margin {fmt2 (log2F q0 - 1 - log2F db)} bits{if o.decOK then "" else "  [NOT below q0/2]"}"
  if let some f := r.failure then
    L := L.push ""
    match f.step with
    | some s =>
      L := L.push s!"First failing instruction: body[{s.idx}]  {instrStr s.instr}{(inp.provenance.find? (·.1 = s.idx)).map (fun p => s!"   [{p.2}]") |>.getD ""}"
      match s.ill with
      | some why => L := L.push s!"  Source.step rejects it: {why}"
      | none =>
        L := L.push s!"  bound after it (diagnostic, locked refBound): {pow2 s.bound} at level {s.level}; Q/2 = {pow2 (s.Q / 2)}"
        L := L.push s!"  overflow: 2*B >= Q by {fmt2 (log2F (2 * s.bound) - log2F s.Q)} bits"
      L := L.push s!"  location {if f.confirmed then "confirmed" else "NOT confirmed"} by {analyzerName} on the prefixes body[0..{s.idx}] (rejects) and body[0..{s.idx}) (accepts)"
    | none => L := L.push s!"Reason: {f.what}"
  if !r.suggestions.isEmpty then
    L := L.push ""
    L := L.push "SUGGESTIONS (smallest change that would certify, found by running the verified analyzer on"
    L := L.push "hypothetical inputs; NOT a theorem, not proved minimal; re-check on the real regenerated input):"
    for sg in r.suggestions do L := L.push s!"  - {sg}"
  if showSteps && !r.steps.isEmpty then
    L := L.push ""
    L := L.push "Steps (diagnostic replay with the locked refBound):"
    for s in r.steps do
      match s.ill with
      | some why => L := L.push s!"  [{s.idx}] {instrStr s.instr}: ill-formed: {why}"
      | none => L := L.push s!"  [{s.idx}] {instrStr s.instr}: level {s.level}, parts {s.parts}, B = {pow2 s.bound}, margin {fmt2 (log2F s.Q - 1 - log2F s.bound)} bits"
  if !inp.noiseDerivation.isNull then
    L := L.push ""
    L := L.push s!"Noise derivation (from the frontend, printed, NOT checked): {inp.noiseDerivation.compress}"
  L := L.push ""
  L := L ++ (meaningText inp r.verdict r.kappa).toArray
  return "\n".intercalate L.toList

/-! ### JSON rendering -/

def natJ (n : Nat) : Json := Json.str (toString n)

def renderJson (path : String) (r : Result) : Json := Id.run do
  let mut fields : List (String × Json) :=
    [("tool", "fhe_check"), ("format", "fhe-check-report/v1"), ("input", Json.str path),
     ("verdict", Json.str r.verdict.label), ("verdictLabel", Json.str r.label), ("summary", Json.str r.headline)]
  if let some inp := r.input then
    let P := inp.P
    fields := fields ++ [("params", Json.mkObj [
      ("N", natJ P.src.N), ("t", natJ P.src.t), ("limbs", toJson (P.src.qs.map toString)),
      ("special", toJson (P.store.special.map (toString ·.q))),
      ("log2Q", jsonF (log2F (P.src.modulus P.src.qs.length))),
      ("schemeParamsOK", toJson r.schemeOK), ("specialOK", toJson r.specialOK)])]
    let qp := qpOf P
    let N := P.src.N
    fields := fields ++ [("security", Json.mkObj [
      ("partOfVerdict", toJson false),
      ("log2QP", jsonF (log2F qp)),
      ("assumption", Json.str s!"INPUT ASSUMPTION, not proved here: {secCitation}"),
      ("N", natJ N),
      ("row", Json.str (if (secNoEntry N).isSome then "none" else if secRowIsExtension N then "openfhe-extension (not in the 2018 standard)" else "standard-2018")),
      ("caps", match secNoEntry N with
        | some _ => Json.null
        | none => Json.mkObj [("128", toJson ((capOf 128 N).getD 0)), ("192", toJson ((capOf 192 N).getD 0)),
                              ("256", toJson ((capOf 256 N).getD 0))]),
      ("noEntry", match secNoEntry N with | some w => Json.str w | none => Json.null),
      ("exceeds128", match capOf 128 N with | some c => toJson (decide (qp ≥ 2 ^ c)) | none => Json.null)])]
    if r.verdict == .certified then
      fields := fields ++ [("certifiedProperty", Json.str "correctness (exact decryption), not security")]
    fields := fields ++ [("assumptions", Json.mkObj [
      ("inputNoise", natJ P.inputNoise), ("keyNoise", natJ P.keyNoise),
      ("secretBound", natJ P.secretBound), ("keySwitchVariant", Json.str inp.ks.variant.name),
      ("declaredBounds", Json.arr (inp.bounds.map fun (x, b) => Json.mkObj [("input", Json.str x), ("bound", natJ b)]).toArray),
      ("modSwitchMethod", Json.str inp.msMethod), ("suppliedBy", Json.str inp.sourceTool),
      ("noiseDerivation", inp.noiseDerivation)])]
    if let some br := r.budget then
      fields := fields ++ [("budget", Json.mkObj [
        ("keySwitch", natJ br.E.keySwitch), ("keySwitchLog2", jsonF (log2F br.E.keySwitch)),
        ("keySwitchFrom", Json.str "Spec.Budget.ksBudget"),
        ("keySwitchCanonical", toJson br.layout.canonical),
        ("keySwitchUsedLevels", toJson br.usedKsLevels),
        ("keySwitchPerLevel", Json.arr (br.ksLevels.map fun k => Json.mkObj [
          ("level", toJson k.level), ("bound", natJ k.bound), ("log2", jsonF (log2F k.bound)),
          ("digits", Json.arr (k.digits.map fun (l, Q) => Json.mkObj [
            ("limbs", toJson l), ("log2Q", jsonF (log2F Q))]).toArray)]).toArray),
        ("modSwitch", natJ br.E.modSwitch), ("modSwitchLog2", jsonF (log2F br.E.modSwitch)),
        ("modSwitchFrom", Json.str "Spec.Budget.msBudget"),
        ("modSwitchOne", natJ br.E.modSwitchOne), ("modSwitchOneFrom", Json.str "Spec.Budget.msBudgetOne"),
        ("modSwitchMany", Json.arr (br.msManyParts.map fun k => Json.mkObj [
          ("parts", toJson k), ("bound", natJ (br.E.modSwitchAt k)),
          ("from", Json.str "Spec.Budget.msBudgetAt")]).toArray)])]
    if let some B := r.analyzed then
      fields := fields ++ [("bound", natJ B), ("boundLog2", jsonF (log2F B))]
    let q0 := P.src.qs.headD 0
    fields := fields ++ [("mode", match r.kappa with
      | none => Json.mkObj [("kind", "worst-case"), ("kappaAvailable", toJson inp.fresh.isSome)]
      | some i => Json.mkObj ([("kind", Json.str (if i.l2.isSome then "fresh-noise-probabilistic-l2" else if i.deterministic then "fresh-noise-worst-case" else "fresh-noise-probabilistic")),
          ("kappa", toJson i.kappa), ("epsForKappa", natJ i.epsKappa),
          ("freshInputs", toJson i.model.inputs), ("varProxy", natJ i.varProxy),
          ("unionCount", natJ i.count), ("eps", natJ i.eps), ("worstError", natJ i.worst),
          ("plaintextBound", natJ i.plainBound), ("plaintextBoundDeclared", toJson i.model.plainBound.isSome),
          ("meanBound", Json.mkObj [("num", natJ i.model.meanNum), ("den", natJ i.model.meanDen),
            ("declared", toJson i.model.meanGiven)]),
          ("meanDrift", natJ i.drift),
          ("inputNoise", natJ i.inputNoise), ("inputNoiseLog2", jsonF (log2F i.inputNoise)),
          ("frontendInputNoise", natJ i.suppliedNoise),
          ("bounds", Json.mkObj [("keyError", toJson i.model.keyError), ("u", toJson i.model.u),
            ("e1", toJson i.model.e1), ("e2", toJson i.model.e2)])] ++
          (match i.l2 with
           | none => []
           | some l =>
             let (gE, gS, gU, g1, g2) := l.given
             [("l2", Json.mkObj [("keyErrorSq", natJ l.E2), ("secretSq", natJ l.S2), ("uProxy", natJ l.Vu),
               ("e1Proxy", natJ l.V1), ("e2Proxy", natJ l.V2),
               ("suppliedByInput", Json.mkObj [("keyErrorSq", toJson gE), ("secretSq", toJson gS),
                 ("uProxy", toJson gU), ("e1Proxy", toJson g1), ("e2Proxy", toJson g2)]),
               ("source", Json.str l.source)])]))),
      ("decryption", Json.str inp.decryption.name)]
    fields := fields ++ [("outputs", Json.arr (r.outputs.map fun o => Json.mkObj ([
      ("name", Json.str o.name), ("level", toJson o.level), ("bound", natJ o.bound),
      ("boundLog2", jsonF (log2F o.bound)), ("halfQLog2", jsonF (log2F o.Q - 1)),
      ("marginBits", jsonF (log2F o.Q - 1 - log2F o.bound)), ("galoisKey", toJson o.key)] ++
      (match o.decBound with
       | some db => [("decBound", natJ db), ("decBoundLog2", jsonF (log2F db)),
                     ("halfQ0Log2", jsonF (log2F q0 - 1)),
                     ("decMarginBits", jsonF (log2F q0 - 1 - log2F db)), ("decOK", toJson o.decOK)]
       | none => []))).toArray)]
    unless r.suggestions.isEmpty do
      fields := fields ++ [("suggestions", toJson r.suggestions)]
    unless r.warnings.isEmpty do
      fields := fields ++ [("warnings", toJson r.warnings)]
    if let some f := r.failure then
      let stepJ := match f.step with
        | some s => Json.mkObj [
            ("index", toJson s.idx), ("instr", Json.str (instrStr s.instr)),
            ("op", Json.str (instrOp s.instr)), ("illFormed", toJson s.ill),
            ("level", toJson s.level), ("bound", natJ s.bound), ("boundLog2", jsonF (log2F s.bound)),
            ("halfQLog2", jsonF (log2F s.Q - 1)),
            ("overflowBits", if s.ill.isSome then Json.null else jsonF (log2F (2 * s.bound) - log2F s.Q)),
            ("confirmedByAnalyze", toJson f.confirmed)]
        | none => Json.null
      fields := fields ++ [("failure", Json.mkObj [("reason", Json.str f.what), ("firstFailing", stepJ)])]
    fields := fields ++ [("analyzer", Json.str analyzerName),
      ("certificateTheorem", Json.str (certificateTheorem r.kappa))]
    if r.verdict == .certified then
      let (cov, line) := r.userDec.getD (userDecryption inp)
      fields := fields ++ [("userDecryption", Json.mkObj [("covered", toJson cov),
        ("theorem", if cov then Json.str "Challenge.Scaling.certify?_user" else Json.null),
        ("line", Json.str line)])]
    fields := fields ++ [("theorems", Json.arr ((theoremsCited inp r.kappa).map fun (n, d) =>
      Json.mkObj [("name", Json.str n), ("says", Json.str d)]).toArray),
      ("statement", Json.str ("\n".intercalate (meaningText inp r.verdict r.kappa)))]
  return Json.mkObj fields

end FHE.Check
