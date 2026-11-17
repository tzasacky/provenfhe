import FHE.Check.BFVBudget
import FHE.Check.Report
import Challenge.BFV.Defs
import Challenge.CertifyBFV.Defs
import Challenge.BFVEncrypt.Defs
import FHE.Holes
import Challenge.BFVDecrypt
import Challenge.BFVDecryptLib
import Spec.DecryptBFV
import Spec.Encrypt
import Spec.Decrypt

/-!
# FHE.Check.BFVReport — the `fhe_check` pipeline for BFV and its report   (UNTRUSTED glue)

**THE VERDICT: CERTIFIED only if the locked `Challenge.CertifyBFV.certifyBFV?` returns a
certificate, and the locked `Challenge.BFVDecryptLib.decryptLibExtOK?` holds of it** (below) for the decoded data (`FHE.Check.BFV.inputBFV` builds its input: parameters,
key-switching layout, program, declared multiplication technique with its auxiliary basis,
`floatTolerant`, plaintext-addition and modulus-switching methods, and under `HPSPOVERQLEVELED`
the declared internal drop of every instruction). `certifyBFV?` performs every check itself
(`Challenge.CertifyBFV.Defs`, module docstring): `Spec.schemeParamsOK?`,
`Spec.Budget.specialOK?`, the layout at every level, `Challenge.BFV.decOK` of every input
ciphertext's bound, the declared technique's side conditions (`Spec.BudgetBFV.Slack.ok`, the
locked `Challenge.BFVMul.hpsAuxOK?` / `poverqAuxOK?` / `leveledAuxOK?` / `behzAuxOK?`, the basis
checks) at every multiplication, the side conditions of a top-level key switch under
`HPSPOVERQLEVELED`, ONE BUDGET PER INSTRUCTION computed from the locked `Spec.BudgetBFV`
definitions (`Challenge.CertifyBFV.budgetBFV`), `Challenge.BFV.refAnalyzeBFVAt` at those budgets,
and `Spec.Encrypt.outputsUnderS?`.

**A verdict CERTIFIED instantiates the locked statement** `Challenge.CertifyBFV.certifyBFV?_sound`
(`certifyBFV? x = some c →` every output of every run in which instruction `k` meets its contract
within `c.budget k` decrypts with the secret key, with noise at most its own bound). The
certificate records what realizability rests on (`c.assumed`): when it records `binary64` (the
multiplication of the HPS family, and the key switch of `HPSPOVERQLEVELED`, are proved for every
arithmetic conforming to the standard model `Spec.Float.Conforms`; that the platform conforms is
a hypothesis) the verdict is printed as "CERTIFIED (binary64 steps … under the standard model
…)"; when it records `idealised` (the file declares `floatTolerant = false`, so the binary64 sums
are taken to be exact) the verdict is NOT CERTIFIED FOR THE LIBRARY (idealised algorithm
certified), with exit status 1, because `certifyBFV?_library_run` excludes it; when it records
`declaredDrops` (`HPSPOVERQLEVELED` with a multiplication or key switch
at the top level, whose internal drops are the frontend's declaration) or `binary64Dec` (the
technique is one of OpenFHE's, so the statement about the library's own decryption applies; it
holds for every arithmetic conforming to `Spec.DecryptBFV.ConformsD`, a hypothesis on the platform)
the verdict says so too; otherwise it is a bare CERTIFIED with the declared technique,
floatTolerant and drops printed.

**The library's own decryption decides too** (`libDecryptStatus`, `Challenge.BFVDecryptLib`). The
verdict is CERTIFIED only if the locked `Challenge.BFVDecryptLib.decryptLibExtOK?` holds, so that
`certifyBFV?_decryptsLibExt` proves that OpenFHE's own decryption (`PKEBFVRNS::Decrypt`, by the
routine it runs on each output: the binary64 `ScaleAndRound(t)` of the HPS family at full level,
BEHZ's integer `ScaleAndRound` at full level, or the drops and the binary64 `MultiplyAndRound`
below it) returns, coefficient by coefficient, a representative in `[0, t]` of each output's
message modulo `t` (decoding is not verified). Any output whose library decryption is not proved
withholds the certificate: NOT CERTIFIED when its routine's side condition or margin fails
(`decParamsOK?`/`decLibOK?`, `behzParamsOK?`/`decBEHZOK?`, `decLowParamsOK?`/`decLowOK?`;
the library's decryption is not covered beyond them); UNSUPPORTED when no proved routine applies: a BEHZ output with
`1 < ℓ < L` limbs (undefined behaviour in the library), or a file that declares no library
multiplication technique.

**Fresh encryptions: the input noise is computed, not declared.** When the file has a
`freshEncryption` section (the OpenFHE frontend writes one for `ENCRYPTION_TECHNIQUE = STANDARD`),
the verdict is that of the locked `Challenge.BFVEncrypt.certifyBFVFresh?` instead: it computes the
input noise from the declared key and sampler bounds (`Spec.EncryptBFV.freshInputNoise`: the error
bound of a fresh OpenFHE encryption, `Spec.EncryptBFV.encryptBFV`, plus its deterministic encoding
term), ignores `params.inputNoise`, checks `Spec.EncryptBFV.freshOKBFV?` and runs `certifyBFV?` at
those parameters. Without `--kappa` the error bound is the worst case of the supports
(`Challenge.BFVEncrypt.certifyBFVFresh?_worst`); with `--kappa K` it holds with probability at
least `1 − 2^(−K)` per execution (`certifyBFVFresh?_kappa`; `--l2`: `certifyBFVFresh?_kappaL2`).
Without that section the declared `params.inputNoise` is used (an ASSUMPTION the report prints)
and `--kappa` is refused.

The budgets this report prints are the locked `Challenge.CertifyBFV.budgetsBFV` evaluated by
`FHE.Check.BFVBudget` (which also explains them and words the refusals) and must equal the
certificate's, as must the bounds; a disagreement withholds the certificate.

Per-output bounds come from `refAnalyzeBFVAt` run with that output alone. The first failing
instruction is found by a replay with the locked `Challenge.BFV.refBoundBFV` (at the budget of
each instruction), `bndOK` and `Source.step`, and confirmed by `refAnalyzeBFVAt` on the prefixes
around it. Everything else (which clause failed, margins in bits, the largest noise `decOK`
accepts, suggestions) is *diagnostic*, labelled so, and never turns a rejection into an
acceptance.
-/

namespace FHE.Check.BFV
open Lean Spec Spec.Source Challenge.BFV
open Spec.TraceBFV (Bnd)

def analyzerName : String := "Challenge.BFV.refAnalyzeBFVAt"

/-- The analyzer `fhe_check` runs for BFV: `FHE.Holes.analyzeBFVFast` (`FHE/Noise/FastBFV.lean`:
environments in search trees, near-linear), which the locked statement
`Challenge.Fast.analyzeBFVFast_eq` proves equal, on every input, to the reference analyzer
`refAnalyzeBFVAt` the cited theorems are about. -/
def analyzer : NoiseAnalyzerBFVAt := FHE.Holes.analyzeBFVFast

/-- What `runCheck` reads instead of calling `analyzer` again: the same value, by definition. -/
theorem analyzer_eq_run (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    analyzer P E prog =
      (FHE.Noise.FastBFV.run P E prog).bind fun r => FHE.Noise.FastBFV.outBound r prog.outputs := by
  simp only [analyzer, FHE.Holes.analyzeBFVFast, FHE.Noise.FastBFV.analyze]; rfl

/-- The one locked statement a CERTIFIED BFV verdict instantiates. -/
def certificateTheorem : String := "Challenge.CertifyBFV.certifyBFV?_sound"

/-! ### Fresh encryptions (`Challenge.BFVEncrypt.certifyBFVFresh?`) -/

/-- The fresh-encryption mode of a run, with the figures the report prints. `eps`, `used`,
`drift` and `inputNoise` are a DIAGNOSTIC MIRROR of `Challenge.BFVEncrypt.certifyBFVFresh?`, whose
own result decides; a disagreement withholds the certificate. -/
structure FreshRun where
  model : FHE.Check.FreshModel
  mode : Spec.EncryptBFV.FreshModeBFV
  kappa : Option Nat := none
  l2 : Bool := false
  eps : Nat
  used : Spec.Certify.NoiseUsed
  drift : Nat := 0
  /-- `Spec.EncryptBFV.freshInputNoise`: the input noise analysed. -/
  inputNoise : Nat
  /-- The frontend's `params.inputNoise` (not used). -/
  supplied : Nat
  /-- `Spec.Encrypt.worstError` at the declared support bounds (for comparison). -/
  worst : Nat

/-- The locked statement a CERTIFIED verdict instantiates in a fresh-encryption mode. -/
def freshTheorem (f : FreshRun) : String :=
  match f.kappa, f.l2 with
  | none, _ => "Challenge.BFVEncrypt.certifyBFVFresh?_worst"
  | some _, false => "Challenge.BFVEncrypt.certifyBFVFresh?_kappa"
  | some _, true => "Challenge.BFVEncrypt.certifyBFVFresh?_kappaL2"

/-- The locked statement a CERTIFIED verdict instantiates. -/
def theoremOf (fr : Option FreshRun) : String :=
  match fr with
  | some f => freshTheorem f
  | none => certificateTheorem

/-- The fresh-encryption mode of a file, if it declares fresh encryptions (`freshEncryption`);
an error for `--kappa` without them, or for unusable numbers. -/
def freshSetup (inp : Input) (opts : FHE.Check.Options) : Except String (Option FreshRun) := do
  let P := inp.base.P
  let N := P.src.N
  let some fm := inp.base.fresh
    | match opts.kappa with
      | some κ => throw s!"--kappa {κ}: this file has no freshEncryption section (which inputs are fresh public-key encryptions and the key and sampler bounds), so there is nothing to bound probabilistically; run without --kappa for the worst-case certificate at the declared input noise"
      | none => return none
  let worst := Encrypt.worstError N P.secretBound fm.keyError fm.u fm.e1 fm.e2
  let n := fm.inputs.length
  let (mode, eps, used, drift, l2) ← match opts.kappa with
    | none =>
      pure (Spec.EncryptBFV.FreshModeBFV.worst fm.inputs fm.keyError fm.u fm.e1 fm.e2, worst,
        Spec.Certify.NoiseUsed.freshWorst, 0, false)
    | some κ =>
      if fm.meanDen = 0 then throw "freshEncryption.mean: the denominator is 0"
      if opts.l2 then
        let v := FHE.Check.l2Values P fm
        let V := Encrypt.varProxyL2 v.E2 v.S2 v.Vu v.V1 v.V2
        if V = 0 then throw "--l2: the l2 variance proxy is 0 (no randomness): nothing to bound probabilistically"
        let drift := Encrypt.meanDrift (v.E2 + 1 + v.S2) fm.meanNum fm.meanDen
        pure (.kappaL2 fm.inputs v.E2 v.S2 v.Vu v.V1 v.V2 fm.meanNum fm.meanDen κ,
          Encrypt.epsFor V (n * (2 * N)) κ + drift, .freshKappaL2, drift, true)
      else
        if Encrypt.varProxy N P.secretBound fm.keyError fm.u fm.e1 fm.e2 = 0 then
          throw "--kappa: the variance proxy is 0 (no randomness): nothing to bound probabilistically"
        let (eps, used, drift) :=
          Spec.Certify.freshEps P n fm.keyError fm.u fm.e1 fm.e2 fm.meanNum fm.meanDen κ
        pure (.kappa fm.inputs fm.keyError fm.u fm.e1 fm.e2 fm.meanNum fm.meanDen κ, eps, used,
          drift, false)
  return some { model := fm, mode, kappa := opts.kappa, l2, eps, used, drift, worst,
                -- `Spec.EncryptBFV.freshInputNoise`, with trees (`Validation.FastBFV.freshInputNoise_eq`)
                inputNoise := FHE.Noise.FastBFV.freshInputNoise P inp.base.prog fm.inputs eps,
                supplied := P.inputNoise }

/-! ### The verdict: `Challenge.CertifyBFV.certifyBFV?` -/

def assumptionName : Spec.CertifyBFV.AssumptionBFV → String
  | .binary64 => "binary64"
  | .idealised => "idealised"
  | .declaredDrops => "declaredDrops"
  | .binary64Dec => "binary64Dec"

/-- The qualifier of a CERTIFIED verdict whose certificate records an assumption (`none`: the
realizability basis is PROVED with no hypothesis on the platform). -/
def qualifier (techName : String) (as : List Spec.CertifyBFV.AssumptionBFV) : Option String :=
  let parts : List String :=
    (if as.contains .binary64 then
      [s!"binary64 steps of OpenFHE's {techName} under the standard model Spec.Float.Conforms; see platform conditions"]
    else if as.contains .idealised then
      [s!"budget of the IDEALISED exact {techName} with floatTolerant = false, NOT the library's binary64 code"]
    else []) ++
    (if as.contains .declaredDrops then
      ["assuming the internal drops declared by the frontend are the library's (FindLevelsToDrop is not modelled)"]
    else []) ++
    (if as.contains .binary64Dec then
      ["the library's decryption under the standard model Spec.DecryptBFV.ConformsD"]
    else [])
  if parts.isEmpty then none else some ("; ".intercalate parts)

/-- What the frontend declared that changes the budget, for the verdict line (no colon: the
tests match the verdict line up to the first colon). -/
def declaredStr (m : Option MulConfig) : String :=
  match m with
  | some m =>
    let drops := match m.internalDrops with
      | some ds => if ds.all (· == 0) then "internal drops all 0" else s!"internal drops {ds}"
      | none => "no internal drops declared"
    s!"declared by the frontend - technique {m.technique.name}, floatTolerant {m.floatTolerant}, {drops}"
  | none => "declared by the frontend - no multiplication technique"

/-- The locked realizability pins of the declared technique at the certificate's budgets
(`Challenge.CertifyBFV`; each is about one instruction, `AtInstr`): the multiplication, and for
`HPSPOVERQLEVELED` on a program that key-switches (`hasKs`) the library's key switch of a
top-level operand: with a nonzero declared drop at some key switch (`ksDrop`,
`Challenge.CertifyBFV.ksDropped`) the pins for every conforming binary64 arithmetic
(`certifyBFV?_leveled_relin`, `_leveled_keySwitch`), otherwise the drop-0 pins, which hold for
every arithmetic (`certifyBFV?_leveled_relin_drop0`, `_leveled_keySwitch_drop0`;
`Challenge.BFVMul.leveledKS_drop_zero`). -/
def realizabilityPins (tech : Option Technique) (as : List Spec.CertifyBFV.AssumptionBFV)
    (hasKs : Bool := false) (ksDrop : Bool := true) : List String :=
  let noFloat := !as.contains .binary64
  match tech with
  | none | some .textbook =>
    ["Challenge.CertifyBFV.certifyBFV?_textbook_mul", "Challenge.CertifyBFV.certifyBFV?_textbook_square"]
  | some .behz => ["Challenge.CertifyBFV.certifyBFV?_behz_mul", "Challenge.CertifyBFV.certifyBFV?_behz_square"]
  | some .hps => if noFloat then ["Challenge.CertifyBFV.certifyBFV?_hps_mul", "Challenge.CertifyBFV.certifyBFV?_hps_square"] else ["Challenge.CertifyBFV.certifyBFV?_hps_mul_float", "Challenge.CertifyBFV.certifyBFV?_hps_square_float"]
  | some .hpsPOverQ => if noFloat then ["Challenge.CertifyBFV.certifyBFV?_poverq_mul"] else ["Challenge.CertifyBFV.certifyBFV?_poverq_mul_float"]
  | some .hpsPOverQLeveled =>
    (if noFloat then ["Challenge.CertifyBFV.certifyBFV?_poverq_mul", "Challenge.CertifyBFV.certifyBFV?_leveled_mul"] else ["Challenge.CertifyBFV.certifyBFV?_poverq_mul_float", "Challenge.CertifyBFV.certifyBFV?_leveled_mul_float"]) ++
    (if !hasKs then []
     else if ksDrop then ["Challenge.CertifyBFV.certifyBFV?_leveled_relin", "Challenge.CertifyBFV.certifyBFV?_leveled_keySwitch"]
     else ["Challenge.CertifyBFV.certifyBFV?_leveled_relin_drop0", "Challenge.CertifyBFV.certifyBFV?_leveled_keySwitch_drop0"])

/-- A pin about the leveled key switch (as opposed to a multiplication pin). -/
def isKsPin (p : String) : Bool :=
  (p.splitOn "_leveled_relin").length > 1 || (p.splitOn "_leveled_keySwitch").length > 1

/-! ### Diagnostics (never decide the verdict) -/

/-- The largest noise bound `decOK t Q` accepts, `⌊(⌊(Q−1)/2⌋ − (Q mod t)·(t−1)) / t⌋`, returned
only if the locked `decOK` accepts it and rejects its successor (so the printed threshold is
checked against the locked definition); `none` if `decOK` accepts no bound. -/
def maxNoise (t Q : Nat) : Option Nat :=
  let c := Q % t * (t - 1)
  let h := (Q - 1) / 2
  if t = 0 || h < c then none else
  let b := (h - c) / t
  if decOK t Q b && !decOK t Q (b + 1) then some b else none

/-- `log₂` of the quantity `decOK` compares with `Q`: `2·(t·B + (Q mod t)·(t−1))`. -/
def decLhs (t Q B : Nat) : Nat := 2 * (t * B + Q % t * (t - 1))

def kindStr : Option Bnd → String
  | some (.ct _) => "a ciphertext"
  | some (.pt _) => "a plaintext"
  | none => "undefined"

/-- Why `refBoundBFV` has no rule (diagnostic). -/
def boundWhy (β : Var → Option Bnd) (i : Instr) : String :=
  s!"Challenge.BFV.refBoundBFV has no rule for {instrOp i} with these operands (" ++
  ", ".intercalate ((operandsOf i).map fun x => s!"{x}: {kindStr (β x)}") ++
  "): add, sub, mul, square, mulConst, automorph, relin, keySwitch, modSwitch take ciphertexts; addPlain, subPlain, mulPlain take a ciphertext and a plaintext (a one-component input); dropLimbs and rescale are not BFV operations"

/-- One step of the replay. -/
structure StepInfo where
  idx : Nat
  instr : Instr
  /-- `some`: `Source.step` or `refBoundBFV` rejected the instruction (with the reason). -/
  ill : Option String := none
  level : Nat := 0
  parts : Nat := 0
  /-- The bound `refBoundBFV` gives the destination. -/
  bnd : Bnd := .ct 0
  /-- `P.src.modulus level`. -/
  Q : Nat := 0
  /-- `Challenge.BFV.bndOK`: the decryption condition for a ciphertext bound. -/
  ok : Bool := true

def StepInfo.failed (s : StepInfo) : Bool := s.ill.isSome || !s.ok

/-- The initial bounds, as in `refAnalyzeBFVAt`. -/
def initBounds (P : FullParams) (prog : Program) : Var → Option Bnd :=
  fun x => (prog.inputs.find? (·.name = x)).map fun d =>
    if d.parts = 1 then .pt (TraceBFV.inputBound P prog d) else .ct (TraceBFV.inputBound P prog d)

/-- Replay of `refRunBFVAt` that records every step up to and including the first one it
rejects. The numbers are those of the locked `Source.step`, `refBoundBFV` (at the budget `E idx`
of the instruction) and `bndOK`; the loop around them is a diagnostic mirror of `refRunBFVAt`
(the verdict comes from `certifyBFV?`). -/
def replay (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) : Array StepInfo := Id.run do
  -- the environments in search trees (as `FHE.Noise.FastBFV.runBody`): near-linear
  let mut ρm : Std.TreeMap Var (Val P.src) := FHE.Noise.Fast.initEnvMap P.src prog
  let mut βm : Std.TreeMap Var Bnd := FHE.Noise.FastBFV.initBndMap P prog
  let Qt := FHE.Noise.Fast.modAt P (FHE.Noise.Fast.modsOf P)
  let mut out := #[]
  let mut idx := 0
  for i in prog.body do
    let ρ : Env P.src := let m := ρm; fun x => m[x]?
    let β : Var → Option Bnd := let m := βm; fun x => m[x]?
    match step P.src ρ i with
    | none =>
      out := out.push { idx, instr := i, ill := some s!"Source.step rejects it: {stepWhy P.src ρ i}" }
      break
    | some ρ' =>
      match ρ' (Trace.dst i) with
      | none =>
        out := out.push { idx, instr := i, ill := some "Source.step did not define the destination" }
        break
      | some v =>
        -- `refBoundBFV`, `bndOK` with the moduli from a table (`FHE.Noise.FastBFV.refBoundBFVQ`,
        -- `bndOKQ`; equal to them: `Validation.FastBFV.Aux.refBoundBFVQ_eq`, `bndOKQ_eq`)
        match FHE.Noise.FastBFV.refBoundBFVQ P (E idx) v.level (Qt v.level) β i with
        | none =>
          out := out.push { idx, instr := i, ill := some (boundWhy β i) }
          break
        | some b =>
          let ok := FHE.Noise.FastBFV.bndOKQ P (Qt v.level) b
          out := out.push { idx, instr := i, level := v.level, parts := v.parts, bnd := b,
                            Q := Qt v.level, ok }
          if !ok then break
          ρm := ρm.insert (Trace.dst i) v
          βm := βm.insert (Trace.dst i) b
    idx := idx + 1
  return out

/-! ### Guard: the library's floating-point decryption (OpenFHE, HPS family)

The certificate is about textbook decryption at the output's level (`Spec.Scheme.bfvDecrypt`). For
the HPS family OpenFHE v1.6.1 decrypts a ciphertext with the FULL number of limbs with
`DCRTPolyImpl::ScaleAndRound(t, …)` (`bfvrns-pke.cpp:238-248`; `dcrtpoly-impl.h:1220-1480`), which
adds an integer sum to a binary64 sum. When their worst-case magnitude reaches `2⁵³` the library's
decryption is outside the precision condition of the proved statement. This
guard is UNTRUSTED glue: it evaluates the library's branch selection and the worst-case magnitude
from the parameters and, when it reaches `2⁵³`, withholds the certificate (it can only refuse:
the verdict CERTIFIED still comes only from `certifyBFV?` and `decryptLibExtOK?`). An output with
fewer limbs (after `Compress`) is decrypted by another binary64 routine (`MultiplyAndRound`,
`bfvrns-pke.cpp:254-275`), which this guard does not cover and which `libDecryptStatus` decides with `decLowOK?`; BEHZ decrypts
with another routine (`ScaleAndRound(…, tgamma, …)`), decided there with
`behzParamsOK?` and `decBEHZOK?`; a power-of-two `t` takes an integer-only path here
(`dcrtpoly-impl.h:1241-1347`). -/

/-- OpenFHE's `GetMSB`: the bit length (`0` for `0`). -/
def msb (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- The library's `ScaleAndRound(t)` at `k` limbs (`qs`, the full chain) for a `t` that is not a
power of two: the branch it takes and a worst-case bound on the magnitude of the binary64 value
`floatSum + intSum` it rounds (`dcrtpoly-impl.h:1348-1480`; `qMSB` the largest bit length of the
`qᵢ`, `sizeQMSB = GetMSB(k)`, `h = qMSB >> 1`):

* `qMSB + sizeQMSB < 52`, `qMSB + tMSB + sizeQMSB < 52` (no reduction): `k·(t−1)·2^qMSB + k·2^qMSB`;
* `qMSB + sizeQMSB < 52`, otherwise (`ModMulFastConst` per term): `k·(t−1) + k·2^qMSB`;
* `qMSB + sizeQMSB ≥ 52` (lo/hi split at `2^h`), `h + tMSB + sizeQMSB < 52`:
  `k·(2^h + 2^(qMSB−h))·(t−1) + k·(2^h + 2^(qMSB−h))`;
* otherwise (split, `ModMulFastConstEq` per half, `:1452-1477`): `2k·(t−1) + k·(2^h + 2^(qMSB−h))`.

`none` for a power-of-two `t` (integer-only path). -/
def libDecryptBound (t : Nat) (qs : List Nat) : Option (String × Nat) :=
  if t ≤ 1 || t &&& (t - 1) == 0 then none else
  let k := qs.length
  let qMSB := (qs.map msb).foldl max 0
  let tMSB := msb t
  let sQ := msb k
  let h := qMSB / 2
  let halves := 2 ^ h + 2 ^ (qMSB - h)
  if qMSB + sQ < 52 then
    if qMSB + tMSB + sQ < 52 then
      some ("non-power-of-two t, qMSB + sizeQMSB < 52 and qMSB + tMSB + sizeQMSB < 52 (no lo/hi split, no intermediate reduction)", k * (t - 1) * 2 ^ qMSB + k * 2 ^ qMSB)
    else
      some ("non-power-of-two t, qMSB + sizeQMSB < 52 (no lo/hi split, one ModMulFastConst per limb)", k * (t - 1) + k * 2 ^ qMSB)
  else if h + tMSB + sQ < 52 then
    some ("non-power-of-two t, qMSB + sizeQMSB >= 52 and qMSBHf + tMSB + sizeQMSB < 52 (lo/hi split, no intermediate reduction)", k * halves * (t - 1) + k * halves)
  else
    some ("non-power-of-two t, qMSB + sizeQMSB >= 52 and qMSBHf + tMSB + sizeQMSB >= 52 (lo/hi split, ModMulFastConstEq per half, dcrtpoly-impl.h:1452-1477: intSum <= 2k(t-1) is added to the double floatSum)", 2 * k * (t - 1) + k * halves)

/-- The guard: `some (refusal, note)`. `refusal`: why the library's decryption of a full-limb
output is not covered (the magnitude reaches `2⁵³`); `note`: the condition holds with less than one
bit to spare. Applies to the HPS family only, and only if some output has every limb. -/
def libDecryptGuard (inp : Input) (outs : List (String × Nat)) : Option String × Option String :=
  let P := inp.base.P
  let L := P.src.qs.length
  let hps := match inp.mul.map (·.technique) with
    | some .hps | some .hpsPOverQ | some .hpsPOverQLeveled => true
    | _ => false
  let full := outs.filter (·.2 == L)
  if !hps || full.isEmpty then (none, none) else
  match libDecryptBound P.src.t P.src.qs with
  | none => (none, none)
  | some (branch, S) =>
    let spare := 53.0 - log2F S
    let what := s!"OpenFHE's decryption of the full-limb output(s) {full.map (·.1)} under {((inp.mul.map (·.technique.name)).getD "")} (PKEBFVRNS::Decrypt -> DCRTPolyImpl::ScaleAndRound(t), bfvrns-pke.cpp:238-248) takes the branch {branch}; at t = {P.src.t} and {L} limbs of at most {(P.src.qs.map msb).foldl max 0} bits the binary64 value it rounds can reach {pow2 S}"
    if S ≥ 2 ^ 53 then
      (some s!"{what}, at or above 2^53: outside the precision condition (below 2^53) under which this check covers the library's floating-point decryption. The certificate (Challenge.CertifyBFV.certifyBFV?_sound) is about textbook decryption (Spec.Scheme.bfvDecrypt), and no proved statement ties it to the library's decryption of this output here, so it is withheld. A smaller plaintext modulus (below about 2^53/(2k) at k limbs), fewer limbs, or decrypting after Compress avoids this.", none)
    else if spare < 1.0 then
      (none, some s!"{what}, {fmt2 spare} bit(s) below 2^53: within the precision condition of the library's floating-point decryption, with less than one bit to spare (an untrusted check of the library, not part of the certificate).")
    else (none, none)

/-! ### The library's own decryption: proved where the locked `decryptLibExtOK?` holds

`Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt`: if `certifyBFV? x = some c` and the locked
`Challenge.BFVDecryptLib.decryptLibExtOK? x c` holds, then for every arithmetic conforming to
`Spec.DecryptBFV.ConformsD` every output's LIBRARY decryption (`Spec.DecryptBFVLib.bfvDecryptOpenFHE`,
the dispatch of `PKEBFVRNS::Decrypt`) is its message (mod `t`). The check covers the three routines,
each output at its own level `ℓ` with its own bound:

* `ℓ = L`, HPS family: the binary64 `ScaleAndRound(t)`, `decParamsOK?` and the margin `decLibOK?`
  (`Spec/DecryptBFV.lean`);
* `ℓ = L`, BEHZ: the integer `ScaleAndRound(…, tgamma, …)`, `behzParamsOK?` (`t < 2³⁷`)
  and the margin `decBEHZOK?` (`Spec/DecryptBFVBEHZ.lean`);
* `ℓ < L` (after `Compress`), every technique: the drops and the binary64 `MultiplyAndRound`,
  `decLowParamsOK?` and the margin `decLowOK?` (`Spec/DecryptBFVLow.lean`; implies `t < 2⁵¹`); under
  BEHZ only at `ℓ = 1` (its drop table is empty).

The proved statement about the library's decryption covers an output only within its routine's
parameters and margin, which are narrower than the textbook decryption condition (for BEHZ
`t < 2³⁷`; after `Compress`, `t < 2⁵¹`), so an output outside them withholds the certificate
(NOT CERTIFIED). An output whose routine has no proved statement at all (BEHZ with `2 ≤ ℓ < L`; no
declared library technique) withholds it too (UNSUPPORTED). -/

/-- A rational as a decimal (diagnostic printing). -/
def ratF (q : ℚ) : String := toString (Float.ofInt q.num / Float.ofNat q.den)

inductive LibDec
  /-- `decryptLibExtOK?` holds: the library's decryption of every output is proved (`how`: the
  routine of each output). -/
  | proved (how : String)
  /-- The certificate is withheld (why). -/
  | refused (why : String)
  /-- The library's decryption of some output is by a routine that is not proved (why): the
  certificate is withheld (UNSUPPORTED). -/
  | unsupported (why : String)

/-- The routine OpenFHE v1.6.1 runs on an output at level `ℓ` of `L` (`Spec.DecryptBFVLib`). -/
def libRoutine (behz : Bool) (L ℓ : Nat) : String :=
  if ℓ == L then
    if behz then "BEHZ ScaleAndRound(moduliQ, t, tgamma, ...) (integer, dcrtpoly-impl.h:1651-1696; Spec/DecryptBFVBEHZ.lean)"
    else "ScaleAndRound(t) (binary64 sums, dcrtpoly-impl.h:1220-1480; Spec/DecryptBFV.lean)"
  else "DropLastElementAndScale and NativeIntegerT::MultiplyAndRound (binary64, bfvrns-pke.cpp:254-275; Spec/DecryptBFVLow.lean)"

def libDecryptStatus (inp : Input) (x : Spec.CertifyBFV.InputBFV)
    (c : Spec.CertifyBFV.CertificateBFV) (outs : List (String × Nat)) : LibDec :=
  let P := inp.base.P
  let t := P.src.t
  let qs := P.src.qs
  let L := qs.length
  let withheld := "so the certificate, which is about textbook decryption, is withheld (fhe_check certifies an OpenFHE program only when the library's own decryption of every output is proved: the locked Challenge.BFVDecryptLib.decryptLibExtOK?)"
  match Challenge.BFVDecryptLib.techLib? x.mul with
  | none => .unsupported s!"no library multiplication technique is declared, so no library decryption routine is identified and none is proved; {withheld}"
  | some behz =>
    -- THE DECISION: the locked check, computed by `FHE.Holes.decryptLibExtFast` (equal to it:
    -- `Challenge.Fast.decryptLibExtFast_eq`); everything else only explains a refusal
    let how := "; ".intercalate (outs.map fun (o, ℓ) => s!"{o} (level {ℓ}): {libRoutine behz L ℓ}")
    if FHE.Holes.decryptLibExtFast x c then .proved how else
    let bnd (o : String) : Option Nat := c.outputs.lookup o
    -- per output: (refused?, why)
    let per : List (Bool × String) := outs.filterMap fun (o, ℓ) =>
      match bnd o with
      | none => some (false, s!"the output {o} has no bound in the certificate")
      | some b =>
        if ℓ == L then
          if behz then
            if !Spec.DecryptBFVBEHZ.behzParamsOK? t qs then
              some (true, s!"the output {o} (all {L} limbs) is decrypted by BEHZ's integer ScaleAndRound, and the parameters are outside its proved side condition Spec.DecryptBFVBEHZ.behzParamsOK? (t*2^26 < 2^63, i.e. t < 2^37; 1..* odd pairwise coprime moduli below 2^60, coprime to t){if t ≥ 2 ^ 37 then s!"; here t = {t} is outside the proved condition t < 2^37" else ""}")
            else if !Spec.DecryptBFVBEHZ.decBEHZOK? t qs b then
              some (true, s!"the bound of the output {o} (all {L} limbs) is outside the proved margin of BEHZ's integer decryption, Spec.DecryptBFVBEHZ.decBEHZOK? (2*2^26*V + 2*L*Q < 2^26*Q: the dropped fractions cost L/2^26 of the rounding interval)")
            else none
          else
            if !Spec.DecryptBFV.decParamsOK? t qs then
              some (true, s!"the output {o} (all {L} limbs) is decrypted by the binary64 ScaleAndRound(t), and the parameters are outside its proved side condition Spec.DecryptBFV.decParamsOK? (2 <= t < 2^50, 1..128 odd pairwise coprime moduli below 2^60)")
            else if !Spec.DecryptBFV.decLibOK? t qs b then
              some (true, s!"the bound of the output {o} (all {L} limbs) passes the textbook decryption condition (decOK) but not the proved margin of OpenFHE's binary64 decryption, Spec.DecryptBFV.decLibOK? (proved float error delta = {ratF (Spec.DecryptBFV.delta t qs)} in units of the rounding, so about {ratF (1 - 2 * Spec.DecryptBFV.delta t qs)} of the textbook threshold is certified for the library); outside this proved margin the library's decryption is not covered")
            else none
        else
          if !Spec.DecryptBFVLow.decLowParamsOK? t qs ℓ then
            some (true, s!"the output {o} (level {ℓ} < L = {L}) is decrypted by DropLastElementAndScale and the binary64 MultiplyAndRound, and the parameters are outside its proved side condition Spec.DecryptBFVLow.decLowParamsOK? (2 <= t, 2t < q0, odd pairwise coprime moduli below 2^60)")
          else if !Spec.DecryptBFVLow.decLowOK? t qs ℓ b then
            some (true, s!"the bound of the output {o} (level {ℓ} < L = {L}) is outside the proved margin of OpenFHE's low-limb decryption (DropLastElementAndScale, then the binary64 MultiplyAndRound of t*x/q0), Spec.DecryptBFVLow.decLowOK? (2*V0 + 2*q0*u*(7t/2 + 1) < q0, V0 the noise after the drops; it implies t < 2^51); library decryption of outputs below the top level is proved only within decLowOK?, and this output is outside that margin")
          else if behz && ℓ != 1 then
            some (false, s!"the output {o} has {ℓ} limbs, 1 < {ℓ} < L = {L}, under BEHZ: OpenFHE's low-limb decryption reads the table m_qlInvModq, which is empty under BEHZ (bfvrns-cryptoparameters.cpp:128-655), and no statement about the library's decryption is proved there")
          else none
    let whys := per.map (·.2)
    if per.any (·.1) || per.isEmpty then
      .refused s!"{if whys.isEmpty then "Challenge.BFVDecryptLib.decryptLibExtOK? = false" else "; ".intercalate whys}; {withheld}"
    else .unsupported s!"{"; ".intercalate whys}; {withheld}"

/-! ### The result of a check -/

structure OutputInfo where
  name : Var
  level : Nat
  /-- `refAnalyzeBFVAt` on the program with this output alone. -/
  bound : Nat
  Q : Nat
  /-- The Galois element of the key the output is under (`Spec.Encrypt.outputKey?`). -/
  key : Option Nat := none
  /-- The largest noise `decOK` accepts at this level (diagnostic, `maxNoise`). -/
  maxB : Option Nat := none

structure Failure where
  what : String
  step : Option StepInfo := none
  /-- Whether `refAnalyzeBFVAt` on the prefixes confirmed the location. -/
  confirmed : Bool := false
  /-- A noise overflow (as opposed to an ill-formed input). -/
  overflow : Bool := false

structure Result where
  verdict : Verdict
  headline : String
  input : Option Input := none
  schemeOK : Option Bool := none
  specialOK : Option Bool := none
  budget : Option BudgetReport := none
  /-- The value `refAnalyzeBFVAt` returned (max over outputs). -/
  analyzed : Option Nat := none
  outputs : List OutputInfo := []
  failure : Option Failure := none
  steps : Array StepInfo := #[]
  warnings : List String := []
  notes : List String := []
  suggestions : List String := []
  /-- Informational: `refAnalyzeBFVAt` with the textbook budgets (`Etextbook`), when the
  technique's budgets differ from them. -/
  textbookBound : Option Nat := none
  /-- The certificate of `Challenge.CertifyBFV.certifyBFV?` (only with `verdict = .certified`). -/
  cert : Option Spec.CertifyBFV.CertificateBFV := none
  /-- The fresh-encryption mode, if the file declares fresh encryptions. -/
  fresh : Option FreshRun := none
  /-- The library's own decryption (`libDecryptStatus`). -/
  libDec : Option LibDec := none

/-- The verdict as printed: a CERTIFIED verdict whose certificate records assumptions carries
them (`qualifier`). -/
def Result.label (r : Result) : String :=
  match r.verdict, r.cert with
  | .certified, some c =>
    let tn := ((r.input.bind (·.mul)).map (·.technique.name)).getD "textbook"
    let d := declaredStr (r.input.bind (·.mul))
    match qualifier tn c.assumed with
    | some q => s!"CERTIFIED ({q}; {d})"
    | none => s!"CERTIFIED ({d})"
  | .notCertified, some c =>
    -- the certificate of an IDEALISED algorithm (`isIdealised`): never headed CERTIFIED, because
    -- `certifyBFV?_library_run` (which excludes `idealised`) does not apply to it
    let tn := ((r.input.bind (·.mul)).map (·.technique.name)).getD "textbook"
    let d := declaredStr (r.input.bind (·.mul))
    let idealTxt := "the file declares the exact algorithm, NOT the library's binary64 one"
    let pre := "NOT CERTIFIED FOR THE LIBRARY (idealised algorithm certified)"
    match qualifier tn c.assumed with
    | some q => s!"{pre} ({idealTxt}; {q}; {d})"
    | none => s!"{pre} ({idealTxt}; {d})"
  | v, _ => v.label

/-- The verdict whose meaning text is printed: a certificate withheld for the library (idealised
algorithm) still has the meaning of the certificate of the algorithm. -/
def Result.meaningVerdict (r : Result) : Verdict :=
  match r.verdict, r.cert with
  | .notCertified, some _ => .certified
  | v, _ => v

/-- Whether the program body `body[0..k)` passes the reference run (the reference analyzer on
that prefix with no outputs: every step well formed and every bound acceptable). -/
def prefixOK (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) (k : Nat) : Bool :=
  (analyzer P E { prog with body := prog.body.take k, outputs := [] }).isSome

/-! ### The acceptance test (verified functions only) -/

/-- The computed hypotheses of `Challenge.BFVMul.certifiedAt_decrypts` other than the parameter
check: `refAnalyzeBFVAt` returns a bound (for the program, and for each output alone, which is
what the report prints), and every output is under the secret key itself. -/
def accepts (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) : Bool :=
  (analyzer P E prog).isSome &&
  (prog.outputs.all fun o => (analyzer P E { prog with outputs := [o] }).isSome) &&
  Encrypt.outputsUnderS? P.src prog

/-- "Smallest fix" suggestion for a noise overflow: the smallest uniform growth of the moduli at
which the verified analyzer accepts, with the multiplication numbers of every instruction kept
and its key-switching and plaintext-addition numbers recomputed at the grown moduli. A search,
not a theorem. -/
def suggest (inp : Input) (br : BudgetReport) : List String := Id.run do
  let prog := inp.base.prog
  if prog.body.length > 3000 then
    return ["(no suggestions computed: the program has more than 3000 instructions)"]
  if br.ksLeveled then
    return ["(no suggestions computed: a key switch of this program is charged Spec.BudgetBFV.ksLeveled for an internal drop, which is not a function of the level alone)"]
  let P := inp.base.P
  let grows := fun (k : Nat) =>
    let Pk := growParams P k
    -- no technique: `ksBoundAt` at every key switch, the declared plaintext-addition number
    let bk := (FHE.Noise.FastBFV.budgets { br.x with P := Pk, mul := none }).toArray
    let E := fun (n : Nat) =>
      let b := Challenge.CertifyBFV.budgetFn bk n
      BudgetBFV.budgetOf b.keySwitch b.modSwitch (br.E n).mulLift (br.E n).mulRound b.plainAdd
    accepts Pk E prog
  match leastTrue grows 1 64 with
  | some k =>
    return [s!"larger moduli: with every ciphertext and special modulus {k} bit(s) larger (hypothetical chain: each modulus multiplied by 2^{k}; same number of limbs, same digits, same program, same multiplication numbers at every instruction: largest mulLift = {br.Emax.mulLift}, mulRound = {br.Emax.mulRound}) the analyzer accepts; {k} is the smallest such increase found by bisection over 1..64. The hypothetical moduli are not primes, and the slacks and side condition of the multiplication technique were NOT re-evaluated (a larger Q needs a larger auxiliary basis): regenerate the parameters with the library and re-run fhe_check on them."]
  | none =>
    return ["larger moduli: no uniform increase of 1..64 bits of every ciphertext and special modulus makes the analyzer accept this program."]

/-- **The pipeline.** -/
def runCheck (inp : Input) (opts : FHE.Check.Options := {}) : Result := Id.run do
  let base : Result := { verdict := .notCertified, headline := "", input := some inp }
  -- the fresh-encryption mode: the input noise is computed from the key and sampler bounds
  let fr ← match freshSetup inp opts with
    | .ok f => pure f
    | .error m => return { base with verdict := .unsupported, headline := m }
  let inp := match fr with
    | some f => { inp with base := { inp.base with P := { inp.base.P with inputNoise := f.inputNoise } } }
    | none => inp
  let base : Result := { base with input := some inp, fresh := fr }
  let mut warnings : List String := []
  if let some f := fr then
    if let some κ := f.kappa then
      if κ < FHE.Check.kappaFloor then
        warnings := warnings ++ [s!"--kappa {κ} IS BELOW {FHE.Check.kappaFloor}: a failure probability of up to 2^-{κ} per execution is NOT negligible. A CERTIFIED verdict at this K is a weak statement; do not read it as \"decrypts correctly\"."]
    -- `Spec.EncryptBFV.freshOKBFV?`, with trees (`Validation.FastBFV.freshOKBFV_eq`)
    if !FHE.Noise.FastBFV.freshOKBFV inp.base.prog f.model.inputs then
      return { base with warnings := warnings, headline := "the inputs do not have the shape the fresh-encryption certificate needs",
                         failure := some { what := s!"Spec.EncryptBFV.freshOKBFV? = false for the fresh inputs {f.model.inputs}: every fresh input must be a declared two-component ciphertext under the secret key (key 1) with no bound of its own, at least one must be listed, and every other input must be a one-component plaintext" } }
  let base : Result := { base with warnings := warnings }
  let P := inp.base.P
  let prog := inp.base.prog
  -- THE DECISION (used below, after the diagnostic checks): the locked `certifyBFV?` /
  -- `certifyBFVFresh?`, computed by the proved-equal fast functions. It reads only the decoded
  -- input and its key-switching layout, so it is started here, in a task of its own, and runs
  -- while the budget and the report's diagnostic replays are computed (parallelism only: the
  -- value is the one the sequential call `decideOn br.x` returns, since `br.x` is
  -- `inputBFV inp lay` for this same `lay`, `computeBudget`).
  let decideOn := fun (x : Spec.CertifyBFV.InputBFV) => match fr with
    | none => FHE.Holes.certifyBFVFast x
    | some f =>
      -- the fresh-encryption certificate; the figures above must be its own
      (FHE.Holes.certifyBFVFreshFast x f.mode).bind fun fc =>
        if fc.params.inputNoise == f.inputNoise && fc.eps == f.eps && fc.used == f.used &&
            fc.drift == f.drift then some fc.cert else none
  let decidedT : Option (Task (Option Spec.CertifyBFV.CertificateBFV)) :=
    match FHE.Check.layoutOf P inp.base.ks with
    | .ok lay => some (Task.spawn fun _ => decideOn (inputBFV inp lay))
    | .error _ => none
  -- what the declared bounds and the input noise mean for this file
  let bm := FHE.Noise.Fast.boundMap prog   -- `prog.boundOf`, in a tree
  let ib := FHE.Noise.FastBFV.inputBound P bm   -- `TraceBFV.inputBound P prog`
  -- (one note per input declared above its default; collected with `filterMap`, since appending
  -- to the end of the list for each of them is quadratic in their number)
  let notes : List String := prog.inputs.filterMap fun d =>
    match bm[d.name]? with
    | none => none
    | some b =>
      let dflt := if d.parts = 1 then P.src.t - 1 else P.inputNoise
      if b > dflt then
        some s!"input {d.name} declares the bound {b}, ABOVE the default {dflt} ({if d.parts = 1 then "t - 1 for a plaintext" else "inputNoise for a ciphertext"}). For BFV the declared bound replaces the default whether smaller or larger (Spec.TraceBFV.inputBound): the analysis starts {d.name} at {b}, and the certificate assumes only that {d.name} is within {b}."
      else none
  let base : Result := { base with notes }
  -- 1. parameters (verified: `schemeParamsOK?`, `specialOK?`)
  if !schemeParamsOK? P then
    return { base with schemeOK := some false, headline := "the parameters are rejected",
                       failure := some { what := s!"Spec.schemeParamsOK? = false. First failing clause (diagnostic): {paramsClause P chainName}" } }
  if !Budget.specialOK? P then
    return { base with schemeOK := some true, specialOK := some false,
                       headline := "the special (key-switching) primes are rejected",
                       failure := some { what := s!"Spec.Budget.specialOK? = false: {specialClause P}" } }
  let base := { base with schemeOK := some true, specialOK := some true }
  -- 1. OpenFHE's word arithmetic is exact on these moduli (`Challenge.Word.ksWordOK?`)
  if let some why := openfheWordRefusal? inp.base.sourceTool P then
    return { base with verdict := .unsupported,
                       headline := "OpenFHE's 64-bit word arithmetic is not shown to be exact on these moduli",
                       failure := some { what := why } }
  -- 1a. OpenFHE's packed encoder keeps a stored coefficient the same integer in every limb only
  -- if t - 1 <= floor(q0/2) and t <= q_i (checked by certifyBFV?, item 5a)
  let q0 := P.src.qs.headD 0
  if !(decide (P.src.t - 1 ≤ q0 / 2) && P.src.qs.all fun q => decide (P.src.t ≤ q)) then
    return { base with
      headline := "the plaintext modulus is outside the condition t - 1 <= floor(q0/2) and t <= every ciphertext prime, under which the input contract describes the packed plaintexts of an OpenFHE file",
      failure := some { what := s!"Challenge.CertifyBFV.checksOK requires t - 1 <= floor(q0/2) and t <= q_i for every limb (certifyBFV?_encodeOK); here t = {P.src.t}, q0 = {q0}, floor(q0/2) = {q0 / 2}: the plaintext modulus is outside the packed-encoding window t - 1 <= floor(q0/2) (and t <= every limb) under which the packed-encoding model of the input contract holds. Use larger ciphertext primes (SetScalingModSize) or a smaller t." } }
  -- 1b. every input ciphertext's own bound decrypts at its level (locked `decOK`). The input
  -- hypothesis of the certificate (`TraceBFV.InputsOK`, through `BFVEncrypts`) says that each
  -- input ciphertext has noise within its bound AND decrypts to its message; with this check
  -- the noise bound alone gives both (`Challenge.BFV.bfv_decrypt_of_noise`), so the assumption
  -- the report prints is only the noise bound. Without it a program could be "certified" from
  -- an input assumption that no noise bound justifies.
  if let some d := prog.inputs.find? fun d =>
      d.parts ≠ 1 && d.ok P.src &&
        !decOK P.src.t (P.src.modulus d.level) (ib d) then
    let b := ib d
    let Q := P.src.modulus d.level
    return { base with
      headline := s!"the noise bound of input {d.name} is above what decrypts at its level",
      failure := some { what := s!"input {d.name} (level {d.level}): its noise bound {b} ({pow2 b}) does not satisfy the decryption condition 2*(t*B + (Q mod t)*(t-1)) < Q (Challenge.BFV.decOK); the largest bound that does is {match maxNoise P.src.t Q with | some m => s!"{m} ({pow2 m})" | none => "none"}. A certificate needs every input ciphertext to decrypt to its message, and at this bound the noise assumption does not give that." } }
  -- 2. budget
  let br ← match computeBudget inp with
    | .ok b => pure b
    | .error (.invalid m) => return { base with verdict := .invalid, headline := m }
    | .error (.unsupported m) => return { base with verdict := .unsupported, headline := m }
  let base := { base with budget := some br }
  -- 2a. the declared key-switching layout is OpenFHE's (checked by certifyBFV?, item 5b)
  if !Challenge.RealizeBFV.ksDeclOK? P br.layout then
    return { base with
      headline := "the declared key-switching layout is not the one OpenFHE uses, so the transcribed key switch and its budget do not apply",
      failure := some { what := s!"Challenge.RealizeBFV.ksDeclOK? = false (checked by Challenge.CertifyBFV.certifyBFV?): with special primes (HYBRID) OpenFHE uses canonical representatives (keySwitching.variant \"openfhe\"); without (BV, digit size 0) one limb per digit at every level. Declared: {P.store.special.length} special prime(s), {if br.layout.canonical then "canonical" else "centred"} representatives." } }
  let E := br.E
  -- the diagnostic replay, the run of the analysis, and (informational) the analysis at the
  -- textbook budgets are independent of each other: computed in parallel tasks
  let stepsT := Task.spawn fun _ => replay P E prog
  let sameB := fun (a b : TraceBFV.Budget) =>
    a.keySwitch == b.keySwitch && a.modSwitch == b.modSwitch && a.mulLift == b.mulLift &&
      a.mulRound == b.mulRound && a.plainAdd == b.plainAdd
  let tbT := Task.spawn fun _ =>
    if br.rows.all (fun row => sameB row.E (br.Etextbook row.idx)) then none
    else analyzer P br.Etextbook prog
  -- Per output, from the final environments of one run of the body
  -- (`FHE.Noise.FastBFV.run`, `outBound`): the value of `refAnalyzeBFVAt` on the one-output
  -- program (`Validation.FastBFV.Aux.refAnalyzeBFV_eq`), and the level and key
  -- `Decrypt.outputLevel?` and `Encrypt.outputKey?` compute.
  let r? := FHE.Noise.FastBFV.run P E prog
  let steps := stepsT.get
  let base := { base with steps }
  -- 3. the verified analyzer: `analyzer P E prog` is, by its definition (`FHE.Noise.FastBFV.analyze`),
  -- `outBound` of this run on the outputs; read from the run instead of running the body again
  match r?.bind fun r => FHE.Noise.FastBFV.outBound r prog.outputs with
  | some B =>
    let valOf := fun (o : Var) => r?.bind fun r => r.1[o]?
    let outs := prog.outputs.filterMap fun o =>
      (r?.bind fun r => FHE.Noise.FastBFV.outBound r [o]).map fun b =>
        let lvl := ((valOf o).map (·.level)).getD 0
        let Q := P.src.modulus lvl
        ({ name := o, level := lvl, bound := b, Q, key := (valOf o).map (·.key),
           maxB := maxNoise P.src.t Q } : OutputInfo)
    -- frontend cross-check (never trusted; a disagreement withholds the certificate)
    let mism := inp.base.expects.filterMap fun e =>
      match steps[e.idx]? with
      | some s =>
        if (e.level.isSome && e.level != some s.level) || (e.parts.isSome && e.parts != some s.parts) then
          some s!"body[{e.idx}] ({e.dst}): the frontend says level {e.level.getD 0}, parts {e.parts.getD 0}; Source.step gives level {s.level}, parts {s.parts}"
        else none
      | none => none
    if !mism.isEmpty then
      return { base with analyzed := some B,
                         headline := "the frontend and the verified semantics disagree on the program's shape, so the certificate is withheld",
                         failure := some { what := String.intercalate "\n" mism } }
    -- 4. every output under the secret key itself (verified: `outputsUnderS?`)
    if let some o := prog.outputs.find? fun o => (valOf o).map (·.key) != some 1 then
      let kd := match (valOf o).map (·.key) with
        | some g => toString g
        | none => "?"
      return { base with
        analyzed := some B, outputs := outs,
        headline := s!"output {o} is left under the rotated key sigma_{kd}(s) (Galois element {kd}), not under the secret key s: the noise bound holds, but decryption with s does not return its message",
        failure := some { what := s!"Spec.Encrypt.outputsUnderS? = false: output {o} is recorded under the Galois element {kd} (Spec.Encrypt.outputKey?). The noise theorem speaks of decryption under sigma_{kd}(s); a library decrypts with s. Key-switch {o} back to s (keySwitch after the automorphism) before it is output, or declare the input under key 1." } }
    -- THE VERDICT: the locked `Challenge.CertifyBFV.certifyBFV?` on the decoded data
    -- (computed by `FHE.Holes.certifyBFVFast`, `certifyBFVFreshFast`, equal to them on every
    -- input: `Challenge.Fast.certifyBFVFast_eq`, `certifyBFVFreshFast_eq`)
    let decided := match decidedT with
      | some t => t.get
      | none => decideOn br.x
    let decider := match fr with
      | none => "Challenge.CertifyBFV.certifyBFV?"
      | some _ => "Challenge.BFVEncrypt.certifyBFVFresh?"
    let some c := decided
      | return { base with analyzed := some B, outputs := outs,
                           headline := s!"internal disagreement: the diagnostic checks found no failure, but {decider} refuses (or its error bound differs from this report's); no certificate",
                           failure := some { what := s!"{decider} = none" } }
    -- the figures printed (untrusted budget, per-output bounds) must be the certificate's
    let badRow := br.rows.find? fun row => !sameB (c.budget row.idx) row.E
    unless badRow.isNone && c.bound == B && c.outputs == outs.map fun o => (o.name, o.bound) do
      return { base with analyzed := some B, outputs := outs,
                         headline := "internal disagreement between the figures of this report and the certificate of Challenge.CertifyBFV.certifyBFV?; no certificate",
                         failure := some { what := s!"certifyBFV?: bound {c.bound}{match badRow with | some row => s!", budget of body[{row.idx}] ({(c.budget row.idx).keySwitch}, {(c.budget row.idx).modSwitch}, {(c.budget row.idx).mulLift}, {(c.budget row.idx).mulRound}, {(c.budget row.idx).plainAdd}); this report: ({row.E.keySwitch}, {row.E.modSwitch}, {row.E.mulLift}, {row.E.mulRound}, {row.E.plainAdd})" | none => ""}; this report: bound {B}" } }
    -- guard (untrusted, can only refuse): the library's floating-point decryption
    let (refuse, note) := libDecryptGuard inp (outs.map fun o => (o.name, o.level))
    let base := { base with notes := base.notes ++ note.toList }
    if let some why := refuse then
      return { base with analyzed := some B, outputs := outs,
                         headline := "the library's floating-point decryption of a full-limb output is outside its precision condition (t too large for the number of limbs), so the certificate is withheld",
                         failure := some { what := why } }
    -- the library's own decryption (`Challenge.BFVDecrypt`): proved, refused, or not covered
    let lib := libDecryptStatus inp br.x c (outs.map fun o => (o.name, o.level))
    if let .refused why := lib then
      return { base with analyzed := some B, outputs := outs, libDec := some lib,
                         headline := "the noise bound is certified for textbook decryption, but not for the library's own decryption, so the certificate is withheld",
                         failure := some { what := why } }
    if let .unsupported why := lib then
      return { base with verdict := .unsupported, analyzed := some B, outputs := outs, libDec := some lib,
                         headline := "the noise bound is certified for textbook decryption, but the library's decryption of some output is by a routine with no proved statement, so the certificate is withheld",
                         failure := some { what := why } }
    let tb := tbT.get
    -- an IDEALISED certificate (the budget of the exact algorithm, which the library does not run;
    -- the file's own `$.source.idealised` flag counts too) is not a certificate for the library:
    -- `certifyBFV?_library_run` excludes `idealised`. Exit status 1 (NOT CERTIFIED), not 0.
    let ideal := c.assumed.contains .idealised || inp.base.idealised
    return { base with verdict := if ideal then .notCertified else .certified,
                       analyzed := some B, outputs := outs, textbookBound := tb,
                       cert := some c, libDec := some lib,
                       headline := match fr with
                         | some { kappa := some κ, .. } => s!"with probability at least 1 - 2^-{κ} over the encryption randomness, every output decrypts correctly, by OpenFHE's own decryption and by textbook decryption, in every run (evaluation in the worst case), under the assumptions below"
                         | some _ => "every output decrypts correctly, by OpenFHE's own decryption and by textbook decryption, in the worst case, with the input noise computed from the key and sampler bounds, under the assumptions below"
                         | none => "every output decrypts correctly, by OpenFHE's own decryption and by textbook decryption, in the worst case, under the assumptions below" }
  | none =>
    -- localise the failure
    if let some d := prog.inputs.find? (fun d => !d.ok P.src) then
      return { base with headline := "the program is ill-formed",
                         failure := some { what := s!"input {d.name} is ill-formed (Source.Decl.ok): parts {d.parts}, level {d.level} (chain has {P.src.qs.length} limbs), key {d.key} (must be odd and < 2N)" } }
    match steps.find? (·.failed) with
    | some s =>
      -- the two prefix runs are independent: in parallel
      let atT := Task.spawn fun _ => prefixOK P E prog (s.idx + 1)
      let beforeT := Task.spawn fun _ => prefixOK P E prog s.idx
      let confirmed := !atT.get && beforeT.get
      match s.ill with
      | some why =>
        return { base with headline := s!"the program is ill-formed at body[{s.idx}]",
                           failure := some { what := why, step := some s, confirmed } }
      | none =>
        let r : Result := { base with
          headline := s!"the worst-case noise bound overflows at body[{s.idx}]",
          failure := some { what := "noise overflow", step := some s, confirmed, overflow := true } }
        return if opts.suggest then { r with suggestions := suggest inp br } else r
    | none =>
      let β := fun (o : Var) => match steps.toList.reverse.find? (fun s => Trace.dst s.instr = o) with
        | some s => some s.bnd
        | none => initBounds P prog o
      let missing := prog.outputs.filter fun o => (β o).isNone
      let plain := prog.outputs.filter fun o => match β o with
        | some (.pt _) => true
        | _ => false
      return { base with headline := "the program is ill-formed",
                         failure := some { what :=
                           if !missing.isEmpty then s!"output(s) never defined: {missing}"
                           else if !plain.isEmpty then s!"output(s) {plain} are plaintexts (one-component values), not ciphertexts: there is nothing to decrypt"
                           else "Challenge.BFV.refAnalyzeBFVAt rejects the program (no failing clause found by the diagnostic replay)" } }

/-- Decode and check a BFV document (`isBFV`). -/
def check (j : Json) (opts : FHE.Check.Options := {}) : Result :=
  match decode j with
  | .error e => { verdict := .invalid, headline := e }
  | .ok (.unsupported what idx why) =>
    { verdict := .unsupported,
      headline := s!"{what}{match idx with | some i => s!" (body[{i}])" | none => ""}: {why}" }
  | .ok (.ok inp) =>
    -- the instruction limit: the same resource guard as for BGV, before any analysis
    if opts.maxInstr != 0 && inp.base.prog.body.length > opts.maxInstr then
      { verdict := .unsupported,
        headline := FHE.Check.tooLargeHeadline inp.base.prog.body.length opts.maxInstr }
    else runCheck inp opts

/-! ### The fixed statement of what a certificate means -/

/-- The locked statements a report cites: the certificate, what it is proved from, and the pins
that the contracts are achievable within the printed budgets. -/
def theoremsCited (inp : Input) (br : Option BudgetReport)
    (cert : Option Spec.CertifyBFV.CertificateBFV) (fr : Option FreshRun := none) :
    List (String × String) :=
  let leveled := (inp.mul.map (·.technique)) == some Technique.hpsPOverQLeveled
  let hasKs := (br.map fun b => !b.usedKsLevels.isEmpty).getD false
  let ksDrop := (br.map fun b => FHE.Noise.FastBFV.ksDroppedGo b.x.prog.body b.x.drops).getD false
  (match fr with
   | some f => [
     (freshTheorem f, match f.kappa with
       | none => "THE CERTIFICATE (fresh encryptions, worst case): if Challenge.BFVEncrypt.certifyBFVFresh? accepts in the mode worst, then for every secret within secretBound, every public key for it with error <= keyError (noise scale 1), all encryption randomness within the support bounds and all messages, every output of every run within the certificate's budget is under s, decrypts WITH s to the message the program computes, and has noise at most its own bound; the input noise is computed (Spec.EncryptBFV.freshInputNoise), not declared"
       | some _ => "THE CERTIFICATE (fresh encryptions, probabilistic): if Challenge.BFVEncrypt.certifyBFVFresh? accepts in this mode, then for every secret and public key within the stated bounds, on any probability space carrying for each fresh input randomness meeting the sampler hypothesis, the probability that there exist messages for which some output of some run fails (not under s, wrong decryption, or noise above its own bound) is at most 2^-K, per execution (a union bound over n*2N events)"),
     ("Challenge.BFVEncrypt.certifyBFVFresh?_spec", "certifyBFVFresh? is certifyBFV? at the declared parameters with the input noise replaced by Spec.EncryptBFV.freshInputNoise (the declared inputNoise is not used), after Spec.EncryptBFV.freshOKBFV?"),
     ("Challenge.BFVEncrypt.encryptBFV_encrypts", "a fresh OpenFHE BFV encryption (Spec.EncryptBFV.encryptBFV: (b*u + e1 + ceil(Q*p/t), a*u + e2)) of m, stored as its [0,t) lift, BFVEncrypts m with noise eps + encodeDev when its error e*u + e1 + e2*s is at most eps and that bound passes decOK"),
     ("Challenge.BFVEncrypt.scaleUpCeil_timesQovert", "ceil(Q*p/t) is, limb by limb, what DCRTPoly::TimesQovert computes (dcrtpoly-impl.h:918-935)")]
   | none => []) ++
  [("Challenge.Fast.certifyBFVFast_eq",
    "the function fhe_check runs, FHE.Holes.certifyBFVFast, returns exactly what Challenge.CertifyBFV.certifyBFV? returns, on every input"),
   ("Challenge.Fast.certifyBFVFreshFast_eq",
    "the function fhe_check runs in the fresh-encryption modes, FHE.Holes.certifyBFVFreshFast, returns exactly what Challenge.BFVEncrypt.certifyBFVFresh? returns, on every input and mode"),
   ("Challenge.Fast.analyzeBFVFast_eq",
    "the analyzer fhe_check runs, FHE.Holes.analyzeBFVFast, returns exactly what Challenge.BFV.refAnalyzeBFVAt returns, on every input"),
   ("Challenge.CertifyBFV.certifyBFV?_sound",
    "THE CERTIFICATE: if Challenge.CertifyBFV.certifyBFV? returns a certificate c for the decoded data (parameters, layout, program, declared multiplication technique and auxiliary basis, floatTolerant, plaintext-addition and modulus-switching methods, declared internal drops), then for every secret key s, all messages and all inputs within their bounds (Spec.TraceBFV.InputsOK), every output of every run in which instruction k meets its Spec.TraceBFV contract within c.budget k (Spec.TraceBFV.RunAt) is under s itself, decrypts WITH s at its own level (Spec.Scheme.bfvDecrypt) to the message the program computes, and has noise at most its own bound in c.outputs"),
   ("Challenge.CertifyBFV.certifyBFV?_spec",
    "the fields of the certificate: every check of Challenge.CertifyBFV.checksOK passed, c.budget = Challenge.CertifyBFV.budgetBFV (one budget per instruction, computed from the locked Spec.BudgetBFV definitions), c.bound and the per-output bounds are what refAnalyzeBFVAt returns at those budgets, every output is under the secret key"),
   ("Challenge.CertifyBFV.certifyBFV?_paramsOK", "the checks establish SchemeParamsOK, BFV, SpecialOK, the layout at every level (usable, and restricting from the top level), and that every level at which the program multiplies is a level of the chain"),
   ("Challenge.CertifyBFV.certifyBFV?_inputs", "the bound of every input ciphertext satisfies decOK at its level"),
   ("Challenge.CertifyBFV.certifyBFV?_budget", "the budget of every instruction covers the textbook pins of every operation but the multiplication, at the operand's own level: modulus switching = msBudget, multiplication numbers >= the textbook ones, at a relin or keySwitch the key-switching number >= ksBoundAt at the operand's level, at an addPlain or subPlain the number of the declared plaintext-addition method at the operand's level"),
   ("Challenge.CertifyBFV.certifyBFV?_assumed", "what realizability rests on (c.assumed): binary64 (the platform conforms to the standard model Spec.Float.Conforms, under which the library's floating-point steps are proved) when floatTol and an HPS-family technique multiplies or a leveled key switch drops limbs; idealised in the same cases with floatTol = false (the budget is then the idealised exact algorithm's, not the library's code); at most one of the two; declaredDrops for HPSPOVERQLEVELED with a multiplication or key switch of a top-level operand; binary64Dec (the library's decryption computes its binary64 steps by an arithmetic conforming to Spec.DecryptBFV.ConformsD, the hypothesis of certifyBFV?_decryptsLibExt) exactly when the declared technique is one of OpenFHE's four")] ++
  (match cert with
   | some c => (realizabilityPins (inp.mul.map (·.technique)) c.assumed (leveled && hasKs) ksDrop).map fun p =>
      (p, if p.endsWith "_drop0" then
            "OpenFHE's key switch of a top-level operand under HPSPOVERQLEVELED with declared internal drop 0 (RelinearizeCore with no limb dropped: its scaling sum is over no limb, so the result is the same in EVERY arithmetic, Challenge.BFVMul.leveledKS_drop_zero) meets the relin/keySwitch contract within the budget of that instruction"
          else if isKsPin p then
            "OpenFHE's key switch of a top-level operand under HPSPOVERQLEVELED (RelinearizeCore: scale down by the dropped limbs with a binary64 sum, key-switch at the reduced level with the top-level keys, scale up), in any arithmetic conforming to Spec.Float.Conforms, meets the relin/keySwitch contract within the budget of that instruction, with its declared internal drop"
          else "the declared technique's limb-level algorithm, applied to the operands of instruction n of the program (Challenge.CertifyBFV.AtInstr), meets the mul/square contract within the budget c.budget n of that instruction")
   | none => []) ++
  [("Challenge.BFVMul.certifiedAt_decrypts",
    "the certificate at any budgets (used by the proof of certifyBFV?_sound): if SchemeParamsOK P, the scheme is BFV, refAnalyzeBFVAt P E prog returns a bound and Spec.Encrypt.outputsUnderS? holds, then for every secret key s, all messages and all inputs within their bounds (Spec.TraceBFV.InputsOK), every output of every run in which instruction k meets its Spec.TraceBFV contract within E k is under s itself and its BFV decryption WITH s at its own level is the message the program computes"),
   ("Challenge.BFV.refAnalyzeBFVAt_sound",
    "the headline with one budget per instruction: under the same hypotheses every output Encrypts the value Source.eval computes with noise at most the bound refAnalyzeBFVAt returned (any budgets E)"),
   ("Challenge.BFV.refAnalyzeBFVAt_const", "at a constant budget refAnalyzeBFVAt is refAnalyzeBFV (Challenge.BFV.refAnalyzeBFV_sound, the single-budget headline)"),
   ("Challenge.BFV.encrypts_bfv_decrypts", "for BFV, a ciphertext that Encrypts a value decrypts to its message exactly, under the key it is recorded under"),
   ("Challenge.BFV.bfv_decrypt_of_noise", "noise B with decOK t Q B decrypts correctly"),
   ("Challenge.Params.schemeParamsOK?_sound", "schemeParamsOK? P = true implies SchemeParamsOK P"),
   ("Challenge.Budget.specialOK?_sound", "specialOK? P = true implies SpecialOK P (special primes)"),
   ("Challenge.FreshNoise.outputKey?_eq", "the key an output is under does not depend on the messages"),
   ("Challenge.BFVMul.stepOK_mul_lifted",
    "every multiplication of two-component operands that multiplies integer representatives with 2*|A_i| <= Q + e and whose result components are within rho/2 of t*T/Q meets the mul contract with mulLift >= mulLiftNormAt P l e, mulRound >= mulRoundApprox P rho, for every secret within secretBound"),
   ("Challenge.BFVMul.stepOK_square_lifted", "the same for square (one lift of the operand)"),
   ("Challenge.BFV.relin_realizable",
    "relinearization by hybrid key switching can be done within Spec.BudgetBFV.ksBoundAt at every level (keys with noise <= keyNoise, SpecialOK, a usable digit layout)"),
   ("Challenge.BFV.keySwitch_realizable", "the same for key switching after an automorphism"),
   ("Challenge.BFVMul.ksCore_realizable", "hybrid key switching at a level below the top one, on the digits of that level, with keys generated once at the top level, stays within ksBoundAt of that level"),
   ("Challenge.BFV.stepOK_modSwitch_textbook",
    "rounding every component of a two-component ciphertext meets the modSwitch contract within msBudget"),
   ("Challenge.BFV.stepOK_add_padded", "componentwise addition meets the add contract"),
   ("Challenge.BFVMul.stepOK_sub_padded", "componentwise subtraction meets the sub contract"),
   ("Challenge.BFV.stepOK_addPlain_textbook", "adding floor(Q/t)*p meets the addPlain contract with deviation 0"),
   ("Challenge.BFVMul.stepOK_subPlain_textbook", "subtracting floor(Q/t)*p meets the subPlain contract with deviation 0"),
   ("Challenge.BFV.stepOK_mulPlain_textbook", "multiplying every component by the plaintext polynomial meets the mulPlain contract"),
   ("Challenge.BFVMul.stepOK_mulConst_textbook", "multiplying every component by the constant meets the mulConst contract"),
   ("Challenge.BFVMul.stepOK_automorph_textbook", "applying X -> X^g to every component meets the automorph contract")] ++
  (if (inp.plainAdd.map (·.method)) == some PlainAddMethod.rounded then
    [("Challenge.BFVMul.stepOK_addPlain_rounded",
      "adding round(Q*p/t) meets the addPlain contract with deviation at most plainAddRoundedAt at the operand's level, for a stored plaintext with |p| <= b"),
     ("Challenge.BFVMul.stepOK_subPlain_rounded", "the same for subPlain")]
   else []) ++
  (match inp.plainAdd.map (·.method) with
   | some (PlainAddMethod.scaled _) =>
    [("Challenge.BFVMul.stepOK_addPlain_scaled",
      "adding any polynomial within one unit of Q*p/t, coefficient by coefficient (rounding up, down or to nearest), meets the addPlain contract with deviation at most plainAddScaledAt at the operand's level, for a stored plaintext with |p| <= b"),
     ("Challenge.BFVMul.stepOK_subPlain_scaled", "the same for subPlain")]
   | _ => []) ++
  (match br.bind (·.mul) with
   | some mb => (mb.pins.filter (fun p => p != "Challenge.BFVMul.stepOK_mul_lifted" && p != "Challenge.BFVMul.stepOK_square_lifted" && p != "Challenge.BFVMul.ksCore_realizable")).map fun p =>
      (p, if leveledKsPins.contains p then "the key switch of HPSPOVERQLEVELED on a top-level operand, with its declared internal drop and the binary64 tolerance of its scaling, meets the relin/keySwitch contract within max(ksBoundAt, ksLeveled)"
          else if mb.proved then (if mb.float then "the declared multiplication technique, with its binary64 sums in any arithmetic conforming to Spec.Float.Conforms, meets the mul/square contract within the printed budget (or bounds the error of those sums)" else "the declared multiplication technique, as the idealised limb-level algorithm, meets the mul/square contract within the printed budget") else "used for the declared multiplication technique")
   | none => [])

/-- What a fresh-encryption mode adds to the meaning of a verdict. -/
def freshText (P : FullParams) (f : FreshRun) : List String :=
  let fm := f.model
  [ "",
    "INPUT NOISE COMPUTED FROM THE ENCRYPTION, NOT DECLARED:",
    s!"  the inputs {fm.inputs} are fresh OpenFHE BFV public-key encryptions (Spec.EncryptBFV.encryptBFV,",
    "  ENCRYPTION_TECHNIQUE = STANDARD: (b*u + e1 + ceil(Q*p/t), a*u + e2) with b + a*s = e_pk), of their",
    "  messages stored as their [0, t) lift (both OpenFHE encoders store that for BFV). fhe_check evaluated",
    "  the locked Challenge.BFVEncrypt.certifyBFVFresh?, which computes the input noise as",
    s!"  Spec.EncryptBFV.freshInputNoise = eps + max over the fresh inputs' levels of encodeDev = {f.inputNoise} ({pow2 f.inputNoise}),",
    s!"  eps = {f.eps} ({pow2 f.eps}) bounding |e_pk*u + e1 + e2*s|inf ({match f.used with | .freshWorst => "the worst case Spec.Encrypt.worstError of the support bounds: no probability" | .freshKappaL2 => s!"Spec.Encrypt.epsFor of the l2 variance proxy + drift {f.drift}" | _ => s!"Spec.Encrypt.epsFor of the variance proxy + drift {f.drift}, below the worst case {f.worst}"}),",
    "  encodeDev = ceil((Q mod t)*(t-1)/t) the deterministic difference between ceil(Q*p/t) and floor(Q/t)*p;",
    s!"  the frontend's params.inputNoise = {f.supplied} is NOT used. Then it runs Challenge.CertifyBFV.certifyBFV? at",
    s!"  that input noise. The locked statement {freshTheorem f} (Challenge/BFVEncrypt.lean,",
    "  proof in Validation/BFVEncrypt.lean) states:"] ++
  (match f.kappa with
   | none => [
    s!"  for EVERY secret with |s_i| <= {P.secretBound}, every public key for it with error <= keyError = {fm.keyError},",
    s!"  ALL encryption randomness with |u_i| <= {fm.u}, |e1_i| <= {fm.e1}, |e2_i| <= {fm.e2}, and ALL messages, every output of",
    "  every run within the budget E is under s, decrypts WITH s to the message the program computes, and has",
    "  noise at most its own bound. No probability, no assumption on the means of the samplers."]
   | some κ => [
    s!"  for every secret {if f.l2 then "and public key with the l2 bounds below" else s!"with |s_i| <= {P.secretBound} and public key with error <= keyError = {fm.keyError}"}, on any probability space",
    s!"  carrying, for each fresh input, randomness whose {3}N coefficients are independent, {if f.l2 then "sub-Gaussian about their means with the proxies below" else s!"within |u_i| <= {fm.u}, |e1_i| <= {fm.e1}, |e2_i| <= {fm.e2}"} and of mean",
    s!"  at most {fm.meanNum}/{fm.meanDen} in absolute value, the probability that there exist messages for which some output of",
    s!"  some run fails (not under s, wrong decryption, or noise above its own bound) is at most 2^-{κ}.",
    s!"  PER EXECUTION on one set of fresh encryptions: a union bound over {fm.inputs.length}*2N = {fm.inputs.length * (2 * P.src.N)} tail events (2N per",
    "  encryption). Only the fresh-encryption randomness is treated probabilistically; every evaluation step",
    "  is worst case. Against a party who can choose among Q encryptions or executions (re-draw, discard,",
    "  select), raise K by log2(Q). The secret and public key are fixed first (universally quantified), not",
    "  random. That the library's samplers meet the hypothesis (independence, the bounds, the mean bound) is",
    "  an ASSUMPTION (OpenFHE's measured Gaussian: support -27..26, mean -3431/2^64; Spec/Encrypt.lean)."] ++
    (if f.l2 then
      let v := FHE.Check.l2Values P fm
      [s!"  l2 description: |e_pk|_2^2 <= {v.E2}, |s|_2^2 <= {v.S2}, proxies Vu = {v.Vu}, V1 = {v.V1}, V2 = {v.V2} (Challenge.FreshNoiseL2)."]
     else [])) ++
  [ s!"  ASSUMED (supplied by the frontend, {fm.source.take 200}{if fm.source.length > 200 then "..." else ""}): which inputs are fresh",
    "  encryptions and the key and sampler bounds. EXTENDED encryption is not modelled (the OpenFHE frontend",
    "  refuses it)."]

def meaningTextBase (inp : Input) (v : Verdict) (br : Option BudgetReport)
    (cert : Option Spec.CertifyBFV.CertificateBFV) : List String :=
  let P := inp.base.P
  let bounds := inp.base.bounds
  let leveled := (inp.mul.map (·.technique)) == some Technique.hpsPOverQLeveled
  let hasKs := (br.map fun b => !b.usedKsLevels.isEmpty).getD false
  let ksDrop := (br.map fun b => FHE.Noise.FastBFV.ksDroppedGo b.x.prog.body b.x.drops).getD false
  let drop0Lines := [
    "  Key switching: every key switch of a top-level operand has declared internal drop 0, so the",
    "  library's RelinearizeCore scales over no limb and computes the same in every arithmetic:",
    "  Challenge.CertifyBFV.certifyBFV?_leveled_relin_drop0, certifyBFV?_leveled_keySwitch_drop0",
    "  (Challenge.BFVMul.leveledKS_drop_zero) prove that it meets the relin/keySwitch contract within E_k,",
    "  with no hypothesis on the platform."]
  let boundsLine :=
    if bounds.isEmpty then "No input declares a bound of its own."
    else s!"{bounds.length} input(s) declare their own bound ({boundsList bounds}), used INSTEAD of the default; the theorem covers only inputs that meet it."
  let header := match v with
    | .certified =>
      (if inp.base.idealised || (cert.map (·.assumed.contains .idealised)).getD false then [
      "NOT CERTIFIED FOR THE LIBRARY: the certificate below is for the IDEALISED algorithm (floatTolerant = false, or the file",
      "declares it), not the library's binary64 algorithm. The statement that ties a certificate to the library's execution",
      "(Challenge.CertifyBFV.certifyBFV?_library_run) excludes the idealised assumption and does not apply to it.",
      ""] else []) ++ [
      "WHAT \"CERTIFIED\" MEANS",
      "fhe_check computed the value of the locked Lean definition Challenge.CertifyBFV.certifyBFV? on the decoded",
      "data (parameters, key-switching layout, program, the declared multiplication technique with its",
      "auxiliary basis and floatTolerant, the plaintext-addition and modulus-switching methods, the",
      "declared internal drops), and it returned a certificate c. certifyBFV? performs every check",
      "itself: Spec.schemeParamsOK?, Spec.Budget.specialOK?, the layout at every level, decOK of every",
      "input ciphertext's bound, the technique's side conditions at every multiplication, ONE BUDGET PER",
      "INSTRUCTION (E_k for body[k], printed above: Challenge.CertifyBFV.budgetBFV, from the locked",
      "Spec.BudgetBFV definitions), the locked reference worst-case BFV noise analysis",
      s!"{analyzerName} at those budgets (infinity norm of e = [phase - floor(Q/t)*m]_Q),",
      "which returned the bound shown for each output, and Spec.Encrypt.outputsUnderS? (every output is",
      s!"under the secret key itself). The locked Lean statement {certificateTheorem}",
      "(Challenge/CertifyBFV.lean; its proof is in Validation/CertifyBFV.lean and is kernel-checked by the",
      "repository's gate; it is Challenge.BFV.refAnalyzeBFVAt_sound followed by exact decryption,",
      "Challenge.BFVMul.certifiedAt_decrypts) then states: for EVERY secret key s, ALL input messages, and",
      "ALL inputs within their bounds (Spec.TraceBFV.InputsOK: each ciphertext input encrypts its message",
      "with BFV noise at most its bound; each one-component input is a plaintext polynomial within its",
      "bound), in EVERY execution of the program in which each operation meets its BFV phase contract",
      "within the budget of its own instruction (Spec.TraceBFV.RunAt: body[k] within E_k), each output is",
      "a ciphertext under s itself whose BFV decryption WITH s at its own level (Spec.Scheme.bfvDecrypt)",
      "is exactly the message the program computes on the input messages (Spec.Source.eval), with noise",
      "at most its own bound. Worst case: no probability is involved anywhere."] ++
      (match cert with
       | some c =>
         let pins := realizabilityPins (inp.mul.map (·.technique)) c.assumed (leveled && hasKs) ksDrop
         let mulPins := pins.filter fun p => !isKsPin p
         match (if c.assumed.contains .binary64 then qualifier ((inp.mul.map (·.technique.name)).getD "textbook") c.assumed else none) with
         | some q => [
             s!"REALIZABILITY: PROVED UNDER THE STANDARD MODEL OF BINARY64. The certificate records {c.assumed.map assumptionName}: the verdict is CERTIFIED ({q}).",
             s!"  Multiplication: {", ".intercalate mulPins} prove that the library's",
             "  limb-level multiplication, with its two binary64 sums as OpenFHE v1.6.1 computes them, applied at",
             "  instruction k meets the mul/square contract within E_k for EVERY arithmetic conforming to",
             "  Spec.Float.Conforms (unit roundoff 2^-53; fused multiply-add contraction allowed). E_k is",
             "  evaluated at the tolerances Spec.BudgetBFV.doubleSw/doubleSr: the floating-point error is CHARGED",
             "  to the budget, the library does not compute the idealised algorithm."] ++
           (if leveled && hasKs && !ksDrop then drop0Lines
            else if leveled && hasKs then [
             "  Key switching: Challenge.CertifyBFV.certifyBFV?_leveled_relin, certifyBFV?_leveled_keySwitch prove",
             "  that the library's key switch of a top-level operand (RelinearizeCore: the switched component is",
             "  scaled down by the limbs dropped internally with a binary64 sum, key-switched at the reduced",
             "  level with the top-level keys, scaled back up), with the declared internal drop of instruction k,",
             "  meets the relin/keySwitch contract within E_k for every conforming arithmetic",
             "  (Challenge.BFVMul.stepOK_relin_leveled_tol, stepOK_keySwitch_leveled_tol, ksCore_realizable)."]
            else []) ++ [
             "  Platform conditions (a hypothesis, Spec/Float.lean):",
             "  IEEE binary64, round to nearest, correctly rounded integer conversion, one rounding per operation",
             "  (x87 extended precision is NOT covered), no -ffast-math-style optimisation. Machine-word integer",
             "  steps and the NTT are modelled as exact modular arithmetic, not verified."]
         | none => [
           if c.assumed.contains .idealised then
             "REALIZABILITY: OF THE IDEALISED ALGORITHM ONLY. The certificate records [idealised] (Challenge.CertifyBFV.certifyBFV?_assumed): floatTolerant = false, the budget is that of the exact algorithm, which OpenFHE does not run:"
           else if c.assumed.contains .binary64Dec then "REALIZABILITY: PROVED. The certificate records no assumption about the multiplication or key switching, only binary64Dec, which is about the library's decryption (Challenge.CertifyBFV.certifyBFV?_assumed; see Library decryption):"
           else "REALIZABILITY: PROVED. The certificate records no assumption (Challenge.CertifyBFV.certifyBFV?_assumed):",
           s!"  {", ".intercalate mulPins} prove that the declared",
           "  technique's idealised limb-level algorithm, applied at instruction k, meets the mul/square",
           "  contract within E_k (not the library's code)."] ++
           (if leveled && hasKs && !ksDrop then drop0Lines
            else if leveled && hasKs then [
             "  Key switching of a top-level operand under HPSPOVERQLEVELED, with its declared internal drop:",
             "  Challenge.CertifyBFV.certifyBFV?_leveled_relin, certifyBFV?_leveled_keySwitch (for every arithmetic",
             "  conforming to Spec.Float.Conforms, the exact one included; the tolerance of its scaling is",
             "  charged to E_k whatever floatTolerant says)."]
            else [])
       | none => [])
    | _ => [
      "WHAT \"NOT CERTIFIED\" / \"UNSUPPORTED\" MEANS",
      "No theorem is claimed. This is not a proof that decryption fails: the analysis could not show",
      "it always succeeds (or the input is outside what is certified). Worst-case bounds are usually",
      "far above what is observed in practice."]
  let mulLines := match br.bind (·.mul), inp.mul with
    | some mb, some m =>
      [s!"  multiplication ({m.technique.name}): Challenge.BFVMul.stepOK_mul_lifted (and stepOK_square_lifted) reduce the contract, for",
       "    two-component operands and every secret within secretBound, to two statements about integers:",
       "    the algorithm multiplies integer representatives A_i of the components with 2*|A_i| <= Q + e,",
       "    and every component of its result is within rho/2 of t*T/Q. At a mul or square at level l,",
       "    mulLift = max(mulLift, Spec.BudgetBFV.mulLiftNormAt P l e) and mulRound = mulRoundApprox P rho",
       "    for the ONE slack (e, rho) of the technique at that level and that internal drop (printed above;",
       "    Challenge.CertifyBFV.slackAt); at every other instruction they are the textbook numbers."] ++
      (if mb.proved then
         [s!"    These slacks are PROVED for the {if mb.float then "library's limb-level algorithm with binary64 sums (standard model)" else "idealised limb-level algorithm"}: {", ".intercalate (mb.pins.filter fun p => !leveledKsPins.contains p)}."]
       else
         ["    These slacks are NOT proved for a limb-level algorithm: they are derived on paper",
          "    (Spec.BudgetBFV.hpsSlack / poverqSlack / leveledSlack / behzSlack) and validated numerically",
          "    against a limb-level model of the library (harness/bfv-rns/validate.py). A DECLARED ASSUMPTION."]) ++
      (if mb.float then
         ["    floatTolerant: the slacks are evaluated at the binary64 tolerances Spec.BudgetBFV.doubleSw /",
          "    doubleSr (the floating-point error is charged to the budget); the tolerances are PROVED under",
          "    the standard model of binary64 (Challenge.BFVMul.nuSw_tol, nuSr_tol; Spec.Float.Conforms)."]
       else [])
    | _, _ => [if br.isSome then "  multiplication: the program does not multiply." else "  multiplication: no budget was computed for this input."]
  header ++ [
    "",
    "HOW THE VERDICT WAS COMPUTED: by FHE.Holes.certifyBFVFast (FHE.Holes.certifyBFVFreshFast in the",
    "fresh-encryption modes), which makes the checks of Challenge.CertifyBFV.certifyBFV?",
    "(Challenge.BFVEncrypt.certifyBFVFresh?) with the environments in search trees and one pass over",
    "the program for each replay (FHE/Noise/FastBFV.lean; near-linear instead of quadratic in the",
    "program length). The locked statements Challenge.Fast.certifyBFVFast_eq and",
    "certifyBFVFreshFast_eq, proved and kernel-checked in this repository, say that they return",
    "exactly what certifyBFV? (certifyBFVFresh?) returns, on every input; so a certificate printed",
    "here is the value of the locked decision, and the theorems cited are about it. The bounds shown",
    "without a certificate are those of Challenge.BFV.refAnalyzeBFVAt, computed by",
    "FHE.Holes.analyzeBFVFast (Challenge.Fast.analyzeBFVFast_eq: equal on every input).",
    "",
    "Where the budget E_k of instruction k comes from (Spec.BudgetBFV; Challenge.CertifyBFV.stepBudget;",
    "locked pins in Challenge.BFV and Challenge.BFVMul):",
    "  key switching (relin, keySwitch; 0 elsewhere): ksBoundAt at the operand's OWN level (the BGV",
    "    hybrid key-switching bound at plaintext modulus 1; with no special primes, one limb per digit",
    "    and centred digits it is OpenFHE's BV key switching with digitSize 0). Challenge.BFV.relin_realizable",
    "    and keySwitch_realizable: at every level, hybrid key switching with keys of noise at most keyNoise",
    "    meets the relin/keySwitch contract within ksBoundAt, given SpecialOK (checked by",
    "    Spec.Budget.specialOK?) and a usable digit layout (Spec.Budget.KSLayout.okAt; keys generated once",
    "    at the top level serve every level, Challenge.Budget.gadgetKeys_restrict). Under HPSPOVERQLEVELED,",
    "    at a top-level operand with a declared internal drop of dr >= 1 limbs, the number is the larger of",
    "    that and Spec.BudgetBFV.ksLeveled N (Q_L/Q_(L-dr)) (ksBoundAt at level L-dr) btgt r1 (btgt = N*B_s^2",
    "    for relin, B_s for keySwitch; r1 the binary64 tolerance of the scaling): PROVED,",
    "    Challenge.BFVMul.stepOK_relin_leveled_tol, stepOK_keySwitch_leveled_tol, ksCore_realizable",
    "    (Challenge.CertifyBFV.certifyBFV?_leveled_relin, certifyBFV?_leveled_keySwitch), for every",
    "    arithmetic conforming to Spec.Float.Conforms.",
    "  modulus switching: msBudget = ceil((1+N*secretBound)/2) at every instruction, for rounding every",
    "    component of a two-component ciphertext (Challenge.BFV.stepOK_modSwitch_textbook)."] ++
    mulLines ++ [
    "  plaintext addition, at the operand's own level l: 0 for adding floor(Q/t)*p",
    "    (Challenge.BFV.stepOK_addPlain_textbook, Challenge.BFVMul.stepOK_subPlain_textbook);",
    "    Spec.BudgetBFV.plainAddRoundedAt P l b for adding round(Q_l*p/t) to a plaintext with |p| <= b",
    "    (Challenge.BFVMul.stepOK_addPlain_rounded, stepOK_subPlain_rounded);",
    "    Spec.BudgetBFV.plainAddScaledAt P l b = floor((Q_l mod t)*b/t) + 1 for adding any polynomial",
    "    within one unit of Q_l*p/t, i.e. ceil, floor or nearest (Challenge.BFVMul.stepOK_addPlain_scaled,",
    "    stepOK_subPlain_scaled).",
    "",
    "DECRYPTION COVERED: textbook BFV decryption WITH THE SECRET KEY s modulo the output's own level,",
    "  round(t*[<ct, s>]_Q / Q) mod t (Spec.Scheme.bfvDecrypt). fhe_check evaluated",
    "  Spec.Encrypt.outputsUnderS?: every output is under s itself (Galois element 1; an output left",
    "  under a rotated key is refused). The decryption condition 2*(t*B + (Q mod t)*(t-1)) < Q",
    "  (Challenge.BFV.decOK) is part of refAnalyzeBFVAt at every step. NOT covered: a decryption that",
    "  first switches the ciphertext to another modulus, or any RNS shortcut of the rounding.",
    "",
    "ASSUMPTIONS (inputs to the theorem, not proved by it):",
    "  (a) The library's operations meet the per-operation phase contracts of Spec.TraceBFV, each within",
    "      the budget of its own instruction printed above, and its key switching uses the declared digit",
    "      layout and representatives. That the contracts are achievable within those budgets is the",
    "      content of locked statements of this repository (proofs in Validation/, kernel-checked by its",
    "      gate), about IDEALISED algorithms: componentwise add/sub, plaintext operations, constants and",
    "      automorphisms (Challenge.BFV.stepOK_*, Challenge.BFVMul.stepOK_*), hybrid key switching",
    "      (Challenge.BFV.relin_realizable, keySwitch_realizable), rounding modulus switching, and",
    "      multiplication as said above. It is NOT",
    "      proved for the library's code, whose agreement with the limb-level algorithms is assumed",
    "      (machine words, NTT). For the HPS family with floatTolerant = true the limb-level algorithm",
    "      includes the library's binary64 sums, and the hypothesis is that the platform's arithmetic",
    "      conforms to the standard model Spec.Float.Conforms (Spec/Float.lean); with floatTolerant =",
    "      false the budget is that of the idealised algorithm, which the library does not compute.",
    "      The frontend's translation of the program",
    "      into the operations listed, and its statement of the technique, are untrusted."] ++
    (if leveled then [
    "      HPSPOVERQLEVELED: the number of limbs the library drops internally at each instruction",
    "      (bfv.multiplication.internalDrops) is DECLARED by the frontend; the library's FindLevelsToDrop is",
    "      not modelled. An understated drop gives a smaller budget and cannot be detected from the file:",
    "      the certificate is about runs in which the library drops exactly the declared number of limbs",
    "      (the OpenFHE extractor reads it from the run and cross-checks it twice)."] else []) ++ [
    s!"  (b) Noise of the inputs: every input ciphertext has BFV noise e = [phase - floor(Q/t)*m]_Q with",
    s!"      |e|inf <= inputNoise = {P.inputNoise} ({pow2 P.inputNoise}) (fhe_check checked Challenge.BFV.decOK",
    "      for the bound of every input ciphertext at its level, so the noise bound alone gives the input",
    "      hypothesis, including that the input decrypts: Challenge.BFV.bfv_decrypt_of_noise); every",
    s!"      plaintext operand has |p|inf <= t - 1; every key-switching key has error <= keyNoise =",
    s!"      {P.keyNoise} ({pow2 P.keyNoise}); every secret-key coefficient has |s_i| <= secretBound = {P.secretBound}.",
    s!"      {boundsLine}",
    s!"      These values{if leveled then ", and the internal drops," else ""} were supplied by the frontend ({inp.base.sourceTool});",
    "      fhe_check did not derive or check them."] ++
    (match inp.base.buildAssumption with
     | some b => [s!"      Build configuration: {b}."]
     | none => []) ++ [
    "  (c) Shapes: the multiplication and modulus-switching pins are for two-component operands",
    "      (fhe_check refuses a program that multiplies or modulus-switches anything else), relin takes",
    "      a three-component ciphertext, keySwitch a two-component one. The certificate theorem itself",
    "      covers every run that meets the contracts, whatever the shapes.",
    "  (d) Worst-case analysis (infinity norm, every coefficient at its extreme); no probabilistic or",
    "      average-case statement.",
    "  (e) No security claim: the parameters are not checked for a security level.",
    "  (f) Scheme-level parameters only: N a power of two, distinct primes coprime to t. Nothing is",
    "      claimed about NTT roots, word sizes or the storage of the limbs.",
    "  (g) Plaintext operands are modelled as one-component values [p], p the unscaled plaintext",
    "      polynomial with p = m (mod t) and |p|inf within its bound (Spec.TraceBFV.PlainOK); an encoding",
    "      that stores something else is outside the model.",
    "  (h) Each output is decrypted with the secret key s the inputs were encrypted under.",
    "  (i) The executable is compiled by the Lean compiler from the verified definitions; the Lean",
    "      compiler and runtime, and this tool's (untrusted) JSON decoding and printing, are trusted.",
    "No library (OpenFHE, HEIR) has been verified."]

/-- The meaning of the verdict; in a fresh-encryption mode with `freshText` inserted before the
assumptions, and the input-noise and worst-case items qualified. -/
def meaningText (inp : Input) (v : Verdict) (br : Option BudgetReport)
    (cert : Option Spec.CertifyBFV.CertificateBFV) (fr : Option FreshRun := none) : List String :=
  let base := meaningTextBase inp v br cert
  match fr with
  | none => base
  | some f =>
    base.flatMap fun l =>
      if l.startsWith "ASSUMPTIONS (inputs to the theorem" then freshText inp.base.P f ++ ["", l]
      else if l.startsWith "      |e|inf <= inputNoise =" then
        [l, "      [inputNoise COMPUTED by Challenge.BFVEncrypt.certifyBFVFresh? from the key and sampler bounds (above); the",
            s!"      frontend's params.inputNoise = {f.supplied} is not used]"]
      else if l.startsWith "  (d) Worst-case analysis" then
        match f.kappa with
        | some κ => [s!"  (d) Worst-case analysis of every evaluation step (infinity norm); only the error of the fresh encryptions is bounded with probability >= 1 - 2^-{κ} (above)."]
        | none => [l]
      else if l.startsWith "      average-case statement." && f.kappa.isSome then []
      else [l]

/-! ### Human-readable rendering -/

def bndStr : Bnd → String
  | .ct b => s!"ciphertext, noise <= {pow2 b}"
  | .pt b => s!"plaintext, |p| <= {pow2 b}"

/-- The margin of a ciphertext bound at modulus `Q`, in bits: `log₂` of the largest noise `decOK`
accepts over the bound (diagnostic). -/
def marginStr (t Q b : Nat) : String :=
  match maxNoise t Q with
  | some m => s!"margin {fmt2 (log2F m - log2F b)} bits"
  | none => "no noise bound is accepted at this modulus"

def renderHuman (path : String) (r : Result) (showSteps : Bool) : String := Id.run do
  let mut L : Array String := #[]
  L := L.push s!"fhe_check: {path}"
  L := L.push s!"VERDICT: {r.label}: {r.headline}"
  for w in r.warnings do L := L.push s!"WARNING: {w}"
  for n in r.notes do L := L.push s!"NOTE: {n}"
  let some inp := r.input | return "\n".intercalate L.toList
  let P := inp.base.P
  let t := P.src.t
  L := L.push ""
  let Qtop := P.src.modulus P.src.qs.length
  L := L.push s!"Parameters (BFV, from {inp.base.sourceTool}): N = {P.src.N}, t = {t}, {P.src.qs.length} ciphertext primes (log2 Q = {fmt2 (log2F Qtop)}), {P.store.special.length} special primes (log2 P = {fmt2 (log2F (P.store.special.map (·.q)).prod)})"
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
  match r.fresh with
  | none => L := L.push s!"Mode: worst case (input noise {pow2 P.inputNoise}, supplied by the frontend; the file declares no fresh encryptions, so there is no --kappa mode for it)"
  | some f =>
    let how := match f.kappa, f.used with
      | none, _ => "worst case of the fresh encryptions (support bounds; no probability)"
      | some κ, .freshWorst => s!"--kappa {κ}: the high-probability bound is not below the worst case, which is used (no probability)"
      | some κ, _ => s!"--kappa {κ}{if f.l2 then " --l2" else ""}: probability >= 1 - 2^-{κ} per execution over the fresh-encryption randomness (union bound over {f.model.inputs.length}*2N events); evaluation worst case"
    L := L.push s!"Mode: {how}"
    L := L.push s!"  fresh inputs {f.model.inputs}; error bound eps = {f.eps} ({pow2 f.eps}){if f.drift != 0 then s!", including the mean drift {f.drift}" else ""}; worst case {f.worst} ({pow2 f.worst})"
    L := L.push s!"  input noise COMPUTED (Spec.EncryptBFV.freshInputNoise): {f.inputNoise} ({pow2 f.inputNoise}); the frontend's params.inputNoise {f.supplied} ({pow2 f.supplied}) is not used"
  L := L.push ""
  match inp.mul with
  | some m =>
    L := L.push s!"Multiplication technique (declared by the frontend): {m.technique.name}{if m.source.isEmpty then "" else s!" [{m.source}]"}"
    unless m.auxBasis.isEmpty do
      L := L.push s!"  auxiliary basis: {m.auxBasis.length} moduli, log2 of their product = {fmt2 (log2F m.auxBasis.prod)}; bits: {m.auxBasis.map fun q => fmt2 (log2F q)}"
    if m.technique != .textbook then
      L := L.push s!"  floatTolerant = {m.floatTolerant}{match m.mSk with | some x => s!", mSk = {x}" | none => ""}{match m.mTilde with | some x => s!", mTilde = {x}" | none => ""}"
    if m.technique == .hpsPOverQLeveled then
      let nz := (inp.drops.zipIdx.filter fun (d, _) => d != 0).map fun (d, k) => s!"body[{k}]: {d}"
      L := L.push s!"  internal drops (declared by the frontend, one per instruction; an ASSUMPTION): {if nz.isEmpty then "none" else ", ".intercalate (nz.take 64) ++ (if nz.length > 64 then s!", ... ({nz.length - 64} more)" else "")}{match m.maxInternalDrop with | some d => s!"; maxInternalDrop = {d} (cross-check)" | none => ""}{match m.maxInternalDropKS with | some d => s!"; maxInternalDropKS = {d} (cross-check)" | none => ""}"
  | none => L := L.push "Multiplication technique: none declared"
  match inp.plainAdd with
  | some pa => L := L.push s!"Plaintext addition (declared by the frontend): {pa.method.name}{if pa.source.isEmpty then "" else s!" [{pa.source}]"}"
  | none => pure ()
  if let some br := r.budget then
    let E := br.Emax
    let tbE := br.EtextbookMax
    let leveled := (inp.mul.map (·.technique)) == some Technique.hpsPOverQLeveled
    L := L.push ""
    L := L.push "Budget (the locked Challenge.CertifyBFV.budgetBFV, computed by fhe_check, not read from the input): ONE BUDGET PER"
    L := L.push "INSTRUCTION, E_k = Spec.BudgetBFV.budgetOf of five numbers for body[k]. Largest value of each over the instructions that use it:"
    let lay := if br.layout.canonical then "canonical" else "centred"
    L := L.push s!"  keySwitch (relin, keySwitch) <= {E.keySwitch} ({pow2 E.keySwitch}): Spec.BudgetBFV.ksBoundAt at the operand's own level, {lay} representatives, variant \"{inp.base.ks.variant.name}\"{if br.ksLeveled then "; at a top-level key switch with an internal drop the larger of that and Spec.BudgetBFV.ksLeveled (PROVED: Challenge.BFVMul.stepOK_relin_leveled_tol, stepOK_keySwitch_leveled_tol)" else ""}"
    for k in br.ksLevels do
      if br.usedKsLevels.contains k.level then
        L := L.push s!"    level {k.level}: ksBoundAt = {pow2 k.bound}; digits (limbs, log2 Q_j): {k.digits.map fun (l, Q) => (l, fmt2 (log2F Q))}  [used]"
    if br.usedKsLevels.isEmpty then L := L.push "    (the program does not key-switch)"
    L := L.push s!"  modSwitch = Spec.BudgetBFV.msBudget = ceil((1+N*secretBound)/2) = {E.modSwitch} ({pow2 E.modSwitch}){if br.hasMs then "" else " (the program does not modulus-switch; unused)"}"
    L := L.push s!"  mulLift (mul, square) <= {E.mulLift} ({pow2 E.mulLift}): max(mulLift, Spec.BudgetBFV.mulLiftNormAt P l e), mulLiftNormAt = floor(((Q_l + e)*(1+N*secretBound) + Q_l)/(2*Q_l)); textbook (e = 0): {tbE.mulLift}{if br.mul.isNone then " (the program does not multiply; unused)" else ""}"
    L := L.push s!"  mulRound (mul, square) <= {E.mulRound} ({pow2 E.mulRound}): Spec.BudgetBFV.mulRoundApprox P rho = rho*(1+N*secretBound+(N*secretBound)^2), largest rho = {(br.mul.map (·.rho)).getD 1}; textbook (rho = 1): {tbE.mulRound}{if br.mul.isNone then " (unused)" else ""}"
    if let some mb := br.mul then
      L := L.push s!"    multiplications at level(s) {br.mulLevels}; slacks (lift excess e: 2*|A_i| <= Q + e; rounding slack rho), one per level and internal drop:"
      for sl in mb.slacks do
        L := L.push s!"      level {sl.level}, {sl.what}: {sl.fn}: e = {sl.slack.e} ({if sl.slack.e = 0 then "0" else s!"Q * 2^{fmt2 (log2F sl.slack.e - log2F (P.src.modulus sl.level))}"}), rho = {sl.slack.rho} ({pow2 sl.slack.rho}), Slack.ok {if sl.slack.ok then "holds" else "FALSE"}{if sl.auxName.isEmpty then "" else s!", {sl.auxName} = {sl.auxOK}"}; at body{sl.sites.take 16}{if sl.sites.length > 16 then s!" and {sl.sites.length - 16} more" else ""}"
      L := L.push s!"    slacks {if mb.proved then s!"PROVED for the {if mb.float then "library's limb-level algorithm with binary64 sums (standard model)" else "idealised limb-level algorithm"} ({", ".intercalate (mb.pins.filter fun p => !leveledKsPins.contains p)})" else s!"NOT proved for a limb-level algorithm (declared assumption; contract from slacks: {", ".intercalate mb.pins})"}"
      for n in mb.notes do L := L.push s!"    - {n}"
    let paHow := match inp.plainAdd.map (·.method) with
      | some PlainAddMethod.rounded => s!"Spec.BudgetBFV.plainAddRoundedAt P l b at the operand's level l, b = {br.plainBound} (the largest plaintext bound of the program), for adding round(Q_l*p/t)"
      | some (PlainAddMethod.scaled how) => s!"Spec.BudgetBFV.plainAddScaledAt P l b at the operand's level l, b = {br.plainBound} (the largest plaintext bound of the program), for adding a polynomial within one unit of Q_l*p/t (declared: {how})"
      | some PlainAddMethod.delta => "0, for adding floor(Q/t)*p exactly"
      | none => "0 (no plaintext-addition method declared)"
    L := L.push s!"  plainAdd (addPlain, subPlain) <= {E.plainAdd}: {paHow}{if br.hasPlainAdd then "" else " (the program does not add a plaintext; unused)"}"
    let shown := br.rows.toList.filter (·.shown)
    unless shown.isEmpty do
      L := L.push s!"  Per instruction (mul, square, relin, keySwitch, addPlain, subPlain; level = that of the first operand{if leveled then "; drop = declared internal drop" else ""}):"
      for row in shown.take 200 do
        let dr := if leveled then s!", drop {row.drop}" else ""
        let what :=
          if isMul row.instr then s!"mulLift = {pow2 row.E.mulLift}, mulRound = {pow2 row.E.mulRound} (rho = {(row.rho.getD 1)})"
          else if isKs row.instr then s!"keySwitch = {pow2 row.E.keySwitch}{if row.ksLeveled then s!" (Spec.BudgetBFV.ksLeveled; ksBoundAt at this level = {pow2 (BudgetBFV.ksBoundAt P br.layout row.level)})" else ""}"
          else s!"plainAdd = {row.E.plainAdd}"
        L := L.push s!"    body[{row.idx}] {instrOp row.instr}: level {row.level}{dr}: {what}"
      if shown.length > 200 then
        L := L.push s!"    ... {shown.length - 200} more (--json lists every instruction: budget.perInstruction)"
  if !r.outputs.isEmpty then
    L := L.push ""
    L := L.push s!"Outputs (bound B = {analyzerName} on the program with this output alone; decryption needs"
    L := L.push "2*(t*B + (Q mod t)*(t-1)) < Q, Challenge.BFV.decOK; margin = log2 of the largest B it accepts over B):"
    for o in r.outputs do
      L := L.push s!"  {o.name}: level {o.level}, noise <= {o.bound} ({pow2 o.bound}); largest accepted {match o.maxB with | some m => pow2 m | none => "none"}; {marginStr t o.Q o.bound}{match o.key with | some 1 => "" | some g => s!"  [UNDER THE ROTATED KEY sigma_{g}(s), NOT s]" | none => "  [key unknown]"}"
  match r.libDec with
  | some (.proved how) =>
    L := L.push s!"Library decryption: PROVED for every output (Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt, the locked check Challenge.BFVDecryptLib.decryptLibExtOK? holds): OpenFHE v1.6.1's own decryption (PKEBFVRNS::Decrypt, bfvrns-pke.cpp:225-278, transcribed in Spec/DecryptBFVLib.lean), by the routine of each output - {how} - returns, coefficient by coefficient, a representative in [0, t] of each output's message modulo t (decoding is not verified), for every arithmetic conforming to Spec.DecryptBFV.ConformsD (IEEE binary64, round to nearest, one rounding per operation, no value-changing optimisation, contraction to fma allowed; see Spec/DecryptBFV.lean), the hypothesis the certificate records as binary64Dec (Challenge.CertifyBFV.certifyBFV?_assumed). Not covered: DecryptCore, the NTT and the word-level modular arithmetic outside those routines (the residues are taken to be the exact phase's)."
  | _ => pure ()
  if let (some tb, some B) := (r.textbookBound, r.analyzed) then
    L := L.push s!"  informational: with the textbook budgets (textbook mulLift and mulRound, ksBoundAt at every key switch) the largest output bound would be {pow2 tb} instead of {pow2 B}: the technique's budget costs {fmt2 (log2F B - log2F tb)} bits"
  if let some f := r.failure then
    L := L.push ""
    match f.step with
    | some s =>
      L := L.push s!"First failing instruction: body[{s.idx}]  {instrStr s.instr}{(inp.base.provenance.find? (·.1 = s.idx)).map (fun p => s!"   [{p.2}]") |>.getD ""}"
      match s.ill, s.bnd with
      | some why, _ => L := L.push s!"  {why}"
      | none, .ct b =>
        L := L.push s!"  bound after it (locked refBoundBFV): {pow2 b} at level {s.level}; largest noise the decryption condition accepts there: {match maxNoise t s.Q with | some m => pow2 m | none => "none"}"
        L := L.push s!"  overflow: 2*(t*B + (Q mod t)*(t-1)) >= Q by {fmt2 (log2F (decLhs t s.Q b) - log2F s.Q)} bits (Challenge.BFV.decOK = false)"
      | none, .pt _ => L := L.push "  (a plaintext bound; not constrained)"
      L := L.push s!"  location {if f.confirmed then "confirmed" else "NOT confirmed"} by {analyzerName} on the prefixes body[0..{s.idx}] (rejects) and body[0..{s.idx}) (accepts)"
    | none => L := L.push s!"Reason: {f.what}"
  if !r.suggestions.isEmpty then
    L := L.push ""
    L := L.push "SUGGESTIONS (smallest change that would certify, found by running the verified analyzer on"
    L := L.push "hypothetical inputs; NOT a theorem, not proved minimal; re-check on the real regenerated input):"
    for sg in r.suggestions do L := L.push s!"  - {sg}"
  if showSteps && !r.steps.isEmpty then
    L := L.push ""
    L := L.push "Steps (diagnostic replay with the locked Source.step, refBoundBFV, bndOK):"
    for s in r.steps do
      match s.ill, s.bnd with
      | some why, _ => L := L.push s!"  [{s.idx}] {instrStr s.instr}: rejected: {why}"
      | none, .ct b => L := L.push s!"  [{s.idx}] {instrStr s.instr}: level {s.level}, parts {s.parts}, B = {pow2 b}, {if s.ok then marginStr t s.Q b else "DECRYPTION CONDITION FAILS"}"
      | none, .pt b => L := L.push s!"  [{s.idx}] {instrStr s.instr}: level {s.level}, parts {s.parts}, plaintext, |p| <= {pow2 b}"
  if !inp.base.noiseDerivation.isNull then
    L := L.push ""
    L := L.push s!"Noise derivation (from the frontend, printed, NOT checked): {inp.base.noiseDerivation.compress}"
  if !inp.encryption.isNull then
    L := L.push ""
    L := L.push s!"Encryption (from the frontend, printed, NOT checked): {inp.encryption.compress}"
  L := L.push ""
  L := L ++ (meaningText inp r.meaningVerdict r.budget r.cert r.fresh).toArray
  return "\n".intercalate L.toList

/-! ### JSON rendering -/

def bndJson : Bnd → List (String × Json)
  | .ct b => [("kind", "ciphertext"), ("bound", natJ b), ("boundLog2", jsonF (log2F b))]
  | .pt b => [("kind", "plaintext"), ("bound", natJ b), ("boundLog2", jsonF (log2F b))]

def renderJson (path : String) (r : Result) : Json := Id.run do
  let mut fields : List (String × Json) :=
    [("tool", "fhe_check"), ("format", "fhe-check-report/v1"), ("input", Json.str path),
     ("scheme", "BFV"), ("verdict", Json.str r.verdict.label), ("summary", Json.str r.headline)]
  -- the full label of a certificate withheld for the library (exit status 1, verdict NOT CERTIFIED)
  if r.verdict == .notCertified && r.cert.isSome then
    fields := fields ++ [("verdictLabel", Json.str r.label)]
  if let some c := r.cert then
    fields := fields ++ [("realizability", Json.mkObj [
      ("basis", Json.str (if r.verdict == .notCertified then "idealised-only" else if c.assumed.all (· == .binary64Dec) then "proved" else "proved-under-binary64-model")),
      ("assumptions", toJson (c.assumed.map assumptionName)),
      ("verdictLabel", Json.str r.label),
      ("pins", toJson (realizabilityPins ((r.input.bind (·.mul)).map (·.technique)) c.assumed
        (((r.input.bind (·.mul)).map (·.technique)) == some Technique.hpsPOverQLeveled &&
          (r.budget.map fun b => !b.usedKsLevels.isEmpty).getD false)
        ((r.budget.map fun b => FHE.Noise.FastBFV.ksDroppedGo b.x.prog.body b.x.drops).getD false))),
      ("pinsAre", Json.str "per instruction (Challenge.CertifyBFV.AtInstr): each statement is about instruction n of the program and its budget c.budget n"),
      ("decidedBy", Json.str (if r.fresh.isSome then "Challenge.BFVEncrypt.certifyBFVFresh?" else "Challenge.CertifyBFV.certifyBFV?"))])]
  if let some inp := r.input then
    let P := inp.base.P
    let t := P.src.t
    fields := fields ++ [("params", Json.mkObj [
      ("N", natJ P.src.N), ("t", natJ t), ("limbs", toJson (P.src.qs.map toString)),
      ("special", toJson (P.store.special.map (toString ·.q))),
      ("log2Q", jsonF (log2F (P.src.modulus P.src.qs.length))),
      ("schemeParamsOK", toJson r.schemeOK), ("specialOK", toJson r.specialOK)])]
    fields := fields ++ [("assumptions", Json.mkObj [
      ("inputNoise", natJ P.inputNoise), ("keyNoise", natJ P.keyNoise),
      ("secretBound", natJ P.secretBound), ("keySwitchVariant", Json.str inp.base.ks.variant.name),
      ("declaredBounds", Json.arr (inp.base.bounds.map fun (x, b) => Json.mkObj [("input", Json.str x), ("bound", natJ b)]).toArray),
      ("modSwitchMethod", Json.str inp.base.msMethod),
      ("multiplication", match inp.mul with
        | some m => Json.mkObj [
            ("technique", Json.str m.technique.name), ("auxBasis", toJson (m.auxBasis.map toString)),
            ("floatTolerant", toJson m.floatTolerant),
            ("internalDrops", if m.technique == .hpsPOverQLeveled then toJson inp.drops else Json.null),
            ("maxInternalDrop", toJson m.maxInternalDrop), ("maxInternalDropKS", toJson m.maxInternalDropKS),
            ("mSk", toJson (m.mSk.map toString)), ("mTilde", toJson (m.mTilde.map toString)),
            ("source", Json.str m.source)]
        | none => Json.null),
      ("plainAdd", match inp.plainAdd with
        | some pa => Json.mkObj [("method", Json.str pa.method.name), ("source", Json.str pa.source)]
        | none => Json.null),
      ("encryption", inp.encryption),
      ("suppliedBy", Json.str inp.base.sourceTool),
      ("noiseDerivation", inp.base.noiseDerivation)])]
    if let some br := r.budget then
      let E := br.Emax
      fields := fields ++ [("budget", Json.mkObj [
        ("from", Json.str "Challenge.CertifyBFV.budgetBFV (Spec.BudgetBFV.budgetOf, one budget per instruction)"),
        ("summary", Json.str "one budget per instruction: perInstruction. keySwitch, mulLift, mulRound, plainAdd below are the largest values over the instructions that use them (keySwitch: relin/keySwitch, 0 if none; plainAdd: addPlain/subPlain, 0 if none)"),
        ("keySwitch", natJ E.keySwitch), ("keySwitchLog2", jsonF (log2F E.keySwitch)),
        ("keySwitchFrom", Json.str (if br.ksLeveled then "Challenge.CertifyBFV.ksAt: max of Spec.BudgetBFV.ksBoundAt at the operand's level and, at a top-level key switch with an internal drop, Spec.BudgetBFV.ksLeveled" else "Spec.BudgetBFV.ksBoundAt at the operand's level")),
        ("keySwitchBudgetAllLevels", natJ br.ksBase),
        ("keySwitchCanonical", toJson br.layout.canonical),
        ("keySwitchUsedLevels", toJson br.usedKsLevels),
        ("keySwitchPerLevel", Json.arr (br.ksLevels.map fun k => Json.mkObj [
          ("level", toJson k.level), ("bound", natJ k.bound), ("log2", jsonF (log2F k.bound)),
          ("digits", Json.arr (k.digits.map fun (l, Q) => Json.mkObj [
            ("limbs", toJson l), ("log2Q", jsonF (log2F Q))]).toArray)]).toArray),
        ("modSwitch", natJ E.modSwitch), ("modSwitchFrom", Json.str "Spec.BudgetBFV.msBudget"),
        ("mulLift", natJ E.mulLift), ("mulLiftFrom", Json.str "Spec.BudgetBFV.mulLiftNormAt"),
        ("mulRound", natJ E.mulRound), ("mulRoundFrom", Json.str "Spec.BudgetBFV.mulRoundApprox"),
        ("roundSlackRho", natJ ((br.mul.map (·.rho)).getD 1)),
        ("slacks", Json.arr (((br.mul.map (·.slacks)).getD []).map fun sl => Json.mkObj [
          ("level", toJson sl.level), ("drop", toJson sl.drop), ("case", Json.str sl.what), ("from", Json.str sl.fn),
          ("e", natJ sl.slack.e), ("rho", natJ sl.slack.rho), ("ok", toJson sl.slack.ok),
          ("auxCheck", Json.str sl.auxName), ("auxOK", toJson sl.auxOK),
          ("instructions", toJson sl.sites)]).toArray),
        ("slacksProved", toJson (br.mul.map (·.proved))),
        ("floatTolerances", toJson (br.mul.map (·.float))),
        ("textbookMulLift", natJ br.EtextbookMax.mulLift), ("textbookMulRound", natJ br.EtextbookMax.mulRound),
        ("mulPins", toJson ((br.mul.map (·.pins)).getD [])),
        ("mulNotes", toJson ((br.mul.map (·.notes)).getD [])),
        ("mulLevels", toJson br.mulLevels),
        ("plainAdd", natJ E.plainAdd),
        ("plainAddFrom", Json.str (match inp.plainAdd.map (·.method) with
          | some PlainAddMethod.rounded => "Spec.BudgetBFV.plainAddRoundedAt"
          | some (PlainAddMethod.scaled _) => "Spec.BudgetBFV.plainAddScaledAt"
          | _ => "0")),
        ("plainBound", natJ br.plainBound),
        ("perInstruction", Json.arr (br.rows.map fun row => Json.mkObj [
          ("index", toJson row.idx), ("op", Json.str (instrOp row.instr)),
          ("level", toJson row.level), ("drop", toJson row.drop),
          ("keySwitch", natJ row.E.keySwitch), ("keySwitchLog2", jsonF (log2F row.E.keySwitch)),
          ("keySwitchFrom", if !isKs row.instr then Json.null
            else Json.str (if row.ksLeveled then "Spec.BudgetBFV.ksLeveled" else "Spec.BudgetBFV.ksBoundAt")),
          ("modSwitch", natJ row.E.modSwitch),
          ("mulLift", natJ row.E.mulLift), ("mulLiftLog2", jsonF (log2F row.E.mulLift)),
          ("mulRound", natJ row.E.mulRound), ("mulRoundLog2", jsonF (log2F row.E.mulRound)),
          ("rho", toJson (row.rho.map toString)),
          ("plainAdd", natJ row.E.plainAdd)]))])]
    if let some B := r.analyzed then
      fields := fields ++ [("bound", natJ B), ("boundLog2", jsonF (log2F B))]
      if let some tb := r.textbookBound then
        fields := fields ++ [("textbookBudgetBound", natJ tb), ("techniqueCostBits", jsonF (log2F B - log2F tb))]
    fields := fields ++ [("libraryDecryption", match r.libDec with
        | some (.proved how) => Json.mkObj [("status", "proved"), ("theorem", "Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt"), ("check", "Challenge.BFVDecryptLib.decryptLibExtOK?"), ("routines", Json.str how)]
        | some (.unsupported why) => Json.mkObj [("status", "unsupported"), ("why", Json.str why)]
        | some (.refused why) => Json.mkObj [("status", "refused"), ("why", Json.str why)]
        | none => Json.null)]
    fields := fields ++ [("mode", match r.fresh with
        | none => Json.mkObj [("kind", "worst-case"), ("inputNoise", "declared"), ("kappaAvailable", toJson false)]
        | some f => Json.mkObj [
            ("kind", Json.str (match f.kappa with | none => "fresh-worst-case" | some _ => if f.l2 then "kappa-l2" else "kappa")),
            ("inputNoise", "computed"), ("kappaAvailable", toJson true),
            ("kappa", toJson f.kappa), ("freshInputs", toJson f.model.inputs),
            ("used", Json.str (match f.used with
              | .freshWorst => "worst" | .freshKappa => "kappa" | .freshKappaL2 => "kappa-l2" | .declared => "declared")),
            ("eps", natJ f.eps), ("drift", natJ f.drift), ("worst", natJ f.worst),
            ("unionBoundEvents", toJson (f.model.inputs.length * (2 * (r.input.map (·.base.P.src.N)).getD 0))),
            ("computedInputNoise", natJ f.inputNoise), ("suppliedInputNoise", natJ f.supplied),
            ("decidedBy", Json.str "Challenge.BFVEncrypt.certifyBFVFresh?")]),
      ("decryption", Json.str inp.base.decryption.name)]
    fields := fields ++ [("outputs", Json.arr (r.outputs.map fun o => Json.mkObj [
      ("name", Json.str o.name), ("level", toJson o.level), ("bound", natJ o.bound),
      ("boundLog2", jsonF (log2F o.bound)),
      ("maxBound", toJson (o.maxB.map toString)),
      ("maxBoundLog2", match o.maxB with | some m => jsonF (log2F m) | none => Json.null),
      ("marginBits", match o.maxB with | some m => jsonF (log2F m - log2F o.bound) | none => Json.null),
      ("galoisKey", toJson o.key)]).toArray)]
    unless r.suggestions.isEmpty do
      fields := fields ++ [("suggestions", toJson r.suggestions)]
    unless r.warnings.isEmpty do
      fields := fields ++ [("warnings", toJson r.warnings)]
    unless r.notes.isEmpty do
      fields := fields ++ [("notes", toJson r.notes)]
    if let some f := r.failure then
      let stepJ := match f.step with
        | some s => Json.mkObj ([
            ("index", toJson s.idx), ("instr", Json.str (instrStr s.instr)),
            ("op", Json.str (instrOp s.instr)), ("illFormed", toJson s.ill),
            ("level", toJson s.level)] ++ bndJson s.bnd ++ [
            ("maxBoundLog2", match maxNoise t s.Q with | some m => jsonF (log2F m) | none => Json.null),
            ("overflowBits", match s.ill, s.bnd with
              | none, .ct b => jsonF (log2F (decLhs t s.Q b) - log2F s.Q)
              | _, _ => Json.null),
            ("confirmedByAnalyze", toJson f.confirmed)])
        | none => Json.null
      fields := fields ++ [("failure", Json.mkObj [("reason", Json.str f.what), ("firstFailing", stepJ)])]
    fields := fields ++ [("analyzer", Json.str analyzerName),
      ("certificateTheorem", Json.str (theoremOf r.fresh))]
    fields := fields ++ [("theorems", Json.arr ((theoremsCited inp r.budget r.cert r.fresh).map fun (n, d) =>
      Json.mkObj [("name", Json.str n), ("says", Json.str d)]).toArray),
      ("statement", Json.str ("\n".intercalate (meaningText inp r.meaningVerdict r.budget r.cert r.fresh)))]
  return Json.mkObj fields

end FHE.Check.BFV
