import Challenge.BFVMul.Float
import FHE.Check.BFVDecode
import FHE.Check.Budget
import FHE.Noise.FastBFV
import Spec.BudgetBFVRns
import Challenge.BFVMul.HPS
import Challenge.BFVMul.BEHZ
import Challenge.BFVMul.POverQ
import Challenge.CertifyBFV.Defs

/-!
# FHE.Check.BFVBudget — the BFV budgets of a check, explained   (UNTRUSTED glue)

A BFV check has ONE BUDGET PER INSTRUCTION: `E k = Challenge.CertifyBFV.budgetBFV x k` for
instruction `k` of the body, `x` the decoded data (`inputBFV`). This file does not choose the
numbers: it evaluates the locked `Challenge.CertifyBFV.budgetsBFV` and explains each entry
(`InstrRow`), and it turns the side conditions of the locked `Challenge.CertifyBFV.checksOK` into
readable refusals. The verdict is `Challenge.CertifyBFV.certifyBFV?` (`FHE.Check.BFVReport`); a
check that passes here and fails there is reported as an internal disagreement, never certified.

What instruction `k` (first operand at level `ℓ`, declared internal drop `dr`) is charged,
`E k = Spec.BudgetBFV.budgetOf ks ms lift round pa` (`Challenge.CertifyBFV.stepBudget`):

* `ks` (`relin`, `keySwitch`; `0` elsewhere) `= Challenge.CertifyBFV.ksAt`:
  `Spec.BudgetBFV.ksBoundAt P lay ℓ`, the bound of hybrid key switching at the operand's own level,
  `lay` the key-switching layout of the input exactly as for BGV (`FHE.Check.layoutOf`). No special
  primes (`special: []`) is hybrid key switching with `P = 1`; with one limb per digit and centred
  digits that is OpenFHE's BV key switching with `digitSize = 0`. Under `HPSPOVERQLEVELED`, at the
  top level with `dr ≥ 1`: the larger of that and
  `Spec.BudgetBFV.ksLeveled N (Q_L/Q_{L−dr}) (ksBoundAt P lay (L−dr)) btgt r1`, `btgt = N·B_s²`
  (`relin`) or `B_s` (`keySwitch`), `r1 = doubleSr` of the dropped limbs (the binary64 tolerance of
  the scaling, charged whatever `floatTolerant` says).
* `ms = Spec.BudgetBFV.msBudget P` (rounding every component of a two-component ciphertext;
  `modSwitch.method` must be `"round"` if the program modulus-switches).
* `lift`, `round` (`mul`, `square`; the textbook numbers elsewhere): the technique has one
  `Spec.BudgetBFV.Slack` `{e, rho, ok}` at `(ℓ, dr)` (`Challenge.CertifyBFV.slackAt`; lift excess
  `2·‖Aᵢ‖∞ ≤ Q_ℓ + e`, rounding slack, side condition), and
  `lift = max (mulLift P) (mulLiftNormAt P ℓ e)`, `round = mulRoundApprox P (max 1 rho)`
  (`Challenge.BFVMul.stepOK_mul_lifted`). `slackSite` names the case and the `Spec.BudgetBFV`
  function, **`techniquePins` is the one table of the pins that prove the slacks**.
* `pa`: `0` if the library adds `⌊Q/t⌋·p` (`bfv.plainAdd.method = "delta"`),
  `Spec.BudgetBFV.plainAddRoundedAt P ℓ b` if it adds `⌊Q·p/t⌉` (`"rounded"`), `b` the largest
  plaintext bound of the program (`Spec.TraceBFV.inputBound` of its one-component inputs), and
  `Spec.BudgetBFV.plainAddScaledAt P ℓ b` if it adds any polynomial within one unit of `Q·p/t`
  (`"ceil"`, `"floor"`, `"scaled"`); at the operand's own level.

**Adding or changing a technique**: its case in the locked `Challenge.CertifyBFV.slackAt`, its
description in `slackSite`, and its row in `techniquePins`.

What the budget does not cover is refused here (UNSUPPORTED), as in `FHE.Check.Budget`: a
product or square of an operand that does not have two components, a modulus switch of anything
but a two-component ciphertext, a modulus-switching method other than `"round"`, a technique
used where its slack function does not apply, a side condition that evaluates to `false`.
-/

namespace FHE.Check.BFV
open Spec Spec.Source
open Spec.BudgetBFV (Slack)

/-- **SWITCH-OVER POINT (HPS side condition).** The decidable check on the auxiliary basis under
which the idealised HPS multiplication is exact: the locked `Challenge.BFVMul.hpsAuxOK?`. -/
def hpsAuxOK? (t N : ℕ) (qs ps : List ℕ) : Bool := Challenge.BFVMul.hpsAuxOK? t N qs ps

def hpsAuxOKName : String := "Challenge.BFVMul.hpsAuxOK?"

/-- The basis check of the slack functions: the locked `Challenge.CertifyBFV.basisOK`. -/
def basisOK (qs aux : List ℕ) : Bool := Challenge.CertifyBFV.basisOK qs aux

/-- The locked technique of a decoded multiplication configuration. -/
def technique (m : MulConfig) : Spec.CertifyBFV.Technique :=
  match m.technique with
  | .textbook => .textbook
  | .hps => .hps m.auxBasis
  | .hpsPOverQ => .poverq m.auxBasis
  | .hpsPOverQLeveled => .leveled m.auxBasis
  | .behz => .behz m.auxBasis (m.mSk.getD 0) (m.mTilde.getD 0)

/-- The input of `Challenge.CertifyBFV.certifyBFV?`: the decoded data, with the layout
`FHE.Check.layoutOf` built. -/
def inputBFV (inp : Input) (lay : Budget.KSLayout) : Spec.CertifyBFV.InputBFV :=
  { P := inp.base.P, lay, prog := inp.base.prog, mul := inp.mul.map technique,
    floatTol := (inp.mul.map (·.floatTolerant)).getD false,
    plainAdd := inp.plainAdd.map fun pa => match pa.method with
      | .delta => .delta
      | .rounded => .rounded
      | .scaled _ => .scaled,
    msRound := inp.base.msMethod == "round",
    drops := inp.drops }

/-- The locked statements about the key switch of `HPSPOVERQLEVELED` on a top-level operand
(with or without an internal drop). -/
def leveledKsPins : List String :=
  ["Challenge.BFVMul.stepOK_relin_leveled_tol", "Challenge.BFVMul.stepOK_keySwitch_leveled_tol",
   "Challenge.BFVMul.ksCore_realizable"]

/-- **The pin table**: the locked statements that prove a technique's slacks for a limb-level
algorithm (for `HPSPOVERQLEVELED` also its key switch with an internal drop), and whether they
do (`true`). -/
def techniquePins (tech : Technique) (floatTolerant : Bool) : List String × Bool :=
  match tech, floatTolerant with
  | .textbook, _ => (["Challenge.BFV.stepOK_mul_textbook", "Challenge.BFVMul.stepOK_square_textbook"], true)
  | .hps, false =>
    (["Challenge.BFVMul.stepOK_mul_hps", "Challenge.BFVMul.stepOK_square_hps",
      "Challenge.BFVMul.hpsMul_congr_bfvMul"], true)
  -- BEHZ is integers only: proved whatever `floatTolerant` says
  | .behz, _ => (["Challenge.BFVMul.stepOK_mul_behz", "Challenge.BFVMul.stepOK_square_behz"], true)
  | .hpsPOverQ, false => (["Challenge.BFVMul.stepOK_mul_poverq"], true)
  | .hpsPOverQLeveled, false =>
    (["Challenge.BFVMul.stepOK_mul_poverq", "Challenge.BFVMul.stepOK_mul_leveled"] ++ leveledKsPins, true)
  -- with the binary64 tolerances: the library's floating-point multiplication, for every
  -- arithmetic conforming to the standard model `Spec.Float.Conforms`
  | .hps, true =>
    (["Challenge.BFVMul.stepOK_mul_hps_float", "Challenge.BFVMul.stepOK_square_hps_float",
      "Challenge.BFVMul.nuSw_tol", "Challenge.BFVMul.nuSr_tol"], true)
  | .hpsPOverQ, true =>
    (["Challenge.BFVMul.stepOK_mul_poverq_float", "Challenge.BFVMul.nuSw_tol",
      "Challenge.BFVMul.nuSr_tol"], true)
  | .hpsPOverQLeveled, true =>
    (["Challenge.BFVMul.stepOK_mul_poverq_float", "Challenge.BFVMul.stepOK_mul_leveled_float",
      "Challenge.BFVMul.nuSw_tol", "Challenge.BFVMul.nuSr_tol"] ++ leveledKsPins, true)

/-- The slack of a technique at one `(level, internal drop)`: what case of the algorithm it is,
the `Spec.BudgetBFV` function it came from, and the slack (the value of the locked
`Challenge.CertifyBFV.slackAt`). -/
structure SlackAt where
  level : Nat
  drop : Nat := 0
  what : String
  fn : String
  slack : Slack
  /-- The locked side condition of the limb-level algorithm (`Challenge.BFVMul.…AuxOK?`)
  evaluated here, with its name; `""` if the technique has none here. -/
  auxName : String := ""
  auxOK : Bool := true
  /-- The instructions charged this slack. -/
  sites : List Nat := []

/-- What a multiplication technique contributes to the budgets. -/
structure MulBudget where
  /-- The largest rounding slack over `slacks`. -/
  rho : Nat
  /-- One entry per `(level, internal drop)` at which the program multiplies. -/
  slacks : List SlackAt
  /-- The slacks are proved (by `pins`) for a limb-level algorithm. -/
  proved : Bool
  /-- The slacks include binary64 tolerances (`doubleSw`, `doubleSr`). -/
  float : Bool := false
  notes : List String := []
  pins : List String := []

/-- Why a technique has no budget. -/
inductive MulError
  /-- The input is malformed (INVALID INPUT). -/
  | invalid (msg : String)
  /-- The technique is outside what is certified, or a side condition is `false` (UNSUPPORTED). -/
  | unsupported (msg : String)

/-- Why `Challenge.BFVMul.behzWordOK?` (the machine-word condition of OpenFHE's BEHZ code) fails,
for the UNSUPPORTED reason. -/
def behzWordReason (t N : Nat) (qs B : List Nat) (msk mt ℓ : Nat) : String :=
  let base := s!"multiplication technique BEHZ at level {ℓ}: the machine-word side condition Challenge.BFVMul.behzWordOK? of OpenFHE's BEHZ code is false on these bases"
  if !(Challenge.BFVMul.floatBasisOK qs && Challenge.BFVMul.floatBasisOK (B ++ [msk])) then
    base ++ s!": a basis has more than 128 moduli or a modulus at or above 2^60 (m_sk = {msk}, {pow2 msk}); OpenFHE's Barrett and Shoup reductions assume moduli below 2^60 (MAX_MODULUS_SIZE64)"
  else if !(B ++ [msk]).all (mt < ·) then
    base ++ s!": m~ = {mt} is not below every modulus of B and m_sk (FastBaseConvqToBskMontgomery moves the Montgomery remainder into [0, b) as r + b - m~)"
  else
    let k := qs.length
    let X := t * N * qs.prod * (mt + 2 * (k - 1)) ^ 2 + 2 * k * mt ^ 2
    let qmin := qs.foldl min (qs.headD 0)
    let over := log2F X - log2F (mt ^ 2 * B.prod * (2 * qmin))
    let amount := if over < 0.01 then "less than 0.01 bits" else s!"{fmt2 over} bits"
    base ++ s!": the Shenoy-Kumaresan correction of FastBaseConvSK can be below -q (its worst case exceeds the bound by {amount}: t*N*Q is too large for B*2*q_min; m_sk was enlarged to {Nat.log2 msk + 1} bits against {Nat.log2 (B.headD 0) + 1}-bit moduli in B), so these bases are outside the proved word condition (BEHZ is covered only for roughly t*N <= 2*q_min); use HPSPOVERQ or HPSPOVERQLEVELED, or larger ciphertext moduli"

/-- **The slack of technique `m` for a multiplication at level `ℓ` with declared internal drop
`dr`** (`Q = Q_ℓ`, ciphertext basis = the first `ℓ` limbs of a chain of `L`): the value is the
locked `Challenge.CertifyBFV.slackAt`; this function names the case and says which of its side
conditions fails.

* `textbook`: `e = 0`, `rho = 1`.
* `HPS` (top level only; `auxBasis = R`): exact (`floatTolerant = false`): `hpsAuxOK? t N qs R`,
  slack `(0, 1)`; float-tolerant: `hpsSlack t N Q R (doubleSw ℓ) (doubleSw |R|) (doubleSr qs)`.
* `HPSPOVERQ` (`P_ℓ` = the first `ℓ` entries of `auxBasis`):
  `poverqSlack t N Q P_ℓ ℓ (doubleSw ℓ) (doubleSr P_ℓ)`.
* `HPSPOVERQLEVELED`: below the top level, or with `dr = 0`, as `HPSPOVERQ`; at the top level with
  `dr ≥ 1`:
  `leveledSlack t N Q Q_{L−dr} P_{L−dr} L (doubleSw L) (doubleSr dropped limbs) (doubleSr P_{L−dr})`.
* `BEHZ` (top level only; `auxBasis = B`): `behzSlack t N Q B mSk ℓ |B| mTilde`; integers only;
  also `Challenge.BFVMul.behzWordOK?` (the library's 64-bit words; reason: `behzWordReason`).

With `floatTolerant = false` every tolerance is `0` (the idealised exact algorithm). -/
def slackSite (P : FullParams) (m : MulConfig) (idx ℓ dr : Nat) : Except MulError SlackAt := do
  let t := P.src.t
  let N := P.src.N
  let L := P.src.qs.length
  let qs := P.src.qs.take ℓ
  let aux := m.auxBasis
  let ft := m.floatTolerant
  let (slack, flag) := Challenge.CertifyBFV.slackAt P ft ℓ dr (technique m)
  let topOnly : Except MulError Unit :=
    if ℓ = L then pure () else
      throw (.unsupported s!"multiplication technique {m.technique.name} at level {ℓ}, below the top level {L}: its slack is derived for the full chain only (the library multiplies at the top level)")
  let needAux := fun (n : Nat) (what : String) =>
    if aux.length < n then
      (throw (.invalid s!"$.bfv.multiplication.auxBasis: {m.technique.name} needs {what} ({n} moduli at level {ℓ}); {aux.length} given") : Except MulError Unit)
    else pure ()
  let basis := fun (ps : List Nat) =>
    if !basisOK qs ps then
      (throw (.unsupported s!"multiplication technique {m.technique.name} at level {ℓ}: the ciphertext moduli and the auxiliary moduli are not all odd, at least 3 and pairwise coprime (Challenge.CertifyBFV.basisOK; the slack functions of Spec.BudgetBFV assume it)") : Except MulError Unit)
    else if ft && m.technique != .behz && !Challenge.BFVMul.floatAuxOK? qs ps then
      throw (.unsupported s!"multiplication technique {m.technique.name} at level {ℓ} with floatTolerant = true: the bases do not pass Challenge.BFVMul.floatAuxOK? (at most 128 moduli per basis, each below 2^60): outside these sizes the library's 128-bit accumulations are not covered by the floating-point statements (Challenge/BFVMul/Float.lean)")
    else pure ()
  -- a flag of the locked `slackAt` this function did not explain
  let done := fun (s : SlackAt) =>
    if s.slack.ok && s.auxOK && !flag then
      (throw (.unsupported s!"multiplication technique {m.technique.name} at level {ℓ} ({s.what}): the side conditions of Challenge.CertifyBFV.slackAt are false on these bases") : Except MulError SlackAt)
    else pure s
  let poverq := fun (what : String) => do
    needAux ℓ "one auxiliary prime per ciphertext limb"
    let Pl := aux.take ℓ
    basis Pl
    done { level := ℓ, what, fn := "Spec.BudgetBFV.poverqSlack", slack,
           auxName := "Challenge.BFVMul.poverqAuxOK?",
           auxOK := Challenge.BFVMul.poverqAuxOK? t N qs Pl }
  match m.technique with
  | .textbook =>
    return { level := ℓ, what := "textbook (centred lift, exact rounding)", fn := "(0, 1)", slack }
  | .hps =>
    topOnly
    needAux 1 "its auxiliary basis R"
    if ft then
      basis aux
      done { level := ℓ, what := "HPS, binary64 conversions", fn := "Spec.BudgetBFV.hpsSlack", slack }
    else
      done { level := ℓ, what := "HPS, idealised exact algorithm (Challenge.BFVMul.hpsMul)",
             fn := "(0, 1)", slack, auxName := hpsAuxOKName, auxOK := hpsAuxOK? t N qs aux }
  | .hpsPOverQ => poverq "P-over-Q"
  | .hpsPOverQLeveled =>
    if ℓ < L then poverq "P-over-Q (below the top level)"
    else if dr = 0 then poverq "P-over-Q (no internal drop)"
    else
      if dr ≥ L then
        throw (.invalid s!"$.bfv.multiplication.internalDrops[{idx}]: {dr} is not below the number of limbs {L}")
      let k := L - dr
      needAux k "one auxiliary prime per remaining limb"
      let Pl := aux.take k
      basis Pl
      done { level := ℓ, drop := dr, what := s!"leveled P-over-Q, {dr} limb(s) dropped internally",
             fn := "Spec.BudgetBFV.leveledSlack", slack,
             auxName := "Challenge.BFVMul.leveledAuxOK?",
             auxOK := Challenge.BFVMul.leveledAuxOK? t N qs aux dr }
  | .behz =>
    topOnly
    needAux 1 "its base B"
    let some msk := m.mSk
      | throw (.invalid "$.bfv.multiplication.mSk: missing (BEHZ needs the modulus m_sk)")
    let some mt := m.mTilde
      | throw (.invalid "$.bfv.multiplication.mTilde: missing (BEHZ needs the modulus m~)")
    basis (aux ++ [msk])
    if Challenge.BFVMul.behzAuxOK? t N qs aux msk mt && !Challenge.BFVMul.behzWordOK? t N qs aux msk mt then
      throw (.unsupported (behzWordReason t N qs aux msk mt ℓ))
    let what := if Challenge.BFVMul.behzWordOK? t N qs aux msk mt then
      "BEHZ (integers only; the library's 64-bit words: Challenge.BFVMul.behzWordOK? = true)"
      else "BEHZ (integers only)"
    done { level := ℓ, what, fn := "Spec.BudgetBFV.behzSlack", slack,
           auxName := "Challenge.BFVMul.behzAuxOK?",
           auxOK := Challenge.BFVMul.behzAuxOK? t N qs aux msk mt }

/-- The contribution of technique `m` for a program that multiplies at `sites`
(`(index, level, drop)` of every `mul` and `square`); `square?` is the index of a `square`
instruction, if any. -/
def mulBudget (P : FullParams) (sites : List (Nat × Nat × Nat)) (square? : Option Nat)
    (m : MulConfig) : Except MulError MulBudget := do
  if let (some i, true) := (square?, m.technique == .hpsPOverQ || m.technique == .hpsPOverQLeveled) then
    throw (.unsupported s!"square under {m.technique.name} (body[{i}]): the library lifts the operand of a squaring in two different ways, so the square contract (one lift of the operand) is not shown to be met; write it as mul a a")
  let mut slacks : List SlackAt := []
  for (idx, ℓ, dr) in sites do
    let dr := if m.technique == .hpsPOverQLeveled && ℓ == P.src.qs.length then dr else 0
    -- the sites of each slack are collected most recent first and reversed below (appending to
    -- the end of the list at every multiplication was quadratic in the number of them)
    match slacks.findIdx? (fun s => s.level == ℓ && s.drop == dr) with
    | some k => slacks := slacks.modify k fun s => { s with sites := idx :: s.sites }
    | none => slacks := slacks ++ [{ (← slackSite P m idx ℓ dr) with sites := [idx] }]
  slacks := slacks.map fun s => { s with sites := s.sites.reverse }
  if let some s := slacks.find? (!·.slack.ok) then
    throw (.unsupported s!"multiplication technique {m.technique.name} at level {s.level} ({s.what}): the side condition of {s.fn} (Spec.BudgetBFV.Slack.ok) on the auxiliary basis is false: the parameters are outside the regime the slack formula is derived and validated for, so the technique has no budget here")
  if let some s := slacks.find? (!·.auxOK) then
    throw (.unsupported s!"multiplication technique {m.technique.name} at level {s.level} ({s.what}): the locked side condition {s.auxName} of the idealised limb-level algorithm is false on these bases, so the technique has no budget at these parameters")
  let (pins, proved) := techniquePins m.technique m.floatTolerant
  let float := m.floatTolerant && (m.technique == .hps || m.technique == .hpsPOverQ || m.technique == .hpsPOverQLeveled)
  let rho := (slacks.map (·.slack.rho)).foldl max 1
  let notes :=
    (if float then ["floatTolerant = true: the slacks are evaluated at the binary64 tolerances Spec.BudgetBFV.doubleSw / doubleSr, which CHARGE the floating-point error of the library's two sums to the budget (the library does not compute the idealised algorithm). PROVED for every arithmetic conforming to the standard model of binary64, Spec.Float.Conforms (Challenge.BFVMul.nuSw_tol, nuSr_tol and the stepOK_*_float statements; bases checked by Challenge.BFVMul.floatAuxOK?). That the platform conforms (IEEE binary64, round to nearest, no value-changing optimisation; x87 extended precision is not covered) is a hypothesis: Spec/Float.lean"]
     else if m.technique == .textbook || m.technique == .behz then []
     else ["floatTolerant = false: the budget is that of the idealised exact algorithm only, so the verdict is NOT CERTIFIED FOR THE LIBRARY; use floatTolerant = true for the budget that covers the library's binary64 sums"]) ++
    (if m.technique == .hps || m.technique == .hpsPOverQ || m.technique == .hpsPOverQLeveled || m.technique == .behz then
       ["the ciphertext and auxiliary moduli are odd, at least 3 and pairwise coprime: checked by Challenge.CertifyBFV.certifyBFV? (basisOK)"]
     else []) ++
    (if proved && m.technique != .textbook then [if float then "PROVED means: for the limb-level algorithm of Challenge/BFVMul/Float.lean (the binary64 sums as OpenFHE v1.6.1 computes them, in any arithmetic conforming to Spec.Float.Conforms; machine-word integer steps and the NTT modelled as exact modular arithmetic), under its locked side conditions (evaluated here)" else "PROVED means: for the idealised limb-level algorithm defined in Challenge/BFVMul/*.lean, under its locked side condition (evaluated here); not for the library's code"] else []) ++
    (if m.technique == .hpsPOverQLeveled then ["one budget per instruction: each multiplication is charged the slack of its own level and of its own declared internal drop (bfv.multiplication.internalDrops), and each key switch its own bound; an instruction at which the library drops nothing does not pay for a drop elsewhere. The declared drops are an input ASSUMPTION: an understated drop gives a smaller budget, and fhe_check cannot detect it from the file"] else []) ++
    (if m.technique == .textbook && !m.auxBasis.isEmpty then ["bfv.multiplication.auxBasis is not used by the textbook technique"] else [])
  return { rho, slacks, proved, float, notes, pins }

/-! ### The sites of the program the budget depends on -/

/-- One instruction of the replay on zero messages: its index, and `(level, parts)` of each of
its operands. -/
structure Site where
  idx : Nat
  instr : Instr
  operands : List (Nat × Nat)

def operandsOf : Instr → List Var
  | .add _ a b | .sub _ a b | .mul _ a b => [a, b]
  | .square _ a | .mulConst _ a _ | .copy _ a | .toEval _ a | .toCoeff _ a | .relin _ a
  | .keySwitch _ a | .automorph _ a _ | .modSwitch _ a | .dropLimbs _ a _ => [a]
  | .addPlain _ a p | .subPlain _ a p | .mulPlain _ a p => [a, p]

/-- Every instruction with the level and parts of its operands, replaying `Source.step` on zero
messages up to the first ill-formed instruction. -/
def sites (P : Params) (prog : Program) : List Site := Id.run do
  -- the environment in a search tree (`ZEnv`): near-linear in the program length
  let mut ρ := ZEnv.init P prog
  let mut out := #[]
  let mut idx := 0
  for i in prog.body do
    out := out.push { idx, instr := i,
                      operands := (operandsOf i).filterMap fun x => (ρ.get x).map fun v => (v.level, v.parts) }
    match ρ.step i with
    | some ρ' => ρ := ρ'
    | none => break
    idx := idx + 1
  return out.toList

def isMul : Instr → Bool
  | .mul .. | .square .. => true
  | _ => false

def isSquare : Instr → Bool
  | .square .. => true
  | _ => false

def isKs : Instr → Bool
  | .relin .. | .keySwitch .. => true
  | _ => false

def isMs : Instr → Bool
  | .modSwitch .. => true
  | _ => false

def isPlainAdd : Instr → Bool
  | .addPlain .. | .subPlain .. => true
  | _ => false

/-- The largest plaintext bound of the program: `Spec.TraceBFV.inputBound` over its
one-component inputs (`0` if there is none). -/
def maxPlainBound (P : FullParams) (prog : Program) : Nat :=
  -- `TraceBFV.inputBound P prog` with the declared bounds in a tree
  -- (`Validation.FastBFV.Aux.inputBound_eq`)
  FHE.Noise.FastBFV.maxPlainBoundWith prog
    (FHE.Noise.FastBFV.inputBound P (FHE.Noise.Fast.boundMap prog))

/-- Why no certified budget exists. -/
inductive BudgetError
  /-- INVALID INPUT. -/
  | invalid (msg : String)
  /-- UNSUPPORTED. -/
  | unsupported (msg : String)

/-- One instruction and its budget. -/
structure InstrRow where
  idx : Nat
  instr : Instr
  /-- The level of the first operand (`Challenge.CertifyBFV.levelOf`). -/
  level : Nat
  /-- The declared internal drop of the instruction (`0` unless `HPSPOVERQLEVELED`). -/
  drop : Nat
  /-- `Challenge.CertifyBFV.budgetsBFV` at this position. -/
  E : TraceBFV.Budget
  /-- The key-switching number is `Spec.BudgetBFV.ksLeveled` (above `ksBoundAt`). -/
  ksLeveled : Bool := false
  /-- A `mul` or `square`: the rounding slack charged. -/
  rho : Option Nat := none

/-- Whether the report prints the row in its per-instruction table: the instructions whose
contract uses a number that depends on the instruction. -/
def InstrRow.shown (r : InstrRow) : Bool := isMul r.instr || isKs r.instr || isPlainAdd r.instr

/-- The budgets, how they were computed, and the sites they were derived from. -/
structure BudgetReport where
  /-- The input of `Challenge.CertifyBFV.certifyBFV?`. -/
  x : Spec.CertifyBFV.InputBFV
  /-- One row per instruction (up to and including the first one `Source.step` rejects). -/
  rows : Array InstrRow
  /-- `Challenge.CertifyBFV.budgetBFV x`: the budget of instruction `k`. -/
  E : ℕ → TraceBFV.Budget
  /-- Summary: for each number, the largest value over the instructions that use it (key
  switching: `relin`/`keySwitch`, `0` if none; plaintext addition: `addPlain`/`subPlain`, `0` if
  none; the multiplication numbers: all instructions, the textbook numbers if none multiplies). -/
  Emax : TraceBFV.Budget
  /-- The budgets with no technique declared: the textbook multiplication numbers and
  `ksBoundAt` at every key switch (informational: what the technique costs). -/
  Etextbook : ℕ → TraceBFV.Budget
  EtextbookMax : TraceBFV.Budget
  layout : Budget.KSLayout
  /-- `Spec.BudgetBFV.ksBoundAt` at every level `1..L`. -/
  ksLevels : List KsLevel
  usedKsLevels : List Nat
  mulLevels : List Nat
  hasMs : Bool
  hasPlainAdd : Bool
  /-- The technique's contribution; `none` iff the program does not multiply. -/
  mul : Option MulBudget
  /-- `Spec.BudgetBFV.ksBudget P lay`: the largest `ksBoundAt` over the levels (informational). -/
  ksBase : Nat
  /-- Some key switch is charged `Spec.BudgetBFV.ksLeveled` (an internal drop at the top level). -/
  ksLeveled : Bool := false
  /-- The plaintext bound `b` of the plaintext-addition number. -/
  plainBound : Nat

/-- The componentwise summary of a list of rows (`BudgetReport.Emax`). -/
def summaryOf (P : FullParams) (rows : List (Instr × TraceBFV.Budget)) : TraceBFV.Budget :=
  let mx := fun (f : TraceBFV.Budget → Nat) (p : Instr → Bool) (z : Nat) =>
    ((rows.filter fun r => p r.1).map fun r => f r.2).foldl max z
  BudgetBFV.budgetOf (mx (·.keySwitch) isKs 0) (BudgetBFV.msBudget P)
    (mx (·.mulLift) (fun _ => true) (BudgetBFV.mulLift P))
    (mx (·.mulRound) (fun _ => true) (BudgetBFV.mulRound P)) (mx (·.plainAdd) isPlainAdd 0)

/-- Compute the budgets of a BFV program (the locked `Challenge.CertifyBFV.budgetsBFV`), or the
reason `Challenge.CertifyBFV.checksOK` has no budget for it. -/
def computeBudget (inp : Input) : Except BudgetError BudgetReport := do
  let P := inp.base.P
  let prog := inp.base.prog
  let L := P.src.qs.length
  let lay ← match layoutOf P inp.base.ks with
    | .ok l => pure l
    | .error e => throw (.invalid e)
  let levels := (List.range L).map (· + 1)
  -- the realizability pins need the layout usable at every level
  if let some ℓ := levels.find? fun ℓ => !lay.okAt ℓ then
    throw (.invalid s!"the key-switching digit layout is not usable at level {ℓ} (Spec.Budget.KSLayout.okAt: nonempty digits covering exactly {ℓ} limbs): {lay.sizes ℓ}")
  let ss := sites P.src prog
  let lvl := fun (s : Site) => (s.operands.head?.map (·.1)).getD 0
  let leveled := (inp.mul.map (·.technique)) == some Technique.hpsPOverQLeveled
  let dropsA := inp.drops.toArray   -- indexed per site: an array, not a list
  let dropOf := fun (s : Site) => if leveled then dropsA.getD s.idx 0 else 0
  let dedup := fun (l : List Nat) => l.eraseDups.mergeSort (· ≥ ·)
  let ksSites := ss.filter (isKs ·.instr)
  let usedKs := dedup (ksSites.map lvl)
  let mulSites := ss.filter (isMul ·.instr)
  let msSites := ss.filter (isMs ·.instr)
  let paSites := ss.filter (isPlainAdd ·.instr)
  -- modulus switching: `Challenge.BFV.stepOK_modSwitch_textbook` is for two-part ciphertexts
  if let some s := msSites.find? fun s => s.operands.any (·.2 ≠ 2) then
    throw (.unsupported (s!"modSwitch of a value that is not a two-part ciphertext (body[{s.idx}]): " ++
      "the BFV modulus-switching budget (Spec.BudgetBFV.msBudget; Challenge.BFV.stepOK_modSwitch_textbook) is for two-part ciphertexts; relinearize first"))
  if inp.base.msMethod != "round" && !msSites.isEmpty then
    throw (.unsupported (s!"modulus-switching method {inp.base.msMethod}{match msSites.head? with | some s => s!" (body[{s.idx}])" | none => ""}: " ++
      "for BFV only rounding every component (\"round\") has a proved budget"))
  -- multiplication: the two numbers are derived for two-part operands
  if let some s := mulSites.find? fun s => s.operands.any (·.2 ≠ 2) then
    throw (.unsupported (s!"multiplication of an operand that is not a two-part ciphertext (body[{s.idx}]): " ++
      "the BFV multiplication budget (Spec.BudgetBFV.mulLiftNormAt, mulRoundApprox; Challenge.BFVMul.stepOK_mul_lifted) is for two-part operands; relinearize first"))
  let mulLevels := dedup (mulSites.map lvl)
  let mb ← match mulSites.head?, inp.mul with
    | none, _ => pure none
    | some s, none =>
      throw (.invalid s!"$.bfv.multiplication: missing, and the program multiplies (body[{s.idx}]); the multiplication technique decides the budget")
    | some _, some m =>
      match mulBudget P (mulSites.map fun s => (s.idx, lvl s, dropOf s))
          ((mulSites.find? (isSquare ·.instr)).map (·.idx)) m with
      | .ok b => pure (some b)
      | .error (.invalid e) => throw (.invalid e)
      | .error (.unsupported e) => throw (.unsupported e)
  if let (some s, none) := (paSites.head?, inp.plainAdd) then
    throw (.invalid s!"$.bfv.plainAdd: missing, and the program adds a plaintext (body[{s.idx}]); the method (delta | rounded | ceil | floor | scaled) decides the budget")
  -- `HPSPOVERQLEVELED`: the library drops limbs only inside a mul, square, relin or keySwitch
  -- of a top-level operand (`Challenge.CertifyBFV.stepChecks` rejects any other nonzero drop)
  if leveled then
    if let some s := ss.find? fun s => dropOf s != 0 && lvl s != L then
      throw (.invalid s!"$.bfv.multiplication.internalDrops[{s.idx}]: {dropOf s}, but the operand of body[{s.idx}] is at level {lvl s}, below the top level {L}: HPSPOVERQLEVELED drops limbs internally only at the top level (0 below it)")
  -- `HPSPOVERQLEVELED`: a key switch of a top-level operand goes through the library's
  -- `RelinearizeCore` (`Challenge.CertifyBFV.stepChecks`)
  if leveled then
    for s in ksSites do
      if lvl s == L then
        if dropOf s ≥ L then
          throw (.invalid s!"$.bfv.multiplication.internalDrops[{s.idx}]: {dropOf s} is not below the number of limbs {L}")
        if !Challenge.BFVMul.floatAuxOK? (P.src.qs.take L) [] then
          throw (.unsupported s!"key switch of a top-level operand under HPSPOVERQLEVELED (body[{s.idx}]): the ciphertext moduli do not pass Challenge.BFVMul.floatAuxOK? (at most 128 moduli, each below 2^60, odd, at least 3, pairwise coprime): the library scales the switched component with a binary64 sum there, and outside these sizes the statements about it (Challenge.BFVMul.stepOK_relin_leveled_tol, stepOK_keySwitch_leveled_tol) do not apply")
  let x := inputBFV inp lay
  -- `Challenge.CertifyBFV.budgetsBFV`, with trees (`Validation.FastBFV.budgets_eq`)
  let bs := (FHE.Noise.FastBFV.budgets x).toArray
  let xtb : Spec.CertifyBFV.InputBFV := { x with mul := none }
  let tbs := (FHE.Noise.FastBFV.budgets xtb).toArray
  let rows := ss.toArray.map fun s =>
    let E := Challenge.CertifyBFV.budgetFn bs s.idx
    let ℓ := lvl s
    ({ idx := s.idx, instr := s.instr, level := ℓ, drop := dropOf s, E,
       ksLeveled := isKs s.instr && E.keySwitch != BudgetBFV.ksBoundAt P lay ℓ,
       rho := match inp.mul with
         | some m => if isMul s.instr then
             -- the slack of this (level, drop), computed once per pair by `mulBudget`
             -- (`slackAt` reads the drop only under HPSPOVERQLEVELED at the top level)
             let dr := if m.technique == .hpsPOverQLeveled && ℓ == P.src.qs.length then dropOf s else 0
             match (mb.bind fun b => b.slacks.find? fun sl => sl.level == ℓ && sl.drop == dr) with
             | some sl => some (max 1 sl.slack.rho)
             | none =>
               some (max 1 (Challenge.CertifyBFV.slackAt P m.floatTolerant ℓ (dropOf s) (technique m)).1.rho)
           else none
         | none => none } : InstrRow)
  let ksLevels := levels.reverse.map fun ℓ =>
    { level := ℓ, bound := BudgetBFV.ksBoundAt P lay ℓ,
      digits := (lay.sizes ℓ).zip (Budget.digitModuli P lay ℓ) : KsLevel }
  return { x, rows, E := Challenge.CertifyBFV.budgetFn bs,
           Emax := summaryOf P (rows.toList.map fun r => (r.instr, r.E)),
           Etextbook := Challenge.CertifyBFV.budgetFn tbs,
           EtextbookMax := summaryOf P (ss.map fun s => (s.instr, Challenge.CertifyBFV.budgetFn tbs s.idx)),
           layout := lay, ksLevels, usedKsLevels := usedKs, mulLevels,
           hasMs := !msSites.isEmpty, hasPlainAdd := !paSites.isEmpty, mul := mb,
           ksBase := BudgetBFV.ksBudget P lay, ksLeveled := rows.any (·.ksLeveled),
           plainBound := maxPlainBound P prog }

end FHE.Check.BFV
