import Spec.BudgetBFVRns
import Spec.Certify
import Spec.CertifyBFV
import Spec.Encrypt
import Challenge.BFV.Defs
import Challenge.BFVMul.HPS
import Challenge.BFVMul.BEHZ
import Challenge.BFVMul.BEHZWord
import Challenge.BFVMul.POverQ
import Challenge.BFVMul.Float
import Challenge.BFVMul.KSLeveled
import Challenge.Realize.OpenFHEBFV

/-!
# Challenge.CertifyBFV.Defs — the function that decides a BFV certificate   (LOCKED definitions)

`certifyBFV?` is the whole decision of `fhe_check` on a BFV program, as `Challenge.Certify.certify?`
is for BGV: it takes exactly the decoded data (parameters, key-switching layout, program, the
declared multiplication technique with its auxiliary basis, the plaintext-addition method, the
modulus-switching method, and under `HPSPOVERQLEVELED` the number of limbs the library drops
inside each instruction) and performs every check a certificate rests on itself. The statements
about it are in `Challenge.CertifyBFV` (`certifyBFV? x = some c → …`); what remains outside is
reading the input and printing.

**One budget per instruction** (`budgetBFV x k`, the budget of instruction `k` of the body;
`Spec.TraceBFV.RunAt`). It is computed in one replay of `Source.step` over the body on all-zero
messages (levels and numbers of components do not depend on the messages): `stepBudget` at the
environment in front of the instruction, with `ℓ` the level of the instruction's first operand
and `dr` its declared internal drop (`x.drops`; read only under `HPSPOVERQLEVELED`):

* key switching (`relin`, `keySwitch`; `0` at any other instruction): `ksAt`. It is
  `Spec.BudgetBFV.ksBoundAt P lay ℓ`, the bound of hybrid key switching at the operand's own
  level; under `HPSPOVERQLEVELED` at the top level with `dr ≥ 1` limbs dropped it is the larger of
  that and `Spec.BudgetBFV.ksLeveled N (Q_L/Q_{L−dr}) (ksBoundAt P lay (L − dr)) btgt r1`, with
  `btgt = N·B_s²` for `relin`, `B_s` for `keySwitch`, and `r1 = doubleSr` of the dropped limbs
  (the binary64 tolerance of the scaling, charged whatever `floatTol` says);
* modulus switching: `Spec.BudgetBFV.msBudget P`;
* multiplication (`mul`, `square`; the textbook numbers at any other instruction): the declared
  technique has ONE slack `(e, ρ)` there (`slackAt`: `hpsSlack`, `poverqSlack`, `behzSlack`,
  `(0, 1)` for the textbook algorithm and idealised exact HPS; under `HPSPOVERQLEVELED`,
  `poverqSlack` below the top level or with no drop, `leveledSlack` for the declared drop at the
  top level); `mulLift = max (mulLift P) (mulLiftNormAt P ℓ e)`,
  `mulRound = mulRoundApprox P (max 1 ρ)`;
* plaintext addition: `0` (adding `⌊Q/t⌋·p`), `plainAddRoundedAt P ℓ b` or
  `plainAddScaledAt P ℓ b` at the operand's level, `b` the largest plaintext bound of the program
  (`maxPlainBound`).

With `floatTol = true` the slacks of the HPS family include the binary64 tolerances
`Spec.BudgetBFV.doubleSw`, `doubleSr` (OpenFHE's floating-point steps: the floating-point error
is charged to the budget), and the bases must pass `Challenge.BFVMul.floatAuxOK?` (at most 128
moduli, each below `2⁶⁰`, odd, at least 3, pairwise coprime); with `false` every tolerance of a
multiplication is `0` (the idealised exact algorithms of `Challenge/BFVMul/`). BEHZ and the
textbook algorithm use integers only: `floatTol` does not change them.

**What `certifyBFV?` checks** (`some` only if all hold; `checksOK`):

1. `Spec.schemeParamsOK?`, the scheme is BFV, `Spec.Budget.specialOK?` (odd special primes),
   and the key-switching layout restricts from the top level to every level `1, …, L`
   (`Spec.Certify.layoutOK?`: usable at every level, and the digits of each level are the
   top-level digits cut down, so that keys generated once at the top level serve every level:
   `Challenge.Budget.gadgetKeys_restrict`, which needs no size condition for BFV);
2. the program has at least one output; every input ciphertext's bound satisfies the decryption
   condition `Challenge.BFV.decOK` at its level (so the noise bound alone gives the input
   hypothesis, `Challenge.BFV.bfv_decrypt_of_noise`); every plaintext input's bound is at least
   `⌊t/2⌋` (`plainBoundsOK`: else the message `⌊t/2⌋` has no plaintext within it, and the
   certificate would be about no inputs for it);
3. a multiplication technique is declared if the program multiplies, a plaintext-addition method
   if it adds or subtracts a plaintext, and modulus switching rounds every component if it
   modulus-switches; no `square` under the P-over-Q techniques (the library lifts the operand of
   a squaring in two ways: no `square` pin covers it);
4. at every `mul` and `square` (`stepChecks`, along the same replay): the operand's level is in
   `1, …, L`, and the slack of the technique there passes its side condition
   `Spec.BudgetBFV.Slack.ok` *and* its flag in `slackAt`: the auxiliary basis is long enough, the
   moduli are odd, at least 3 and pairwise coprime (`basisOK`), with `floatTol` the bases of the
   HPS family pass `Challenge.BFVMul.floatAuxOK?`, the locked side condition of the limb-level
   algorithm holds (`Challenge.BFVMul.hpsAuxOK?`, `poverqAuxOK?`, `leveledAuxOK?`,
   `behzAuxOK?`), under BEHZ also the machine-word condition of the library's code
   (`Challenge.BFVMul.behzWordOK?`: the transcription's arithmetic is exact only when it holds), HPS and BEHZ multiply at the top level only, and a declared drop is below
   the number of limbs;
5. under `HPSPOVERQLEVELED`: `x.drops` has one entry per instruction; a nonzero declared drop
   only at a `mul`, `square`, `relin` or `keySwitch` of a top-level operand (the only places
   where the library drops limbs internally: the `HPSPOVERQLEVELED` branches that start at
   `bfvrns-leveledshe.cpp:263`, `:485`, `:869` and call `FindLevelsToDrop` at `:271`, `:491`,
   `:874`; the fourth call, `EvalFastRotationPrecompute` at `:779`, is unreachable because the
   extractor refuses fast rotations; a
   nonzero drop anywhere else is rejected, not ignored); at every `relin` and `keySwitch` at
   the top level the declared drop is below the number of limbs and the ciphertext basis passes
   `Challenge.BFVMul.floatAuxOK?` (the library scales the switched component there with a
   binary64 sum, also when it drops nothing);
5a. `t − 1 ≤ ⌊q₀/2⌋`. OpenFHE's packed encoder (`packedencoding.cpp:119-131`) stores the `[0, t)`
   coefficients in limb 0 and fills every other limb with a CENTRED modulus switch from `q₀`
   (`NativeVector(values, q_j)`, `mubintvecnat.cpp:192-213`): a coefficient above `⌊q₀/2⌋`
   becomes `x − q₀` there, so the stored plaintext (and `TimesQovert` of it in encryption and
   plaintext addition) is not the small integer the input contract (`Spec.TraceBFV.PlainOK`,
   `Spec.EncryptBFV.encryptBFV` of `liftMsg m`) describes; with this condition every stored
   coefficient in `[0, t)` is the same integer in every limb; and `t ≤ q_i`
   for every limb, so that this integer is its own residue in every limb, which `TimesQovert`
   (`dcrtpoly-impl.h:918-935`) reduces modulo `t` limb by limb;
5b. the declared key-switching layout is OpenFHE's (`Challenge.RealizeBFV.ksDeclOK?`): with
   special primes (HYBRID) canonical representatives, without (BV, digit size 0) one limb per digit
   at every level; the transcribed key switch (`Challenge.RealizeBFV.ksBFV`) and its budget are
   about that layout (`Challenge.CertifyBFV.certifyBFV?_library_run`);
6. `Challenge.BFV.refAnalyzeBFVAt` accepts the program at the budgets `budgetBFV x`;
7. every output is under the secret key itself (`Spec.Encrypt.outputsUnderS?`), and for **each**
   output `o`, `refAnalyzeBFVAt` accepts the program with `o` as its only output (its own bound).

**Which realizability basis applies** (`assumptionsOf`; empty = PROVED with no hypothesis on the
platform and for the algorithm the declared technique names). The
certificate is about every run in which instruction `k` meets its `Spec.TraceBFV` contract within
`c.budget k`. That the contracts are met by the declared technique's limb-level algorithms is
proved (`Challenge.CertifyBFV`, realizability pins) for the textbook algorithm, BEHZ (integers
only), the HPS family with exact arithmetic (`floatTol = false`), and, for every arithmetic
conforming to the standard model of binary64 (`Spec.Float.Conforms`), the library's
floating-point multiplications (`Challenge.BFVMul.Fl.hpsMul`, `poverqMul`, `leveledMul` with the
sums of `Fl.floatSums A`) and its key switch with an internal drop
(`Challenge.BFVMul.Fl.leveledKS`). What a certificate records:

**The declared drops are an input hypothesis.** OpenFHE chooses the drop of each instruction with
`FindLevelsToDrop` (`bfvrns-leveledshe.cpp:98-198`, binary64 `log2`/`sqrt`/`pow` heuristics),
which is not modelled: a certificate is about runs in which the library drops exactly
`x.drops` (the realizability statements are instantiated at the declared drop of each
instruction). The evidence that the declared drops are the library's is untrusted and outside
this function: the OpenFHE extractor (`harness/frontend/openfhe/extract_bfv.py`) declares, for
every instruction, the drop the library recorded at run time, and refuses the extraction unless
it equals both the library's own `FindLevelsToDrop` table dumped from the context and an
independent Python replica of it. Charging every drop the library could choose instead (`0` to
`L − 1`) needs no such evidence but certifies almost nothing at OpenFHE's parameters
(`harness/frontend/levelbfv/README.md`).

* `binary64`: `floatTol = true` and either the HPS family on a program that multiplies, or
  `HPSPOVERQLEVELED` on a program with a key switch at which the library drops limbs (with drop
  `0` the scaling inside the key switch rounds nothing: `Challenge.BFVMul.leveledKS_drop_zero`). What is recorded is the hypothesis that the
  platform conforms (`Spec/Float.lean` lists what that requires of a build).
* `declaredDrops`: `HPSPOVERQLEVELED` with a `mul`, `square`, `relin` or `keySwitch` of a
  top-level operand (`opLevels`): the budget there is computed for the drop the frontend
  declared, an unchecked input (above).
* `idealised`: the binary64 cases with `floatTol = false`: the certificate is then about the
  idealised exact algorithms (the exact arithmetic conforms, `Challenge.BFVMul.exact_conforms`),
  which the library does not run, and says so.
* `binary64Dec`: the declared technique is one of OpenFHE's four (`libTechnique`), whatever
  `floatTol` says: the statement about the library's own decryption of the outputs
  (`Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt`) applies, and it holds for every
  arithmetic conforming to `Spec.DecryptBFV.ConformsD`; what is recorded is the hypothesis that
  the platform's decryption conforms. Appended after the others, so it does not change their
  order.
-/

namespace Challenge.CertifyBFV
open Spec Spec.Source Spec.BudgetBFV Spec.CertifyBFV Challenge.BFV Challenge.BFVMul

/-! ## The data

`Technique`, `PlainAddMethod`, `InputBFV`, `AssumptionBFV` and `CertificateBFV` are trusted
definitions of `Spec.CertifyBFV`. -/

/-! ## The shape of the program -/

/-- The level of the (first) operand of every `mul` and `square` of the body, replaying
`Source.step` from `ρ` up to the first instruction it rejects. -/
def mulLevelsAux (Pr : Params) : List Instr → Env Pr → List ℕ
  | [], _ => []
  | i :: is, ρ =>
    let here : List ℕ := match i with
      | .mul _ a _ | .square _ a => ((ρ a).map (·.level)).toList
      | _ => []
    match step Pr ρ i with
    | some ρ' => here ++ mulLevelsAux Pr is ρ'
    | none => here

/-- The levels at which the program multiplies (on all-zero messages: levels do not depend on
the messages), without repetitions. -/
def mulLevels (Pr : Params) (prog : Program) : List ℕ :=
  (mulLevelsAux Pr prog.body (initEnv Pr prog fun _ => .exact 0)).eraseDups

def isMul : Instr → Bool
  | .mul .. | .square .. => true
  | _ => false

/-- The level of the operand of every `mul`, `square`, `relin` and `keySwitch` of the body (the
instructions at which `HPSPOVERQLEVELED` may drop limbs internally), replaying `Source.step` as
`mulLevelsAux`. -/
def opLevelsAux (Pr : Params) : List Instr → Env Pr → List ℕ
  | [], _ => []
  | i :: is, ρ =>
    let here : List ℕ := match i with
      | .mul _ a _ | .square _ a | .relin _ a | .keySwitch _ a => ((ρ a).map (·.level)).toList
      | _ => []
    match step Pr ρ i with
    | some ρ' => here ++ opLevelsAux Pr is ρ'
    | none => here

/-- The levels of the operands of the multiplications and key switches of the program. -/
def opLevels (Pr : Params) (prog : Program) : List ℕ :=
  opLevelsAux Pr prog.body (initEnv Pr prog fun _ => .exact 0)

def isSquare : Instr → Bool
  | .square .. => true
  | _ => false

def isKS : Instr → Bool
  | .relin .. | .keySwitch .. => true
  | _ => false

def isMS : Instr → Bool
  | .modSwitch .. => true
  | _ => false

def isPlainAdd : Instr → Bool
  | .addPlain .. | .subPlain .. => true
  | _ => false

/-- The first operand of an instruction: the variable whose level is the level of the
operation. -/
def operand : Instr → Var
  | .add _ a _ | .sub _ a _ | .addPlain _ a _ | .subPlain _ a _ | .mulPlain _ a _ | .mul _ a _
  | .square _ a | .mulConst _ a _ | .copy _ a | .toEval _ a | .toCoeff _ a | .automorph _ a _
  | .relin _ a | .keySwitch _ a | .modSwitch _ a | .dropLimbs _ a _ => a

/-- The level of variable `a` in `ρ` (`0` if it is not bound). -/
def levelOf {Pr : Params} (ρ : Env Pr) (a : Var) : ℕ := ((ρ a).map (·.level)).getD 0

/-- The largest plaintext bound of the program: `Spec.TraceBFV.inputBound` over its
one-component inputs (`0` if there is none). -/
def maxPlainBound (P : FullParams) (prog : Program) : ℕ :=
  ((prog.inputs.filter (·.parts = 1)).map (TraceBFV.inputBound P prog)).foldl max 0

/-- **Every plaintext input can hold every message** (item 2): the bound of every one-component
input (`Spec.TraceBFV.inputBound`: its declared bound, or `t − 1`) is at least `⌊t/2⌋`. -/
def plainBoundsOK (P : FullParams) (prog : Program) : Bool :=
  prog.inputs.all fun d =>
    decide (d.parts ≠ 1) || decide (P.src.t / 2 ≤ TraceBFV.inputBound P prog d)

/-! ## The slack of a technique -/

/-- The moduli of a ciphertext basis and an auxiliary basis are odd, at least 3 and pairwise
coprime: what the `Spec.BudgetBFV.*Slack` functions assume of them. -/
def basisOK (qs aux : List ℕ) : Bool :=
  (qs ++ aux).all (fun m => decide (3 ≤ m) && decide (m % 2 = 1)) && Budget.pairwiseCoprime? (qs ++ aux)

/-- A tolerance, or `0` for the idealised exact algorithm. -/
def tol (floatTol : Bool) (n : ℕ) : ℕ := if floatTol then n else 0

/-- P-over-Q at level `ℓ`: the slack with `P_ℓ` = the first `ℓ` auxiliary primes, and its flag. -/
def poverqAt (P : FullParams) (ft : Bool) (ℓ : ℕ) (Ps : List ℕ) : Slack × Bool :=
  let qs := P.src.qs.take ℓ
  (poverqSlack P.src.t P.src.N (P.src.modulus ℓ) (Ps.take ℓ).prod ℓ (tol ft (doubleSw ℓ))
      (tol ft (doubleSr (Ps.take ℓ))),
    decide (ℓ ≤ Ps.length) && basisOK qs (Ps.take ℓ) &&
      poverqAuxOK? P.src.t P.src.N qs (Ps.take ℓ) && (!ft || floatAuxOK? qs (Ps.take ℓ)))

/-- Leveled P-over-Q at the top level `L` with `drop ≥ 1` limbs dropped internally
(`k = L − drop` remain): the slack, and its flag. -/
def leveledAt (P : FullParams) (ft : Bool) (Ps : List ℕ) (drop : ℕ) : Slack × Bool :=
  let L := P.src.qs.length
  let k := L - drop
  (leveledSlack P.src.t P.src.N (P.src.modulus L) (P.src.modulus k) (Ps.take k).prod L
      (tol ft (doubleSw L)) (tol ft (doubleSr (P.src.qs.drop k))) (tol ft (doubleSr (Ps.take k))),
    decide (drop < L) && decide (k ≤ Ps.length) && basisOK (P.src.qs.take L) (Ps.take k) &&
      leveledAuxOK? P.src.t P.src.N (P.src.qs.take L) Ps drop &&
      (!ft || floatAuxOK? (P.src.qs.take L) (Ps.take k)))

/-- The slack of technique `m` for a multiplication at level `ℓ` at which the library drops `dr`
limbs internally (`dr` matters under `HPSPOVERQLEVELED` at the top level only), with its flag
(the checks besides `Slack.ok`: module docstring, item 4). -/
def slackAt (P : FullParams) (ft : Bool) (ℓ dr : ℕ) : Technique → Slack × Bool
  | .textbook => (⟨0, 1, true⟩, true)
  | .hps R =>
    let qs := P.src.qs.take ℓ
    let top := decide (ℓ = P.src.qs.length) && decide (1 ≤ R.length)
    if ft then
      (hpsSlack P.src.t P.src.N (P.src.modulus ℓ) R.prod (doubleSw ℓ) (doubleSw R.length)
          (doubleSr qs), top && basisOK qs R && floatAuxOK? qs R)
    else (⟨0, 1, true⟩, top && hpsAuxOK? P.src.t P.src.N qs R)
  | .poverq Ps => poverqAt P ft ℓ Ps
  | .leveled Ps =>
    if ℓ = P.src.qs.length ∧ dr ≠ 0 then leveledAt P ft Ps dr else poverqAt P ft ℓ Ps
  | .behz B msk mt =>
    let qs := P.src.qs.take ℓ
    (behzSlack P.src.t P.src.N (P.src.modulus ℓ) B.prod msk ℓ B.length mt,
      decide (ℓ = P.src.qs.length) && decide (1 ≤ B.length) && basisOK qs (B ++ [msk]) &&
        behzAuxOK? P.src.t P.src.N qs B msk mt && behzWordOK? P.src.t P.src.N qs B msk mt)

/-! ## The budget of one instruction -/

/-- The key-switching number of a `relin` or `keySwitch` of an operand at level `ℓ` at which the
library drops `dr` limbs internally; `btgt` bounds the key the switched component multiplies
(module docstring). -/
def ksAt (x : InputBFV) (ℓ dr btgt : ℕ) : ℕ :=
  let P := x.P
  match x.mul with
  | some (.leveled _) =>
    if ℓ = P.src.qs.length ∧ dr ≠ 0 then
      max (ksBoundAt P x.lay ℓ)
        (ksLeveled P.src.N (P.src.modulus ℓ / P.src.modulus (ℓ - dr))
          (ksBoundAt P x.lay (ℓ - dr)) btgt (doubleSr ((P.src.qs.take ℓ).drop (ℓ - dr))))
    else ksBoundAt P x.lay ℓ
  | _ => ksBoundAt P x.lay ℓ

/-- The plaintext-addition number of the declared method at level `ℓ`. -/
def plainAddAt (x : InputBFV) (ℓ : ℕ) : ℕ :=
  match x.plainAdd with
  | some .rounded => plainAddRoundedAt x.P ℓ (maxPlainBound x.P x.prog)
  | some .scaled => plainAddScaledAt x.P ℓ (maxPlainBound x.P x.prog)
  | _ => 0

/-- The slack charged at instruction `i`: that of the declared technique if `i` is a `mul` or a
`square`, the textbook `(0, 1)` otherwise. -/
def slackOf (x : InputBFV) (ℓ dr : ℕ) (i : Instr) : Slack :=
  match x.mul with
  | some m => if isMul i then (slackAt x.P x.floatTol ℓ dr m).1 else ⟨0, 1, true⟩
  | none => ⟨0, 1, true⟩

/-- **The budget of instruction `i`** in front of which the message-level environment is `ρ`,
with declared internal drop `dr` (module docstring). -/
def stepBudget (x : InputBFV) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) : TraceBFV.Budget :=
  let P := x.P
  let ℓ := levelOf ρ (operand i)
  let sl := slackOf x ℓ dr i
  budgetOf
    (match i with
      | .relin .. => ksAt x ℓ dr (P.src.N * P.secretBound * P.secretBound)
      | .keySwitch .. => ksAt x ℓ dr P.secretBound
      | _ => 0)
    (msBudget P) (max (mulLift P) (mulLiftNormAt P ℓ sl.e)) (mulRoundApprox P (max 1 sl.rho))
    (plainAddAt x ℓ)

/-- The side conditions of instruction `i` (module docstring, items 4 and 5). -/
def stepChecks (x : InputBFV) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) : Bool :=
  let P := x.P
  let L := P.src.qs.length
  let ℓ := levelOf ρ (operand i)
  (match x.mul with
    | some m =>
      !isMul i || (decide (1 ≤ ℓ) && decide (ℓ ≤ L) &&
        (slackAt P x.floatTol ℓ dr m).1.ok && (slackAt P x.floatTol ℓ dr m).2)
    | none => true) &&
  (match x.mul with
    | some (.leveled _) =>
      !isKS i || decide (ℓ ≠ L) || (decide (dr < ℓ) && floatAuxOK? (P.src.qs.take ℓ) [])
    | _ => true) &&
  (match x.mul with
    | some (.leveled _) => decide (dr = 0) || (decide (ℓ = L) && (isMul i || isKS i))
    | _ => true)

/-- The budgets of the instructions of a body, in order, replaying `Source.step` from `ρ` (up
to and including the first instruction it rejects); `ds` are the declared drops of these
instructions (a missing entry reads as `0`). -/
def budgetsAux (x : InputBFV) : List Instr → List ℕ → Env x.P.src → List TraceBFV.Budget
  | [], _, _ => []
  | i :: is, ds, ρ =>
    stepBudget x ρ (ds.headD 0) i ::
      match step x.P.src ρ i with
      | some ρ' => budgetsAux x is ds.tail ρ'
      | none => []

/-- `stepChecks` at every instruction of a body, along the same replay. -/
def checksAux (x : InputBFV) : List Instr → List ℕ → Env x.P.src → Bool
  | [], _, _ => true
  | i :: is, ds, ρ =>
    stepChecks x ρ (ds.headD 0) i &&
      match step x.P.src ρ i with
      | some ρ' => checksAux x is ds.tail ρ'
      | none => true

/-- The declared drops as the budget reads them: `x.drops` under `HPSPOVERQLEVELED`, nothing
otherwise. -/
def dropsOf (x : InputBFV) : List ℕ :=
  match x.mul with
  | some (.leveled _) => x.drops
  | _ => []

/-- The budgets of the instructions of the program, in order (on all-zero messages). -/
def budgetsBFV (x : InputBFV) : List TraceBFV.Budget :=
  budgetsAux x x.prog.body (dropsOf x) (initEnv x.P.src x.prog fun _ => .exact 0)

/-- A list of budgets as a function of the position (the zero budget beyond the list). -/
def budgetFn (bs : Array TraceBFV.Budget) : ℕ → TraceBFV.Budget :=
  fun k => bs.getD k (budgetOf 0 0 0 0 0)

/-- **The budget**: `budgetBFV x k` is the budget of instruction `k` of the body (module
docstring). -/
def budgetBFV (x : InputBFV) : ℕ → TraceBFV.Budget := budgetFn (budgetsBFV x).toArray

/-! ## The assumptions -/

/-- Some `relin` or `keySwitch` of the body has a nonzero declared internal drop. -/
def ksDropped (x : InputBFV) : Bool :=
  (List.range x.prog.body.length).any fun n =>
    (x.prog.body[n]?.map isKS).getD false && x.drops.getD n 0 != 0

/-- The declared technique is one of OpenFHE's four (HPS, HPSPOVERQ, HPSPOVERQLEVELED, BEHZ):
the library's decryption routines (`Spec.DecryptBFVLib`) are those of a declared library
technique. Agrees with `Challenge.BFVDecryptLib.techLib?` being `some`. -/
def libTechnique : Option Technique → Bool
  | some (.hps _) | some (.poverq _) | some (.leveled _) | some (.behz ..) => true
  | _ => false

/-- What realizability and the library's decryption rest on beyond the locked pins (module
docstring). Under `HPSPOVERQLEVELED` a key switch rests on the binary64 model only if the library
drops limbs there: with drop `0` its scaling sum is over no limb
(`Challenge.BFVMul.leveledKS_drop_zero`). `binary64Dec` comes last. -/
def assumptionsOf (x : InputBFV) : List AssumptionBFV :=
  let mults := !(mulLevels x.P.src x.prog).isEmpty
  let a : AssumptionBFV := if x.floatTol then .binary64 else .idealised
  (match x.mul with
  | some (.hps _) | some (.poverq _) => if mults then [a] else []
  | some (.leveled _) =>
    (if mults || ksDropped x then [a] else []) ++
      (if (opLevels x.P.src x.prog).contains x.P.src.qs.length then [.declaredDrops] else [])
  | _ => []) ++
  (if libTechnique x.mul then [.binary64Dec] else [])

/-! ## The decision -/

/-- The checks that do not involve the analyzer (module docstring, items 1–5). -/
def checksOK (x : InputBFV) : Bool :=
  let P := x.P
  let prog := x.prog
  schemeParamsOK? P && decide (P.src.kind = .bfv) && Budget.specialOK? P &&
    Spec.Certify.layoutOK? P x.lay && !prog.outputs.isEmpty &&
    prog.inputs.all (fun d => decide (d.parts = 1) || !d.ok P.src ||
      decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P prog d)) &&
    plainBoundsOK P prog &&
    (x.mul.isSome || !prog.body.any isMul) &&
    (x.plainAdd.isSome || !prog.body.any isPlainAdd) &&
    (x.msRound || !prog.body.any isMS) &&
    (match x.mul with
      | some (.poverq _) | some (.leveled _) => !prog.body.any isSquare
      | _ => true) &&
    (match x.mul with
      | some (.leveled _) => decide (x.drops.length = prog.body.length)
      | _ => true) &&
    (decide (P.src.t - 1 ≤ P.src.qs.headD 0 / 2) && P.src.qs.all fun q => decide (P.src.t ≤ q)) &&
    Challenge.RealizeBFV.ksDeclOK? P x.lay &&
    checksAux x prog.body (dropsOf x) (initEnv P.src prog fun _ => .exact 0)

/-- **The decision.** See the module docstring for the list of checks. -/
def certifyBFV? (x : InputBFV) : Option CertificateBFV := do
  guard (checksOK x)
  let bs := (budgetsBFV x).toArray
  let E := budgetFn bs
  let B ← refAnalyzeBFVAt x.P E x.prog
  guard (Encrypt.outputsUnderS? x.P.src x.prog)
  let outs ← x.prog.outputs.mapM fun o =>
    (refAnalyzeBFVAt x.P E { x.prog with outputs := [o] }).map fun b => (o, b)
  pure ⟨E, B, outs, mulLevels x.P.src x.prog, assumptionsOf x⟩

end Challenge.CertifyBFV
