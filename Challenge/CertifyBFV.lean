import Challenge.CertifyBFV.Defs
import Challenge.BFVMul
import Challenge.BFVMul.Float
import Challenge.BFVMul.KSLeveled
import Challenge.BFV.PerInstr

/-!
# Challenge.CertifyBFV — what a certificate of `certifyBFV?` means   (LOCKED statements; proofs in `Validation/`)

`Challenge.CertifyBFV.Defs.certifyBFV?` is the one function that decides whether `fhe_check`
prints "certified" for a BFV program. Every statement here has the form
`certifyBFV? x = some c → …`; the hypotheses of the underlying pins (`Challenge.BFV`,
`Challenge.BFVMul`) are discharged from the computation of `certifyBFV?` in the proofs.

The budget of a certificate is **one budget per instruction**: `c.budget k` for instruction `k`
of the body, and a run is `Spec.TraceBFV.RunAt` (instruction `k` meets its contract within
`c.budget k`).

* `certifyBFV?_spec`, `certifyBFV?_paramsOK`, `certifyBFV?_inputs`, `certifyBFV?_budget`: what
  the fields of the certificate are, and the propositions the checks decide.
* `certifyBFV?_sound`, `certifyBFV?_decrypts`: **every output of every run within `c.budget`
  decrypts with the secret key itself** to the message the program computes, with noise at most
  its own bound in `c.outputs`; all outputs at once.
* **Realizability, instruction by instruction** (`AtInstr x msgs n i ρ`: `i` is instruction `n`
  of the program and `ρ` the message-level environment in front of it in every run on `msgs`):
  at every `mul` (and `square`) of the program the limb-level algorithm of the declared technique
  meets the contract within `c.budget n`: the textbook algorithm (always), idealised exact HPS
  (`certifyBFV?_hps_mul`, `_square`), BEHZ (`certifyBFV?_behz_mul`, `_square`; integers only),
  idealised exact P-over-Q (`certifyBFV?_poverq_mul`) and `HPSPOVERQLEVELED` with the declared
  internal drop of that instruction (`certifyBFV?_leveled_mul`); for the HPS family each of these
  needs `x.floatTol = false`. With `x.floatTol = true` the budget is evaluated at the tolerances
  `Spec.BudgetBFV.doubleSw`/`doubleSr`, and the **library's floating-point multiplication** meets
  the contract at it for every arithmetic conforming to the standard model of binary64
  (`Spec.Float.Conforms`): `certifyBFV?_hps_mul_float`, `_hps_square_float`,
  `_poverq_mul_float`, `_leveled_mul_float`. Under `HPSPOVERQLEVELED`, at every `relin` and
  `keySwitch` of a top-level operand the **library's key switch with the declared internal
  drop** (`Challenge.BFVMul.Fl.leveledKS`: scale down, key-switch at the reduced level with the
  top-level keys, multiply back) meets the contract within `c.budget n`, for every conforming
  arithmetic: `certifyBFV?_leveled_relin`, `certifyBFV?_leveled_keySwitch`. `binary64` in
  `c.assumed` records the hypothesis that the platform conforms; it is not an unproved claim.
  `idealised` in `c.assumed` (the same cases with `x.floatTol = false`) records that the budget is
  the idealised exact algorithms', which the library does not run.
  The floating-point error is charged to the budget; nothing says the library computes the
  idealised algorithm (it does not). Every other operation is covered at `c.budget n` by the
  textbook pins of `Challenge.BFV` and `Challenge.BFVMul` (`certifyBFV?_budget` gives the
  inequalities they need, at the operand's own level).
* `certifyBFV?_mulLevels`: every `mul` and `square` a run reaches has its operand at a level of
  `c.mulLevels`.
* `certifyBFV?_textbook_run_exists`: a run within `c.budget` exists (the proof exhibits the
  all-textbook one; the statement is only `∃ σ, RunAt …`). It shows the certificate is not vacuous; it says nothing about the declared technique or the
  library's arithmetic (see its docstring).
* Discrimination: closed pins and `#guard`s at the end.

**Assumptions that no check discharges** (hypotheses of the statements):

* *The library's execution is a run* (`Spec.TraceBFV.RunAt`) within `c.budget`.
* *The inputs* meet `Spec.TraceBFV.InputsOK`: each ciphertext input encrypts its message with
  noise at most its bound (and the check that the bound satisfies `decOK`,
  `certifyBFV?_inputs`, makes the noise bound alone give that it decrypts:
  `Challenge.BFV.bfv_decrypt_of_noise`); each plaintext input is within its bound.
* *The secret* is within `secretBound` where a realizability statement says `SecretOK`.
* *The declared drops* `x.drops` are the numbers of limbs the library drops (`HPSPOVERQLEVELED`);
  `FindLevelsToDrop` is not modelled.
* *The declared technique and its auxiliary basis* (`x.mul`) are the library's: the budget is
  computed for the declared algorithm (a context declared `textbook` or with another technique
  gets that technique's budget, and the realizability statements are about that algorithm).
* *`x.floatTol`*: with `true` the budget includes the library's binary64 error; with `false` it
  is the idealised algorithm's, recorded as `idealised` in `c.assumed` (`certifyBFV?_assumed`).
* *The library's decryption*: for a technique of OpenFHE's, `binary64Dec` in `c.assumed` records
  that the statement about the library's own decryption of the outputs
  (`Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt`) rests on the platform's decryption
  conforming to `Spec.DecryptBFV.ConformsD` (`certifyBFV?_assumed`).
* *The plaintext-addition and modulus-switching methods* (`x.plainAdd`, `x.msRound`) are the
  library's (`plainAdd = some .delta` charges `0`; OpenFHE adds `⌈Q·p/t⌉`).
* *The parameters' bounds*: every secret coefficient is within `secretBound` and every
  key-switching key error within `keyNoise`, and the key-switching layout (digits, and whether
  the library uses canonical or centred representatives, `lay.canonical`) is the library's.

**For which secrets** (as for BGV, `Challenge/Certify.lean`). `certifyBFV?_sound` and
`certifyBFV?_decrypts` hold for *every* integer polynomial `s`: they take no `SecretOK`
hypothesis. This is weaker than it may sound. They are about the runs within `c.budget`, and the
budget is computed from `secretBound`: for a secret outside it nothing says that any algorithm
stays within the budget, and the statements may be about no run at all. That a run exists
(`certifyBFV?_textbook_run_exists`) and that the limb-level algorithms meet the budget (the
realizability statements above) is proved for secrets within `secretBound` only.
-/

namespace Challenge.CertifyBFV
open Spec NPoly Scheme Source Correct Spec.BudgetBFV Spec.CertifyBFV Challenge.BFV Challenge.BFVMul

/-! ## What the certificate contains -/

/-- **The fields of a certificate, and the checks behind it.** If `certifyBFV? x = some c`: the
checks of `checksOK` passed; the budget is `budgetBFV x` (one per instruction), the levels are
`mulLevels`, the recorded assumptions are `assumptionsOf x`; `c.bound` is what the reference
analysis returns on the whole program at that budget; every output is under the secret key
itself; the program has an output, `c.outputs` lists the outputs in order, and the bound of each
is what the reference analysis returns on the program with that output alone. -/
theorem certifyBFV?_spec (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    checksOK x = true ∧ c.budget = budgetBFV x ∧ c.mulLevels = mulLevels x.P.src x.prog ∧
    c.assumed = assumptionsOf x ∧
    refAnalyzeBFVAt x.P c.budget x.prog = some c.bound ∧
    Encrypt.outputsUnderS? x.P.src x.prog = true ∧
    x.prog.outputs ≠ [] ∧ c.outputs.map Prod.fst = x.prog.outputs ∧
    ∀ o ∈ x.prog.outputs, ∃ B, c.outputs.lookup o = some B ∧
      refAnalyzeBFVAt x.P c.budget { x.prog with outputs := [o] } = some B := sorry

/-- **The checks establish the side conditions** of the BFV pins: the parameters are valid at
the scheme level, BFV, the special primes are usable, the layout is usable at every level of
the chain and restricts from the top level to it, and every level at which the program
multiplies is a level of the chain. -/
theorem certifyBFV?_paramsOK (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    SchemeParamsOK x.P ∧ x.P.src.kind = .bfv ∧ Budget.SpecialOK x.P ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ x.P.src.qs.length → x.lay.okAt ℓ = true ∧
      Budget.restrictsTo x.lay x.P.src.qs.length ℓ = true) ∧
    (∀ ℓ ∈ c.mulLevels, 1 ≤ ℓ ∧ ℓ ≤ x.P.src.qs.length) := sorry

/-- **The packed-encoding condition holds**: `t − 1 ≤ ⌊q₀/2⌋`, so every stored plaintext
coefficient in `[0, t)` is the same integer in every limb under OpenFHE's packed encoder, and
`t ≤ q_i` for every limb, so that integer is its own residue in every limb (item 5a of the
checks in `Challenge.CertifyBFV.Defs`). -/
theorem certifyBFV?_encodeOK (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    x.P.src.t - 1 ≤ x.P.src.qs.headD 0 / 2 ∧ ∀ q ∈ x.P.src.qs, x.P.src.t ≤ q := sorry

/-- **The bound of every input ciphertext decrypts at its level** (`Challenge.BFV.decOK`), so
the noise bound alone gives the input hypothesis `TraceBFV.InputsOK`, including that the input
decrypts (`Challenge.BFV.bfv_decrypt_of_noise`). -/
theorem certifyBFV?_inputs (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (d : Decl) (hd : d ∈ x.prog.inputs) (hp : d.parts ≠ 1) (hok : d.ok x.P.src = true) :
    decOK x.P.src.t (x.P.src.modulus d.level) (TraceBFV.inputBound x.P x.prog d) = true := sorry

/-- **`i` is instruction number `n` of the program, and `ρ` is the message-level environment in
front of it**: the body splits as `pre ++ i :: post` with `pre` of length `n`, and `Source.step`
over `pre` from the initial environment of the inputs gives `ρ`. This `ρ` is the environment in
front of `i` in *every* run on the messages `msgs` (`Spec.TraceBFV.RunAt` advances it by
`Source.step`, which is a function), and `c.budget n` is the budget of `i` in a run. -/
def AtInstr (x : InputBFV) (msgs : Var → Msg x.P.src.t x.P.src.N) (n : ℕ) (i : Instr)
    (ρ : Env x.P.src) : Prop :=
  ∃ pre post, x.prog.body = pre ++ i :: post ∧ pre.length = n ∧
    pre.foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ

/-- **The budget of every instruction covers the textbook pins** of every operation but the
multiplication, at the operand's own level: the modulus-switching number is `msBudget`
(`stepOK_modSwitch_textbook`), the multiplication numbers are at least the textbook ones, at a
`relin` or `keySwitch` the key-switching number is at least `ksBoundAt` at the operand's level
(`Challenge.BFV.relin_realizable`, `keySwitch_realizable`; with top-level keys,
`Challenge.BFVMul.ksCore_realizable`), and at an `addPlain` or `subPlain` the plaintext-addition
number is that of the declared method at the operand's level (`stepOK_addPlain_textbook`,
`Challenge.BFVMul.stepOK_addPlain_rounded`, `stepOK_addPlain_scaled`). -/
theorem certifyBFV?_budget (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)
    (n : ℕ) (i : Instr) (ρ : Env x.P.src) (hat : AtInstr x msgs n i ρ) :
    (c.budget n).modSwitch = msBudget x.P ∧
    mulLift x.P ≤ (c.budget n).mulLift ∧ mulRound x.P ≤ (c.budget n).mulRound ∧
    (∀ d a xa, i = .relin d a ∨ i = .keySwitch d a → ρ a = some xa →
      ksBoundAt x.P x.lay xa.level ≤ (c.budget n).keySwitch) ∧
    (∀ d a p xa, i = .addPlain d a p ∨ i = .subPlain d a p → ρ a = some xa →
      (c.budget n).plainAdd = plainAddAt x xa.level) := sorry

/-! ## What "certified" means for the outputs -/

/-- **Every output decrypts with the secret key, and has noise at most its own bound.** The
program is well formed and, at the end of every run in which instruction `k` meets its contract
within the budget `E k`, each output `o` is a ciphertext that encrypts the value `Source.eval`
computes with noise at most the bound `bounds` lists for `o`, is under the secret key `s` itself,
and decrypts *with `s`* by textbook BFV decryption at its own level to that value. This is
`Challenge.BFVMul.OutputsDecryptAt` with the per-output noise bounds added. -/
def OutputsCertifiedBFV (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (bounds : List (Var × ℕ)) (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
    ∀ σ, TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ v ct m B, ρ o = some v ∧ σ o = some ct ∧
        bounds.lookup o = some B ∧ Encrypts P s B v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
        bfvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m

/-- **The BFV certificate.** If `certifyBFV? x = some c`, then for every secret key `s`, all
messages and all inputs within their bounds, every output of every run within the budgets
`c.budget` is under `s` itself, decrypts with `s` at its own level to the message the program
computes, and has noise at most its own bound in `c.outputs`: all outputs at once. (Every
secret: see "For which secrets" in the module docstring; the budget is realizable only for
secrets within `secretBound`.) -/
theorem certifyBFV?_sound (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    OutputsCertifiedBFV x.P c.budget x.prog c.outputs s msgs cts := sorry

/-- **The same, as `Challenge.BFVMul.OutputsDecryptAt`** (decryption alone). -/
theorem certifyBFV?_decrypts (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    OutputsDecryptAt x.P c.budget x.prog s msgs cts := sorry

/-! ## Realizability at `c.budget`, instruction by instruction

Each statement: the limb-level algorithm of the technique, applied to the operands of
instruction `n` of the program (a `mul`, a `square`, a `relin` or a `keySwitch`; `AtInstr`),
produces a ciphertext that meets the contract of `Spec.TraceBFV` within the budget `c.budget n`
of that instruction, under every secret within `secretBound`. `hin` is used only for the fact
that every input message is exact. -/

/-- **Level coverage: every multiplication of the program is at a level of `c.mulLevels`.**
Split the body anywhere, `x.prog.body = pre ++ i :: post`, with `i` a `mul` or a `square` whose
(first) operand is `a`. If `Source.step` over `pre` from the initial environment of the inputs
gives `ρ` and `ρ a = some xa`, then `xa.level ∈ c.mulLevels`. (`c.mulLevels` is computed on
all-zero messages; `InputsOK` is used only for the fact that every input message is exact.) -/
theorem certifyBFV?_mulLevels (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)
    (pre post : List Instr) (i : Instr) (hbody : x.prog.body = pre ++ i :: post)
    (ρ : Env x.P.src)
    (hρ : pre.foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ)
    (a : Var) (xa : Val x.P.src) (hi : (∃ d b, i = .mul d a b) ∨ ∃ d, i = .square d a)
    (hx : ρ a = some xa) :
    xa.level ∈ c.mulLevels := sorry

/-- **Textbook multiplication** meets the `mul` contract within the budget of every instruction
of the program, whatever the declared technique (the multiplication numbers of every budget are
at least the textbook ones). -/
theorem certifyBFV?_textbook_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (bfvMul x.P.src.t (x.P.src.modulus xa.level) ca cb)) (.mul d a b) := sorry

/-- **Textbook squaring** meets the `square` contract within the budget of the instruction. -/
theorem certifyBFV?_textbook_square (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (bfvMul x.P.src.t (x.P.src.modulus xa.level) ca ca)) (.square d a) := sorry

/-- **Idealised exact HPS multiplication** (`Challenge.BFVMul.hpsMul`, auxiliary basis `R`)
meets the `mul` contract within the budget of every `mul` of the program, when the budget does
not include the binary64 tolerances. -/
theorem certifyBFV?_hps_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (R : List ℕ) (hm : x.mul = some (.hps R)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (hpsMul x.P.src.t (x.P.src.qs.take xa.level) R ca cb)) (.mul d a b) := sorry

/-- **Idealised exact HPS squaring** meets the `square` contract within the budget of every
`square` of the program. -/
theorem certifyBFV?_hps_square (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (R : List ℕ) (hm : x.mul = some (.hps R)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (hpsMul x.P.src.t (x.P.src.qs.take xa.level) R ca ca)) (.square d a) := sorry

/-- **BEHZ multiplication** (`Challenge.BFVMul.behzMul`; integers only) meets the `mul` contract
within the budget of every `mul` of the program. -/
theorem certifyBFV?_behz_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (B : List ℕ) (msk mt : ℕ) (hm : x.mul = some (.behz B msk mt))
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (behzMul x.P.src.t (x.P.src.qs.take xa.level) B msk mt ca cb)) (.mul d a b) :=
  sorry

/-- **BEHZ squaring** meets the `square` contract within the budget of every `square` of the
program. -/
theorem certifyBFV?_behz_square (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (B : List ℕ) (msk mt : ℕ) (hm : x.mul = some (.behz B msk mt))
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (behzMul x.P.src.t (x.P.src.qs.take xa.level) B msk mt ca ca)) (.square d a) :=
  sorry

/-- **Idealised exact P-over-Q multiplication** (`Challenge.BFVMul.poverqMul` with the first `ℓ`
auxiliary primes) meets the `mul` contract within the budget of every `mul` of the program under
`HPSPOVERQ`, when the budget does not include the binary64 tolerances. -/
theorem certifyBFV?_poverq_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (Ps : List ℕ) (hm : x.mul = some (.poverq Ps)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (poverqMul x.P.src.t (x.P.src.qs.take xa.level) (Ps.take xa.level) ca cb))
      (.mul d a b) := sorry

/-- **Idealised exact `HPSPOVERQLEVELED` multiplication** meets the `mul` contract within the
budget of every `mul` of the program, with the internal drop declared for that instruction
(`x.drops`): at the top level with a drop `dr ≥ 1` the algorithm is
`Challenge.BFVMul.leveledMul … dr`; below the top level, or with no drop, it is
`Challenge.BFVMul.poverqMul`. When the budget does not include the binary64 tolerances. -/
theorem certifyBFV?_leveled_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (Ps : List ℕ) (hm : x.mul = some (.leveled Ps)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d
        (if xa.level = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0 then
          leveledMul x.P.src.t (x.P.src.qs.take xa.level) Ps (x.drops.getD n 0) ca cb
        else poverqMul x.P.src.t (x.P.src.qs.take xa.level) (Ps.take xa.level) ca cb))
      (.mul d a b) := sorry

/-- **The hypothesis "a run within `c.budget`" is not vacuous: the textbook run exists.** For
every secret within `secretBound` and all inputs within their bounds there is a run of the
program in which instruction `k` meets its contract within `c.budget k`, so `certifyBFV?_sound`
is not true for lack of runs.

**What this does not say.** The statement asserts only that some run exists; which run is a
property of the proof, not of the statement. The proof exhibits the run in which *every*
operation is performed by the textbook algorithm (`Challenge.BFV`: textbook multiplication,
relinearization and key switching at the operand's level, modulus switching by rounding, adding
`⌊Q/t⌋·p`); it exists because every `c.budget k` is at least the textbook numbers
(`certifyBFV?_budget`), whatever technique is declared and **whether or not `c.assumed` is
empty**. It is not a statement about the library's execution, nor about the declared technique:
that the limb-level algorithms of the declared technique meet the contracts is the content of
the realizability statements. This statement itself gives no evidence that OpenFHE's arithmetic
stays within the budget. -/
theorem certifyBFV?_textbook_run_exists (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ σ, TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
      (Trace.initCt x.P x.prog cts) σ := sorry

/-! ## Realizability of the library's floating-point multiplication (`floatTol = true`)

The multiplications of `Challenge.BFVMul.Float`: the limb-level algorithms with the two sums
computed in binary64 as OpenFHE v1.6.1 computes them (`Fl.floatSums A`), for **every** arithmetic
`A` conforming to the standard model `Spec.Float.Conforms`. They meet the contract within
`c.budget n`, whose slacks are evaluated at the tolerances `doubleSw`, `doubleSr`: the
floating-point error is charged to the budget (the library does not compute the idealised
algorithm). What these do not cover is listed in `Challenge/BFVMul/Float.lean`: machine words and
the NTT are modelled as exact modular arithmetic; squaring is covered for `HPS` only
(`certifyBFV?` rejects a `square` under the P-over-Q techniques). -/

/-- **OpenFHE's `HPS` multiplication in any conforming binary64 arithmetic** meets the `mul`
contract within the budget of every `mul` of the program. -/
theorem certifyBFV?_hps_mul_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (R : List ℕ) (hm : x.mul = some (.hps R))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (Fl.hpsMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level) R ca cb))
      (.mul d a b) := sorry

/-- **OpenFHE's `HPS` squaring in any conforming binary64 arithmetic** meets the `square`
contract within the budget of every `square` of the program. -/
theorem certifyBFV?_hps_square_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (R : List ℕ) (hm : x.mul = some (.hps R))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (Fl.hpsMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level) R ca ca))
      (.square d a) := sorry

/-- **OpenFHE's `HPSPOVERQ` multiplication in any conforming binary64 arithmetic** meets the
`mul` contract within the budget of every `mul` of the program. -/
theorem certifyBFV?_poverq_mul_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.poverq Ps))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (Fl.poverqMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level)
        (Ps.take xa.level) ca cb))
      (.mul d a b) := sorry

/-- **OpenFHE's `HPSPOVERQLEVELED` multiplication in any conforming binary64 arithmetic** meets
the `mul` contract within the budget of every `mul` of the program, with the internal drop
declared for that instruction: `Fl.leveledMul … dr` at the top level with a drop `dr ≥ 1`,
`Fl.poverqMul` below the top level or with no drop (`bfvrns-leveledshe.cpp:238-301`). -/
theorem certifyBFV?_leveled_mul_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d
        (if xa.level = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0 then
          Fl.leveledMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level) Ps
            (x.drops.getD n 0) ca cb
        else Fl.poverqMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level)
          (Ps.take xa.level) ca cb))
      (.mul d a b) := sorry

/-! ## Realizability of the library's key switch under `HPSPOVERQLEVELED`

On a top-level operand the library key-switches through `RelinearizeCore`
(`bfvrns-leveledshe.cpp:856-900`): `Challenge.BFVMul.Fl.leveledKS` with the declared drop of the
instruction (possibly `0`), the scaling sum computed in binary64, and the key switch at the
reduced level performed with the top-level keys. For every conforming arithmetic it meets the
contract within `c.budget n`. The key switch at the reduced level is the function `core` of
`Challenge.BFVMul.ksCore_realizable` (plain hybrid key switching on the digits of that level),
chosen before the secret and the keys. Below the top level the library key-switches at the
operand's own level, which `certifyBFV?_budget` covers. -/

/-- **OpenFHE's relinearisation of a top-level operand under `HPSPOVERQLEVELED`, in any
conforming binary64 arithmetic,** meets the `relin` contract within the budget of the
instruction, with the declared drop, from top-level relinearisation keys. -/
theorem certifyBFV?_leveled_relin (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A) (n : ℕ) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s keys →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.relin d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.relin d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 3 → xa.level = x.P.src.qs.length →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) (x.drops.getD n 0)
            (fun c2 => core c2
              (keys.take (x.lay.sizes (xa.level - x.drops.getD n 0)).length)) ca))
          (.relin d a) := sorry

/-- **OpenFHE's key switch of a top-level operand under `HPSPOVERQLEVELED`, in any conforming
binary64 arithmetic,** meets the `keySwitch` contract within the budget of the instruction, with
the declared drop, from top-level keys for `σ_g(s)`, `g` the operand's key. -/
theorem certifyBFV?_leveled_keySwitch (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A) (n : ℕ) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.keySwitch d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.keySwitch d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 2 → xa.level = x.P.src.qs.length →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois xa.key) s keys →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) (x.drops.getD n 0)
            (fun c1 => core c1
              (keys.take (x.lay.sizes (xa.level - x.drops.getD n 0)).length)) ca))
          (.keySwitch d a) := sorry

/-- **With no internal drop, OpenFHE's relinearisation under `HPSPOVERQLEVELED` meets the
`relin` contract for EVERY floating-point arithmetic** (no `Spec.Float.Conforms`): the scaling
inside it is over no limb (`Challenge.BFVMul.leveledKS_drop_zero`). Otherwise as
`certifyBFV?_leveled_relin`. -/
theorem certifyBFV?_leveled_relin_drop0 (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (n : ℕ) (h0 : x.drops.getD n 0 = 0) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s keys →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.relin d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.relin d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 3 → xa.level = x.P.src.qs.length →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) 0
            (fun c2 => core c2 (keys.take (x.lay.sizes xa.level).length)) ca))
          (.relin d a) := sorry

/-- **With no internal drop, OpenFHE's key switch under `HPSPOVERQLEVELED` meets the
`keySwitch` contract for EVERY floating-point arithmetic.** Otherwise as
`certifyBFV?_leveled_keySwitch`. -/
theorem certifyBFV?_leveled_keySwitch_drop0 (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (n : ℕ) (h0 : x.drops.getD n 0 = 0) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.keySwitch d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.keySwitch d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 2 → xa.level = x.P.src.qs.length →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois xa.key) s keys →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) 0
            (fun c1 => core c1 (keys.take (x.lay.sizes xa.level).length)) ca))
          (.keySwitch d a) := sorry

/-- **Which hypothesis a certificate records.** `binary64` (the platform conforms to the
standard model: `Spec.CertifyBFV.AssumptionBFV`) exactly when the budget includes the binary64
tolerances (`floatTol`) and either the technique is of the HPS family and the program
multiplies, or it is `HPSPOVERQLEVELED` and the library drops limbs inside some key switch of the
program (with drop `0` nothing is rounded: `certifyBFV?_leveled_relin_drop0`); `idealised` (the
budget is the idealised exact algorithm's, which the library does not run) in exactly the same
cases with `floatTol = false` (never both); `declaredDrops` exactly for `HPSPOVERQLEVELED` with a
multiplication or key switch of a top-level operand (`opLevels`), whose budget is computed for
the frontend's declared internal drop; `binary64Dec` (the library's decryption routines compute
their binary64 steps by an arithmetic conforming to `Spec.DecryptBFV.ConformsD`) exactly when the
declared technique is one of OpenFHE's four, i.e. neither undeclared nor the textbook algorithm:
exactly when the statement about the library's own decryption,
`Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt`, applies; it is the hypothesis that
statement takes, recorded per certificate. (The key switch after an internal drop,
formerly recorded as the unproved assumption `ksLeveled`, is proved:
`certifyBFV?_leveled_relin`, `certifyBFV?_leveled_keySwitch`.) -/
theorem certifyBFV?_assumed (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    (AssumptionBFV.binary64 ∈ c.assumed ↔
      x.floatTol = true ∧
        ((c.mulLevels ≠ [] ∧
            ((∃ R, x.mul = some (.hps R)) ∨ (∃ Ps, x.mul = some (.poverq Ps)) ∨
              ∃ Ps, x.mul = some (.leveled Ps))) ∨
          ((∃ n i, x.prog.body[n]? = some i ∧ isKS i = true ∧ x.drops.getD n 0 ≠ 0) ∧
            ∃ Ps, x.mul = some (.leveled Ps)))) ∧
    (AssumptionBFV.idealised ∈ c.assumed ↔
      x.floatTol = false ∧
        ((c.mulLevels ≠ [] ∧
            ((∃ R, x.mul = some (.hps R)) ∨ (∃ Ps, x.mul = some (.poverq Ps)) ∨
              ∃ Ps, x.mul = some (.leveled Ps))) ∨
          ((∃ n i, x.prog.body[n]? = some i ∧ isKS i = true ∧ x.drops.getD n 0 ≠ 0) ∧
            ∃ Ps, x.mul = some (.leveled Ps)))) ∧
    (AssumptionBFV.declaredDrops ∈ c.assumed ↔
      (∃ Ps, x.mul = some (.leveled Ps)) ∧ x.P.src.qs.length ∈ opLevels x.P.src x.prog) ∧
    (AssumptionBFV.binary64Dec ∈ c.assumed ↔ x.mul ≠ none ∧ x.mul ≠ some .textbook) ∧
    ¬ (AssumptionBFV.binary64 ∈ c.assumed ∧ AssumptionBFV.idealised ∈ c.assumed) := sorry

/-! ## Discrimination: what `certifyBFV?` accepts and what it rejects

At `tinyBFV` (`N = 4`, `t = 17`, `Q = 65537 · 786433`, no special prime, one limb per digit),
the program `mulProg` (a product, relinearized). The auxiliary bases are odd numbers coprime to
the chain (`basisOK`); `hpsAux` is large enough for `hpsAuxOK?` (`P > t·N·Q`), `hpsAuxSmall`
is not. The closed pins at the end are the same facts checked by the kernel. -/

/-- A product of two fresh ciphertexts, relinearized. -/
def mulProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c"], outputs := ["c"] }

/-- An input at `tinyBFV` with one limb per digit and modulus switching by rounding. -/
def tinyIn (prog : Program) (m : Option Technique) (ft : Bool) : InputBFV :=
  ⟨tinyBFV, Budget.uniformLayout 1, prog, m, ft, none, true, []⟩

def hpsAux : List ℕ := [1000003, 1000033, 1000037]
def hpsAuxSmall : List ℕ := [1000003]
def behzTech : Technique := .behz [1000003, 1000033] 1000037 65536

/-- What the guards compare: the bound, the per-output bounds, the levels, the assumptions. -/
def summary (o : Option CertificateBFV) :
    Option (ℕ × List (Var × ℕ) × List ℕ × List AssumptionBFV) :=
  o.map fun c => (c.bound, c.outputs, c.mulLevels, c.assumed)

/-- A layout that is not usable at level 1 (no digit). -/
def badLayout : Budget.KSLayout := ⟨fun ℓ => if ℓ = 1 then [] else List.replicate ℓ 1, false⟩

-- ACCEPTED, nothing assumed about multiplication: textbook, BEHZ; exact HPS and exact P-over-Q
-- record `idealised`. Every one of OpenFHE's four techniques records `binary64Dec` (last): the
-- library's decryption applies; the textbook algorithm, which OpenFHE does not run, records nothing.
#guard summary (certifyBFV? (tinyIn mulProg (some .textbook) false)) ==
  some (109100904, [("c", 109100904)], [2], [])
#guard summary (certifyBFV? (tinyIn mulProg (some behzTech) true)) ==
  some (109100936, [("c", 109100936)], [2], [.binary64Dec])
#guard summary (certifyBFV? (tinyIn mulProg (some (.hps hpsAux)) false)) ==
  some (109100904, [("c", 109100904)], [2], [.idealised, .binary64Dec])
#guard summary (certifyBFV? (tinyIn mulProg (some (.poverq [1000003, 1000033])) false)) ==
  some (109101062, [("c", 109101062)], [2], [.idealised, .binary64Dec])
-- ACCEPTED at the budget with the binary64 tolerances: HPS and P-over-Q with `floatTol`; the
-- certificate records the platform hypothesis `binary64`.
#guard summary (certifyBFV? (tinyIn mulProg (some (.hps hpsAux)) true)) ==
  some (109100915, [("c", 109100915)], [2], [.binary64, .binary64Dec])
#guard summary (certifyBFV? (tinyIn mulProg (some (.poverq [1000003, 1000033])) true)) ==
  some (109101062, [("c", 109101062)], [2], [.binary64, .binary64Dec])
-- A program that does not multiply rests on no tolerance, whatever the technique (only the
-- library's decryption, `binary64Dec`).
#guard summary (certifyBFV? (tinyIn { mulProg with body := [.add "c" "a" "b"] }
  (some (.hps hpsAux)) true)) == some (137, [("c", 137)], [], [.binary64Dec])
-- `HPSPOVERQLEVELED` at `sealBFV` (four limbs), one limb dropped inside the relinearization:
-- ACCEPTED with `idealised` recorded for the idealised budget, with `binary64` when the budget
-- includes the tolerances; the key-switching number of the relinearization is `ksLeveled`, far
-- above `ksBoundAt` (which is what it is with no drop). REJECTED without one declared drop per
-- instruction. At `tinyBFV` the same drop makes the key-switching number overflow.
def sealLeveled (ft : Bool) (drops : List ℕ) : InputBFV :=
  ⟨sealBFV, Budget.uniformLayout 1 true,
    { mulProg with inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩] },
    some (.leveled [17592186044423, 17592186044435, 17592186044443, 17592186044447]), ft,
    none, true, drops⟩
#guard (summary (certifyBFV? (sealLeveled false [0, 1]))).map (·.2.2.2) ==
  some [.idealised, .declaredDrops, .binary64Dec]
#guard (summary (certifyBFV? (sealLeveled true [0, 1]))).map (·.2.2.2) ==
  some [.binary64, .declaredDrops, .binary64Dec]
#guard (summary (certifyBFV? (sealLeveled true [0, 0]))).map (·.2.2.2) ==
  some [.binary64, .declaredDrops, .binary64Dec]
-- A program that only rotates (automorphism, key switch): with drop 0 inside the key switch
-- nothing is rounded and only `declaredDrops` (and `binary64Dec`) is recorded; with a drop,
-- `binary64` too.
#guard (summary (certifyBFV? { sealLeveled true [0, 0] with
  prog := { (sealLeveled true []).prog with
    body := [.automorph "c" "a" 3, .keySwitch "c" "c"], outputs := ["c"] } })).map (·.2.2.2) ==
  some [.declaredDrops, .binary64Dec]
#guard (summary (certifyBFV? { sealLeveled true [0, 1] with
  prog := { (sealLeveled true []).prog with
    body := [.automorph "c" "a" 3, .keySwitch "c" "c"], outputs := ["c"] } })).map (·.2.2.2) ==
  some [.binary64, .declaredDrops, .binary64Dec]
#guard (certifyBFV? (sealLeveled false [0])).isNone
-- REJECTED: a nonzero drop declared at an instruction where the library drops nothing (an
-- addition); ACCEPTED with drop 0 there.
#guard (certifyBFV? { sealLeveled false [0, 1, 1] with
  prog := { (sealLeveled false []).prog with
    body := [.mul "c" "a" "b", .relin "c" "c", .add "c" "c" "c"] } }).isNone
#guard (certifyBFV? { sealLeveled false [0, 1, 0] with
  prog := { (sealLeveled false []).prog with
    body := [.mul "c" "a" "b", .relin "c" "c", .add "c" "c" "c"] } }).isSome
#guard (certifyBFV? (sealLeveled false [0, 4])).isNone
#guard ((certifyBFV? (sealLeveled false [0, 0])).map fun c => (c.budget 1).keySwitch) ==
  some (ksBoundAt sealBFV (Budget.uniformLayout 1 true) 4)
#guard ((certifyBFV? (sealLeveled false [0, 1])).map fun c =>
    decide ((c.budget 1).keySwitch = ksLeveled sealBFV.src.N
      (sealBFV.src.modulus 4 / sealBFV.src.modulus 3) (ksBoundAt sealBFV (Budget.uniformLayout 1 true) 3)
      (sealBFV.src.N * sealBFV.secretBound * sealBFV.secretBound)
      (doubleSr (sealBFV.src.qs.drop 3))) &&
    decide (2 ^ 40 * ksBoundAt sealBFV (Budget.uniformLayout 1 true) 4 < (c.budget 1).keySwitch)) ==
  some true
-- the budget of the multiplication (instruction 0) does not pay for the drop of instruction 1
#guard ((certifyBFV? (sealLeveled false [0, 1])).map fun c => (c.budget 0).mulRound) ==
  ((certifyBFV? (sealLeveled false [0, 0])).map fun c => (c.budget 0).mulRound)
#guard (certifyBFV? ⟨tinyBFV, Budget.uniformLayout 1, mulProg, some (.leveled [1000003, 1000033]),
  false, none, true, [0, 1]⟩).isNone
-- REJECTED: an HPS auxiliary basis too small for `hpsAuxOK?`.
#guard (certifyBFV? (tinyIn mulProg (some (.hps hpsAuxSmall)) false)).isNone
#guard !Challenge.BFVMul.hpsAuxOK? 17 4 [65537, 786433] hpsAuxSmall
-- REJECTED: a layout not usable at level 1.
#guard (certifyBFV? ⟨tinyBFV, badLayout, mulProg, some .textbook, false, none, true, []⟩).isNone
-- REJECTED: an output left under a rotated key (accepted once it is key-switched back).
#guard (certifyBFV? (tinyIn
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 3], outputs := ["o"] }
  none false)).isNone
#guard (certifyBFV? (tinyIn
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 3, .keySwitch "o" "o"],
    outputs := ["o"] } none false)).isSome
-- REJECTED: a program the reference analysis rejects (four squarings overflow).
#guard (certifyBFV? (tinyIn
  { inputs := [⟨"a", 2, 2, 1, 1⟩],
    body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
    outputs := ["c"] } (some .textbook) false)).isNone
-- REJECTED: a square under P-over-Q; a product with no technique declared.
#guard (certifyBFV? (tinyIn
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "c" "a", .relin "c" "c"], outputs := ["c"] }
  (some (.poverq [1000003, 1000033])) false)).isNone
#guard (certifyBFV? (tinyIn mulProg none false)).isNone
-- The packed-encoding condition `t − 1 ≤ ⌊q₀/2⌋` (q₀ = 65537 at `tinyBFV`, so `⌊q₀/2⌋ = 32768`),
-- on a program that only adds: ACCEPTED at t = 32769 (t − 1 = 32768), REJECTED at t = 32771.
/-- `tinyBFV` with plaintext modulus `t`, adding two fresh ciphertexts. -/
def addAtT (t : ℕ) : InputBFV :=
  { tinyIn { mulProg with body := [.add "c" "a" "b"] } none false with
    P := { tinyBFV with src := { tinyBFV.src with t := t } } }
#guard (certifyBFV? (addAtT 32769)).isSome
#guard (certifyBFV? (addAtT 32771)).isNone
#guard schemeParamsOK? (addAtT 32771).P

/-- `certifyBFV?` accepts `mulProg` with BEHZ, recording no assumption about the multiplication,
only `binary64Dec` (the library's decryption). -/
theorem certifyBFV?_accepts_behz :
    (certifyBFV? (tinyIn mulProg (some behzTech) true)).map (·.assumed) = some [.binary64Dec] := sorry

/-- `certifyBFV?` accepts `mulProg` with exact HPS (`floatTol = false`), recording that the
budget is the idealised algorithm's (`idealised`), and `binary64Dec`. -/
theorem certifyBFV?_accepts_hps :
    (certifyBFV? (tinyIn mulProg (some (.hps hpsAux)) false)).map (·.assumed) =
      some [.idealised, .binary64Dec] := sorry

/-- `certifyBFV?` accepts `mulProg` with HPS and the binary64 tolerances, recording the
platform hypothesis `binary64`, and `binary64Dec`. -/
theorem certifyBFV?_accepts_hps_binary64 :
    (certifyBFV? (tinyIn mulProg (some (.hps hpsAux)) true)).map (·.assumed) =
      some [.binary64, .binary64Dec] := sorry

/-- `certifyBFV?` rejects an HPS auxiliary basis that fails `hpsAuxOK?`. -/
theorem certifyBFV?_rejects_badAux :
    (certifyBFV? (tinyIn mulProg (some (.hps hpsAuxSmall)) false)).isSome = false := sorry

/-- `certifyBFV?` rejects a layout that is not usable at some level. -/
theorem certifyBFV?_rejects_badLayout :
    (certifyBFV? ⟨tinyBFV, badLayout, mulProg, some .textbook, false, none, true, []⟩).isSome =
      false := sorry

/-- `certifyBFV?` rejects an output left under a rotated key. -/
theorem certifyBFV?_rejects_rotatedKey :
    (certifyBFV? (tinyIn
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 3], outputs := ["o"] }
      none false)).isSome = false := sorry

/-- `certifyBFV?` rejects a program the reference analysis rejects (a noise overflow). -/
theorem certifyBFV?_rejects_overflow :
    (certifyBFV? (tinyIn
      { inputs := [⟨"a", 2, 2, 1, 1⟩],
        body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
        outputs := ["c"] } (some .textbook) false)).isSome = false := sorry

/-- `certifyBFV?` rejects a `square` under P-over-Q (no `square` pin covers the library's two
lifts). -/
theorem certifyBFV?_rejects_square_poverq :
    (certifyBFV? (tinyIn
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "c" "a", .relin "c" "c"],
        outputs := ["c"] } (some (.poverq [1000003, 1000033])) false)).isSome = false := sorry

/-- `certifyBFV?` rejects a plaintext modulus with `t − 1 > ⌊q₀/2⌋` (OpenFHE's packed encoder
stores a coefficient above `⌊q₀/2⌋` as `x − q₀` in the limbs after the first), and accepts the
same program at `t − 1 = ⌊q₀/2⌋`. -/
theorem certifyBFV?_rejects_packedWindow :
    (certifyBFV? (addAtT 32769)).isSome = true ∧ (certifyBFV? (addAtT 32771)).isSome = false :=
  sorry

end Challenge.CertifyBFV
