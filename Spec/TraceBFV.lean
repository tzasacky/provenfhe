import Spec.Trace

/-!
# Spec.TraceBFV — what it means to run a BFV source program on ciphertexts   (TRUSTED)

The BFV counterpart of `Spec.Trace` (which is BGV). `Spec.Source` gives a program its meaning on
messages; this file says what any correct implementation of each BFV operation must do to the
*phase* `⟨ct, (1, s, s², …)⟩ mod Q` of a ciphertext, and nothing more. Decryption and noise
(`Spec.Scheme.bfvDecrypt`, `BFVEncrypts`: phase `= ⌊Q/t⌋·m + e`) are functions of the phase alone.

Notation: `Q` the modulus of the result's level, `t` the plaintext modulus, `Δ = ⌊Q/t⌋`,
`φ_a` the operand's phase in `Z_Q[X]/(X^N+1)`, `Φ_a` its centred lift to `ℤ[X]/(X^N+1)`
(coefficients in `(-Q/2, Q/2]`).

| operation | contract on the result's phase `φ` |
|---|---|
| `add`, `sub` | `φ = φ_a ± φ_b` |
| `addPlain`, `subPlain` | `φ = φ_a ± Δ·φ_p + δ` with `‖δ‖∞ ≤ E.plainAdd` (`φ_p = p mod Q` is the phase of the one-component plaintext `[p]`, the *unscaled* plaintext polynomial; `δ = 0` for the textbook `c₀ ± Δ·p`; libraries that add `⌊Q·p/t⌉` instead declare `δ`) |
| `mulPlain` | `φ = φ_a · φ_p` (every component times the unscaled plaintext polynomial) |
| `mulConst c` | `φ = c · φ_a` |
| `copy`, `toEval`, `toCoeff` | `φ = φ_a` |
| `automorph g` | `φ = σ_g(φ_a)`, read under `σ_g` of the operand's key |
| `relin`, `keySwitch` | `φ = φ_a + e` with `‖e‖∞ ≤ E.keySwitch`; the result is under `s` (no divisibility by `t`, unlike BGV) |
| `modSwitch` | `φ = (Φ_a + δ) / q_last` exactly, with `q_last ∣ Φ_a + δ` and `‖δ‖∞ ≤ q_last · E.modSwitch` (rounding `⌊c/q_last⌉` of every component of a two-component ciphertext does this with `E.modSwitch = ⌈(1 + N·B_s)/2⌉`: `Challenge.BFV.stepOK_modSwitch_textbook`) |
| `mul`, `square` | scale-invariant product, below |
| `dropLimbs` | not a BFV operation (`False`) |

**Multiplication** (Fan–Vercauteren 2012, §4, "FV.SH.Mul"; the same map is the specification of
the RNS variants of Bajard–Eynard–Hasan–Zucca 2016 and Halevi–Polyakov–Shoup 2018). The textbook
algorithm lifts both ciphertexts to centred integer representatives, takes their tensor product
over `ℤ[X]/(X^N+1)` (no reduction modulo `Q`), and scales every component by `t/Q` with rounding:
`c' = ⌊t·(c ⊗ d)/Q⌉ mod Q`. On phases: the *integer* phase of the centred representatives,
`Ψ_a = Σ cᵢ·sⁱ` over `ℤ`, is congruent to `Φ_a` modulo `Q` but not equal to it; write
`Ψ_a = Φ_a + Q·k_a`. The tensor product has integer phase `Ψ_a·Ψ_b`, and the rounding of the
components changes the phase by `ρ₀ + ρ₁·s + ρ₂·s²` with `|ρᵢ| ≤ 1/2`. So the contract is:

  there are integer polynomials `k_a`, `k_b`, `X`, `D` with
  `‖k_a‖∞, ‖k_b‖∞ ≤ E.mulLift`,  `2·‖D‖∞ ≤ Q · E.mulRound`,
  `Q·X = t·(Φ_a + Q·k_a)·(Φ_b + Q·k_b) + D`  in `ℤ[X]/(X^N+1)`,  and  `φ = X mod Q`.

`E.mulLift` bounds how far the lift an implementation multiplies is from the centred phase, in
units of `Q` (textbook, two components, secret bound `B_s`: `⌊(2 + N·B_s)/2⌋`); `E.mulRound`
bounds twice the phase error of the scaling, in units of `1` (textbook: `1 + N·B_s + (N·B_s)²`).
An RNS multiplication (approximate base extension, approximate scaling) meets the same contract
with larger values of the two numbers, and then nothing else about it enters a noise claim. That
an algorithm meets the contract with given numbers is proved only where a locked realizability
pin says so: the textbook algorithm on two-component operands (`Challenge.BFV.stepOK_mul_textbook`,
`stepOK_square_textbook`), and the limb-level RNS algorithms of `Challenge/BFVMul.lean` with the
slacks of `Spec.BudgetBFV` (`Spec/BudgetBFVRns.lean`): BEHZ with integers only; the HPS family
with exact arithmetic in place of OpenFHE's binary64 steps, and with those steps as the library
computes them under the standard model of binary64 (`Challenge.BFVMul.Float`, `Spec.Float`). The two
numbers do not depend on the operands' numbers of components, while what an algorithm needs
does (the lift of a three-component value is of order `N²·B_s²`), so the reference analyzer
rejects products of values that do not have exactly two components
(`Challenge.BFV.domainOK`).

**Plaintexts.** A plaintext operand is a one-component value `[p]`, `p` the plaintext polynomial
itself (*not* multiplied by `Δ`), with `p ≡ m (mod t)` and `‖p mod Q‖∞` small: what
`Spec.Scheme.BGVEncrypts` says of the one-component "ciphertext" `[p]` (`PlainOK`). It is not a BFV
encryption of `m` (that would be `Δ·m`), so a noise claim for BFV distinguishes ciphertext inputs
(two or more components, `Spec.Correct.Encrypts`) from plaintext inputs (one component, `PlainOK`):
`InputsOK`.

Statements that use this file assume `P.src.kind = .bfv`.
-/

namespace Spec.TraceBFV
open NPoly Scheme Source Correct

/-- What a BFV backend declares about its approximate operations (worst case, every level). -/
structure Budget where
  /-- Bound on `‖e‖∞`, the phase error one `relin` or `keySwitch` adds. -/
  keySwitch : ℕ
  /-- Bound on `‖δ‖∞ / q_last`, the phase error one `modSwitch` adds after the division. -/
  modSwitch : ℕ
  /-- Bound on `‖k‖∞`, where the integer phase `mul` multiplies is `Φ + Q·k` (module
  docstring). -/
  mulLift : ℕ
  /-- Bound on `2·‖D‖∞ / Q`: twice the phase error of the scaling by `t/Q` in `mul`. -/
  mulRound : ℕ
  /-- Bound on `‖δ‖∞`, the deviation of `addPlain`/`subPlain` from adding exactly `Δ·p`. -/
  plainAdd : ℕ
  deriving Repr

/-- What a worst-case analysis tracks for a variable of a BFV program: a ciphertext with noise at
most `b`, or a plaintext polynomial with coefficients at most `b` in absolute value. (Used by the
reference analyzer in `Challenge.BFV`.) -/
inductive Bnd
  | ct (b : ℕ)
  | pt (b : ℕ)
  deriving DecidableEq, Repr

variable (P : FullParams)

/-- A plaintext operand: one or more components whose phase, centred modulo `Q`, is congruent to
the message modulo `t` and has every coefficient of absolute value at most `b`. For the
one-component `[p]` the phase is `p mod Q`, under every key. -/
def PlainOK (s : IntPoly P.src.N) (b : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N)) : Prop :=
  ct.length = v.parts ∧ ∃ m, v.msg = .exact m ∧
    BGVEncrypts P.src.t b (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) m

/-- The bound a noise claim assumes of input `d`: its declared bound (`Program.bounds`) if it has
one; otherwise `P.inputNoise` for a ciphertext and `t - 1` for a plaintext (one component), which
every encoding with coefficients in `[0, t)` or centred meets. -/
def inputBound (prog : Program) (d : Decl) : ℕ :=
  (prog.boundOf d.name).getD (if d.parts = 1 then P.src.t - 1 else P.inputNoise)

/-- The input hypothesis of a BFV noise claim, by the *first* declaration of each name (as
`Source.initEnv` and `Trace.initCt`): a one-component input is a plaintext within its bound
(`PlainOK`); any other input is a ciphertext that encrypts its message with noise within its bound
(`Spec.Correct.Encrypts`, which for BFV is `BFVEncrypts`: phase `= ⌊Q/t⌋·m + e`, `‖e‖∞ ≤` bound,
and it decrypts to `m`). -/
def InputsOK (s : IntPoly P.src.N) (prog : Program) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∀ x d, prog.inputs.find? (·.name = x) = some d →
    if d.parts = 1 then PlainOK P s (inputBound P prog d) (inputVal P msgs d) (cts x)
    else Encrypts P s (inputBound P prog d) (inputVal P msgs d) (cts x)

/-- One step of a ciphertext-level BFV run. As `Spec.Trace.StepOK`: `ρ`, `ρ'` are the
message-level environments before and after the instruction, `σ`, `σ'` the ciphertext
environments; the step assigns the destination some ciphertext with the recorded number of
components whose phase meets the instruction's contract (module docstring). -/
def StepOK (E : Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P)
    (i : Instr) : Prop :=
  ∃ v ct, ρ' (Trace.dst i) = some v ∧ ct.length = v.parts ∧ σ' = σ.set (Trace.dst i) ct ∧
    let Q := P.src.modulus v.level
    let t := P.src.t
    let φ := Trace.phaseAt P Q v.key s ct
    match i with
    | .add _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = Trace.phaseAt P Q x.key s ca + Trace.phaseAt P Q y.key s cb
    | .sub _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = Trace.phaseAt P Q x.key s ca - Trace.phaseAt P Q y.key s cb
    | .addPlain _ a b => ∃ x y ca cb δ, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧
        σ b = some cb ∧ normInf δ ≤ E.plainAdd ∧
        φ = Trace.phaseAt P Q x.key s ca + ((Q / t : ℕ) : ZMod Q) • Trace.phaseAt P Q y.key s cb
          + ofInt Q δ
    | .subPlain _ a b => ∃ x y ca cb δ, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧
        σ b = some cb ∧ normInf δ ≤ E.plainAdd ∧
        φ = Trace.phaseAt P Q x.key s ca - ((Q / t : ℕ) : ZMod Q) • Trace.phaseAt P Q y.key s cb
          + ofInt Q δ
    | .mulPlain _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧
        σ b = some cb ∧ φ = Trace.phaseAt P Q x.key s ca * Trace.phaseAt P Q y.key s cb
    | .mul _ a b => ∃ x y ca cb ka kb X D, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧
        σ b = some cb ∧
        normInf ka ≤ E.mulLift ∧ normInf kb ≤ E.mulLift ∧ 2 * normInf D ≤ Q * E.mulRound ∧
        (Q : ℤ) • X =
          (t : ℤ) • ((centered (Trace.phaseAt P Q x.key s ca) + (Q : ℤ) • ka) *
                     (centered (Trace.phaseAt P Q y.key s cb) + (Q : ℤ) • kb)) + D ∧
        φ = ofInt Q X
    | .square _ a => ∃ x ca ka X D, ρ a = some x ∧ σ a = some ca ∧
        normInf ka ≤ E.mulLift ∧ 2 * normInf D ≤ Q * E.mulRound ∧
        (Q : ℤ) • X =
          (t : ℤ) • ((centered (Trace.phaseAt P Q x.key s ca) + (Q : ℤ) • ka) *
                     (centered (Trace.phaseAt P Q x.key s ca) + (Q : ℤ) • ka)) + D ∧
        φ = ofInt Q X
    | .mulConst _ a c => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = (c : ZMod Q) • Trace.phaseAt P Q x.key s ca
    | .copy _ a | .toEval _ a | .toCoeff _ a => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = Trace.phaseAt P Q x.key s ca
    | .automorph _ a g => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = automorph g (Trace.phaseAt P Q x.key s ca)
    | .relin _ a | .keySwitch _ a => ∃ x ca e, ρ a = some x ∧ σ a = some ca ∧
        normInf e ≤ E.keySwitch ∧ φ = Trace.phaseAt P Q x.key s ca + ofInt Q e
    | .modSwitch _ a => ∃ x ca δ q, ρ a = some x ∧ σ a = some ca ∧
        P.src.qs[x.level - 1]? = some q ∧
        let Φ := centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca)
        normInf δ ≤ q * E.modSwitch ∧ (∀ j, (q : ℤ) ∣ Φ.coeff j + δ.coeff j) ∧
        φ = ofInt Q ⟨fun j => (Φ.coeff j + δ.coeff j) / q⟩
    | .dropLimbs _ _ _ => False

/-- `Run E s body ρ σ σf`: starting from message environment `ρ` and ciphertext environment `σ`,
some ciphertext-level execution of `body` in which every step meets its BFV contract ends in
`σf`. -/
def Run (E : Budget) (s : IntPoly P.src.N) :
    List Instr → Env P.src → Trace.CtEnv P → Trace.CtEnv P → Prop
  | [], _, σ, σf => σf = σ
  | i :: is, ρ, σ, σf =>
    ∃ ρ' σ', step P.src ρ i = some ρ' ∧ StepOK P E s ρ ρ' σ σ' i ∧ Run E s is ρ' σ' σf

/-- `RunAt E s n body ρ σ σf`: as `Run`, with one budget **per instruction**: the instruction at
position `j` of `body` meets its BFV contract within the budget `E (n + j)`. `n` is the position
of the first instruction of `body` in the whole program (`0` for a whole program), so `E k` is
the budget of instruction `k` of the program. A library whose approximate operations depend on
where they stand in the program declares its budget this way (OpenFHE's `HPSPOVERQLEVELED` drops,
inside a multiplication or a key switch, a number of limbs that depends on the operand's
history). The step contract `StepOK` is the same as in `Run`; with a constant `E` this is `Run`
(`Challenge.BFV.runAt_const`). -/
def RunAt (E : ℕ → Budget) (s : IntPoly P.src.N) :
    ℕ → List Instr → Env P.src → Trace.CtEnv P → Trace.CtEnv P → Prop
  | _, [], _, σ, σf => σf = σ
  | n, i :: is, ρ, σ, σf =>
    ∃ ρ' σ', step P.src ρ i = some ρ' ∧ StepOK P (E n) s ρ ρ' σ σ' i ∧
      RunAt E s (n + 1) is ρ' σ' σf

end Spec.TraceBFV
