import Spec.BudgetBFV
import Challenge.Source

/-!
# Challenge.BFV.Defs — the BFV noise headline: definitions   (LOCKED definitions)

This file imports only trusted code (`Spec/`) and other locked files. It defines

* `NoiseSoundBFV analyze`: what it means for a BFV noise analyzer to be certified. Whenever
  `analyze` returns a bound `B` for a source program, every ciphertext-level run of the program
  (`Spec.TraceBFV`), on inputs within their bounds, ends with outputs that encrypt what
  `Spec.Source.eval` computes with noise at most `B`. For BFV, "encrypts"
  (`Spec.Scheme.BFVEncrypts`) contains exact decryption.
* `refAnalyzeBFV`: the reference analyzer, a worst-case analysis in the infinity norm of the BFV
  noise `e = [phase − ⌊Q/t⌋·m]_Q` (message representatives in `[0, t)`, as `BFVEncrypts` has
  them). `Challenge.BFV` states its soundness.
* the textbook operations used as realizability witnesses.

**The rules** (`refBoundBFV`), at modulus `Q` of the result's level, `r = Q mod t`,
`Δ = ⌊Q/t⌋`, operand bounds `B`, `B₁`, `B₂`, plaintext bound `b` (`‖p‖∞`):

| operation | bound |
|---|---|
| `add`, `sub` | `B₁ + B₂ + r` |
| `addPlain`, `subPlain` | `B + r·⌈b/t⌉ + E.plainAdd` |
| `mulPlain` | `N·b·(B + r)` |
| `mulConst c` | `|c|·(B + r)` |
| `automorph` | `B + r` |
| `copy`, `toEval`, `toCoeff` | `B` |
| `relin`, `keySwitch` | `B + E.keySwitch` |
| `modSwitch` | `⌊B/q_last⌋ + E.modSwitch + r` (`r` of the new modulus; two-component operand only) |
| `mul`, `square` | `mulBound` (two-component operands only: "The domain" below) |

The `r` terms are carries: `Δ·t = Q − r`, so reducing a message modulo `t` by `k·t` moves `k·r`
into the noise. With `M = t − 1`, `K = E.mulLift + 1`, `R = E.mulRound`:

  `mulBound = N·(B₁+B₂)·(t·K + M) + r·N·M·(2K + 1)
              + ⌊(Q·R + 2N·(r·Δ·M² + r·M·(B₁+B₂) + t·B₁·B₂)) / (2Q)⌋`.

For the textbook algorithm `K = ⌊N·B_s/2⌋ + 2`, so the leading term is about
`t·N·(N·B_s/2 + 3)·(B₁+B₂)` (compare Fan–Vercauteren 2012, Lemma 2: `2·t·δ_R·E·(δ_R·‖s‖ + 1)`
with `δ_R = N`).

**The domain** (`domainOK`). `E.mulLift`, `E.mulRound` and `E.modSwitch` are single numbers,
and the values `Spec.BudgetBFV.certified` gives them are proved achievable for *two-component*
operands only (`Challenge.BFV.stepOK_mul_textbook`, `stepOK_square_textbook`,
`stepOK_modSwitch_textbook`): the lift and the rounding error of a product, and the rounding
error of a modulus switch, grow with the number of components. So the analysis *rejects* a
`mul` or `square` with an operand that does not have exactly two components and a `modSwitch` of
a value that does not have exactly two components (relinearize first). Every other accepted
operation has a realizability pin for every number of components the analysis accepts
(`Challenge/BFV/Domain.lean`, which also pins that every program accepted at the certified
budget has a run: `certified_run_exists`).

| operation | accepted when (besides `Source.step` and the bound's `decOK`) |
|---|---|
| `mul` | both operands are ciphertexts with exactly 2 components |
| `square`, `modSwitch` | the operand is a ciphertext with exactly 2 components |
| `add`, `sub`, `mulConst`, `automorph` | ciphertext operands (any number of components) |
| `addPlain`, `subPlain`, `mulPlain` | a ciphertext (any number of components) and a one-component plaintext |
| `relin` | a 3-component ciphertext under `s` (`Source.step`) |
| `keySwitch` | a 2-component ciphertext (`Source.step`) |
| `copy`, `toEval`, `toCoeff` | any tracked value |

**Decryption.** A bound `B` is accepted at modulus `Q` only if `2·(t·B + r·(t−1)) < Q`
(`decOK`); then `BFVEncrypts`' noise clause implies its decryption clause
(`Challenge.BFV.bfv_decrypt_of_noise`).
-/

namespace Challenge.BFV
open Spec NPoly Scheme Source Correct
open Spec.TraceBFV (Bnd)

/-! ## The headline predicate -/

/-- The type of a BFV noise analyzer: parameters, the backend's error budget, source program ↦ a
bound on the noise of every output, or `none` (reject). -/
abbrev NoiseAnalyzerBFV : Type := FullParams → TraceBFV.Budget → Source.Program → Option ℕ

/-- **Noise soundness (BFV).** If the parameters are valid at the scheme level and `analyze`
returns `B`, then for every secret key, all messages and all inputs within their bounds
(`TraceBFV.InputsOK`: ciphertext inputs encrypt their messages with noise at most their declared
bound or `P.inputNoise`; one-component inputs are plaintext polynomials within their declared
bound or `t − 1`): the source program is well formed, and at the end of *every* ciphertext-level
run of it in which each operation meets its BFV phase contract (`Spec.TraceBFV`: any backend, any
representation, within the budget `E`), each output variable holds a ciphertext that encrypts
the message `Source.eval` computes, with noise at most `B`.

For BFV, "encrypts" includes exact decryption (`Challenge.BFV.encrypts_bfv_decrypts`). -/
def NoiseSoundBFV (analyze : NoiseAnalyzerBFV) : Prop :=
  ∀ (P : FullParams) (E : TraceBFV.Budget) (prog : Source.Program) (B : ℕ),
    SchemeParamsOK P → P.src.kind = .bfv → analyze P E prog = some B →
    ∀ (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
      (cts : Var → List (IntPoly P.src.N)), TraceBFV.InputsOK P s prog msgs cts →
      ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
        ∀ σ, TraceBFV.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
          ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct

/-- `analyze` rejects every program outside BFV. -/
def NoiseRejectsNonBFV (analyze : NoiseAnalyzerBFV) : Prop :=
  ∀ (P : FullParams) (E : TraceBFV.Budget) (prog : Source.Program),
    P.src.kind ≠ .bfv → analyze P E prog = none

/-! ## The reference analyzer -/

/-- The noise bound of a BFV product (module docstring). `K` is `E.mulLift`, `R` is
`E.mulRound`, `B₁`, `B₂` the operands' bounds. -/
def mulBound (N t Q K R B₁ B₂ : ℕ) : ℕ :=
  let r := Q % t
  let M := t - 1
  let K₁ := K + 1
  N * (B₁ + B₂) * (t * K₁ + M) + r * N * M * (2 * K₁ + 1) +
    (Q * R + 2 * N * (r * (Q / t) * M * M + r * M * (B₁ + B₂) + t * B₁ * B₂)) / (2 * Q)

/-- The decryption condition: noise `B` at modulus `Q` decrypts correctly. -/
def decOK (t Q B : ℕ) : Bool := decide (2 * (t * B + Q % t * (t - 1)) < Q)

/-- The reference bound for the destination of one instruction, at the level `ℓ` of its result,
from the bounds `β` of its operands. -/
def refBoundBFV (P : FullParams) (E : TraceBFV.Budget) (ℓ : ℕ) (β : Var → Option Bnd) :
    Instr → Option Bnd
  | .add _ a b | .sub _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) => some (.ct (x + y + P.src.modulus ℓ % P.src.t))
    | _, _ => none
  | .addPlain _ a p | .subPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) =>
      some (.ct (x + P.src.modulus ℓ % P.src.t * ((y + P.src.t - 1) / P.src.t) + E.plainAdd))
    | _, _ => none
  | .mulPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) =>
      some (.ct (P.src.N * y * (x + P.src.modulus ℓ % P.src.t)))
    | _, _ => none
  | .mul _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) =>
      some (.ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x y))
    | _, _ => none
  | .square _ a =>
    match β a with
    | some (.ct x) =>
      some (.ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x x))
    | _ => none
  | .mulConst _ a c =>
    match β a with
    | some (.ct x) => some (.ct (c.natAbs * (x + P.src.modulus ℓ % P.src.t)))
    | _ => none
  | .copy _ a | .toEval _ a | .toCoeff _ a => β a
  | .automorph _ a _ =>
    match β a with
    | some (.ct x) => some (.ct (x + P.src.modulus ℓ % P.src.t))
    | _ => none
  | .relin _ a | .keySwitch _ a =>
    match β a with
    | some (.ct x) => some (.ct (x + E.keySwitch))
    | _ => none
  | .modSwitch _ a =>
    match β a, P.src.qs[ℓ]? with
    | some (.ct x), some q => some (.ct (x / q + E.modSwitch + P.src.modulus ℓ % P.src.t))
    | _, _ => none
  | .dropLimbs _ _ _ => none

/-- Whether a tracked bound is acceptable at level `ℓ`: a ciphertext bound must satisfy the
decryption condition; a plaintext bound is not constrained. -/
def bndOK (P : FullParams) (ℓ : ℕ) : Bnd → Bool
  | .ct b => decOK P.src.t (P.src.modulus ℓ) b
  | .pt _ => true

/-- The domain of the product and modulus-switching rules (module docstring): `mul` and `square`
need operands with exactly two components, `modSwitch` an operand with exactly two components
(`ρ` records the number of components of every variable). Outside it no realizability pin
supports charging `E.mulLift`, `E.mulRound`, `E.modSwitch`, and the analysis rejects. -/
def domainOK {Pr : Params} (ρ : Env Pr) : Instr → Bool
  | .mul _ a b =>
    match ρ a, ρ b with
    | some x, some y => x.parts == 2 && y.parts == 2
    | _, _ => false
  | .square _ a | .modSwitch _ a =>
    match ρ a with
    | some x => x.parts == 2
    | none => false
  | _ => true

/-- Run the reference analysis over a program body: the instruction must be in the domain of the
rules (`domainOK`), `Source.step` checks well-formedness and tracks levels, `refBoundBFV` gives
each new bound, which must be acceptable at its level. -/
def refRunBFV (P : FullParams) (E : TraceBFV.Budget) :
    List Instr → Env P.src → (Var → Option Bnd) → Option (Env P.src × (Var → Option Bnd))
  | [], ρ, β => some (ρ, β)
  | i :: is, ρ, β => do
    guard (domainOK ρ i)
    let ρ' ← step P.src ρ i
    let v ← ρ' (Trace.dst i)
    let b ← refBoundBFV P E v.level β i
    guard (bndOK P v.level b)
    refRunBFV P E is ρ' (fun y => if y = Trace.dst i then some b else β y)

/-- The ciphertext bound of an output, if it is tracked as a ciphertext. -/
def ctBound (β : Var → Option Bnd) (o : Var) : Option ℕ :=
  match β o with
  | some (.ct b) => some b
  | _ => none

/-- The reference analyzer: BFV only; every input declaration must be well formed; a
one-component input starts as a plaintext, any other as a ciphertext, at
`TraceBFV.inputBound`; every output must be a ciphertext; the result is the largest bound among
the outputs. Well-formedness is checked on all-zero messages (it does not depend on them). -/
def refAnalyzeBFV : NoiseAnalyzerBFV := fun P E prog => do
  guard (P.src.kind = .bfv)
  guard (prog.inputs.all fun d => d.ok P.src)
  let β₀ : Var → Option Bnd := fun x => (prog.inputs.find? (·.name = x)).map fun d =>
    if d.parts = 1 then .pt (TraceBFV.inputBound P prog d) else .ct (TraceBFV.inputBound P prog d)
  let (ρ, β) ← refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0) β₀
  guard (prog.outputs.all fun o => (ρ o).isSome)
  let bs ← prog.outputs.mapM (ctBound β)
  pure (bs.foldl max 0)

/-! ## The same analysis with one budget per instruction

`Spec.TraceBFV.RunAt` lets every instruction have its own budget `E k` (`k` its position in the
program). `refRunBFVAt` and `refAnalyzeBFVAt` are `refRunBFV` and `refAnalyzeBFV` with the bound of
instruction `k` computed from `E k`; nothing else differs, and at a constant budget they are the
same functions (`Challenge.BFV.refAnalyzeBFVAt_const`). -/

/-- `refRunBFV` with the budget `E n` for the instruction at position `n` (the position of the
first instruction of the list; the recursion counts up). -/
def refRunBFVAt (P : FullParams) (E : ℕ → TraceBFV.Budget) :
    ℕ → List Instr → Env P.src → (Var → Option Bnd) → Option (Env P.src × (Var → Option Bnd))
  | _, [], ρ, β => some (ρ, β)
  | n, i :: is, ρ, β => do
    guard (domainOK ρ i)
    let ρ' ← step P.src ρ i
    let v ← ρ' (Trace.dst i)
    let b ← refBoundBFV P (E n) v.level β i
    guard (bndOK P v.level b)
    refRunBFVAt P E (n + 1) is ρ' (fun y => if y = Trace.dst i then some b else β y)

/-- The type of a BFV noise analyzer with one budget per instruction. -/
abbrev NoiseAnalyzerBFVAt : Type :=
  FullParams → (ℕ → TraceBFV.Budget) → Source.Program → Option ℕ

/-- `refAnalyzeBFV` with the budget `E k` for instruction `k` of the body. -/
def refAnalyzeBFVAt : NoiseAnalyzerBFVAt := fun P E prog => do
  guard (P.src.kind = .bfv)
  guard (prog.inputs.all fun d => d.ok P.src)
  let β₀ : Var → Option Bnd := fun x => (prog.inputs.find? (·.name = x)).map fun d =>
    if d.parts = 1 then .pt (TraceBFV.inputBound P prog d) else .ct (TraceBFV.inputBound P prog d)
  let (ρ, β) ← refRunBFVAt P E 0 prog.body (initEnv P.src prog fun _ => .exact 0) β₀
  guard (prog.outputs.all fun o => (ρ o).isSome)
  let bs ← prog.outputs.mapM (ctBound β)
  pure (bs.foldl max 0)

/-- **Noise soundness (BFV) with one budget per instruction**: `NoiseSoundBFV` with
`Spec.TraceBFV.RunAt` in the place of `Run`. If `analyze` returns `B`, every output of every run
in which instruction `k` meets its contract within `E k` encrypts the message `Source.eval`
computes with noise at most `B`. -/
def NoiseSoundBFVAt (analyze : NoiseAnalyzerBFVAt) : Prop :=
  ∀ (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Source.Program) (B : ℕ),
    SchemeParamsOK P → P.src.kind = .bfv → analyze P E prog = some B →
    ∀ (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
      (cts : Var → List (IntPoly P.src.N)), TraceBFV.InputsOK P s prog msgs cts →
      ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
        ∀ σ, TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog msgs)
            (Trace.initCt P prog cts) σ →
          ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct

/-! ## Textbook operations (realizability witnesses) -/

variable {N : ℕ}

/-- `⌊t·a/Q⌉`, coefficient by coefficient. -/
def scaleRound (t Q : ℕ) (a : IntPoly N) : IntPoly N := ⟨fun i => roundDiv (t * a.coeff i) Q⟩

/-- Textbook BFV multiplication (Fan–Vercauteren 2012) of two 2-component ciphertexts modulo `Q`:
centred representatives, tensor product over `ℤ[X]/(X^N+1)`, every component scaled by `t/Q`
and rounded. -/
def bfvMul (t Q : ℕ) (c d : List (IntPoly N)) : List (IntPoly N) :=
  (Challenge.Source.tensor (c.map fun x => centered (ofInt Q x))
    (d.map fun x => centered (ofInt Q x))).map (scaleRound t Q)

/-- BFV modulus switching of one component by `q`: `⌊c/q⌉`. -/
def bfvModSwitchComp (q : ℕ) (c : IntPoly N) : IntPoly N := ⟨fun i => roundDiv (c.coeff i) q⟩

/-- Textbook plaintext addition: `c₀ + Δ·p`. -/
def bfvAddPlain (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) : List (IntPoly N) :=
  Challenge.Source.padZip (· + ·) c [((Q / t : ℕ) : ℤ) • p]

end Challenge.BFV
