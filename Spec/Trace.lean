import Spec.Correct

/-!
# Spec.Trace — what it means to run a BGV source program on ciphertexts   (TRUSTED)

`Spec.Source` gives a program its meaning on *messages*. A noise claim is about *ciphertexts*:
"if the inputs have noise at most `b`, the outputs decrypt correctly". To state it without naming
a library, a compiler or a machine, this file says what any correct implementation of each
operation must do, and nothing more.

**Phase contracts.** The phase of a ciphertext is `⟨ct, (1, s, s², …)⟩ mod Q`; decryption and
noise (`Spec.Scheme`) are functions of the phase alone. Each operation is specified by what it does
to the phase:

| operation | contract on the result's phase `φ` |
|---|---|
| `add`, `sub`, `addPlain`, `subPlain` | `φ = φ_a ± φ_b` (the operands may have different numbers of components; a plaintext operand is the one-component `[p]`, with phase `p`) |
| `mul`, `square`, `mulPlain` | `φ = φ_a · φ_b` |
| `mulConst c` | `φ = c · φ_a` |
| `copy`, `toEval`, `toCoeff` | `φ = φ_a` |
| `automorph g` | `φ = σ_g(φ_a)`, read under `σ_g` of the operand's key |
| `dropLimbs k` | `φ = Φ_a mod Q'`: the centered phase of the operand, as an integer polynomial, reduced modulo the shorter modulus `Q'` (keeping the same components does this) |
| `relin`, `keySwitch` | `φ = φ_a + e` with `‖e‖∞ ≤ E.keySwitch` and `t ∣ e`; the result is under `s` |
| `modSwitch` | `φ = (Φ_a + δ) / q_last` exactly, where `q_last` is the modulus the operand's level ends with (it must exist), `Φ_a` is the centered phase of the operand, `t ∣ δ`, `q_last ∣ Φ_a + δ` and `‖δ‖∞ ≤ q_last · E.modSwitchAt k`, `k` the number of components of the operand: `E.modSwitchOne` for `k = 1` (a plaintext, whose correction has no secret-dependent term), `E.modSwitch` for `k = 2`, `E.modSwitchMany k` for any other `k` (`k ≥ 3`: a product that has not been relinearized) |

plus: the result has the number of components `Source.step` records. A step may produce *any*
ciphertext meeting its contract; the textbook algorithms do (componentwise sum, tensor product,
`⌊(c + δ_c)/q⌉` with `δ_c = t·[−c·t⁻¹]_q`, any key-switching method: the pins of
`Challenge.Trace` and `Challenge.Budget` say for which operands and budgets), and so does any RNS,
NTT or Montgomery realization of them. `Budget` is the only thing a backend has to declare: how
much phase error its key switching adds, and how much its modulus switching of a value with `k`
components adds (`Budget.modSwitchAt`: one number each for `k = 1` and `k = 2`, a function of `k`
beyond). The modulus-switching error of the textbook algorithm grows with `k`: the correction of
the phase is `Σ_{i<k} sⁱ·δ_i`, one term per component, so no single number can be right for a
two-component ciphertext and for a three-component product.

These are the BGV contracts. `mul` and `modSwitch` differ for BFV (scale-invariant product;
`Spec.TraceBFV`). Statements that use this file assume `P.src.kind = .bgv`.

Nothing here mentions storage, limbs, memory or keys. Key material enters only through
`Budget.keySwitch`.
-/

namespace Spec.Trace
open NPoly Scheme Source Correct

/-- The variable an instruction defines. -/
def dst : Instr → Var
  | .add d _ _ | .sub d _ _ | .mul d _ _ | .square d _ | .mulConst d _ _ | .copy d _
  | .toEval d _ | .toCoeff d _ | .relin d _ | .keySwitch d _ | .automorph d _ _
  | .modSwitch d _ | .addPlain d _ _ | .subPlain d _ _ | .mulPlain d _ _
  | .dropLimbs d _ _ => d

/-- What a backend declares about its approximate operations (worst case, every level). (No
`Repr` instance: one field is a function.) -/
structure Budget where
  /-- Bound on `‖e‖∞`, the phase error one `relin` or `keySwitch` adds. -/
  keySwitch : ℕ
  /-- Bound on `‖δ‖∞ / q_last`, the phase error one `modSwitch` of a 2-component ciphertext adds
  after the division. The textbook switch (centered correction, `|δ_c| ≤ t·q_last/2` per
  component) meets `⌈t · (1 + N · secretBound) / 2⌉`
  (`Challenge.Trace.stepOK_modSwitch_textbook`). -/
  modSwitch : ℕ
  /-- The same for a `modSwitch` whose operand has exactly one component (a plaintext operand
  `[p]`, which the automatic scaling modes of OpenFHE switch before a plaintext operation). Its
  phase is `p` itself, so the correction is `δ = t·[−p·t⁻¹]_{q_last}` with no secret-dependent
  term: the centred correction meets `⌈t / 2⌉`
  (`Challenge.Budget.modSwitch_realizable_one`). -/
  modSwitchOne : ℕ
  /-- The same for a `modSwitch` whose operand has `k` components, as a function of `k`; read
  only at `k ∉ {1, 2}` (`Budget.modSwitchAt`), in practice `k ≥ 3`: a product that has not been
  relinearized (OpenFHE `EvalMultNoRelin` then `ModReduce`; HEIR's lazy relinearization). The
  textbook switch corrects every component, and the phase correction is `Σ_{i<k} sⁱ·δ_i`, so it
  meets `⌈t · Σ_{i<k} (N · secretBound)ⁱ / 2⌉`
  (`Spec.Budget.msBudgetAt`, `Challenge.Budget.modSwitch_realizable_parts`). -/
  modSwitchMany : ℕ → ℕ

/-- The declared modulus-switching bound for an operand with `k` components: `modSwitchOne` for
`k = 1`, `modSwitch` for `k = 2`, `modSwitchMany k` otherwise. -/
def Budget.modSwitchAt (E : Budget) (k : ℕ) : ℕ :=
  if k = 1 then E.modSwitchOne else if k = 2 then E.modSwitch else E.modSwitchMany k

variable (P : FullParams)

/-- Ciphertext environments: each defined variable holds its components (integer
representatives, as in `Spec.Correct`). -/
abbrev CtEnv := Var → Option (List (IntPoly P.src.N))

/-- Assign one variable. -/
def CtEnv.set {P : FullParams} (σ : CtEnv P) (x : Var) (ct : List (IntPoly P.src.N)) : CtEnv P :=
  fun y => if y = x then some ct else σ y

/-- The phase of `ct` modulo `Q` under the key `σ_key(s)`. For `Q = P.src.modulus v.level` and
`key = v.key` this is the phase that `Spec.Correct.Encrypts P s B v ct` decrypts and bounds
(`Challenge.Trace.encrypts_bgv_iff_phase`). -/
def phaseAt (Q key : ℕ) (s : IntPoly P.src.N) (ct : List (IntPoly P.src.N)) : Poly Q P.src.N :=
  phase (ofInt Q (automorph key s)) (ct.map (ofInt Q))

/-- The initial ciphertext environment: each declared input holds its ciphertext. -/
def initCt (prog : Program) (cts : Var → List (IntPoly P.src.N)) : CtEnv P :=
  fun x => (prog.inputs.find? (·.name = x)).map fun _ => cts x

/-- Every input with a declared bound (`Program.bounds`) meets it: its ciphertext encrypts its
message with noise at most the declared bound. For a plaintext input (one component, `[p]`) this
says `‖p mod Q‖∞ ≤ bound` and `p ≡ m (mod t)`. Inputs without a declared bound are covered by
`Spec.Correct.InputsOK` alone. -/
def BoundsOK (s : IntPoly P.src.N) (prog : Program) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∀ x d b, prog.inputs.find? (·.name = x) = some d → prog.boundOf x = some b →
    Encrypts P s b (inputVal P msgs d) (cts x)

/-- One step of a ciphertext-level run. `ρ`, `ρ'` are the message-level environments before and
after the instruction (`ρ' = Source.step ρ i`); `σ`, `σ'` the ciphertext environments. The step
assigns the destination some ciphertext `ct` with the recorded number of components whose phase
meets the instruction's contract (module docstring), and changes nothing else. -/
def StepOK (E : Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ σ' : CtEnv P) (i : Instr) :
    Prop :=
  ∃ v ct, ρ' (dst i) = some v ∧ ct.length = v.parts ∧ σ' = σ.set (dst i) ct ∧
    let Q := P.src.modulus v.level
    let φ := phaseAt P Q v.key s ct
    match i with
    | .add _ a b | .addPlain _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = phaseAt P Q x.key s ca + phaseAt P Q y.key s cb
    | .sub _ a b | .subPlain _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = phaseAt P Q x.key s ca - phaseAt P Q y.key s cb
    | .mul _ a b | .mulPlain _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = phaseAt P Q x.key s ca * phaseAt P Q y.key s cb
    | .square _ a => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = phaseAt P Q x.key s ca * phaseAt P Q x.key s ca
    | .mulConst _ a c => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = (c : ZMod Q) • phaseAt P Q x.key s ca
    | .copy _ a | .toEval _ a | .toCoeff _ a => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = phaseAt P Q x.key s ca
    | .automorph _ a g => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = automorph g (phaseAt P Q x.key s ca)
    | .relin _ a | .keySwitch _ a => ∃ x ca e, ρ a = some x ∧ σ a = some ca ∧
        normInf e ≤ E.keySwitch ∧ (∀ j, (P.src.t : ℤ) ∣ e.coeff j) ∧
        φ = phaseAt P Q x.key s ca + ofInt Q e
    | .modSwitch _ a => ∃ x ca δ q, ρ a = some x ∧ σ a = some ca ∧
        P.src.qs[x.level - 1]? = some q ∧
        let Φ := centered (phaseAt P (P.src.modulus x.level) x.key s ca)
        normInf δ ≤ q * E.modSwitchAt x.parts ∧
        (∀ j, (P.src.t : ℤ) ∣ δ.coeff j) ∧
        (∀ j, (q : ℤ) ∣ Φ.coeff j + δ.coeff j) ∧
        φ = ofInt Q ⟨fun j => (Φ.coeff j + δ.coeff j) / q⟩
    | .dropLimbs _ a _ => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = ofInt Q (centered (phaseAt P (P.src.modulus x.level) x.key s ca))

/-- `Run E s body ρ σ σf`: starting from message environment `ρ` and ciphertext environment `σ`,
some ciphertext-level execution of `body` in which every step meets its contract ends in `σf`. -/
def Run (E : Budget) (s : IntPoly P.src.N) : List Instr → Env P.src → CtEnv P → CtEnv P → Prop
  | [], _, σ, σf => σf = σ
  | i :: is, ρ, σ, σf =>
    ∃ ρ' σ', step P.src ρ i = some ρ' ∧ StepOK P E s ρ ρ' σ σ' i ∧ Run E s is ρ' σ' σf

end Spec.Trace
