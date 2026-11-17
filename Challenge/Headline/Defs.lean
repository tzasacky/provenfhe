import Spec.Budget
import Challenge.Corpus
import Challenge.Source

/-!
# Challenge.Headline.Defs — what the headline theorem says   (LOCKED definitions)

This file imports only trusted code (`Spec/`) and other locked files. It defines, as predicates
over an *arbitrary* checker, what it means for that checker to be certified:

* **H6, noise.** `NoiseSoundBGV analyze`: whenever `analyze` returns a bound `B` for a source
  program, every ciphertext-level run of the program (`Spec.Trace`), on inputs with noise at most
  `P.inputNoise`, ends with outputs that decrypt exactly to what `Spec.Source.eval` computes and
  have noise at most `B`.

A checker that rejects everything satisfies the soundness predicate. So the headline also has
acceptance predicates the same checker must satisfy: a locked reference analyzer (`refAnalyze`,
the textbook worst-case analysis) that it must never be worse than, on any program, and a named
program it must accept.

The checker itself is a *definition hole*: `Challenge/Headline.lean` instantiates these
predicates at `FHE.Holes.analyze`. Nothing in this file depends on it.
-/

namespace Challenge.Headline
open Spec NPoly Scheme Layout Source Correct Challenge.Corpus

/-! ## H6: noise -/

/-- The type of a noise analyzer: parameters, the backend's error budget, source program ↦ a
bound on the noise of every output, or `none` (reject). -/
abbrev NoiseAnalyzer : Type := FullParams → Trace.Budget → Source.Program → Option ℕ

/-- **H6 (BGV).** If the parameters are valid at the scheme level (`SchemeParamsOK`: no bound on
the size of the primes, nothing about storage) and `analyze` returns `B`, then for every secret
key, all messages and all input ciphertexts encrypting them with noise at most `P.inputNoise`
(and at most the input's own declared bound, if the program declares one in `Program.bounds`:
`Trace.BoundsOK`; this is how a plaintext input, a one-component value, gets the bound of its
encoding instead of that of a fresh ciphertext):
the source program is well formed, and at the end of *every* ciphertext-level run of it in which
each operation meets its phase contract (`Spec.Trace`: any backend, any representation, key
switching and modulus switching within the budget `E`), each output variable holds a ciphertext
that encrypts the message `Source.eval` computes, with noise at most `B`.

For BGV, "encrypts" includes exact decryption (`encrypts_bgv_decrypts`): acceptance means the
program decrypts correctly, not only that a number bounds the noise. -/
def NoiseSoundBGV (analyze : NoiseAnalyzer) : Prop :=
  ∀ (P : FullParams) (E : Trace.Budget) (prog : Source.Program) (B : ℕ),
    SchemeParamsOK P → P.src.kind = .bgv → analyze P E prog = some B →
    ∀ (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
      (cts : Var → List (IntPoly P.src.N)), InputsOK P s prog msgs cts →
      Trace.BoundsOK P s prog msgs cts →
      ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
        ∀ σ, Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
          ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct

/-! ### The reference analyzer (yardstick)

The textbook worst-case analysis in the infinity norm of the phase: `B_a + B_b` for a sum,
`N · B_a · B_b` for a product (the same two rules for a plaintext operand, whose bound is the
norm of the plaintext), `|c| · B` for a constant multiple, `B` for a copy, an automorphism or
dropping limbs, `B + E.keySwitch` for a key switch, `⌊B / q_last⌋ + E.modSwitchAt k` for a
modulus switch of an operand with `k` components (`Trace.Budget.modSwitchAt`: `E.modSwitchOne`
for `k = 1`, `E.modSwitch` for `k = 2`, `E.modSwitchMany k` otherwise, e.g. for a three-component
product that has not been relinearized; rejected if the level has no `q_last`); every
intermediate bound must stay below `Q/2` at its level. It is defined here so that a certified
analyzer can be required to be at least this good.

Each rule is the worst case of the matching `Spec.Trace` contract, for whatever numbers of
components `Source.step` accepts; that the contracts can be met at the budget computed from the
parameters (`Spec.Budget.certified`), for every step this analysis accepts, is
`Challenge.Budget.certified_run_exists`. -/

/-- The reference bound for the destination of one instruction, from the bounds `β` of its
operands (`ρ` supplies the operand's level and number of components for `modSwitch`). -/
def refBound (P : FullParams) (E : Trace.Budget) (ρ : Env P.src) (β : Var → Option ℕ) :
    Instr → Option ℕ
  | .add _ a b | .sub _ a b | .addPlain _ a b | .subPlain _ a b => do
    let x ← β a; let y ← β b
    pure (x + y)
  | .mul _ a b | .mulPlain _ a b => do
    let x ← β a; let y ← β b
    pure (P.src.N * x * y)
  | .square _ a => do
    let x ← β a
    pure (P.src.N * x * x)
  | .mulConst _ a c => do
    let x ← β a
    pure (c.natAbs * x)
  | .copy _ a | .toEval _ a | .toCoeff _ a | .automorph _ a _ | .dropLimbs _ a _ => β a
  | .relin _ a | .keySwitch _ a => do
    let x ← β a
    pure (x + E.keySwitch)
  | .modSwitch _ a => do
    let x ← β a; let v ← ρ a
    let q ← P.src.qs[v.level - 1]?
    pure (x / q + E.modSwitchAt v.parts)

/-- Run the reference analysis over a program body: `Source.step` checks well-formedness and
tracks levels, `refBound` gives each new bound, which must satisfy `2 · B < Q` at its level. -/
def refRun (P : FullParams) (E : Trace.Budget) :
    List Instr → Env P.src → (Var → Option ℕ) → Option (Env P.src × (Var → Option ℕ))
  | [], ρ, β => some (ρ, β)
  | i :: is, ρ, β => do
    let ρ' ← step P.src ρ i
    let b ← refBound P E ρ β i
    let v ← ρ' (Trace.dst i)
    guard (2 * b < P.src.modulus v.level)
    refRun P E is ρ' (fun y => if y = Trace.dst i then some b else β y)

/-- The reference analyzer: BGV only; every input declaration must be well formed
(`Source.Decl.ok`, as `Source.eval` requires); inputs start at `P.inputNoise`, or at their
declared bound (`Program.bounds`) if that is smaller; the result is the
largest bound among the outputs. Well-formedness is checked on all-zero messages (it does not
depend on the messages). -/
def refAnalyze : NoiseAnalyzer := fun P E prog => do
  guard (P.src.kind = .bgv)
  guard (prog.inputs.all fun d => d.ok P.src)
  let β₀ : Var → Option ℕ := fun x => (prog.inputs.find? (·.name = x)).map fun _ =>
    match prog.boundOf x with
    | some b => min b P.inputNoise
    | none => P.inputNoise
  let (ρ, β) ← refRun P E prog.body (initEnv P.src prog fun _ => .exact 0) β₀
  guard (prog.outputs.all fun o => (ρ o).isSome)
  let bs ← prog.outputs.mapM β
  pure (bs.foldl max 0)

/-- **Tightness.** On every scheme-level valid BGV instance and every program the reference analysis accepts,
`analyze` also accepts, with a bound no larger. Together with `NoiseSoundBGV` this rules out an
analyzer that rejects everything, one that special-cases a test corpus, and one that returns
uselessly large bounds.

For the current hole this is trivially true: `FHE.Holes.analyze` *is* `refAnalyze` (by
definition, through `FHE.Noise.analyze`), so `Challenge.Headline.analyze_tight` says `B ≤ B`. The
predicate is a constraint on future analyzers only (one that tracks more than a worst-case norm
must still accept everything the textbook analysis accepts, with bounds at least as good). -/
def NoiseTightBGV (analyze : NoiseAnalyzer) : Prop :=
  ∀ (P : FullParams) (E : Trace.Budget) (prog : Source.Program) (B : ℕ),
    SchemeParamsOK P → P.src.kind = .bgv → refAnalyze P E prog = some B →
      ∃ B', analyze P E prog = some B' ∧ B' ≤ B

/-- A depth-2 program: `y = (a + b) · c` on fresh 2-component ciphertexts at level 2. -/
def addMulProg : Source.Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩, ⟨"c", 2, 2, 1, 1⟩],
    body := [.add "x" "a" "b", .mul "y" "x" "c"], outputs := ["y"] }

/-- A budget for programs with no key switching or modulus switching. -/
def noBudget : Trace.Budget := ⟨0, 0, 0, fun _ => 0⟩

-- What the reference analysis returns on the corpus (compiled evaluation, checked at build time).
#guard refAnalyze FullParams.tinyBGV noBudget addProg == some 128
#guard refAnalyze FullParams.tinyBGV noBudget mulProg == some 16384
#guard refAnalyze .exampleBGV31 noBudget addProg == some (2 ^ 22)
#guard refAnalyze .exampleBGV31 noBudget mulProg == some (2 ^ 56)
#guard refAnalyze .exampleBGV31 noBudget addMulProg == some (2 ^ 57)
-- The largest of these is below `Q/2` (`Q = 1073872897 · 1074266113 ≈ 2^60.0009`).
#guard 2 * 2 ^ 57 < 1073872897 * 1074266113
-- One squaring of a fresh input is accepted at `exampleBGV31`, with `N · inputNoise² = 2⁵⁶`.
#guard refAnalyze .exampleBGV31 noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "a" "a"], outputs := ["a"] } == some (2 ^ 56)
-- Rejections: an undefined operand; noise past `Q/2` (two squarings at `exampleBGV31`).
#guard refAnalyze FullParams.tinyBGV noBudget { addProg with body := [.add "c" "a" "nope"] } == none
#guard refAnalyze .exampleBGV31 noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "a" "a", .square "a" "a"],
    outputs := ["a"] } == none
-- Rejections: an input declared above the modulus chain (level 3 of 2), at level 0, with no
-- parts, or under an even key; and a modulus switch below level 1.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 3, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 3, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 0, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 0, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 2⟩], body := [.copy "c" "a"], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 1, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] } == none
-- Accepted: a modulus switch from level 2 (`⌊64 / 786433⌋ + 0`), and a key switch of an input
-- declared under `σ₃(s)`.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] } == some 0
#guard refAnalyze FullParams.tinyBGV ⟨5, 0, 0, fun _ => 0⟩
  { inputs := [⟨"a", 2, 2, 1, 3⟩], body := [.keySwitch "c" "a"], outputs := ["c"] } == some 69
-- A modulus switch of a one-component value (a plaintext) is charged `E.modSwitchOne`; of a
-- two-component ciphertext, `E.modSwitch`; of a value with `k ≥ 3` components (here the
-- three-component product, and the four-component product of it with a fresh ciphertext),
-- `E.modSwitchMany k`.
#guard refAnalyze FullParams.tinyBGV ⟨0, 7, 3, fun k => 100 * k⟩
  { inputs := [⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)], body := [.modSwitch "c" "p"],
    outputs := ["c"] } == some 3
#guard refAnalyze FullParams.tinyBGV ⟨0, 7, 3, fun k => 100 * k⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] } == some 7
#guard refAnalyze FullParams.tinyBGV ⟨0, 7, 3, fun k => 100 * k⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .modSwitch "c" "c"], outputs := ["c"] } == some 300
#guard refAnalyze FullParams.tinyBGV ⟨0, 7, 3, fun k => 100 * k⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .mul "c" "c" "a", .modSwitch "c" "c"], outputs := ["c"] }
  == some (4 * 16384 * 64 / 786433 + 400)
#guard [1, 2, 3, 4].map (Trace.Budget.modSwitchAt ⟨0, 7, 3, fun k => 100 * k⟩) == [3, 7, 300, 400]

/-! The same at the budget computed from the parameters (`Spec.Budget.certified`; one limb per
digit, which does not matter here: no key switch).

A modulus switch of the three-component product of two fresh ciphertexts, before
relinearization (OpenFHE `EvalMultNoRelin` then `ModReduce`): `⌊16384 / 786433⌋ + ⌈17·(1+4+16)/2⌉
= 179`. An earlier version of `refBound` charged the two-component budget here and returned 43;
the textbook switch of such a product reaches 85 (`Challenge.Budget`, "The many-component budget
is needed"), so 43 was not a bound that the real algorithm meets. -/

/-- `c = a · b` without relinearization, then a modulus switch of the three components. -/
def mulSwitchProg : Source.Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .modSwitch "c" "c"], outputs := ["c"] }

#guard refAnalyze FullParams.tinyBGV (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1)) mulSwitchProg
  == some 179
#guard 16384 / 786433 + (17 * (1 + 4 + 16) + 1) / 2 == 179
#guard (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1)).modSwitch == 43
-- One and two components are charged `msBudgetOne` and `msBudget`, as before.
#guard Budget.msBudgetAt FullParams.tinyBGV 1 == Budget.msBudgetOne FullParams.tinyBGV &&
  Budget.msBudgetAt FullParams.tinyBGV 2 == Budget.msBudget FullParams.tinyBGV
#guard Budget.msBudgetAt .exampleBGV31 1 == Budget.msBudgetOne .exampleBGV31 &&
  Budget.msBudgetAt .exampleBGV31 2 == Budget.msBudget .exampleBGV31
#guard [1, 2, 3].map (Budget.msBudgetAt FullParams.tinyBGV) == [9, 43, 179]
#guard [1, 2, 3].map (Budget.msBudgetAt .exampleBGV31) == [32769, 536911873, 8796764151809]
#guard refAnalyze FullParams.tinyBGV (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := [⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)], body := [.modSwitch "c" "p"],
    outputs := ["c"] } == some 9
#guard refAnalyze FullParams.tinyBGV (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] } == some 43
-- At `exampleBGV31` the three-component budget (`≈ 2⁴³`) does not fit under `q₀/2 ≈ 2²⁹`: rejected.
#guard refAnalyze .exampleBGV31 (Budget.certified .exampleBGV31 (Budget.uniformLayout 1))
  mulSwitchProg == none

/-! Plaintext operands, mixed numbers of components, dropped limbs (`tinyBGV`: `N = 4`,
`inputNoise = 64`, `q₀ = 65537`). -/

-- A plaintext input (one component) with declared bound 8: `64 + 8` and `N · 64 · 8`.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)],
    body := [.addPlain "c" "a" "p"], outputs := ["c"] } == some 72
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)],
    body := [.subPlain "c" "a" "p"], outputs := ["c"] } == some 72
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)],
    body := [.mulPlain "c" "a" "p"], outputs := ["c"] } == some 2048
-- Without a declared bound the plaintext counts as any other input; a declared bound above
-- `inputNoise` gains nothing; a bound declared for another name is not used.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩],
    body := [.addPlain "c" "a" "p"], outputs := ["c"] } == some 128
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 1000)],
    body := [.addPlain "c" "a" "p"], outputs := ["c"] } == some 128
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("q", 8)],
    body := [.addPlain "c" "a" "p"], outputs := ["c"] } == some 128
-- The plaintext is used under any key (here the ciphertext is under `σ₃(s)`); with `add` it is not.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 3⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)],
    body := [.addPlain "c" "a" "p"], outputs := ["c"] } == some 72
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 3⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)],
    body := [.add "c" "a" "p"], outputs := ["c"] } == none
-- Rejections: a "plaintext" operand with two components; a plaintext at another level.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 2, 2, 1, 1⟩],
    body := [.addPlain "c" "a" "p"], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 2, 2, 1, 1⟩],
    body := [.mulPlain "c" "a" "p"], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 1, 1, 1⟩], bounds := [("p", 8)],
    body := [.mulPlain "c" "a" "p"], outputs := ["c"] } == none
-- A sum of a 3-component product and a fresh 2-component ciphertext: `4 · 64² + 64`.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .add "c" "c" "a"], outputs := ["c"] } == some 16448
-- Dropping one limb keeps the bound; dropping every limb is ill-formed; a bound that fits `Q/2`
-- at level 2 (`4 · 16384² = 2³⁰`) but not `q₀/2` at level 1 is rejected.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.dropLimbs "c" "a" 1], outputs := ["c"] } == some 64
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.dropLimbs "c" "a" 2], outputs := ["c"] } == none
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "a" "a", .square "a" "a"],
    outputs := ["a"] } == some (2 ^ 30)
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩],
    body := [.square "a" "a", .square "a" "a", .dropLimbs "a" "a" 1], outputs := ["a"] } == none
-- `dropLimbs` does not divide: unlike `modSwitch` the bound does not shrink.
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "a" "a", .dropLimbs "a" "a" 1],
    outputs := ["a"] } == some 16384
#guard refAnalyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "a" "a", .modSwitch "a" "a"],
    outputs := ["a"] } == some 0

/-- The reference analyzer rejects every program with an ill-formed input declaration (in
particular one declared above the modulus chain), whatever the rest of the program is. -/
theorem refAnalyze_badDecl (P : FullParams) (E : Trace.Budget) (prog : Source.Program) (d : Decl)
    (hd : d ∈ prog.inputs)
    (h : d.parts = 0 ∨ d.level = 0 ∨ P.src.qs.length < d.level ∨ d.key % 2 = 0 ∨
      2 * P.src.N ≤ d.key) :
    refAnalyze P E prog = none := sorry

/-- **Scope.** `analyze` rejects every program outside BGV: an accepted program of another scheme
would carry no theorem (`NoiseSoundBGV` is about BGV only). -/
def NoiseRejectsNonBGV (analyze : NoiseAnalyzer) : Prop :=
  ∀ (P : FullParams) (E : Trace.Budget) (prog : Source.Program),
    P.src.kind ≠ .bgv → analyze P E prog = none

/-- `analyze` accepts `y = (a + b) · c` at `exampleBGV31` (`N = 2¹⁴`, `Q ≈ 2⁶⁰`,
`inputNoise = 2²¹`) with a bound of at most `N · (2 · 2²¹) · 2²¹ = 2⁵⁷`, the exact worst case
(below `Q/2 ≈ 2⁵⁹`). -/
def NoiseAcceptsAddMul (analyze : NoiseAnalyzer) : Prop :=
  ∃ B, analyze .exampleBGV31 noBudget addMulProg = some B ∧ B ≤ 2 ^ 57

end Challenge.Headline
