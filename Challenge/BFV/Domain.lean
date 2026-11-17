import Challenge.BFV

/-!
# Challenge.BFV.Domain — the domain of the certified BFV budget   (LOCKED statements; proofs in `Validation/BFV/Domain.lean`)

`Spec.BudgetBFV.certified` gives the product and the modulus switch one number each
(`mulLift`, `mulRound`, `modSwitch`), proved achievable for **two-component operands only**. A
soundness theorem about "every run meeting the contracts within the budget" says nothing about a
step for which no such run exists. This file makes the following a locked fact:

  *every step the reference analyzer accepts at the certified budget is one the textbook
  algorithm performs within that budget.*

* **Rejection outside the domain.** `refAnalyzeBFV_rejects_unrelinearized`: a program in which,
  at some point, a `mul`, `square` or `modSwitch` has an operand recorded with a number of
  components other than two is rejected, at every budget (`Challenge.BFV.domainOK`). The three
  scenarios that were accepted before this guard existed are `#guard`s below and the closed pin
  `refAnalyzeBFV_rejects_seal_scenarios`; their relinearized versions are still accepted.
* **The remaining textbook pins.** With `Challenge/BFV.lean` (`add`, `addPlain`, `mulPlain`,
  `mul`, `modSwitch`, `relin`, `keySwitch`), the pins here (`sub`, `subPlain`, `square`,
  `mulConst`, `copy`/`toEval`/`toCoeff`, `automorph`) cover every BFV operation. The exact ones
  hold for every budget and every number of components.
* **Every accepted program has a run.** `certified_run_exists`: if the analyzer accepts a program
  at the certified budget (valid parameters and special primes, a layout usable at every level, a
  secret within its bound), then from *every* input meeting `TraceBFV.InputsOK` there is a
  ciphertext-level run of the whole program in which each step meets its contract within the
  certified budget. So the conclusion of `refAnalyzeBFV_sound` is never about an empty set of
  runs at the certified budget. `sealProgMS_run_exists` is the instance at `sealBFV` for a
  program with `mul`, `relin`, `automorph`, `keySwitch` and `modSwitch`.

What is *not* claimed: a budget for products or modulus switches of three-component values (a
budget depending on the number of components is future work; such steps are rejected), RNS
multiplications (BEHZ, HPS family) are not treated in this file; their realizability pins are in
`Challenge/BFVMul.lean`.
-/

namespace Challenge.BFV
open Spec NPoly Scheme Source Correct

/-! ## Rejection outside the domain -/

/-- **A product, square or modulus switch of a value that does not have exactly two components
is rejected**, at every budget and wherever it occurs: if the body is `pre ++ i :: post`, the
instructions `pre` are well formed and lead (on the all-zero messages the analysis runs on; the
recorded numbers of components do not depend on the messages) to the environment `ρ`, and `i` is
a `mul` one of whose operands, or a `square` or `modSwitch` whose operand, is recorded in `ρ`
with `parts ≠ 2`, then the analyzer returns `none`. -/
theorem refAnalyzeBFV_rejects_unrelinearized (P : FullParams) (E : TraceBFV.Budget)
    (prog : Source.Program) (pre post : List Instr) (i : Instr) (ρ : Env P.src) (x : Val P.src)
    (hbody : prog.body = pre ++ i :: post)
    (hpre : pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ)
    (hx : x.parts ≠ 2)
    (hi : (∃ d a b, i = .mul d a b ∧ (ρ a = some x ∨ ρ b = some x)) ∨
      (∃ d a, (i = .square d a ∨ i = .modSwitch d a) ∧ ρ a = some x)) :
    refAnalyzeBFV P E prog = none := sorry

/-- The certified budget at `sealBFV` with one limb per key-switching digit. -/
def sealBudget : TraceBFV.Budget := BudgetBFV.certified sealBFV (Budget.uniformLayout 1)

-- The three scenarios, at `sealBFV` with the certified budget: each is
-- rejected; each is accepted once the three-component value is relinearized first.
-- 1. `mul; modSwitch` on the three-component product.
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩],
    body := [.mul "c" "a" "b", .modSwitch "c" "c"], outputs := ["c"] } == none
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c", .modSwitch "c" "c"], outputs := ["c"] }
  == some 186048
-- 2. `mul d c c` with `c` a three-component input (the lift of a three-component value is about
-- `(1 + N + N²)/2`, not `mulLift = 4097`); also with only one three-component operand.
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.mul "d" "c" "c"], outputs := ["d"] } == none
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"c", 3, 4, 1, 1⟩], body := [.mul "d" "a" "c"],
    outputs := ["d"] } == none
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"c", 3, 4, 1, 1⟩], body := [.mul "d" "c" "a"],
    outputs := ["d"] } == none
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.relin "c" "c", .mul "d" "c" "c"],
    outputs := ["d"] } == some 3671159023584503623
-- 3. `square` of a three-component value.
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.square "d" "c"], outputs := ["d"] } == none
#guard refAnalyzeBFV sealBFV sealBudget
  { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.relin "c" "c", .square "d" "c"],
    outputs := ["d"] } == some 3671159023584503623
-- The guard is on the number of components, whatever the budget (here: all zero).
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"c", 3, 2, 1, 1⟩], body := [.modSwitch "d" "c"], outputs := ["d"] } == none
#guard domainOK (initEnv tinyBFV.src { inputs := [⟨"c", 3, 2, 1, 1⟩], body := [], outputs := [] }
    fun _ => .exact 0) (.square "d" "c") == false
#guard domainOK (initEnv tinyBFV.src { inputs := [⟨"c", 2, 2, 1, 1⟩], body := [], outputs := [] }
    fun _ => .exact 0) (.square "d" "c")
#guard domainOK (initEnv tinyBFV.src { inputs := [⟨"c", 3, 2, 1, 1⟩], body := [], outputs := [] }
    fun _ => .exact 0) (.add "d" "c" "c")

/-- The three scenarios are rejected at `sealBFV` with the certified budget (closed; the
`#guard`s above are the compiled evaluation of the same terms). -/
theorem refAnalyzeBFV_rejects_seal_scenarios :
    refAnalyzeBFV sealBFV sealBudget
      { inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩],
        body := [.mul "c" "a" "b", .modSwitch "c" "c"], outputs := ["c"] } = none ∧
    refAnalyzeBFV sealBFV sealBudget
      { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.mul "d" "c" "c"], outputs := ["d"] } = none ∧
    refAnalyzeBFV sealBFV sealBudget
      { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.square "d" "c"], outputs := ["d"] } = none :=
  sorry

/-! ## The remaining textbook operations -/

section Ops
variable {N : ℕ}

/-- Textbook plaintext subtraction: `c₀ − Δ·p`. -/
def bfvSubPlain (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) : List (IntPoly N) :=
  Challenge.Source.padZip (· - ·) c [((Q / t : ℕ) : ℤ) • p]

/-- The integer multiple `c·a`, coefficient by coefficient. -/
def bfvMulConst (c : ℤ) (a : IntPoly N) : IntPoly N := ⟨fun i => c * a.coeff i⟩

end Ops

variable (P : FullParams)

/-- Componentwise subtraction (the shorter ciphertext padded with zero components) meets the
`sub` contract, for any numbers of components and every budget. -/
theorem stepOK_sub_padded (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.sub d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· - ·) ca cb))
      (.sub d a b) := sorry

/-- Subtracting `⌊Q/t⌋·p` from the first component meets the `subPlain` contract, with no
deviation (every budget, any number of components). -/
theorem stepOK_subPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvSubPlain P.src.t (P.src.modulus x.level) ca c)) (.subPlain d a p) := sorry

/-- **Textbook squaring meets the `square` contract** with the same `mulLift` and `mulRound` as
the product (`bfvMul` of the ciphertext with itself), for a two-component operand under any
secret within the bound. -/
theorem stepOK_square_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)) (.square d a) := sorry

/-- Multiplying every component by the integer `c` meets the `mulConst` contract (every budget,
any number of components). -/
theorem stepOK_mulConst_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (c : ℤ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mulConst d a c) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (bfvMulConst c))) (.mulConst d a c) := sorry

/-- Assigning the operand's components unchanged meets the contract of `copy`, `toEval` and
`toCoeff` (every budget, any number of components, ciphertext or plaintext). -/
theorem stepOK_copy_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (i : Instr) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hi : i = .copy d a ∨ i = .toEval d a ∨ i = .toCoeff d a)
    (hstep : step P.src ρ i = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ca) i := sorry

/-- Applying `X ↦ X^g` to every component meets the `automorph` contract: the result is read
under `σ_g` of the operand's key (every budget, any number of components). -/
theorem stepOK_automorph_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (g : ℕ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.automorph d a g) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (automorph g))) (.automorph d a g) := sorry

/-! ## Every accepted program has a run -/

/-- **Every program the reference analyzer accepts at the certified budget has a run from every
valid input, within that budget.** The run is the textbook one: each step is performed by the
algorithm of its realizability pin (`stepOK_*`, `relin_realizable`, `keySwitch_realizable`).

Hypotheses, and why each is there:
* `hP`: the parameters are valid at the scheme level (the product and the modulus switch need a
  ring dimension that is a power of two and prime moduli);
* `hS`, `hlay`: key switching needs the special primes to be usable and the layout to split
  every level of the chain into nonempty digits (`Budget.uniformLayout` does, at every level:
  `Challenge.Budget.uniformLayout_ok`);
* `h`: the analyzer accepts the program at the certified budget (this contains
  `P.src.kind = .bfv`, well-formed input declarations, and `domainOK` at every step);
* `hs`: the secret is within `P.secretBound` (the budget's `mulLift`, `mulRound`, `modSwitch`
  and `keySwitch` are functions of that bound);
* `hin`: the inputs are what the noise headline assumes of them.

The key-switching keys of the run are chosen in the proof: the noiseless keys of
`Challenge.Scheme.keyValid_exists` (`a = 0`), which are valid keys in the sense of
`Budget.GadgetKeysOK`; `relin_realizable` and `keySwitch_realizable` cover every valid key
list. The statement is existence of a run, hence non-vacuity of `refAnalyzeBFV_sound` at the
certified budget; it says nothing about security or about what a library computes. -/
theorem certified_run_exists (lay : Budget.KSLayout) (prog : Source.Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hS : Budget.SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (h : refAnalyzeBFV P (BudgetBFV.certified P lay) prog = some B)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : TraceBFV.InputsOK P s prog msgs cts) :
    ∃ σ, TraceBFV.Run P (BudgetBFV.certified P lay) s prog.body (initEnv P.src prog msgs)
      (Trace.initCt P prog cts) σ := sorry

/-- `sealProg` followed by a modulus switch of its (relinearized, two-component) result: a
program with `mul`, `relin`, `automorph`, `keySwitch`, `mulPlain`, `addPlain` and `modSwitch`. -/
def sealProgMS : Source.Program :=
  { sealProg with body := sealProg.body ++ [.modSwitch "y" "y"] }

/-- `sealProgMS` is accepted at `sealBFV` with the certified budget (the modulus switch divides
the bound of `sealProg` by the 44-bit prime it drops). -/
theorem refAnalyzeBFV_accepts_sealMS :
    ∃ B, refAnalyzeBFV sealBFV sealBudget sealProgMS = some B ∧ B ≤ 2 ^ 87 := sorry

#guard (refAnalyzeBFV sealBFV sealBudget sealProgMS).isSome

/-- The instance of `certified_run_exists` at `sealBFV`: under every ternary secret and from
every valid input, `sealProgMS` has a run within the certified budget. -/
theorem sealProgMS_run_exists (s : IntPoly sealBFV.src.N) (hs : SecretOK sealBFV.secretBound s)
    (msgs : Var → Msg sealBFV.src.t sealBFV.src.N) (cts : Var → List (IntPoly sealBFV.src.N))
    (hin : TraceBFV.InputsOK sealBFV s sealProgMS msgs cts) :
    ∃ σ, TraceBFV.Run sealBFV sealBudget s sealProgMS.body
      (initEnv sealBFV.src sealProgMS msgs) (Trace.initCt sealBFV sealProgMS cts) σ := sorry

end Challenge.BFV
