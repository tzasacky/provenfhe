import Challenge.Profile

/-!
# Challenge.Profile.Tool — the tool's computed budget is one profile   (LOCKED statements; proofs in `Validation/Profile/Tool.lean`)

`fhe_check` runs `Challenge.Certify.certify?` (BGV) and `Challenge.CertifyBFV.certifyBFV?` (BFV),
which compute their budget: `Spec.Budget.certified c.params x.lay` for BGV, and the
per-instruction table `budgetBFV x` of the declared technique for BFV. The statements here say
that this computation is one policy for choosing a profile of `Challenge.Profile`:

* `certify?_profile`, `certifyBFV?_profile`: **tool acceptance implies profile acceptance at the
  computed budget, with the same bounds**: `certifyProfile? c.params c.budget x.prog x.switched =
  some (c.bound, c.outputs)` (every mode of `certify?`), and
  `certifyBFVProfile? x.P c.budget x.prog = some (c.bound, c.outputs)`. The converse fails: the
  tools refuse more (special primes, layout and key restriction for BGV; the technique's side
  conditions, declared methods, word and basis conditions for BFV). No extra hypothesis is
  needed: every check of the profile functions is one the tools make.
* `certify?_covers`: the computed BGV profile passes `coversBGV?` for the tool's layout and
  every number `K` of modulus-switched components, so the realizability corollaries
  `coversBGV?_relin`, `_keySwitch`, `_modSwitch` apply to it.
* BFV coverage. The conservative check `coversBFV?` asks at every key switch for `ksBoundAt` at
  EVERY level of the chain; the tool charges a key switch `ksBoundAt` at the operand's own level
  only, so the computed profile does not pass it in general (a `#guard` below exhibits a
  key switch at level 2 of `sealBFV` that the computed profile does not cover that way).
  This file adds the level-exact check `coversBFVAt?`, which replays `Source.step` on all-zero
  messages, as the tool does, and reads the level of each key switch's operand; its realizability
  corollaries `coversBFVAt?_mul`, `_square`, `_relin`, `_keySwitch`, `_modSwitch` are about the
  instruction at position `pre.length` of a run on any messages. `certifyBFV?_coversAt`: the
  computed BFV profile passes `coversBFVAt?` for the tool's layout with the textbook family
  `U = 0`, `r = 1`, for EVERY declared technique (`HPSPOVERQLEVELED` included: its key-switching
  numbers are at least `ksBoundAt` at the operand's level). It does not hold for the declared RNS
  technique's own slack in the `(U, r)` form: the tool charges an RNS product by the size of the
  representatives it multiplies (`Spec.BudgetBFV.mulLiftNormAt`, `Challenge.BFVMul.stepOK_mul_lifted`),
  a different family; the declared technique's algorithms are covered at the computed budget by
  the existing pins `Challenge.CertifyBFV.certifyBFV?_hps_mul`, `_behz_mul`, `_poverq_mul`,
  `_leveled_mul` and their binary64 versions.
-/

namespace Challenge.Profile
open Spec NPoly Scheme Source Correct Challenge.Certify Challenge.CertifyBFV Challenge.BFV
  Challenge.BFVMul Spec.Certify Spec.CertifyBFV

/-! ## The level-exact BFV coverage check -/

/-- What instruction `i`, in front of the (zero-message) environment `ρ`, asks of its budget
`Ek` for the families `(lay, U, r)`; key switching at the level of its operand in `ρ`. -/
def needAt (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (Ek : TraceBFV.Budget)
    (ρ : Env P.src) : Instr → Bool
  | .mul .. | .square .. =>
    decide (BudgetBFV.mulLiftApprox P U ≤ Ek.mulLift) &&
      decide (BudgetBFV.mulRoundApprox P r ≤ Ek.mulRound)
  | .relin _ a | .keySwitch _ a => decide (BudgetBFV.ksBoundAt P lay (levelOf ρ a) ≤ Ek.keySwitch)
  | .modSwitch .. => decide (BudgetBFV.msBudget P ≤ Ek.modSwitch)
  | _ => true

/-- `needAt` along the replay of a body from instruction `n` (up to the first instruction
`Source.step` rejects). -/
def needAux (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (E : ℕ → TraceBFV.Budget) :
    ℕ → List Instr → Env P.src → Bool
  | _, [], _ => true
  | n, i :: is, ρ =>
    needAt P lay U r (E n) ρ i &&
      match step P.src ρ i with
      | some ρ' => needAux P lay U r E (n + 1) is ρ'
      | none => true

/-- **The level-exact coverage check** (module docstring): the side conditions of the
realizability pins and `needAt` at every instruction of the zero-message replay. -/
def coversBFVAt? (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) : Bool :=
  schemeParamsOK? P && decide (P.src.kind = .bfv) && Budget.specialOK? P &&
    (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
    needAux P lay U r E 0 prog.body (initEnv P.src prog fun _ => .exact 0)

/-! ## The tool's acceptance is profile acceptance -/

/-- **BGV: tool acceptance implies profile acceptance at the computed budget, with the same
whole-program and per-output bounds** (every mode; in the fresh modes `c.params` carries the
fresh input noise). -/
theorem certify?_profile (x : Input) (c : Certificate) (h : certify? x = some c) :
    certifyProfile? c.params c.budget x.prog x.switched = some (c.bound, c.outputs) := sorry

/-- **BGV: the computed profile is covered** by hybrid key switching on the tool's layout and
the centred t-corrected modulus switch of any number of components. -/
theorem certify?_covers (x : Input) (c : Certificate) (h : certify? x = some c) (K : ℕ) :
    coversBGV? c.params x.lay K c.budget = true := sorry

/-- **BFV: tool acceptance implies profile acceptance at the computed per-instruction budget,
with the same bounds.** -/
theorem certifyBFV?_profile (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    certifyBFVProfile? x.P c.budget x.prog = some (c.bound, c.outputs) := sorry

/-- **BFV: the computed profile is covered, level by level, by the textbook family** (`U = 0`,
`r = 1`) and hybrid key switching on the tool's layout, whatever technique is declared. -/
theorem certifyBFV?_coversAt (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    coversBFVAt? x.P x.lay 0 1 x.prog c.budget = true := sorry

/-! ## Realizability under the level-exact check

Each statement is about instruction number `pre.length` of the program (`prog.body = pre ++ i ::
post`), in front of the environment `ρ` that `Source.step` gives on any messages. -/

/-- **Approximate multiplication of the family `(U, r)`** meets the `mul` contract within the
budget of every `mul` of the program (`Challenge.BFVMul.stepOK_mul_approx`). -/
theorem coversBFVAt?_mul (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a b : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .mul d a b :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua ub X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hub : ub.length = 2) (hX : X.length = 3)
    (hUa : ∀ u ∈ ua, normInf u ≤ U) (hUb : ∀ u ∈ ub, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) cb ub)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d out) (.mul d a b) := sorry

/-- **Approximate squaring of the family `(U, r)`** (`Challenge.BFVMul.stepOK_square_approx`). -/
theorem coversBFVAt?_square (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .square d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hX : X.length = 3) (hUa : ∀ u ∈ ua, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) ca ua)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d out) (.square d a) := sorry

/-- **Hybrid relinearization on the digits of `lay`** meets the `relin` contract within the
budget of every `relin` of the program, at the level of its operand: one function per level,
fixed before the messages, the secret and the keys (`Challenge.BFV.relin_realizable`). -/
theorem coversBFVAt?_relin (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true) (ℓ : ℕ)
    (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ : Env P.src),
        prog.body = pre ++ .relin d a :: post →
        pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := sorry

/-- **Hybrid key switching on the digits of `lay`** meets the `keySwitch` contract within the
budget of every `keySwitch` of the program, at the level of its operand
(`Challenge.BFV.keySwitch_realizable`). -/
theorem coversBFVAt?_keySwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (prog : Program) (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ : Env P.src),
        prog.body = pre ++ .keySwitch d a :: post →
        pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := sorry

/-- **Rounding every component** meets the `modSwitch` contract within the budget of every
`modSwitch` of the program (`Challenge.BFV.stepOK_modSwitch_textbook`). -/
theorem coversBFVAt?_modSwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (prog : Program) (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .modSwitch d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (hla : ca.length = 2) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ
      (σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))) (.modSwitch d a) := sorry


-- The conservative check `coversBFV?` (every level at every key switch) and the level-exact one,
-- at the budget `certifyBFV?` computes, for a key switch of an input at level 2 of `sealBFV`
-- (canonical digits, one limb each): the tool charges it `ksBoundAt` at level 2 (180225), below
-- `ksBoundAt` at the top level 4 (524289), so only the level-exact check passes.
#guard (certifyBFV? ⟨sealBFV, { Budget.uniformLayout 1 with canonical := true },
    { inputs := [⟨"a", 2, 2, 3, 1⟩], body := [.keySwitch "c" "a"], outputs := ["c"] },
    some .textbook, false, none, true, []⟩).any fun c =>
  coversBFVAt? sealBFV { Budget.uniformLayout 1 with canonical := true } 0 1
      { inputs := [⟨"a", 2, 2, 3, 1⟩], body := [.keySwitch "c" "a"], outputs := ["c"] }
      c.budget &&
    !coversBFV? sealBFV { Budget.uniformLayout 1 with canonical := true } 0 1
      [.keySwitch "c" "a"] c.budget

end Challenge.Profile
