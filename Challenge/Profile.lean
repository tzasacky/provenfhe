import Challenge.Profile.Defs
import Challenge.Certify
import Challenge.CertifyBFV
import Challenge.Params

/-!
# Challenge.Profile — what a profile certificate means, and when a profile is achievable   (LOCKED statements; proofs in `Validation/Profile.lean`)

The decisions are in `Challenge.Profile.Defs`. An implementation profile is a budget given
directly (BGV: one `Spec.Trace.Budget`; BFV: one `Spec.TraceBFV.Budget` per instruction), with no
library, layout or technique in it.

1. **Soundness at every profile** (`certifyProfile?_sound`, `certifyBFVProfile?_sound`): if the
   decision accepts at `E`, every output of every run in which each operation meets its contract
   within `E` decrypts with the secret key to what the program computes, with noise at most its
   own bound (`Challenge.Certify.OutputsCertified`, `Challenge.CertifyBFV.OutputsCertifiedBFV`).
   `certifyBFVProfile?_inputs`: every declared input ciphertext bound passes the decryption
   condition at its level.
2. **The inputs exist** (`certifyBFVProfile?_inputs_exist`, `certifyProfile?_inputs_exist`): the
   input hypotheses of 1 are met, for every secret and every message, by some input ciphertexts
   (BFV: plaintext inputs declared at a bound of at least `t − 1`; BGV: programs that declare no
   per-input bound and whose inputs have two components). For EVERY accepted program, with no
   further hypothesis: `Challenge.Profile.Inputs` (the decisions check that every input can hold
   every message, `Challenge.Certify.inputsMsgOK?`, `Challenge.CertifyBFV.plainBoundsOK`).
3. **Budget order** (`stepOK_mono`, `run_mono`, `stepOK_mono_bfv`, `runAt_mono`): a step or a run
   that meets the contracts within `E` meets them within every `E'` above `E` (`BudgetLEBGV`,
   `BudgetLEBFV`). Hence (`outputsCertified_mono`, `outputsCertifiedBFV_mono`) a certificate at a
   profile covers every implementation proved to meet the contracts within a smaller budget.
4. **Achievability by named families** (`coversBFV?_mul`, `_square`, `_relin`, `_keySwitch`,
   `_modSwitch`; `coversBGV?_relin`, `_keySwitch`, `_modSwitch`): when the coverage check of
   `Challenge.Profile.Defs` passes, the algorithms of the families it names meet the contract of
   instruction `k` within `E k`, under every secret within `secretBound`: ANY multiplication that
   multiplies lifts `[c]_Q + Q·u` with `‖u‖∞ ≤ U` and rounds within `r/2`
   (`Challenge.BFVMul.stepOK_mul_approx`); hybrid key switching on the digits of the layout
   (`Challenge.BFV.relin_realizable`, `keySwitch_realizable`; BGV: `Challenge.Budget`); the
   rounding (BFV) and the centred t-corrected (BGV, `modSwitch_realizable_parts`) modulus switch.
5. **Instances** (closed, at the end): acceptance and coverage at `tinyBFV` (kernel) and at
   `sealBFV` (compiled); the zero profile ACCEPTED for a product (with a smaller bound than the
   textbook profile gives) and rejected by the coverage check.

**What a profile certificate does not say.** It is sound for every budget, so on its own it says
nothing about whether any implementation stays within the budget: that is what 4 (or a proof
for a specific implementation) supplies. The secret is within `secretBound` in 4 and arbitrary in
1, as for `Challenge.Certify` ("For which secrets"). The keys of 4 are hypotheses
(`Spec.Budget.GadgetKeysOK`), as in `Challenge.Budget`.
-/

namespace Challenge.Profile
open Spec NPoly Scheme Source Correct Challenge.Certify Challenge.CertifyBFV Challenge.BFV
  Challenge.BFVMul

/-! ## 1. Soundness at every profile -/

/-- **Profile soundness (BGV).** For every budget `E`: if `certifyProfile?` accepts at `E`, then
for every integer polynomial `s` as the secret, all messages and all input ciphertexts within
the input noise and their declared bounds, every output of every run within `E` decrypts with
`s` and has noise at most its own bound in `outs`. -/
theorem certifyProfile?_sound (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    OutputsCertified P E prog sw outs s msgs cts := sorry

/-- **Profile soundness (BFV).** For every per-instruction budget `E`: if `certifyBFVProfile?`
accepts at `E`, then for every integer polynomial `s` as the secret, all messages and all inputs
within their bounds, every output of every run in which instruction `k` meets its contract
within `E k` is under `s`, decrypts with `s` and has noise at most its own bound in `outs`. -/
theorem certifyBFVProfile?_sound (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    OutputsCertifiedBFV P E prog outs s msgs cts := sorry

/-- **The bound of every input ciphertext decrypts at its level**, so its noise bound alone gives
that it decrypts (`Challenge.BFV.bfv_decrypt_of_noise`), as `certifyBFV?_inputs`. -/
theorem certifyBFVProfile?_inputs (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (d : Decl) (hd : d ∈ prog.inputs) (hp : d.parts ≠ 1) :
    decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P prog d) = true := sorry

/-! ## 2. The inputs exist -/

/-- **The BFV input hypothesis is satisfiable for every secret and every message.** If
`certifyBFVProfile?` accepts and every one-component (plaintext) input has a bound of at least
`t − 1`, then for every secret and every assignment of messages there are inputs meeting
`TraceBFV.InputsOK`: each ciphertext input a noiseless encryption, each plaintext input its
stored representative `liftMsg`. -/
theorem certifyBFVProfile?_inputs_exist (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Program) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs))
    (hpt : ∀ d ∈ prog.inputs, d.parts = 1 → P.src.t - 1 ≤ TraceBFV.inputBound P prog d)
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, TraceBFV.InputsOK P s prog (fun x => .exact (m x)) cts := sorry

/-- **The BGV input hypotheses are satisfiable for every secret and every message**, for a
program that declares no per-input bound and whose inputs have two components at levels whose
modulus exceeds `t`. -/
theorem certifyProfile?_inputs_exist (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (hbd : prog.bounds = [])
    (h2 : ∀ d ∈ prog.inputs, d.parts = 2 ∧ P.src.t < P.src.modulus d.level)
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts := sorry

/-! ## 3. Budget order -/

/-- **A BGV step within `E` is a step within every budget above `E`.** -/
theorem stepOK_mono (P : FullParams) (E E' : Trace.Budget) (hE : BudgetLEBGV E E')
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P) (i : Instr)
    (h : Trace.StepOK P E s ρ ρ' σ σ' i) : Trace.StepOK P E' s ρ ρ' σ σ' i := sorry

/-- **A BGV run within `E` is a run within every budget above `E`.** -/
theorem run_mono (P : FullParams) (E E' : Trace.Budget) (hE : BudgetLEBGV E E')
    (s : IntPoly P.src.N) (body : List Instr) (ρ : Env P.src) (σ σf : Trace.CtEnv P)
    (h : Trace.Run P E s body ρ σ σf) : Trace.Run P E' s body ρ σ σf := sorry

/-- **A BGV certificate at `E'` covers every run within a budget below `E'`.** -/
theorem outputsCertified_mono (P : FullParams) (E E' : Trace.Budget) (hE : BudgetLEBGV E E')
    (prog : Program) (sw : Bool) (bounds : List (Var × ℕ)) (s : IntPoly P.src.N)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (h : OutputsCertified P E' prog sw bounds s msgs cts) :
    OutputsCertified P E prog sw bounds s msgs cts := sorry

/-- **A BFV step within `E` is a step within every budget above `E`.** -/
theorem stepOK_mono_bfv (P : FullParams) (E E' : TraceBFV.Budget) (hE : BudgetLEBFV E E')
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P) (i : Instr)
    (h : TraceBFV.StepOK P E s ρ ρ' σ σ' i) : TraceBFV.StepOK P E' s ρ ρ' σ σ' i := sorry

/-- **A BFV run with budgets `E` is a run with every pointwise larger `E'`.** -/
theorem runAt_mono (P : FullParams) (E E' : ℕ → TraceBFV.Budget)
    (hE : ∀ k, BudgetLEBFV (E k) (E' k)) (s : IntPoly P.src.N) (n : ℕ) (body : List Instr)
    (ρ : Env P.src) (σ σf : Trace.CtEnv P) (h : TraceBFV.RunAt P E s n body ρ σ σf) :
    TraceBFV.RunAt P E' s n body ρ σ σf := sorry

/-- **A BFV certificate at `E'` covers every run within pointwise smaller budgets.** -/
theorem outputsCertifiedBFV_mono (P : FullParams) (E E' : ℕ → TraceBFV.Budget)
    (hE : ∀ k, BudgetLEBFV (E k) (E' k)) (prog : Program) (bounds : List (Var × ℕ))
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N))
    (h : OutputsCertifiedBFV P E' prog bounds s msgs cts) :
    OutputsCertifiedBFV P E prog bounds s msgs cts := sorry

/-! ## 4. Achievability by named families (BFV) -/

/-- **Every approximate multiplication of the family `(U, r)` meets the `mul` contract within
the budget of every `mul` of the body**, when the profile covers the family: the hypotheses are
those of `Challenge.BFVMul.stepOK_mul_approx` (lifts within `U`, rounding within `r/2`), with the
budget numbers replaced by the coverage check. -/
theorem coversBFV?_mul (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (k : ℕ) (d a b : Var)
    (hk : body[k]? = some (.mul d a b))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
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
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d out) (.mul d a b) := sorry

/-- **Every approximate squaring of the family `(U, r)` meets the `square` contract** within the
budget of every `square` of the body (`Challenge.BFVMul.stepOK_square_approx`). -/
theorem coversBFV?_square (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (k : ℕ) (d a : Var)
    (hk : body[k]? = some (.square d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
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
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d out) (.square d a) := sorry

/-- **Hybrid relinearization on the digits of `lay` meets the `relin` contract within the budget
of every `relin` of the body**, at every level of the chain: one function per level, fixed before
the secret and the keys (`Challenge.BFV.relin_realizable`). -/
theorem coversBFV?_relin (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (k : ℕ) (d a : Var), body[k]? = some (.relin d a) →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := sorry

/-- **Hybrid key switching on the digits of `lay` meets the `keySwitch` contract within the
budget of every `keySwitch` of the body**, at every level (`Challenge.BFV.keySwitch_realizable`). -/
theorem coversBFV?_keySwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (k : ℕ) (d a : Var), body[k]? = some (.keySwitch d a) →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := sorry

/-- **Rounding every component meets the `modSwitch` contract within the budget of every
`modSwitch` of the body** (`Challenge.BFV.stepOK_modSwitch_textbook`). -/
theorem coversBFV?_modSwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (k : ℕ) (d a : Var) (hk : body[k]? = some (.modSwitch d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (hla : ca.length = 2) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ
      (σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))) (.modSwitch d a) := sorry

/-! ## 4. Achievability by named families (BGV) -/

/-- **Hybrid relinearization on the digits of `lay` meets the BGV `relin` contract within a
covering profile**, at every level (`Challenge.Budget.relin_realizable`). -/
theorem coversBGV?_relin (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := sorry

/-- **Hybrid key switching on the digits of `lay` meets the BGV `keySwitch` contract within a
covering profile**, at every level (`Challenge.Budget.keySwitch_realizable`). -/
theorem coversBGV?_keySwitch (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := sorry

/-- **The centred t-corrected modulus switch of an operand with `k ≤ K` components meets the BGV
`modSwitch` contract within a covering profile**, at every level
(`Challenge.Budget.modSwitch_realizable_parts`). -/
theorem coversBGV?_modSwitch (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = k → ca.length = k →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := sorry

/-! ## 5. Instances -/

/-- The product of two fresh inputs at `tinyBFV`, relinearized, then switched down one level. -/
def tinyProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c", .modSwitch "c" "c"], outputs := ["c"] }

/-- The constant profile of the textbook budget at `tinyBFV` with one limb per digit. -/
def tinyProfile : ℕ → TraceBFV.Budget :=
  fun _ => BudgetBFV.certified tinyBFV (Budget.uniformLayout 1)

/-- **Non-vacuity at `tinyBFV`, kernel-checked**: the profile certificate accepts `tinyProg` at
the textbook profile, the profile covers the textbook families (`U = 0`, `r = 1`) and hybrid key
switching with one limb per digit, and the zero profile does not cover the product. -/
theorem tiny_accepts :
    (certifyBFVProfile? tinyBFV tinyProfile tinyProg).isSome = true ∧
      coversBFV? tinyBFV (Budget.uniformLayout 1) 0 1 tinyProg.body tinyProfile = true ∧
      coversBFV? tinyBFV (Budget.uniformLayout 1) 0 1 tinyProg.body
        (fun _ => ⟨0, 0, 0, 0, 0⟩) = false := sorry

-- At `sealBFV` (`N = 2¹³`, four limbs) the program `Challenge.BFV.sealProg` (two products, two
-- relinearizations, a rotation, plaintext operations) at the textbook profile: accepted, and
-- covered by the textbook families; also by an approximate multiplication with lift slack 1 and
-- rounding slack 3 once the profile's multiplication numbers are raised to theirs.
#guard (certifyBFVProfile? sealBFV
  (fun _ => BudgetBFV.certified sealBFV (Budget.uniformLayout 1)) sealProg).isSome
#guard coversBFV? sealBFV (Budget.uniformLayout 1) 0 1 sealProg.body
  (fun _ => BudgetBFV.certified sealBFV (Budget.uniformLayout 1))
#guard !coversBFV? sealBFV (Budget.uniformLayout 1) 1 3 sealProg.body
  (fun _ => BudgetBFV.certified sealBFV (Budget.uniformLayout 1))
#guard coversBFV? sealBFV (Budget.uniformLayout 1) 1 3 sealProg.body
  (fun _ => { BudgetBFV.certified sealBFV (Budget.uniformLayout 1) with
    mulLift := BudgetBFV.mulLiftApprox sealBFV 1, mulRound := BudgetBFV.mulRoundApprox sealBFV 3 })
#guard (certifyBFVProfile? sealBFV
  (fun _ => { BudgetBFV.certified sealBFV (Budget.uniformLayout 1) with
    mulLift := BudgetBFV.mulLiftApprox sealBFV 1,
    mulRound := BudgetBFV.mulRoundApprox sealBFV 3 }) sealProg).isSome
-- THE ZERO PROFILE. A program that only adds is accepted at the zero budget (it needs none).
-- So is `tinyProg`, with the bound 2 against 143 at the textbook profile: soundness at the zero
-- profile is about the runs whose product, relinearization and modulus switch add no error, and
-- no implementation is shown to produce one; the coverage check rejects the zero profile
-- (`tiny_accepts`). Acceptance of a profile is not evidence that it is achievable.
#guard (certifyBFVProfile? tinyBFV (fun _ => ⟨0, 0, 0, 0, 0⟩)
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.add "c" "a" "b"],
    outputs := ["c"] }).isSome
#guard certifyBFVProfile? tinyBFV (fun _ => ⟨0, 0, 0, 0, 0⟩) tinyProg == some (2, [("c", 2)])
#guard certifyBFVProfile? tinyBFV tinyProfile tinyProg == some (143, [("c", 143)])
-- REJECTED: an input ciphertext bound that fails the decryption condition at its level.
#guard (certifyBFVProfile? { tinyBFV with inputNoise := 10 ^ 12 } tinyProfile
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] }).isNone

end Challenge.Profile
