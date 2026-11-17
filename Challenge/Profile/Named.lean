import Challenge.Profile.Tool
import Challenge.Realize
import Challenge.RealizeBFV
import Challenge.Trace

/-!
# Challenge.Profile.Named — a passing coverage check gives the named algorithms   (LOCKED statements; proofs in `Validation/Profile/Named.lean`)

The realizability corollaries of `Challenge.Profile` (`coversBFV?_relin`, `_keySwitch`;
`coversBGV?_relin`, `_keySwitch`, `_modSwitch`) and of `Challenge.Profile.Tool`
(`coversBFVAt?_relin`, `_keySwitch`) are existential: SOME function, fixed per level, meets the
contract. The statements here compose the coverage checks with the named step statements of
`Challenge.RealizeBFV`, `Challenge.Realize` and `Challenge.Trace`, so that the function is the
transcribed hybrid key switch (`relinBFV`, `keySwitchBFV`; `relinOpenFHE`, `keySwitchOpenFHE`)
and, for the BGV modulus switch, the centred t-corrected switch of every component
(`Challenge.Source.bgvModSwitchComp`). No statement here has an existential over functions.

* **What the checks give** (`coversBGV?_side`, `coversBGV?_ksBound`, `coversBGV?_msBudget`;
  `coversBFV?_side`, `coversBFV?_ksBound`; `coversBFVAt?_side`, `coversBFVAt?_ksBound`): the
  parameter conditions `SchemeParamsOK`, `SpecialOK`, a usable layout at every level `1, …, L`,
  and `ksBoundAt ≤` the key-switching budget: for `coversBGV?` at every level `1, …, L`; for
  `coversBFV?` at every level `1, …, L` for the budget of every `relin` / `keySwitch` of the body;
  for `coversBFVAt?` at the level of the operand of every `relin` / `keySwitch` in a run on any
  messages (no level range needed). `coversBGV?_msBudget`: `msBudgetAt P k ≤ E.modSwitchAt k`
  for `1 ≤ k ≤ K`.
* **The named algorithms** (`coversBFV?_relinBFV`, `coversBFV?_keySwitchBFV`,
  `coversBFVAt?_relinBFV`, `coversBFVAt?_keySwitchBFV`, `coversBGV?_relinOpenFHE`,
  `coversBGV?_keySwitchOpenFHE`, `coversBGV?_modSwitchTextbook`). Hypotheses the coverage check
  does NOT discharge, kept explicit: BFV: `ksDeclOK? P lay` (the declared layout is the one the
  transcription uses; with special primes and `lay.canonical = false` the check is made at the
  centred bound, which the canonical algorithm can exceed); BGV: `lay.canonical = true` (the same
  reason); the operand's level in `1, …, L` for `coversBFV?` and `coversBGV?` (the check covers
  exactly those levels; `Source.step` does not bound the level), and the gadget keys valid for the
  secret at the operand's level; for the BGV modulus switch, `x.parts ≤ K`.
-/

namespace Challenge.ProfileNamed
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.CertifyBFV Challenge.BFV
  Challenge.RealizeBFV Challenge.Realize

/-! ## What a passing check gives -/

/-- **The BGV check, read**: the parameter conditions and a usable layout at every level. -/
theorem coversBGV?_side (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) :
    SchemeParamsOK P ∧ P.src.kind = .bgv ∧ Budget.SpecialOK P ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := sorry

/-- **A passing BGV check gives `ksBoundAt ≤ E.keySwitch` at every level `1, …, L`.** -/
theorem coversBGV?_ksBound (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    Budget.ksBoundAt P lay ℓ ≤ E.keySwitch := sorry

/-- **A passing BGV check gives the modulus-switching budget for `1, …, K` components.** -/
theorem coversBGV?_msBudget (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (k : ℕ) (h1 : 1 ≤ k) (hk : k ≤ K) :
    Budget.msBudgetAt P k ≤ E.modSwitchAt k := sorry

/-- **The conservative BFV check, read**: the parameter conditions and a usable layout at every
level. -/
theorem coversBFV?_side (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) :
    SchemeParamsOK P ∧ Budget.SpecialOK P ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := sorry

/-- **A passing conservative BFV check gives `ksBoundAt ≤ (E k).keySwitch` at every level
`1, …, L`, for every `relin` and `keySwitch` `k` of the body.** -/
theorem coversBFV?_ksBound (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (k : ℕ) (d a : Var)
    (hk : body[k]? = some (.relin d a) ∨ body[k]? = some (.keySwitch d a))
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    BudgetBFV.ksBoundAt P lay ℓ ≤ (E k).keySwitch := sorry

/-- **The level-exact BFV check, read**: the parameter conditions and a usable layout at every
level. -/
theorem coversBFVAt?_side (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true) :
    SchemeParamsOK P ∧ P.src.kind = .bfv ∧ Budget.SpecialOK P ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := sorry

/-- **A passing level-exact BFV check gives `ksBoundAt` at the operand's level below the budget
of every `relin` and `keySwitch`**, in a run on any messages (instruction `pre.length`). -/
theorem coversBFVAt?_ksBound (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ : Env P.src)
    (hbody : prog.body = pre ++ .relin d a :: post ∨ prog.body = pre ++ .keySwitch d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (x : Val P.src) (hx : ρ a = some x) :
    BudgetBFV.ksBoundAt P lay x.level ≤ (E pre.length).keySwitch := sorry

/-! ## BFV: the transcribed key switch meets the contract within a covering profile -/

/-- **The conservative check names the BFV relinearization**: the transcribed hybrid
relinearization `relinBFV` at the operand's level meets the contract of every `relin` of the body
within its budget. -/
theorem coversBFV?_relinBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (hdecl : ksDeclOK? P lay = true) (k : ℕ) (d a : Var) (hk : body[k]? = some (.relin d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level .square s keys) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (relinBFV P lay x.level ca keys)) (.relin d a) :=
  sorry

/-- **The conservative check names the BFV key switch** (`keySwitchBFV`, keys for the target
`σ_g(s)`, `g` the operand's key). -/
theorem coversBFV?_keySwitchBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (hdecl : ksDeclOK? P lay = true) (k : ℕ) (d a : Var) (hk : body[k]? = some (.keySwitch d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level (.galois x.key) s keys) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (keySwitchBFV P lay x.level ca keys))
      (.keySwitch d a) := sorry

/-- **The level-exact check names the BFV relinearization**, at instruction `pre.length` of a run
on any messages. -/
theorem coversBFVAt?_relinBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (hdecl : ksDeclOK? P lay = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .relin d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level .square s keys) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (relinBFV P lay x.level ca keys))
      (.relin d a) := sorry

/-- **The level-exact check names the BFV key switch**, at instruction `pre.length` of a run on
any messages. -/
theorem coversBFVAt?_keySwitchBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (prog : Program) (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (hdecl : ksDeclOK? P lay = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .keySwitch d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level (.galois x.key) s keys) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (keySwitchBFV P lay x.level ca keys))
      (.keySwitch d a) := sorry

/-! ## BGV: the transcribed key switch and the centred modulus switch within a covering profile -/

/-- **The BGV check names the relinearization**: the transcribed hybrid relinearization
`relinOpenFHE` (canonical digits) at the operand's level meets the `relin` contract within `E`. -/
theorem coversBGV?_relinOpenFHE (P : FullParams) (lay : Budget.KSLayout) (K : ℕ)
    (E : Trace.Budget) (hc : coversBGV? P lay K E = true) (hcan : lay.canonical = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level .square s keys) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (relinOpenFHE P lay x.level ca keys)) (.relin d a) := sorry

/-- **The BGV check names the key switch** (`keySwitchOpenFHE`, keys for the target `σ_g(s)`,
`g` the operand's key). -/
theorem coversBGV?_keySwitchOpenFHE (P : FullParams) (lay : Budget.KSLayout) (K : ℕ)
    (E : Trace.Budget) (hc : coversBGV? P lay K E = true) (hcan : lay.canonical = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level (.galois x.key) s keys) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (keySwitchOpenFHE P lay x.level ca keys))
      (.keySwitch d a) := sorry

/-- **The BGV check names the modulus switch**: the centred t-corrected switch of every
component of an operand with at most `K` components meets the `modSwitch` contract within `E`. -/
theorem coversBGV?_modSwitchTextbook (P : FullParams) (lay : Budget.KSLayout) (K : ℕ)
    (E : Trace.Budget) (hc : coversBGV? P lay K E = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hlen : ca.length = x.parts) (hpK : x.parts ≤ K) :
    Trace.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)))
      (.modSwitch d a) := sorry

end Challenge.ProfileNamed
