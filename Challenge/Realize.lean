import Challenge.Realize.OpenFHE
import Challenge.Certify

/-!
# Challenge.Realize — the functions that reproduce OpenFHE meet the run contracts   (LOCKED statements; proofs in `Validation/`)

`Challenge.Budget.relin_realizable` and `keySwitch_realizable` say that *some* function of the
operand and the keys meets the `relin` / `keySwitch` contract within `ksBoundAt`. The statements
here name the function: the transcription of OpenFHE v1.6.1's key switching in
`Challenge.Realize.OpenFHE` (canonical representatives, the default build), which is proved equal
limb for limb to the Lean functions the conformance harness finds bit-exact with OpenFHE on
recorded runs (that module's docstring says exactly how: the equality is a kernel-checked theorem
of the untrusted library, the agreement with OpenFHE an executed comparison).

* `relinOpenFHE_stepOK`, `keySwitchOpenFHE_stepOK`: at every level `ℓ` of the chain with a usable
  layout, for every budget whose key-switching bound is at least `ksBoundAt P lay ℓ` (with
  `lay.canonical = true`: the canonical bound), every secret within the bound and every list of
  gadget keys valid for it with noise at most `keyNoise`, the output of `relinOpenFHE` /
  `keySwitchOpenFHE` meets the `relin` / `keySwitch` step contract of `Spec.Trace.StepOK`.
* `rotateOpenFHE161_run`: OpenFHE v1.6.1's rotation is **one** operation; the source mapping of
  the frontend (`harness/frontend/openfhe/extract.py`) is the two instructions
  `automorph m a g; keySwitch d m`. What is proved: the run of these two instructions whose
  intermediate ciphertext is the textbook automorphism `σ_g` of every component of the operand
  (`m` holds `ca.map (automorph g)`, which OpenFHE never computes) and whose final ciphertext is
  `rotateOpenFHE161 …` is a `Spec.Trace.Run` at every budget with key-switching bound at least
  `ksBoundAt P lay ℓ`. The keys are OpenFHE's stored rotation keys: gadget keys for the secret
  `s'` with `σ_g(s') = s` and the target `σ_g(s')` (`KeyTarget.galois g`), i.e. encryptions of
  (gadget factor)`·s` under `σ_{g⁻¹}(s)`; such an `s'` exists for every `s`, with the same norm
  (`rotKeySecret_exists`). The operand must be under `s` itself (`x.key = 1`, as every OpenFHE
  ciphertext is). This differs from the key convention of `Challenge.Budget.keySwitch_realizable`
  (keys for the secret `s` and the target `σ_g(s)`).
* `certify?_relinOpenFHE`, `certify?_keySwitchOpenFHE`, `certify?_rotateOpenFHE161`,
  `certify?_modSwitch`: the same at the budget `c.budget` of a certificate (`certify? x = some c`),
  with **one** key set generated at the top level of the chain and used at every level as OpenFHE
  does (the functions read only the first digits of it), under exactly the conditions the
  certificate's checks establish (`Challenge.Certify.certify?_paramsOK`, `certify?_keys_restrict`)
  plus what no check discharges: `x.lay.canonical = true` (the declared representatives are
  OpenFHE's default ones; with `canonical = false` the budget is the centred one, which this
  algorithm can exceed), the secret within `secretBound`, and keys with noise at most `keyNoise`.
  `certify?_modSwitch` is the same for the modulus switch the harness compares
  (`Challenge.Source.bgvModSwitchComp`, centred correction; any number of components).

What is not claimed: anything about OpenFHE's code itself (the link is the executed comparison);
the RNS form `FHE.RNS.Basis.bgvModSwitchPoly` of the modulus switch (equal to
`bgvModSwitchComp` on residues by an unlocked theorem, `FHE.RNS.Basis.bgvModSwitchPoly_toRNS`);
OpenFHE's fused rotation sums (`EvalSum`, `EvalFastRotation` with precomputation), which the
frontend refuses.
-/

namespace Challenge.Realize
open Spec NPoly Scheme Source Correct Spec.Budget Spec.Certify Challenge.Certify

/-! ## At one level, for every budget at least `ksBoundAt` -/

/-- **OpenFHE's relinearization meets the `relin` contract** within the canonical `ksBoundAt`. -/
theorem relinOpenFHE_stepOK (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (hc : lay.canonical = true) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) (hkeys : GadgetKeysOK P lay ℓ .square s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (relinOpenFHE P lay ℓ ca keys)) (.relin d a) := sorry

/-- **OpenFHE's key switch meets the `keySwitch` contract** within the canonical `ksBoundAt`,
with keys for the secret `s` and the target `σ_g(s)`, `g` the operand's key. -/
theorem keySwitchOpenFHE_stepOK (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (hc : lay.canonical = true) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P lay ℓ (.galois x.key) s keys) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (keySwitchOpenFHE P lay ℓ ca keys)) (.keySwitch d a) :=
  sorry

/-- **OpenFHE's rotation keys exist for every secret.** For odd `g` and `N` a power of two, every
secret `s` is `σ_g(s')` for some `s'` of the same norm (`s' = σ_{g⁻¹}(s)`), so the key hypothesis
of `rotateOpenFHE161_run` (keys valid for `s'`) can be met whenever keys for a secret within the
bound can. -/
theorem rotKeySecret_exists (N : ℕ) (hN : ∃ k, N = 2 ^ k) (g : ℕ) (hg : g % 2 = 1)
    (s : IntPoly N) : ∃ s' : IntPoly N, automorph g s' = s ∧ normInf s' = normInf s := sorry

/-- **OpenFHE v1.6.1's rotation is a run of `automorph m a g; keySwitch d m`** within the canonical
`ksBoundAt`. The operand `ca` (two components, under `s` itself) is at level `ℓ`; the keys are the
stored rotation keys for `g`: gadget keys for the secret `s'` with `σ_g(s') = s` and the target
`σ_g(s')`. The intermediate ciphertext is the textbook `σ_g` of every component (in variable `m`);
the final one, in `d`, is `rotateOpenFHE161 P lay ℓ g ca keys`. -/
theorem rotateOpenFHE161_run (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (hc : lay.canonical = true) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ : Env P.src) (σ : Trace.CtEnv P) (d m a : Var) (g : ℕ) (hg : g % 2 = 1) (x : Val P.src)
    (ca : List (IntPoly P.src.N)) (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hkey : x.key = 1) (hparts : x.parts = 2) (hlen : ca.length = 2)
    (s' : IntPoly P.src.N) (hs' : automorph g s' = s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P lay ℓ (.galois g) s' keys) :
    Trace.Run P E s [.automorph m a g, .keySwitch d m] ρ σ
      ((σ.set m (ca.map (automorph g))).set d (rotateOpenFHE161 P lay ℓ g ca keys)) := sorry

/-! ## At the budget of a certificate, with one top-level key set

The hypothesis `x.lay.canonical = true` is met by accepted inputs (it is what the OpenFHE frontend
declares, `FHE.Check.Budget`): `certify?` accepts the demo program of `Challenge.Budget` (tensor
product, relinearization, rotation, modulus switch) at `tinyBGV` with the canonical layout. -/

#guard (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1 true, Challenge.Budget.runDemoProg,
  true, .worstCase, .centred⟩).isSome

/-- **Relinearization at the certified budget.** If `certify?` accepts and declares canonical
representatives, then at every level of the chain, for every secret within the bound and every
set of gadget keys for `s²` generated at the top level with noise at most `keyNoise`, OpenFHE's
relinearization (reading the first digits of those keys) meets the `relin` contract at
`c.budget`. -/
theorem certify?_relinOpenFHE (x : Input) (c : Certificate) (h : certify? x = some c)
    (hc : x.lay.canonical = true)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N))
    (hkeys : GadgetKeysOK c.params x.lay c.params.src.qs.length .square s keys)
    (ρ ρ' : Env c.params.src) (σ : Trace.CtEnv c.params) (d a : Var) (v : Val c.params.src)
    (ca : List (IntPoly c.params.src.N))
    (hstep : step c.params.src ρ (.relin d a) = some ρ') (hv : ρ a = some v)
    (hca : σ a = some ca) (h1 : 1 ≤ v.level) (hL : v.level ≤ c.params.src.qs.length)
    (hlen : ca.length = v.parts) :
    Trace.StepOK c.params c.budget s ρ ρ' σ
      (σ.set d (relinOpenFHE c.params x.lay v.level ca keys)) (.relin d a) := sorry

/-- **Key switching at the certified budget**, with top-level keys for the secret `s` and the
target `σ_g(s)`, `g` the operand's key. -/
theorem certify?_keySwitchOpenFHE (x : Input) (c : Certificate) (h : certify? x = some c)
    (hc : x.lay.canonical = true)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (ρ ρ' : Env c.params.src) (σ : Trace.CtEnv c.params) (d a : Var) (v : Val c.params.src)
    (ca : List (IntPoly c.params.src.N))
    (hstep : step c.params.src ρ (.keySwitch d a) = some ρ') (hv : ρ a = some v)
    (hca : σ a = some ca) (h1 : 1 ≤ v.level) (hL : v.level ≤ c.params.src.qs.length)
    (hlen : ca.length = v.parts)
    (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N))
    (hkeys : GadgetKeysOK c.params x.lay c.params.src.qs.length (.galois v.key) s keys) :
    Trace.StepOK c.params c.budget s ρ ρ' σ
      (σ.set d (keySwitchOpenFHE c.params x.lay v.level ca keys)) (.keySwitch d a) := sorry

/-- **OpenFHE v1.6.1's rotation at the certified budget**: the run of
`automorph m a g; keySwitch d m` of `rotateOpenFHE161_run`, at `c.budget`, with OpenFHE's stored
rotation keys for `g` generated once at the top level (gadget keys for `s'`, `σ_g(s') = s`,
target `σ_g(s')`). -/
theorem certify?_rotateOpenFHE161 (x : Input) (c : Certificate) (h : certify? x = some c)
    (hc : x.lay.canonical = true)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (ρ : Env c.params.src) (σ : Trace.CtEnv c.params) (d m a : Var) (g : ℕ) (hg : g % 2 = 1)
    (v : Val c.params.src) (ca : List (IntPoly c.params.src.N)) (hv : ρ a = some v)
    (hca : σ a = some ca) (h1 : 1 ≤ v.level) (hL : v.level ≤ c.params.src.qs.length)
    (hkey : v.key = 1) (hparts : v.parts = 2) (hlen : ca.length = 2)
    (s' : IntPoly c.params.src.N) (hs' : automorph g s' = s)
    (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N))
    (hkeys : GadgetKeysOK c.params x.lay c.params.src.qs.length (.galois g) s' keys) :
    Trace.Run c.params c.budget s [.automorph m a g, .keySwitch d m] ρ σ
      ((σ.set m (ca.map (automorph g))).set d
        (rotateOpenFHE161 c.params x.lay v.level g ca keys)) := sorry

/-- **Modulus switching at the certified budget**: the centred t-corrected switch of every
component (`Challenge.Source.bgvModSwitchComp`, the integer form the harness compares with
OpenFHE's `ModReduce`) meets the `modSwitch` contract at `c.budget`, for any number of
components, for every secret within the bound. -/
theorem certify?_modSwitch (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (ρ ρ' : Env c.params.src) (σ : Trace.CtEnv c.params) (d a : Var) (v : Val c.params.src)
    (ca : List (IntPoly c.params.src.N))
    (hstep : step c.params.src ρ (.modSwitch d a) = some ρ') (hv : ρ a = some v)
    (hca : σ a = some ca) (hlen : ca.length = v.parts) :
    Trace.StepOK c.params c.budget s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp c.params.src.t
        c.params.src.qs[v.level - 1]!))) (.modSwitch d a) := sorry

end Challenge.Realize
