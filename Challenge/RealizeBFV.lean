import Challenge.Realize.OpenFHEBFV
import Challenge.BFVMul.KSLeveled

/-!
# Challenge.RealizeBFV — OpenFHE's BFV key switching meets the contracts   (LOCKED statements; proofs in `Validation/RealizeBFV.lean`)

`Challenge.BFV.relin_realizable`, `keySwitch_realizable` and `Challenge.BFVMul.ksCore_realizable`
say that *some* function of the operand and the keys meets the contract (their witness is an
idealised centred algorithm). The statements here name the function: the transcription of
OpenFHE v1.6.1's BFV key switching in `Challenge.Realize.OpenFHEBFV` (HYBRID: the BGV
transcription `Challenge.Realize.ksOpenFHE` at plaintext modulus `1`, canonical ModUp as the
default build computes it; BV with digit size 0: centred CRT digits). The bound is the one BFV
certificates already charge, `Spec.BudgetBFV.ksBoundAt` (for HYBRID the canonical bound,
`lay.canonical = true`, which is what the OpenFHE frontend declares; for BV the bound with one
limb per digit and no special prime): **no budget changes**.

The hypothesis `ksDeclOK? P lay` says the declared layout is the one the library uses (HYBRID:
special primes and canonical representatives; BV: no special prime and one limb per digit). It
is checked by `certifyBFV?` (`checksOK`, item 5b); with special primes and `lay.canonical = false`
the budget would be the centred one, which the canonical algorithm can exceed.

* `ksBFV_coreOK`: at level `ℓ`, with gadget keys valid at level `ℓ`, `ksBFV P lay ℓ · keys`
  meets the key-switch contract `Challenge.BFVMul.KSCoreOK` at `Q_ℓ` within `ksBoundAt P lay ℓ`.
* `ksBFV_coreOK_top`: the same with ONE key set generated at the top level and used at every level
  (the function reads its first digits), when the layout restricts (`Spec.Budget.restrictsTo`):
  what `Challenge.BFVMul.ksCore_realizable` says of an unnamed function, for the library's.
* `relinBFV_stepOK`, `keySwitchBFV_stepOK`: the `relin` and `keySwitch` step contracts of
  `Spec.TraceBFV` at every budget at least `ksBoundAt P lay ℓ` (for `keySwitch`, keys for the
  target `σ_g(s)` of the operand's key `g`, as in `Challenge.BFV.keySwitch_realizable`).
* `rotateBFV_run`: OpenFHE's BFV rotation (`EvalAutomorphism`: key switch, then `σ_g` of both
  components) is a `Spec.TraceBFV.Run` of the two instructions `automorph m a g; keySwitch d m`
  the frontend maps it to, with the intermediate `m` the textbook `σ_g` of every component (which
  OpenFHE never computes), from OpenFHE's stored rotation keys: gadget keys for the secret `s'`
  with `σ_g(s') = s` and the target `σ_g(s')` (`Challenge.Realize.rotKeySecret_exists`: such an
  `s'` exists, of the same norm).

The certificate forms, with the internal drop of `HPSPOVERQLEVELED`, are in
`Challenge.CertifyBFV.Library`, with the composition `certifyBFV?_library_run`.
-/

namespace Challenge.RealizeBFV
open Spec NPoly Scheme Source Correct Challenge.BFVMul

/-- **OpenFHE's BFV key switch of one component meets the key-switch contract** at level `ℓ`
within `Spec.BudgetBFV.ksBoundAt P lay ℓ`, for every secret within the bound, every target and
every list of gadget keys valid at level `ℓ`. -/
theorem ksBFV_coreOK (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ tgt s keys) :
    KSCoreOK (P.src.modulus ℓ) (BudgetBFV.ksBoundAt P lay ℓ) s (tgt.eval s)
      (fun d => ksBFV P lay ℓ d keys) := sorry

/-- **The same with one key set generated at the top level**, used at every level `ℓ` to which
the layout restricts (BFV: no size condition on the keys). -/
theorem ksBFV_coreOK_top (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hk : P.src.kind = .bfv) (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : Budget.restrictsTo lay P.src.qs.length ℓ = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay P.src.qs.length tgt s keys) :
    KSCoreOK (P.src.modulus ℓ) (BudgetBFV.ksBoundAt P lay ℓ) s (tgt.eval s)
      (fun d => ksBFV P lay ℓ d keys) := sorry

/-- **OpenFHE's BFV relinearization meets the `relin` contract** within `ksBoundAt`. -/
theorem relinBFV_stepOK (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : TraceBFV.Budget) (hE : BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ .square s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (relinBFV P lay ℓ ca keys)) (.relin d a) := sorry

/-- **OpenFHE's BFV key switch of a two-component ciphertext meets the `keySwitch` contract**
within `ksBoundAt`, with keys for the secret `s` and the target `σ_g(s)`, `g` the operand's key. -/
theorem keySwitchBFV_stepOK (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : TraceBFV.Budget) (hE : BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (keySwitchBFV P lay ℓ ca keys)) (.keySwitch d a) :=
  sorry

/-- **OpenFHE's BFV rotation is a run of `automorph m a g; keySwitch d m`** within `ksBoundAt`.
The operand `ca` (two components, under `s` itself) is at level `ℓ`; the keys are the stored
rotation keys for `g`: gadget keys for the secret `s'` with `σ_g(s') = s` and the target
`σ_g(s')`. The intermediate ciphertext is the textbook `σ_g` of every component (in `m`); the
final one, in `d`, is `rotateBFV P lay ℓ g ca keys`. -/
theorem rotateBFV_run (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : TraceBFV.Budget) (hE : BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ : Env P.src) (σ : Trace.CtEnv P) (d m a : Var) (g : ℕ) (hg : g % 2 = 1) (x : Val P.src)
    (ca : List (IntPoly P.src.N)) (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hkey : x.key = 1) (hparts : x.parts = 2) (hlen : ca.length = 2)
    (s' : IntPoly P.src.N) (hs' : automorph g s' = s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ (.galois g) s' keys) :
    TraceBFV.Run P E s [.automorph m a g, .keySwitch d m] ρ σ
      ((σ.set m (ca.map (automorph g))).set d (rotateBFV P lay ℓ g ca keys)) := sorry

end Challenge.RealizeBFV
