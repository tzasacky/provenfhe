import Challenge.Profile.Tool
import Challenge.IndCpaD.ProfileBGVKS
import Challenge.IndCpaD.LMBFV

/-!
# Challenge.Profile.Achieve — accepted and covered: a named evaluator's run exists and its outputs decrypt   (LOCKED statements; proofs in `Validation/Profile/Achieve.lean`)

A profile certificate (`Challenge.Profile`) is sound at every budget, the zero budget included;
on its own it does not say that any run within the budget exists. The statements here say that
when the profile certificate accepts AND the coverage check passes, a concrete evaluator produces
a run that meets the contracts within the profile, so the certificate applies to it and its
outputs decrypt:

* `achieve_bgv`: the evaluator `Challenge.IndCpaDProfile.ksRun` (exact operations, hybrid
  relinearization and key switching `relinOpenFHE`, `keySwitchOpenFHE` at the operand's level with
  ONE top-level key set, the centred t-corrected modulus switch), on input ciphertexts meeting the
  input hypotheses of `certifyProfile?_sound`;
* `achieve_bfv`: the evaluator `bfvRun` below, the run of the step function
  `Challenge.IndCpaDLM.bfvStep` (textbook operations, the textbook Fan–Vercauteren product, the
  transcribed key switch `relinBFV`, `keySwitchBFV` with per-level keys, the rounding modulus
  switch), under the level-exact check `coversBFVAt?` with any lift slack `U` and any rounding
  slack `r ≥ 1` (the textbook product is in every such family). `bfvRun_eq_irun`: it is the run
  `Challenge.IndCpaDLM.irun` of `interpEval` with that step function.

Hypotheses that the certificate and the coverage check do NOT discharge, kept explicit:
BGV: canonical digits (`lay.canonical`), and the two conditions under which one top-level key set
can be cut to every level (`Spec.Certify.layoutOK?`, `Spec.Certify.keysRestrict?`; `certify?`
checks both, `coversBGV?` neither); every key switch's operand under a Galois element whose keys
are supplied (`rots`); every modulus switch's operand with at most `K` components. BFV:
`ksDeclOK?`; the Galois elements as for BGV; two-component operands at every `mul`, `square` and
`modSwitch` (the textbook product and the rounding switch are proved for two components only).
These conditions on instructions are stated on a run on the given messages (`pre ++ i :: post`,
as `Challenge.Profile.Tool`); levels and numbers of components do not depend on the messages.
-/

namespace Challenge.ProfileAchieve
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.CertifyBFV Challenge.BFV
  Challenge.RealizeBFV Challenge.Realize Challenge.IndCpaDProfile Challenge.IndCpaDLM

/-- **The BFV evaluator's run**: `Challenge.IndCpaDLM.bfvStep` along a body, alongside the replay
of `Source.step` (as `Challenge.IndCpaDProfile.ksRun`). -/
def bfvRun (P : FullParams) (lay : Budget.KSLayout)
    (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N)) :
    List Instr → Env P.src → Trace.CtEnv P → Option (Trace.CtEnv P)
  | [], _, σ => some σ
  | i :: is, ρ, σ => (step P.src ρ i).bind fun ρ' =>
      (bfvStep P lay rk gk ρ σ i).bind fun σ' => bfvRun P lay rk gk is ρ' σ'

/-- `bfvRun` is the run of the interpreter `interpEval` with the step function `bfvStepFn`. -/
theorem bfvRun_eq_irun (D : Spec.IndCpaDProfile.AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) (pk : D.PK)
    (body : List Instr) (ρ : Env D.P.src) (σ : Trace.CtEnv D.Pe) :
    irun D (bfvStepFn D lay rk gk) pk body ρ σ = bfvRun D.Pe lay (rk pk) (gk pk) body ρ σ := sorry

/-- **Achievability (BGV).** If `certifyProfile?` accepts at `E` and `coversBGV? P lay K E`
passes, then for every secret within the bound, top-level gadget keys for `s²` and for `σ_g(s)`,
`g ∈ rots`, and input ciphertexts meeting the input hypotheses, the evaluator `ksRun` produces a
run within `E`, and every output of it decrypts with `s` to the message the program computes,
within its certified bound. -/
theorem achieve_bgv (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool) (B : ℕ)
    (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (lay : Budget.KSLayout) (K : ℕ) (hc : coversBGV? P lay K E = true)
    (hcan : lay.canonical = true) (hlo : Spec.Certify.layoutOK? P lay = true)
    (hkr : Spec.Certify.keysRestrict? P = true) (rots : List ℕ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (hrk : Budget.GadgetKeysOK P lay P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hgk : ∀ g ∈ rots, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) s (gk g))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : InputsOK P s prog msgs cts) (hb : Trace.BoundsOK P s prog msgs cts)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.key ∈ rots)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.parts ≤ K) :
    ∃ σf, ksRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
        ∀ o ∈ prog.outputs, ∃ v ct m b, ρ o = some v ∧ σf o = some ct ∧
          outs.lookup o = some b ∧ Encrypts P s b v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
          bgvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m := sorry

/-- **Achievability (BFV).** If `certifyBFVProfile?` accepts at `E` and the level-exact check
`coversBFVAt? P lay U r prog E` passes with `r ≥ 1`, then for every secret within the bound,
gadget keys at every level for `s²` and for `σ_g(s)`, `g ∈ rots`, and inputs meeting the input
hypothesis, the evaluator `bfvRun` produces a run within `E`, and every output of it decrypts
with `s` to the message the program computes, within its certified bound. -/
theorem achieve_bfv (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) (B : ℕ)
    (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (lay : Budget.KSLayout) (U r : ℕ) (hc : coversBFVAt? P lay U r prog E = true) (hr : 1 ≤ r)
    (hdecl : ksDeclOK? P lay = true) (rots : List ℕ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
      Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : TraceBFV.InputsOK P s prog msgs cts)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.key ∈ rots)
    (hmul : ∀ (pre post : List Instr) (d a b : Var) (ρ : Env P.src) (x y : Val P.src),
      prog.body = pre ++ .mul d a b :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → ρ b = some y →
      x.parts = 2 ∧ y.parts = 2)
    (hsq : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .square d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.parts = 2)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.parts = 2) :
    ∃ σf, bfvRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
        ∀ o ∈ prog.outputs, ∃ v ct m b, ρ o = some v ∧ σf o = some ct ∧
          outs.lookup o = some b ∧ Encrypts P s b v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
          bfvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m := sorry

end Challenge.ProfileAchieve
