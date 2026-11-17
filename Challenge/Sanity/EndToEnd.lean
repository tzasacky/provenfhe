import Challenge.Profile.Achieve
import Challenge.Profile.Inputs
import Challenge.Budget

/-!
# Challenge.Sanity.EndToEnd — every hypothesis of the headlines, jointly   (LOCKED statements; proofs in `Validation/Sanity/EndToEnd.lean`)

The soundness statements assume acceptance, inputs meeting the input hypotheses, and quantify
over the runs within the budget. Each was shown satisfiable separately (`docs/TRUSTED-CORE.md`,
F4). The statements here satisfy them TOGETHER: for every accepted program, every secret within
`secretBound` and every assignment of messages there are inputs meeting the input hypotheses and
a run within the budget, so the conclusion of the soundness statement is about at least one run
for every message. In the profile modes the run is the one a named evaluator computes from the
public keys alone, for EVERY choice of valid keys; valid keys exist with every random part
(`gadgetKeys_exist_any`).

What remains a hypothesis is listed in each docstring; everything else is discharged by
acceptance and the coverage check. In particular the two-component conditions of
`Challenge.ProfileAchieve.achieve_bfv` (`hmul`, `hsq`, `hms`) are gone (acceptance implies
them: the reference analysis rejects the other cases, `Challenge.BFV.domainOK`), and the Galois
condition (`hrot`) and BGV's component bound (`hms`) become properties of the program on the
zero-message replay. In the `*_end_to_end` statements `hrot` is discharged by keys for every
Galois element below `2N` (every key a replay reaches is below `2N`).
-/

namespace Challenge.Sanity
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.CertifyBFV Challenge.BFV
  Challenge.RealizeBFV Challenge.Realize Challenge.IndCpaDProfile Challenge.ProfileAchieve
  Spec.CertifyBFV

/-! ## Keys with any random part -/

/-- **Valid gadget keys exist for every secret and every choice of their random parts**: for every
list `as` of the right length there are keys whose second components are `as` (so the witness
is not the degenerate `a = 0`). -/
theorem gadgetKeys_exist_any (P : FullParams) (lay : Budget.KSLayout) (ℓ : ℕ) (tgt : KeyTarget)
    (s : IntPoly P.src.N) (as : List (IntPoly P.src.N)) (has : as.length = (lay.sizes ℓ).length) :
    ∃ keys : List (IntPoly P.src.N × IntPoly P.src.N),
      keys.map Prod.snd = as ∧ Budget.GadgetKeysOK P lay ℓ tgt s keys := sorry

/-! ## BFV, profile mode -/

/-- **BFV achievability with only the hypotheses no check discharges.** As
`Challenge.ProfileAchieve.achieve_bfv`, without `hmul`, `hsq`, `hms` (implied by acceptance), and
with the Galois condition `hrot` stated on the zero-message replay (a property of the program
alone, decidable by running it) instead of on the run on `msgs`. What remains: the coverage
check, `r ≥ 1`, `ksDeclOK?`, `hrot`, the keys, the secret bound and the inputs. -/
theorem achieve_bfv_accepted (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) (B : ℕ)
    (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (lay : Budget.KSLayout) (U r : ℕ) (hc : coversBFVAt? P lay U r prog E = true) (hr : 1 ≤ r)
    (hdecl : ksDeclOK? P lay = true) (rots : List ℕ)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.key ∈ rots)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
      Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : TraceBFV.InputsOK P s prog msgs cts) :
    ∃ σf, bfvRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      OutputsCertifiedBFV P E prog outs s msgs cts := sorry

/-- **BFV profile mode, all hypotheses at once.** If the profile decision accepts and the
level-exact coverage check passes (with `r ≥ 1` and the key-switching declaration check), then for
every secret within the bound and every assignment of messages there are valid keys for `s²` and
every `σ_g(s)` at every level, inputs meeting `TraceBFV.InputsOK`, and a run within `E` (the one
`bfvRun` computes), and every output of every run is certified. -/
theorem certifyBFVProfile?_end_to_end (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (lay : Budget.KSLayout) (U r : ℕ) (hc : coversBFVAt? P lay U r prog E = true) (hr : 1 ≤ r)
    (hdecl : ksDeclOK? P lay = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (m : Var → Poly P.src.t P.src.N) :
    ∃ (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
      (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
      (cts : Var → List (IntPoly P.src.N)) (σf : Trace.CtEnv P),
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
        Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
        ∀ g, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ)) ∧
      TraceBFV.InputsOK P s prog (fun x => .exact (m x)) cts ∧
      bfvRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σf ∧
      OutputsCertifiedBFV P E prog outs s (fun x => .exact (m x)) cts := sorry

/-! ## BGV, profile mode -/

/-- **BGV achievability with only the hypotheses no check discharges.** As
`Challenge.ProfileAchieve.achieve_bgv`, with the bound `K` on the components of every
modulus-switched operand (`hms`) and the Galois condition (`hrot`) stated on the zero-message
replay (properties of the program alone, decidable by running it) instead of on the run on
`msgs`. What remains: canonical digits, `layoutOK?` and `keysRestrict?` (which `coversBGV?` does
not check; `certify?` checks the last two), `hms`, `hrot`, the keys, the secret bound and the
inputs. -/
theorem achieve_bgv_accepted (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (lay : Budget.KSLayout) (K : ℕ) (hc : coversBGV? P lay K E = true)
    (hcan : lay.canonical = true) (hlo : Spec.Certify.layoutOK? P lay = true)
    (hkr : Spec.Certify.keysRestrict? P = true)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.parts ≤ K)
    (rots : List ℕ)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.key ∈ rots)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (hrk : Budget.GadgetKeysOK P lay P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hgk : ∀ g ∈ rots, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) s (gk g))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : InputsOK P s prog msgs cts) (hb : Trace.BoundsOK P s prog msgs cts) :
    ∃ σf, ksRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      Certify.OutputsCertified P E prog sw outs s msgs cts := sorry

/-- **BGV profile mode, all hypotheses at once.** Under the hypotheses of `achieve_bgv_accepted`
that concern the program and the parameters, for every secret within the bound and every
assignment of messages there are valid top-level keys for `s²` and every `σ_g(s)`, inputs meeting
`InputsOK` and `Trace.BoundsOK`, and a run within `E` (the one `ksRun` computes), and every output
of every run is certified. -/
theorem certifyProfile?_end_to_end (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (lay : Budget.KSLayout) (K : ℕ) (hc : coversBGV? P lay K E = true)
    (hcan : lay.canonical = true) (hlo : Spec.Certify.layoutOK? P lay = true)
    (hkr : Spec.Certify.keysRestrict? P = true)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.parts ≤ K)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (m : Var → Poly P.src.t P.src.N) :
    ∃ (rk : List (IntPoly P.src.N × IntPoly P.src.N))
      (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
      (cts : Var → List (IntPoly P.src.N)) (σf : Trace.CtEnv P),
      Budget.GadgetKeysOK P lay P.src.qs.length .square s rk ∧
      (∀ g, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) s (gk g)) ∧
      InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts ∧
      ksRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      Trace.Run P E s prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σf ∧
      Certify.OutputsCertified P E prog sw outs s (fun x => .exact (m x)) cts := sorry

/-! ## BFV and BGV, default mode -/

/-- **`certifyBFV?`, all hypotheses at once**: for every accepted input, every secret within the
bound and every assignment of messages, there are inputs meeting `TraceBFV.InputsOK` and a run
within `c.budget`, and the certificate's conclusion holds. No further hypothesis. -/
theorem certifyBFV?_end_to_end (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (m : Var → Poly x.P.src.t x.P.src.N) :
    ∃ (cts : Var → List (IntPoly x.P.src.N)) (σ : Trace.CtEnv x.P),
      TraceBFV.InputsOK x.P s x.prog (fun y => .exact (m y)) cts ∧
      TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog fun y => .exact (m y))
        (Trace.initCt x.P x.prog cts) σ ∧
      OutputsCertifiedBFV x.P c.budget x.prog c.outputs s (fun y => .exact (m y)) cts := sorry

/-- **`certify?`, all hypotheses at once**: for every accepted input (any mode), every secret
within the bound and every assignment of messages, there are inputs meeting `InputsOK` and
`Trace.BoundsOK` at the analysed parameters and a run within `c.budget`, and the certificate's
conclusion holds. No further hypothesis. -/
theorem certify?_end_to_end (x : Certify.Input) (c : Certify.Certificate)
    (h : Certify.certify? x = some c)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (m : Var → Poly c.params.src.t c.params.src.N) :
    ∃ (cts : Var → List (IntPoly c.params.src.N)) (σ : Trace.CtEnv c.params),
      InputsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.BoundsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.Run c.params c.budget s x.prog.body (initEnv c.params.src x.prog fun y => .exact (m y))
        (Trace.initCt c.params x.prog cts) σ ∧
      Certify.OutputsCertified c.params c.budget x.prog x.switched c.outputs s
        (fun y => .exact (m y)) cts := sorry

end Challenge.Sanity
