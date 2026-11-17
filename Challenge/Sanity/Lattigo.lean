import Challenge.Sanity.EndToEnd
import Challenge.Instances.Lattigo

/-!
# Challenge.Sanity.Lattigo — every hypothesis at once, at the computed BGV profile and at Lattigo's parameters   (LOCKED statements; proofs in `Validation/Sanity/Lattigo.lean`)

`Challenge.Sanity.certifyProfile?_end_to_end` needs canonical digits (`lay.canonical`): its run
is the one OpenFHE's evaluator `ksRun` computes. Lattigo's layout uses centred representatives
(`(Challenge.Instances.Lattigo.layout P).canonical = false`), so that statement does not apply
to the Lattigo instance. The statements here do not name an evaluator: at the BGV profile
`Spec.Budget.certified P lay` (the Lattigo profile is this one), acceptance and the coverage
check give, for every secret within the bound and every message, inputs and a run, jointly. At
Lattigo's 128-bit `LogN = 14` example and at its small conformance set this holds for the
programs the instance file certifies: a realistic parameter set at which every hypothesis of
`Challenge.Profile.certifyProfile?_sound` is met at once.
-/

namespace Challenge.Sanity
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.Instances.Lattigo

/-- **At the computed BGV profile, all hypotheses at once.** If `certifyProfile?` accepts at
`Budget.certified P lay` and that profile passes the coverage check (any `K`), then for every
secret within the bound and every assignment of messages there are inputs meeting `InputsOK` and
`Trace.BoundsOK` and a run within the profile, and every output of every run is certified. -/
theorem certifyProfile?_certified_end_to_end (P : FullParams) (lay : Budget.KSLayout) (K : ℕ)
    (prog : Program) (sw : Bool) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyProfile? P (Budget.certified P lay) prog sw = some (B, outs))
    (hc : coversBGV? P lay K (Budget.certified P lay) = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (m : Var → Poly P.src.t P.src.N) :
    ∃ (cts : Var → List (IntPoly P.src.N)) (σ : Trace.CtEnv P),
      InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.Run P (Budget.certified P lay) s prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σ ∧
      Certify.OutputsCertified P (Budget.certified P lay) prog sw outs s (fun x => .exact (m x))
        cts := sorry

/-- **The Lattigo instance, all hypotheses at once**: wherever `instanceOK?` holds, every program
`certifyProfile?` accepts at the Lattigo profile has, for every secret within the bound and every
message, inputs and a run within the profile. -/
theorem lattigo_end_to_end (P : FullParams) (hi : instanceOK? P = true) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyProfile? P (profile P) prog sw = some (B, outs))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (m : Var → Poly P.src.t P.src.N) :
    ∃ (cts : Var → List (IntPoly P.src.N)) (σ : Trace.CtEnv P),
      InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.Run P (profile P) s prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σ ∧
      Certify.OutputsCertified P (profile P) prog sw outs s (fun x => .exact (m x)) cts := sorry

/-- **A realistic joint witness**: at Lattigo's 128-bit `LogN = 14` example (`N = 2¹⁴`, twelve
ciphertext primes, `t = 65537`), the four-level chain is certified at the Lattigo profile, and
for every ternary-bounded secret and every message there are inputs and a run, with every
output certified. -/
theorem lattigoLogN14_end_to_end :
    ∃ B outs, certifyProfile? exampleLogN14 (profile exampleLogN14) (chain 12 4) false =
        some (B, outs) ∧
      ∀ (s : IntPoly exampleLogN14.src.N), SecretOK exampleLogN14.secretBound s →
      ∀ (m : Var → Poly exampleLogN14.src.t exampleLogN14.src.N),
      ∃ (cts : Var → List (IntPoly exampleLogN14.src.N)) (σ : Trace.CtEnv exampleLogN14),
        InputsOK exampleLogN14 s (chain 12 4) (fun x => .exact (m x)) cts ∧
        Trace.BoundsOK exampleLogN14 s (chain 12 4) (fun x => .exact (m x)) cts ∧
        Trace.Run exampleLogN14 (profile exampleLogN14) s (chain 12 4).body
          (initEnv exampleLogN14.src (chain 12 4) fun x => .exact (m x))
          (Trace.initCt exampleLogN14 (chain 12 4) cts) σ ∧
        Certify.OutputsCertified exampleLogN14 (profile exampleLogN14) (chain 12 4) false outs s
          (fun x => .exact (m x)) cts := sorry

end Challenge.Sanity
