import Challenge.Sanity.Lattigo
import Validation.Sanity.EndToEnd
import Validation.Profile.Named
import Validation.Instances.Lattigo

/-!
# Validation.Sanity.Lattigo — proofs of the pins of `Challenge.Sanity.Lattigo`

The run is `Validation.Budget.certified_run_exists` (textbook steps, noiseless keys inside the
proof); acceptance gives the analysis, the coverage check the special primes and the layout.
-/

namespace Validation.Sanity
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.Instances.Lattigo

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
      Challenge.Certify.OutputsCertified P (Budget.certified P lay) prog sw outs s
        (fun x => .exact (m x)) cts := by
  obtain ⟨hP, hk, hS, hlay⟩ := Validation.ProfileNamed.coversBGV?_side P lay K _ hc
  obtain ⟨-, -, hB, -⟩ := Validation.Profile.certifyProfile?_some h
  obtain ⟨cts, hin, hb⟩ :=
    Validation.ProfileInputs.certifyProfile?_inputs_exist_all P _ prog sw B outs h s m
  obtain ⟨σ, hσ⟩ := Validation.Budget.certified_run_exists P lay prog B hP hk hS hlay hB s hs _
    cts hin
  exact ⟨cts, σ, hin, hb, hσ,
    Validation.Profile.certifyProfile?_sound P _ prog sw B outs h s _ cts hin hb⟩

theorem lattigo_end_to_end (P : FullParams) (hi : instanceOK? P = true) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyProfile? P (profile P) prog sw = some (B, outs))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (m : Var → Poly P.src.t P.src.N) :
    ∃ (cts : Var → List (IntPoly P.src.N)) (σ : Trace.CtEnv P),
      InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.Run P (profile P) s prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σ ∧
      Challenge.Certify.OutputsCertified P (profile P) prog sw outs s (fun x => .exact (m x))
        cts :=
  certifyProfile?_certified_end_to_end P (layout P) maxParts prog sw B outs h
    (Validation.Instances.Lattigo.instanceOK?_facts hi).1 s hs m

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
        Challenge.Certify.OutputsCertified exampleLogN14 (profile exampleLogN14) (chain 12 4)
          false outs s (fun x => .exact (m x)) cts := by
  have hacc := (Validation.Instances.Lattigo.exampleLogN14_accepts).1
  rcases hr : certifyProfile? exampleLogN14 (profile exampleLogN14) (chain 12 4) false with
    _ | ⟨B, outs⟩
  · rw [hr] at hacc; exact absurd hacc (by decide)
  exact ⟨B, outs, rfl, fun s hs m => lattigo_end_to_end exampleLogN14
    Validation.Instances.Lattigo.exampleLogN14_instanceOK _ false B outs hr s hs m⟩

example := (@certifyProfile?_certified_end_to_end :
  type_of% @Challenge.Sanity.certifyProfile?_certified_end_to_end)
example := (@lattigo_end_to_end : type_of% @Challenge.Sanity.lattigo_end_to_end)
example := (@lattigoLogN14_end_to_end : type_of% @Challenge.Sanity.lattigoLogN14_end_to_end)

end Validation.Sanity
