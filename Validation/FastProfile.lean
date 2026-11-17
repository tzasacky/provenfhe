import Challenge.Fast.Profile
import Challenge.Profile.Tool
import Validation.Fast
import Validation.FastBFV
import Validation.Profile.Tool

/-!
# Validation.FastProfile — the fast profile decisions and BFV coverage checks equal the locked ones

Proofs of the pins of `Challenge.Fast.Profile`, by the argument of `Validation.Fast` and
`Validation.FastBFV`, whose lemmas are stated at every budget:

* `certifyProfile?` is `Challenge.Certify.checked?` with three guards fewer and a scheme guard
  more, at the budget `E`: `refAnalyze` is `run` followed by `outBound`
  (`Validation.Fast.Aux.refAnalyze_eq`), and `outputBound?` reads the final environments of that
  same run (`outputBound?_eq`);
* `certifyBFVProfile?` is the analysis part of `certifyBFV?` at `E`
  (`Validation.FastBFV.Aux.refAnalyzeBFV_eq`, `Aux2.outputsUnderS?_eq`), and its input clause is
  `inputsDecOKWith` at the locked input bound, by `rfl`;
* `coversBFV?` reads the body by position; `needAllGo` walks it once, and the per-level
  key-switching check is the comparison with the largest bound (`ksCoversBFV_eq`);
* `coversBFVAt?` replays the body on closures; `needGo` replays it in a tree (`Source.step`
  changes only the destination), and `needAtWith` is `needAt` at the locked numbers by `rfl`.

No `Challenge.*` definition is unfolded with `simp`/`rw`/`unfold`: local `rfl` equations only.
-/

namespace Validation.FastProfile
open Spec Spec.Source Challenge.Headline Challenge.Profile
open FHE.Noise.Fast (VMap mapOf boundMap initEnvMap)
open FHE.Noise.FastProfile
open Validation.Fast.Aux (insert_get initEnvMap_get)

namespace Aux

/-! ### BGV -/

theorem certifyProfile_eq (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool) :
    certifyProfile P E prog sw = certifyProfile? P E prog sw := by
  have e : certifyProfile? P E prog sw = (do
      guard (schemeParamsOK? P)
      guard (P.src.kind = .bgv)
      guard (!prog.outputs.isEmpty)
      guard (Challenge.Certify.inputsMsgOK? P prog)
      let B ← refAnalyze P E prog
      let outs ← prog.outputs.mapM fun o =>
        (Challenge.Certify.outputBound? P E prog sw o).map fun b => (o, b)
      pure (B, outs)) := rfl
  rw [e, certifyProfile, Validation.Fast.Aux.refAnalyze_eq, Validation.Fast.inputsMsgOK_eq]
  cases hr : FHE.Noise.Fast.run P E prog with
  | none => simp only [Option.bind_eq_bind, Option.bind_none]
  | some r =>
    have hf : (fun o => (Challenge.Certify.outputBound? P E prog sw o).map fun b => (o, b)) =
        fun o => (FHE.Noise.Fast.outputBound P r sw o).map fun b => (o, b) := by
      funext o; rw [Validation.Fast.Aux.outputBound?_eq P E hr]
    rw [hf]
    rfl

/-! ### BFV -/

theorem inputsDecOK_eq (P : FullParams) (prog : Program) :
    inputsDecOKWith P prog (FHE.Noise.FastBFV.inputBound P (boundMap prog)) =
      inputsDecOK P prog := by
  rw [Validation.FastBFV.Aux2.inputBound_eq']; rfl

theorem plainBoundsOK_eq (P : FullParams) (prog : Program) :
    FHE.Noise.FastBFV.plainBoundsOKWith P prog (FHE.Noise.FastBFV.inputBound P (boundMap prog)) =
      Challenge.CertifyBFV.plainBoundsOK P prog := by
  rw [Validation.FastBFV.Aux2.inputBound_eq']; rfl

theorem certifyBFVProfile_eq (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    certifyBFVProfile P E prog = certifyBFVProfile? P E prog := by
  have e : certifyBFVProfile? P E prog = (do
      guard (schemeParamsOK? P)
      guard (P.src.kind = .bfv)
      guard (!prog.outputs.isEmpty)
      guard (inputsDecOK P prog)
      guard (Challenge.CertifyBFV.plainBoundsOK P prog)
      guard (P.src.t - 1 ≤ P.src.qs.headD 0 / 2)
      let B ← Challenge.BFV.refAnalyzeBFVAt P E prog
      guard (Encrypt.outputsUnderS? P.src prog)
      let outs ← prog.outputs.mapM fun o =>
        (Challenge.BFV.refAnalyzeBFVAt P E { prog with outputs := [o] }).map fun b => (o, b)
      pure (B, outs)) := rfl
  rw [e, certifyBFVProfile, inputsDecOK_eq, plainBoundsOK_eq, Validation.FastBFV.Aux.refAnalyzeBFV_eq]
  cases hr : FHE.Noise.FastBFV.run P E prog with
  | none => simp only [Option.bind_eq_bind, Option.bind_none]
  | some r =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases hB : FHE.Noise.FastBFV.outBound r prog.outputs with
    | none => simp only [Option.bind_none]
    | some B =>
      simp only [Option.bind_some]
      rw [Validation.FastBFV.Aux2.outputsUnderS?_eq P E hr
        (Validation.FastBFV.Aux2.outBound_isSome hB)]
      have hf : (fun o => (Challenge.BFV.refAnalyzeBFVAt P E
          { prog with outputs := [o] }).map fun b => (o, b)) =
          fun o => (FHE.Noise.FastBFV.outBound r [o]).map fun b => (o, b) := by
        funext o
        have hrun : FHE.Noise.FastBFV.run P E { prog with outputs := [o] } = some r := hr
        rw [Validation.FastBFV.Aux.refAnalyzeBFV_eq, hrun]; rfl
      rw [hf]

/-! ### The conservative coverage check -/

theorem all_le_foldl_max (b : ℕ) : ∀ (l : List ℕ) (a : ℕ),
    ((l.all fun x => decide (x ≤ b)) && decide (a ≤ b)) = decide (l.foldl max a ≤ b) := by
  intro l
  induction l with
  | nil =>
    intro a; simp only [List.all_nil, Bool.true_and, List.foldl_nil]
    exact decide_eq_decide.mpr Iff.rfl
  | cons x l ih =>
    intro a
    rw [List.foldl_cons, ← ih]
    simp only [List.all_cons, max_le_iff, Bool.decide_and]
    cases (l.all fun x => decide (x ≤ b)) <;> cases decide (x ≤ b) <;> cases decide (a ≤ b) <;>
      rfl

theorem ksCoversBFV_eq (P : FullParams) (lay : Budget.KSLayout) (b : ℕ) :
    ksCoversBFV P lay b = decide (ksMax P lay ≤ b) := by
  have e : ksCoversBFV P lay b = (List.range P.src.qs.length).all fun j =>
      decide (BudgetBFV.ksBoundAt P lay (j + 1) ≤ b) := rfl
  rw [e, ksMax, ← all_le_foldl_max, List.all_map]
  simp only [Nat.zero_le, decide_true, Bool.and_true]
  rfl

/-- What the locked `coversBFV?` asks of the instruction at one position. -/
def needOpt (ml mr km ms : ℕ) (Ek : TraceBFV.Budget) : Option Instr → Bool
  | some i => needWith ml mr km ms Ek i
  | none => true

theorem needAllGo_range (ml mr km ms : ℕ) (E : ℕ → TraceBFV.Budget) : ∀ (l : List Instr) (n : ℕ),
    needAllGo ml mr km ms E n l =
      (List.range l.length).all fun k => needOpt ml mr km ms (E (n + k)) l[k]? := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons i l ih =>
    intro n
    rw [needAllGo, ih, List.length_cons, List.range_succ_eq_map, List.all_cons, List.all_map]
    simp only [Nat.add_zero, List.getElem?_cons_zero, Function.comp_def,
      List.getElem?_cons_succ]
    have h : ∀ k, n + 1 + k = n + (k + 1) := fun k => by omega
    simp only [h]
    rfl

theorem coversBFV_eq (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) : coversBFV P lay U r body E = coversBFV? P lay U r body E := by
  have e : coversBFV? P lay U r body E =
      (schemeParamsOK? P && Budget.specialOK? P &&
        (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
        (List.range body.length).all fun k =>
          match body[k]? with
          | some (.mul ..) | some (.square ..) =>
            decide (BudgetBFV.mulLiftApprox P U ≤ (E k).mulLift) &&
              decide (BudgetBFV.mulRoundApprox P r ≤ (E k).mulRound)
          | some (.relin ..) | some (.keySwitch ..) => ksCoversBFV P lay (E k).keySwitch
          | some (.modSwitch ..) => decide (BudgetBFV.msBudget P ≤ (E k).modSwitch)
          | _ => true) := rfl
  rw [e, coversBFV, needAllGo_range]
  congr 1
  congr 1
  funext k
  simp only [Nat.zero_add]
  cases body[k]? with
  | none => rfl
  | some i => cases i <;> simp only [needOpt, needWith, ksCoversBFV_eq]

/-! ### The level-exact coverage check -/

theorem ksAtT_ksTable (P : FullParams) (lay : Budget.KSLayout) :
    ksAtT P lay (ksTable P lay) = fun ℓ => BudgetBFV.ksBoundAt P lay ℓ := by
  funext ℓ
  unfold ksAtT
  cases h : (ksTable P lay)[ℓ]? with
  | none => rfl
  | some q =>
    simp only [ksTable, List.getElem?_toArray, List.getElem?_map] at h
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
    have : k = ℓ := by
      rw [List.getElem?_eq_some_iff] at hk
      obtain ⟨_, hk⟩ := hk
      simpa using hk.symm
    subst this
    rfl

theorem needAtWith_eq (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (Ek : TraceBFV.Budget) (ρ : Env P.src) (i : Instr) :
    needAtWith (BudgetBFV.mulLiftApprox P U) (BudgetBFV.mulRoundApprox P r)
      (BudgetBFV.msBudget P) (fun ℓ => BudgetBFV.ksBoundAt P lay ℓ) Ek ρ i =
      needAt P lay U r Ek ρ i := by
  cases i <;> rfl

theorem needAux_cons (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (E : ℕ → TraceBFV.Budget) (n : ℕ) (i : Instr) (is : List Instr) (ρ : Env P.src) :
    needAux P lay U r E n (i :: is) ρ = (needAt P lay U r (E n) ρ i &&
      match step P.src ρ i with
      | some ρ' => needAux P lay U r E (n + 1) is ρ'
      | none => true) := rfl

theorem needGo_eq (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (E : ℕ → TraceBFV.Budget) : ∀ (is : List Instr) (n : ℕ) (ρ : VMap (Val P.src)),
    needGo P.src (BudgetBFV.mulLiftApprox P U) (BudgetBFV.mulRoundApprox P r)
      (BudgetBFV.msBudget P) (fun ℓ => BudgetBFV.ksBoundAt P lay ℓ) E n is ρ =
      needAux P lay U r E n is (fun x => ρ[x]?) := by
  intro is
  induction is with
  | nil => intro n ρ; rfl
  | cons i is ih =>
    intro n ρ
    rw [needAux_cons, needGo, needAtWith_eq]
    cases hs : step P.src (fun y => ρ[y]?) i with
    | none => rfl
    | some ρ' =>
      obtain ⟨v, hv⟩ := Validation.Headline.NoiseAux.step_set hs
      have hd : ρ' (Trace.dst i) = some v := by rw [hv]; simp [Env.set]
      simp only [hd]
      rw [ih, insert_get, hv]
      rfl

theorem coversBFVAt_eq (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) : coversBFVAt P lay U r prog E = coversBFVAt? P lay U r prog E := by
  have e : coversBFVAt? P lay U r prog E =
      (schemeParamsOK? P && decide (P.src.kind = .bfv) && Budget.specialOK? P &&
        (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
        needAux P lay U r E 0 prog.body (initEnv P.src prog fun _ => .exact 0)) := rfl
  rw [e, coversBFVAt, ksAtT_ksTable, needGo_eq, initEnvMap_get]

end Aux

end Validation.FastProfile

/-! ### The pins -/

namespace Validation.Fast

theorem certifyProfileFast_eq : Challenge.Fast.ProfileEqRef FHE.Holes.certifyProfileFast :=
  fun P E prog sw => Validation.FastProfile.Aux.certifyProfile_eq P E prog sw

theorem certifyBFVProfileFast_eq :
    Challenge.Fast.ProfileBFVEqRef FHE.Holes.certifyBFVProfileFast :=
  fun P E prog => Validation.FastProfile.Aux.certifyBFVProfile_eq P E prog

theorem coversBFVFast_eq : Challenge.Fast.CoversBFVEqRef FHE.Holes.coversBFVFast :=
  fun P lay U r body E => Validation.FastProfile.Aux.coversBFV_eq P lay U r body E

theorem coversBFVAtFast_eq : Challenge.Fast.CoversBFVAtEqRef FHE.Holes.coversBFVAtFast :=
  fun P lay U r prog E => Validation.FastProfile.Aux.coversBFVAt_eq P lay U r prog E

end Validation.Fast

/-! ### The tool's computed budget passes the fast profile decision (round trip)

Table-mode acceptance implies fast profile-mode acceptance at the computed budget, with the
same bounds: `Challenge.Profile.certify?_profile` (`certifyBFV?_profile`) with the equalities
above. Not locked: two lines from locked statements. -/

namespace Validation.FastProfile

theorem certifyFast_profileFast (x : Spec.Certify.Input) (c : Spec.Certify.Certificate)
    (h : FHE.Holes.certifyFast x = some c) :
    FHE.Holes.certifyProfileFast c.params c.budget x.prog x.switched = some (c.bound, c.outputs) := by
  rw [Validation.Fast.certifyFast_eq x] at h
  rw [Validation.Fast.certifyProfileFast_eq c.params c.budget x.prog x.switched]
  exact Validation.Profile.certify?_profile x c h

theorem certifyBFVFast_profileFast (x : Spec.CertifyBFV.InputBFV)
    (c : Spec.CertifyBFV.CertificateBFV) (h : FHE.Holes.certifyBFVFast x = some c) :
    FHE.Holes.certifyBFVProfileFast x.P c.budget x.prog = some (c.bound, c.outputs) := by
  rw [Validation.Fast.certifyBFVFast_eq x] at h
  rw [Validation.Fast.certifyBFVProfileFast_eq x.P c.budget x.prog]
  exact Validation.Profile.certifyBFV?_profile x c h

end Validation.FastProfile
