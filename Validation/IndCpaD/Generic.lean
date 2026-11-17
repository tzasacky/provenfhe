import Challenge.IndCpaD.Generic
import Validation.IndCpaD

/-!
# Validation.IndCpaD.Generic — proofs of the pins of `Challenge.IndCpaD.Generic`

`correct_of_meets` is the proof of `Validation.IndCpaD.correct` with the library's run replaced by
the run `EvalMeets` provides, and `certifyBFV?_library_decrypts` by `certifyBFV?_sound` (every
run within the certificate's budget). `libEval_meets` is the run half of that proof:
`certifyBFV?_library_run`, after extending the rotation keys (`gk_extend`) and forgetting the
input noise (`runLibrary_inputNoise`). No locked definition is unfolded by name here: the
branches of `admissible` are reached by `change` (no equation lemma of a `Challenge` definition
is generated in this module).
-/

namespace Validation.IndCpaD
open Spec NPoly Scheme Source Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
  Challenge.CertifyBFV Challenge.BFVEncrypt Challenge.IndCpaD Spec.IndCpaDBFV

variable {St : Setting}

/-- The accepting branch of `admissible`, by `change` (local; no equation lemma). -/
theorem admissible_some (C : Circ St) (fc : FreshCertBFV)
    (hfc : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc)
    (h : admissible C = true) :
    (!(fc.cert.assumed.contains .idealised) && C.extraOK) = true := by
  change (match certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with
    | some fc => !(fc.cert.assumed.contains .idealised) && C.extraOK
    | none => false) = true at h
  rw [hfc] at h
  exact h

/-- The rejecting branch of `admissible`. -/
theorem admissible_none (C : Circ St)
    (hfc : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = none)
    (h : admissible C = true) : False := by
  change (match certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with
    | some fc => !(fc.cert.assumed.contains .idealised) && C.extraOK
    | none => false) = true at h
  rw [hfc] at h
  exact Bool.false_ne_true h

theorem correct_of_meets (St : Setting) (hSt : freshDecOK St = true)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev) : Spec.IndCpaD.Correct (schemeWith St ev) where
  fresh pk sk hk m r hr := fresh_correct hSt pk sk hk m r hr
  eval pk sk hk C hC ins hins := by
    change (if (ins.map fun p => enc pk p.1 p.2).length = C.fresh.length
        then ev pk C (ins.map fun p => enc pk p.1 p.2) else []).map (dec sk) =
      sem C (ins.map Prod.fst)
    have hadm : admissible C = true := hC
    rcases hfc : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with _ | fc
    · exact (admissible_none C hfc hadm).elim
    have hx : C.extraOK = true := ((Bool.and_eq_true _ _).mp (admissible_some C fc hfc hadm)).2
    have hcert := analysed_cert C fc hfc
    obtain ⟨-, hkind, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK _ fc.cert hcert
    by_cases hlen : ins.length = C.fresh.length
    · have hin := inputsOK_fresh C fc hfc hx pk sk hk ins hins hlen
      obtain ⟨σ, hσ, hevq⟩ := hev pk sk hk C hadm fc hfc hx ins hins hlen
      obtain ⟨ρ, hρ, hout⟩ := Validation.CertifyBFV.certifyBFV?_sound
        (analysed C fc.params.inputNoise) fc.cert hcert sk.s _ _ hin
      simp only [List.length_map, hlen, ite_true]
      rw [hevq]
      simp only [sem, List.length_map, hlen, ite_true]
      erw [List.map_map]
      change Source.eval St.base.P.src C.prog _ = some ρ at hρ
      erw [hρ]
      dsimp only
      apply List.map_congr_left
      intro o ho
      obtain ⟨v, ct, m, B, hv, hct, -, -, hm, -, hd⟩ := hout σ hσ o ho
      simp only [Function.comp, hv, hct, hm]
      unfold dec
      rw [outLevel_eq C hkind _ ρ hρ o v hv]
      exact hd
    · simp only [sem, List.length_map, hlen, ite_false]
      rfl

theorem meets_prob_eq (St : Setting) (hSt : freshDecOK St = true)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins)
    (A : Coins → PK (St := St) → Spec.IndCpaD.Adv (schemeWith St ev) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω) ∧ ∀ i, GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | Spec.IndCpaD.gameD (S := schemeWith St ev) b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | Spec.IndCpaD.gameCPA (S := schemeWith St ev) b (pk ω) (tape ω)
        (Spec.IndCpaD.reduction (S := schemeWith St ev) A (coins ω) (pk ω)) 0 = true} :=
  prob_eq (schemeWith St ev) (correct_of_meets St hSt ev hev) μ pk sk tape coins A b hgood

theorem meets_prob_le (St : Setting) (hSt : freshDecOK St = true)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins)
    (A : Coins → PK (St := St) → Spec.IndCpaD.Adv (schemeWith St ev) Bool) (b : Bool)
    (q : ℕ) (hq : ∀ r p, Spec.IndCpaD.Bounded (A r p) q) :
    μ {ω | Spec.IndCpaD.gameD (S := schemeWith St ev) b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | Spec.IndCpaD.gameCPA (S := schemeWith St ev) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := schemeWith St ev) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | Spec.IndCpaD.gameCPA (S := schemeWith St ev) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := schemeWith St ev) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | Spec.IndCpaD.gameD (S := schemeWith St ev) b (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} :=
  prob_le (schemeWith St ev) (correct_of_meets St hSt ev hev) μ pk sk tape coins A b q hq

/-- `libEval`, unfolded (a local `rfl` equation). -/
theorem libEval_eq (St : Setting) (pk : PK (St := St)) (C : Circ St) (cs : List (CT (St := St))) :
    libEval St pk C cs = C.prog.outputs.map fun o =>
      (C.outLevel o, (runLibrary C.input St.A pk.rk pk.gk (C.cts cs) o).getD []) := rfl

theorem libEval_meets (St : Setting) (hA : Spec.Float.Conforms St.A) :
    EvalMeets St (libEval St) := by
  intro pk sk hk C hadm fc hfc hx ins hins hlen
  have hadm' := admissible_some C fc hfc hadm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hadm'
  have hid' : AssumptionBFV.idealised ∉ fc.cert.assumed := by
    intro hm
    have : fc.cert.assumed.contains AssumptionBFV.idealised = true := List.elem_eq_true_of_mem hm
    rw [this] at hadm'; exact absurd hadm'.1 (by simp)
  have hcert := analysed_cert C fc hfc
  obtain ⟨hP, -, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK _ fc.cert hcert
  have hks : ksKeysIn St.base.P.src St.rots C.prog.body
      (initEnv St.base.P.src C.prog fun _ => .exact 0) = true := by
    unfold Circ.extraOK at hx
    simp only [Bool.and_eq_true] at hx
    exact hx.2
  have hin := inputsOK_fresh C fc hfc hx pk sk hk ins hins hlen
  obtain ⟨gk', hagree, hgk'⟩ := gk_extend hP.N_pow2 pk sk hk
  obtain ⟨hs, -, -, hrk, -⟩ := hk
  have hrun := Validation.CertifyBFV.certifyBFV?_library_run
    (analysed C fc.params.inputNoise) fc.cert hcert hid' St.A (fun _ => hA) sk.s hs pk.rk
    hrk gk' hgk' _ _ hin
  refine ⟨runLibrary C.input St.A pk.rk pk.gk (C.cts (ins.map fun p => enc pk p.1 p.2)), ?_, ?_⟩
  swap
  · exact (libEval_eq St pk C _).symm ▸ rfl
  have e1 := runLibrary_gk_congr C.input St.rots St.A pk.rk pk.gk gk'
    (C.cts (ins.map fun p => enc pk p.1 p.2)) hks hagree
  have e2 := runLibrary_inputNoise C.input fc.params.inputNoise St.A pk.rk gk'
    (C.cts (ins.map fun p => enc pk p.1 p.2))
  rw [e1, ← e2]
  exact hrun

theorem schemeWith_libEval (St : Setting) : schemeWith St (libEval St) = scheme St := rfl

theorem correct_libEval (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A) : Spec.IndCpaD.Correct (schemeWith St (libEval St)) :=
  correct_of_meets St hSt _ (libEval_meets St hA)

example := (@correct_of_meets : type_of% @Challenge.IndCpaD.correct_of_meets)
example := (@meets_prob_eq : type_of% @Challenge.IndCpaD.meets_prob_eq)
example := (@meets_prob_le : type_of% @Challenge.IndCpaD.meets_prob_le)
example := (@libEval_meets : type_of% @Challenge.IndCpaD.libEval_meets)
example := (@schemeWith_libEval : type_of% @Challenge.IndCpaD.schemeWith_libEval)
example := (@correct_libEval : type_of% @Challenge.IndCpaD.correct_libEval)

end Validation.IndCpaD
