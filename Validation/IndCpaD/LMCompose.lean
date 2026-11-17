import Challenge.IndCpaD.LMCompose
import Validation.IndCpaD.LM
import Validation.IndCpaD.Profile
import Validation.IndCpaD.ProfileBGV

/-!
# Validation.IndCpaD.LMCompose — proofs of the pins of `Challenge.IndCpaD.LMCompose`

`freshScheme D adm (interpEval D stepF) D.decBFV` and `schemeBFV D (interpEval D stepF) adm` are
the same structure value (both are abbreviations with the same fields), so `correct_bfv` gives the
correctness hypothesis of the reduction of `Validation.IndCpaD.LM` directly; likewise for BGV.
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDLM Challenge.IndCpaDProfile MeasureTheory

/-! ## BFV -/

/-- **Fresh-only correctness of a BFV interpreter on a profile class.** -/
theorem correct_interp_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true) (stepF : StepFn D)
    (hev : EvalMeetsBFV D prof adm (interpEval D stepF)) :
    Correct (freshScheme D adm (interpEval D stepF) D.decBFV) :=
    Validation.IndCpaDProfile.correct_bfv D henc prof adm hadm (interpEval D stepF) hev

/-- **Perfect simulation, evaluation on earlier results, BFV, from the profile hypotheses.** -/
theorem gameLM_eq_gameCPA_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBFV D prof adm (interpEval D stepF)) [DecidableEq (M D)] (b : Bool)
    (pk : D.PK) (sk : D.SK) (tape : ℕ → D.ER) (hk : D.KeysOK pk sk) (A : LAdv D Bool)
    (ht : TapeOKLM pk sk tape A 0) :
    gameLM mk adm (interpEval D stepF) D.decBFV b pk sk tape A 0 [] (Global.empty D) =
      gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBFV) b pk tape
        (reduceLM mk adm (interpEval D stepF) D.decBFV pk A [] (Global.empty D)) 0 :=
    Validation.IndCpaDLM.gameLM_eq_gameCPA D mk hmk adm D.decBFV stepF hI
      (Validation.IndCpaDLM.correct_interp_bfv D henc prof adm hadm stepF hev)
      b pk sk tape hk A ht

/-- **Equal winning probabilities, evaluation on earlier results, BFV, from the profile
hypotheses.** -/
theorem probLM_eq_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBFV D prof adm (interpEval D stepF)) [DecidableEq (M D)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mk adm (interpEval D stepF) D.decBFV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true} =
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBFV) b (pk ω) (tape ω)
        (reductionLM mk adm (interpEval D stepF) D.decBFV A (coins ω) (pk ω)) 0 = true} :=
    Validation.IndCpaDLM.probLM_eq D mk hmk adm D.decBFV stepF hI
      (Validation.IndCpaDLM.correct_interp_bfv D henc prof adm hadm stepF hev)
      μ pk sk tape coins A b hgood

/-- **The bad-event version, evaluation on earlier results, BFV, from the profile hypotheses.** -/
theorem probLM_le_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBFV D prof adm (interpEval D stepF)) [DecidableEq (M D)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    μ {ω | gameLM mk adm (interpEval D stepF) D.decBFV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true} ≤
        μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBFV) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) D.decBFV A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBFV) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) D.decBFV A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameLM mk adm (interpEval D stepF) D.decBFV b (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} :=
    Validation.IndCpaDLM.probLM_le D mk hmk adm D.decBFV stepF hI
      (Validation.IndCpaDLM.correct_interp_bfv D henc prof adm hadm stepF hev)
      μ pk sk tape coins A b q hq

/-- **The advantage bound, evaluation on earlier results, BFV, from the profile hypotheses**,
under a finite measure. -/
theorem advLM_le_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBFV D prof adm (interpEval D stepF)) [DecidableEq (M D)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mk adm (interpEval D stepF) D.decBFV true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal -
        (μ {ω | gameLM mk adm (interpEval D stepF) D.decBFV false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBFV) true (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) D.decBFV A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBFV) false (pk ω)
          (tape ω) (reductionLM mk adm (interpEval D stepF) D.decBFV A (coins ω) (pk ω)) 0
            = true}).toReal| +
      2 * (μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  Validation.IndCpaDLM.advLM_le D mk hmk adm D.decBFV stepF hI
      (Validation.IndCpaDLM.correct_interp_bfv D henc prof adm hadm stepF hev)
      μ pk sk tape coins A q hq

/-! ## BGV -/

/-- **Fresh-only correctness of a BGV interpreter on a profile class.** -/
theorem correct_interp_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true) (stepF : StepFn D)
    (hev : EvalMeetsBGV D prof adm (interpEval D stepF)) :
    Correct (freshScheme D adm (interpEval D stepF) D.decBGV) :=
    Validation.IndCpaDProfile.correct_bgv D henc prof adm hadm (interpEval D stepF) hev

/-- **Perfect simulation, evaluation on earlier results, BGV, from the profile hypotheses.** -/
theorem gameLM_eq_gameCPA_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBGV D prof adm (interpEval D stepF)) [DecidableEq (M D)] (b : Bool)
    (pk : D.PK) (sk : D.SK) (tape : ℕ → D.ER) (hk : D.KeysOK pk sk) (A : LAdv D Bool)
    (ht : TapeOKLM pk sk tape A 0) :
    gameLM mk adm (interpEval D stepF) D.decBGV b pk sk tape A 0 [] (Global.empty D) =
      gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBGV) b pk tape
        (reduceLM mk adm (interpEval D stepF) D.decBGV pk A [] (Global.empty D)) 0 :=
    Validation.IndCpaDLM.gameLM_eq_gameCPA D mk hmk adm D.decBGV stepF hI
      (Validation.IndCpaDLM.correct_interp_bgv D henc prof adm hadm stepF hev)
      b pk sk tape hk A ht

/-- **Equal winning probabilities, evaluation on earlier results, BGV, from the profile
hypotheses.** -/
theorem probLM_eq_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBGV D prof adm (interpEval D stepF)) [DecidableEq (M D)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mk adm (interpEval D stepF) D.decBGV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true} =
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBGV) b (pk ω) (tape ω)
        (reductionLM mk adm (interpEval D stepF) D.decBGV A (coins ω) (pk ω)) 0 = true} :=
    Validation.IndCpaDLM.probLM_eq D mk hmk adm D.decBGV stepF hI
      (Validation.IndCpaDLM.correct_interp_bgv D henc prof adm hadm stepF hev)
      μ pk sk tape coins A b hgood

/-- **The bad-event version, evaluation on earlier results, BGV, from the profile hypotheses.** -/
theorem probLM_le_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBGV D prof adm (interpEval D stepF)) [DecidableEq (M D)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    μ {ω | gameLM mk adm (interpEval D stepF) D.decBGV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true} ≤
        μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBGV) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) D.decBGV A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBGV) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) D.decBGV A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameLM mk adm (interpEval D stepF) D.decBGV b (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} :=
    Validation.IndCpaDLM.probLM_le D mk hmk adm D.decBGV stepF hI
      (Validation.IndCpaDLM.correct_interp_bgv D henc prof adm hadm stepF hev)
      μ pk sk tape coins A b q hq

/-- **The advantage bound, evaluation on earlier results, BGV, from the profile hypotheses**,
under a finite measure. -/
theorem advLM_le_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (stepF : StepFn D) (hI : InterpOK D stepF)
    (hev : EvalMeetsBGV D prof adm (interpEval D stepF)) [DecidableEq (M D)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mk adm (interpEval D stepF) D.decBGV true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal -
        (μ {ω | gameLM mk adm (interpEval D stepF) D.decBGV false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBGV) true (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) D.decBGV A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) D.decBGV) false (pk ω)
          (tape ω) (reductionLM mk adm (interpEval D stepF) D.decBGV A (coins ω) (pk ω)) 0
            = true}).toReal| +
      2 * (μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  Validation.IndCpaDLM.advLM_le D mk hmk adm D.decBGV stepF hI
      (Validation.IndCpaDLM.correct_interp_bgv D henc prof adm hadm stepF hev)
      μ pk sk tape coins A q hq

example := (@correct_interp_bfv : type_of% @Challenge.IndCpaDLM.correct_interp_bfv)
example := (@gameLM_eq_gameCPA_bfv : type_of% @Challenge.IndCpaDLM.gameLM_eq_gameCPA_bfv)
example := (@probLM_eq_bfv : type_of% @Challenge.IndCpaDLM.probLM_eq_bfv)
example := (@probLM_le_bfv : type_of% @Challenge.IndCpaDLM.probLM_le_bfv)
example := (@advLM_le_bfv : type_of% @Challenge.IndCpaDLM.advLM_le_bfv)
example := (@correct_interp_bgv : type_of% @Challenge.IndCpaDLM.correct_interp_bgv)
example := (@gameLM_eq_gameCPA_bgv : type_of% @Challenge.IndCpaDLM.gameLM_eq_gameCPA_bgv)
example := (@probLM_eq_bgv : type_of% @Challenge.IndCpaDLM.probLM_eq_bgv)
example := (@probLM_le_bgv : type_of% @Challenge.IndCpaDLM.probLM_le_bgv)
example := (@advLM_le_bgv : type_of% @Challenge.IndCpaDLM.advLM_le_bgv)

end Validation.IndCpaDLM
