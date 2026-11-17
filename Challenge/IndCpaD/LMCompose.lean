import Challenge.IndCpaD.LM
import Challenge.IndCpaD.Profile
import Challenge.IndCpaD.ProfileBGV

/-!
# Challenge.IndCpaD.LMCompose — the profile reduction composed into the game with evaluation on earlier results   (LOCKED statements; proofs in `Validation/IndCpaD/LMCompose.lean`)

`Challenge.IndCpaD.LM` proves the reduction for the game with evaluation on earlier results
(`Spec.IndCpaDLM.gameLM`) under two hypotheses on the evaluator: it is a local interpreter
(`InterpOK`), and the scheme is perfectly correct in the fresh-only game
(`Correct (freshScheme D adm (interpEval D stepF) dec)`). `Challenge.IndCpaD.Profile` and
`Challenge.IndCpaD.ProfileBGV` prove that perfect correctness for an abstract BFV or BGV scheme
from (i) the encryption hypothesis, (ii) the evaluator hypothesis within a profile on the class,
(iii) the class inside the profile class. Here the two are composed, for EVERY local interpreter:

* `correct_interp_bfv`, `correct_interp_bgv`: under (i)–(iii) for the evaluator
  `interpEval D stepF`, the scheme of the fresh-only game with textbook decryption
  (`freshScheme D adm (interpEval D stepF) D.decBFV`, resp. `D.decBGV`) is perfectly correct.
  It is the scheme `schemeBFV D (interpEval D stepF) adm` (resp. `schemeBGV`) of the profile
  statements: the same encryption, evaluator (with the same arity guard), decryption, semantics,
  class and good-key and good-randomness predicates.
* `gameLM_eq_gameCPA_bfv`, `probLM_eq_bfv`, `probLM_le_bfv`, `advLM_le_bfv` and the four
  `…_bgv`: the conclusions of `Challenge.IndCpaD.LM` with no correctness hypothesis: it is
  discharged by (i)–(iii) and `InterpOK`.

No library, technique or particular encryption algorithm is named in these statements.
-/

namespace Challenge.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile MeasureTheory

/-! ## BFV -/

/-- **Fresh-only correctness of a BFV interpreter on a profile class.** -/
theorem correct_interp_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true) (stepF : StepFn D)
    (hev : EvalMeetsBFV D prof adm (interpEval D stepF)) :
    Correct (freshScheme D adm (interpEval D stepF) D.decBFV) := sorry

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
        (reduceLM mk adm (interpEval D stepF) D.decBFV pk A [] (Global.empty D)) 0 := sorry

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
        (reductionLM mk adm (interpEval D stepF) D.decBFV A (coins ω) (pk ω)) 0 = true} := sorry

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
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} := sorry

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
  sorry

/-! ## BGV -/

/-- **Fresh-only correctness of a BGV interpreter on a profile class.** -/
theorem correct_interp_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true) (stepF : StepFn D)
    (hev : EvalMeetsBGV D prof adm (interpEval D stepF)) :
    Correct (freshScheme D adm (interpEval D stepF) D.decBGV) := sorry

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
        (reduceLM mk adm (interpEval D stepF) D.decBGV pk A [] (Global.empty D)) 0 := sorry

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
        (reductionLM mk adm (interpEval D stepF) D.decBGV A (coins ω) (pk ω)) 0 = true} := sorry

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
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} := sorry

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
  sorry

end Challenge.IndCpaDLM
