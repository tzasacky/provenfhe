import Challenge.IndCpaD.ProfileAdv
import Validation.IndCpaD.Profile
import Validation.IndCpaD.ProfileBGV

/-!
# Validation.IndCpaD.ProfileAdv — proofs of the pins of `Challenge.IndCpaD.ProfileAdv`

`Validation.IndCpaD.prob_le` for each bit, read in `ℝ` (every set has finite measure), and the
triangle inequality.
-/

namespace Validation.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Challenge.IndCpaDProfile
  MeasureTheory

/-- `a ≤ b + c` in `ℝ≥0∞`, read in `ℝ`, for sets of a finite measure. -/
theorem toReal_le_add {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (a b c : Set Ω) (h : μ a ≤ μ b + μ c) : (μ a).toReal ≤ (μ b).toReal + (μ c).toReal := by
  rw [← ENNReal.toReal_add (measure_ne_top μ b) (measure_ne_top μ c)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ b, measure_ne_top μ c⟩) h

theorem adv_le (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    |(μ {ω | gameD true (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal -
        (μ {ω | gameD false (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal| ≤
      |(μ {ω | gameCPA true (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA false (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))}).toReal := by
  obtain ⟨h1, h1'⟩ := Validation.IndCpaD.prob_le S hC μ pk sk tape coins A true q hq
  obtain ⟨h0, h0'⟩ := Validation.IndCpaD.prob_le S hC μ pk sk tape coins A false q hq
  have r1 := toReal_le_add μ _ _ _ h1
  have r1' := toReal_le_add μ _ _ _ h1'
  have r0 := toReal_le_add μ _ _ _ h0
  have r0' := toReal_le_add μ _ _ _ h0'
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self ((μ {ω | gameCPA true (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0
        = true}).toReal - (μ {ω | gameCPA false (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0
        = true}).toReal),
      neg_abs_le ((μ {ω | gameCPA true (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0
        = true}).toReal - (μ {ω | gameCPA false (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0
        = true}).toReal)]

theorem bfv_adv_le (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBFV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Adv (schemeBFV D ev adm) Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    |(μ {ω | gameD (S := schemeBFV D ev adm) true (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
          = true}).toReal -
        (μ {ω | gameD (S := schemeBFV D ev adm) false (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
          0 [] = true}).toReal| ≤
      |(μ {ω | gameCPA (S := schemeBFV D ev adm) true (pk ω) (tape ω)
          (reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := schemeBFV D ev adm) false (pk ω) (tape ω)
          (reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  adv_le (schemeBFV D ev adm) (correct_bfv D henc prof adm hadm ev hev) μ pk sk tape coins A q hq

theorem bgv_adv_le (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBGV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Adv (schemeBGV D ev adm) Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    |(μ {ω | gameD (S := schemeBGV D ev adm) true (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
          = true}).toReal -
        (μ {ω | gameD (S := schemeBGV D ev adm) false (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
          0 [] = true}).toReal| ≤
      |(μ {ω | gameCPA (S := schemeBGV D ev adm) true (pk ω) (tape ω)
          (reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := schemeBGV D ev adm) false (pk ω) (tape ω)
          (reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  adv_le (schemeBGV D ev adm) (correct_bgv D henc prof adm hadm ev hev) μ pk sk tape coins A q hq

example := (@adv_le : type_of% @Challenge.IndCpaDProfile.adv_le)
example := (@bfv_adv_le : type_of% @Challenge.IndCpaDProfile.bfv_adv_le)
example := (@bgv_adv_le : type_of% @Challenge.IndCpaDProfile.bgv_adv_le)

end Validation.IndCpaDProfile
