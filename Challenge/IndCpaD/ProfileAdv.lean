import Challenge.IndCpaD.Profile
import Challenge.IndCpaD.ProfileBGV
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Challenge.IndCpaD.ProfileAdv — the advantage form of the reduction   (LOCKED statements; proofs in `Validation/IndCpaD/ProfileAdv.lean`)

The probability statements (`Challenge.IndCpaD.prob_le`, `Challenge.IndCpaDProfile.bfv_prob_le`,
`bgv_prob_le`) bound, for each bit `b`, the difference of the two games' winning probabilities by
the probability of the bad event. Under a finite measure (a probability measure in use) the
advantage, the difference of the winning probabilities for `b = true` and `b = false`, follows
with the constant `2`:

`|Pr[IND-CPA-D game, b = 1, outputs 1] − Pr[IND-CPA-D game, b = 0, outputs 1]|
   ≤ |Pr[IND-CPA game against the reduction, b = 1, outputs 1] − Pr[…, b = 0, outputs 1]|
     + 2·Pr[bad]`,

with `bad` the event "the keys or one of the first `q` encryptions are not good". The same
measure, the same keys, randomness and coins serve both bits (the games differ only in `b`).
`adv_le` is the statement for every scheme that is perfectly correct on its class;
`bfv_adv_le` and `bgv_adv_le` are the library-free instances.
-/

namespace Challenge.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile MeasureTheory

/-- **The advantage bound** for every scheme perfectly correct on its class. -/
theorem adv_le (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    |(μ {ω | gameD true (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal -
        (μ {ω | gameD false (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal| ≤
      |(μ {ω | gameCPA true (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA false (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  sorry

/-- **The advantage bound, BFV, no library**: `adv_le` for `schemeBFV` under the hypotheses of
`correct_bfv`. -/
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
  sorry

/-- **The advantage bound, BGV, no library**: `adv_le` for `schemeBGV` under the hypotheses of
`correct_bgv`. -/
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
  sorry

end Challenge.IndCpaDProfile
