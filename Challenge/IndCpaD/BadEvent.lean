import Challenge.IndCpaD.LMCompose
import Challenge.IndCpaD.LMBFV
import Challenge.IndCpaD.ProfileAdv

/-!
# Challenge.IndCpaD.BadEvent — the bad event bounded by a union bound   (LOCKED statements; proofs in `Validation/IndCpaD/BadEvent.lean`)

The probability statements of the reduction (`Challenge.IndCpaD.prob_le`,
`Challenge.IndCpaDProfile.adv_le`, `Challenge.IndCpaDLM.probLM_le`, `advLM_le`, and the composed
`advLM_le_bfv`, `advLM_le_bgv`) carry the probability of the bad event "the keys or one of the
first `q` encryptions are not good". This file bounds it.

1. **Union bound** (`bad_le_sum`): for arbitrary predicates `KeysOK`, `GoodE`, key and randomness
   maps and any measure, `μ{bad} ≤ μ{keys not good} + Σ_{i<q} μ{encryption i not good}`. It is
   countable subadditivity of the outer measure: no measurability of the events is assumed.
2. **Advantage bounds with the sum** (`adv_le_sum`: fresh-only game, any scheme perfectly correct
   on its class; `advLM_le_sum`: the game with evaluation on earlier results, any local
   interpreter perfectly correct in the fresh-only game; `advLM_le_sum_bfv`, `advLM_le_sum_bgv`:
   the same from the profile hypotheses), under a finite measure:
   `Adv^{IND-CPA-D}(A) ≤ Adv^{IND-CPA}(reduction A) + 2·(μ{keys not good} + Σ_{i<q} μ{encryption i not good})`.
3. **The exact case** (`adv_eq`, `advLM_eq`): if the keys and every tape entry are good almost
   surely, the two advantages are equal (any measure).
4. **Coefficient tails** (`normInf_bad_le`, `goodE3_bad_le` and the instances `goodE_bad_le_bgvData`,
   `goodE_bad_le_bgvKSData`, `goodE_bad_le_bfvKSData`, `goodE_bad_le_dataOf`): where good randomness
   means three sampled polynomials within declared coefficient bounds, the probability that it is
   not good is at most the sum, over the three polynomials and their `N` coefficients, of the
   probability that the coefficient's absolute value exceeds its bound. These are statements about
   an arbitrary measure on the randomness: nothing is assumed of the distribution.
-/

namespace Challenge.IndCpaDBad
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile Challenge.IndCpaDLM MeasureTheory

/-! ## 1. Union bound -/

/-- **The union bound for the bad event.** -/
theorem bad_le_sum {Ω PK SK ER : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (KeysOK : PK → SK → Prop) (GoodE : PK → SK → ER → Prop)
    (pk : Ω → PK) (sk : Ω → SK) (tape : Ω → ℕ → ER) (q : ℕ) :
    μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ≤
      μ {ω | ¬ KeysOK (pk ω) (sk ω)} +
        ∑ i ∈ Finset.range q, μ {ω | ¬ GoodE (pk ω) (sk ω) (tape ω i)} := sorry

/-! ## 2–3. Advantages -/

/-- **The advantage bound with the union bound, fresh-only game.** -/
theorem adv_le_sum (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    |(μ {ω | gameD true (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal -
        (μ {ω | gameD false (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal| ≤
      |(μ {ω | gameCPA true (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA false (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * ((μ {ω | ¬ S.KeysOK (pk ω) (sk ω)}).toReal +
        ∑ i ∈ Finset.range q, (μ {ω | ¬ S.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := sorry

/-- **Equal advantages, fresh-only game**, when the keys and every tape entry are good almost
surely (any measure). -/
theorem adv_eq (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool)
    (hgood : ∀ᵐ ω ∂μ, S.KeysOK (pk ω) (sk ω) ∧ ∀ i, S.GoodE (pk ω) (sk ω) (tape ω i)) :
    |(μ {ω | gameD true (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal -
        (μ {ω | gameD false (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true}).toReal| =
      |(μ {ω | gameCPA true (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA false (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal| :=
  sorry

/-- **The advantage bound with the union bound, evaluation on earlier results.** -/
theorem advLM_le_sum (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mk adm (interpEval D stepF) dec true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal -
        (μ {ω | gameLM mk adm (interpEval D stepF) dec false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) true (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) false (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * ((μ {ω | ¬ D.KeysOK (pk ω) (sk ω)}).toReal +
        ∑ i ∈ Finset.range q, (μ {ω | ¬ D.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := sorry

/-- **Equal advantages, evaluation on earlier results**, when the keys and every tape entry are
good almost surely (any measure). -/
theorem advLM_eq (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    |(μ {ω | gameLM mk adm (interpEval D stepF) dec true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal -
        (μ {ω | gameLM mk adm (interpEval D stepF) dec false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal| =
      |(μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) true (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) false (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal| :=
  sorry

/-- **The advantage bound with the union bound, evaluation on earlier results, BFV, from the
profile hypotheses.** -/
theorem advLM_le_sum_bfv (D : AbsScheme) (henc : D.EncOKBFV)
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
      2 * ((μ {ω | ¬ D.KeysOK (pk ω) (sk ω)}).toReal +
        ∑ i ∈ Finset.range q, (μ {ω | ¬ D.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := sorry

/-- **The advantage bound with the union bound, evaluation on earlier results, BGV, from the
profile hypotheses.** -/
theorem advLM_le_sum_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
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
      2 * ((μ {ω | ¬ D.KeysOK (pk ω) (sk ω)}).toReal +
        ∑ i ∈ Finset.range q, (μ {ω | ¬ D.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := sorry

/-! ## 4. Coefficient tails -/

/-- **A polynomial outside its bound has a coefficient outside it**, in measure. -/
theorem normInf_bad_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (f : Ω → IntPoly N) (B : ℕ) :
    μ {ω | ¬ normInf (f ω) ≤ B} ≤ ∑ j : Fin N, μ {ω | B < ((f ω).coeff j).natAbs} := sorry

/-- **Three sampled polynomials within their bounds**: the probability that one is not is at most
the sum of the coefficient tails. -/
theorem goodE3_bad_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (r : Ω → IntPoly N × IntPoly N × IntPoly N) (Bu B1 B2 : ℕ) :
    μ {ω | ¬ (normInf (r ω).1 ≤ Bu ∧ normInf (r ω).2.1 ≤ B1 ∧ normInf (r ω).2.2 ≤ B2)} ≤
      ∑ j : Fin N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
  sorry

/-- **The coefficient tails of `bgvData`** (BGV encryption, `Challenge.IndCpaD.ProfileBGVInstances`). -/
theorem goodE_bad_le_bgvData (P : FullParams) (Bk Bu B1 B2 : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bgvData P Bk Bu B1 B2).PK) (sk : Ω → (bgvData P Bk Bu B1 B2).SK)
    (r : Ω → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    μ {ω | ¬ (bgvData P Bk Bu B1 B2).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin P.src.N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
  sorry

/-- **The coefficient tails of `bgvKSData`** (BGV with evaluation keys,
`Challenge.IndCpaD.ProfileBGVKS`). -/
theorem goodE_bad_le_bgvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (r : Ω → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    μ {ω | ¬ (bgvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin P.src.N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
  sorry

/-- **The coefficient tails of `bfvKSData`** (BFV with evaluation keys,
`Challenge.IndCpaD.LMBFV`; `bfvSealData` is an instance). -/
theorem goodE_bad_le_bfvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).SK)
    (r : Ω → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    μ {ω | ¬ (bfvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin P.src.N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
  sorry

/-- **The coefficient tails of the OpenFHE-shaped BFV data** `dataOf St`
(`Challenge.IndCpaD.ProfileInstances`; the same predicate as `Spec.IndCpaDBFV.GoodE`). -/
theorem goodE_bad_le_dataOf (St : Spec.IndCpaDBFV.Setting) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (pk : Ω → (dataOf St).PK) (sk : Ω → (dataOf St).SK)
    (r : Ω → IntPoly St.base.P.src.N × IntPoly St.base.P.src.N × IntPoly St.base.P.src.N) :
    μ {ω | ¬ (dataOf St).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin St.base.P.src.N, (μ {ω | St.Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | St.B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | St.B2 < ((r ω).2.2.coeff j).natAbs}) :=
  sorry

end Challenge.IndCpaDBad
