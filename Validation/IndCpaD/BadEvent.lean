import Challenge.IndCpaD.BadEvent
import Validation.IndCpaD.LMCompose
import Validation.IndCpaD.ProfileAdv
import Validation.IndCpaD

/-!
# Validation.IndCpaD.BadEvent — proofs of the pins of `Challenge.IndCpaD.BadEvent`

Monotonicity and finite subadditivity of the outer measure (`measure_mono`, `measure_union_le`,
`measure_biUnion_finset_le`, `measure_iUnion_fintype_le`: no measurability needed), the advantage
bounds of `Validation.IndCpaD.ProfileAdv` and `Validation.IndCpaD.LM` read in `ℝ`, and
`Finset.sup_le_iff` for the norm.
-/

namespace Validation.IndCpaDBad
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile Challenge.IndCpaDLM Challenge.IndCpaDBad MeasureTheory

/-! ## 1. Union bound -/

/-- **The union bound for the bad event.** -/
theorem bad_le_sum {Ω PK SK ER : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (KeysOK : PK → SK → Prop) (GoodE : PK → SK → ER → Prop)
    (pk : Ω → PK) (sk : Ω → SK) (tape : Ω → ℕ → ER) (q : ℕ) :
    μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ≤
      μ {ω | ¬ KeysOK (pk ω) (sk ω)} +
        ∑ i ∈ Finset.range q, μ {ω | ¬ GoodE (pk ω) (sk ω) (tape ω i)} := by
  calc μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))}
      ≤ μ ({ω | ¬ KeysOK (pk ω) (sk ω)} ∪
          ⋃ i ∈ Finset.range q, {ω | ¬ GoodE (pk ω) (sk ω) (tape ω i)}) := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_ofPred_eq, not_and, not_forall] at hω
        by_cases hk : KeysOK (pk ω) (sk ω)
        · obtain ⟨i, hi, hg⟩ := hω hk
          exact Or.inr (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hi)) hg)
        · exact Or.inl hk
    _ ≤ μ {ω | ¬ KeysOK (pk ω) (sk ω)} +
          μ (⋃ i ∈ Finset.range q, {ω | ¬ GoodE (pk ω) (sk ω) (tape ω i)}) := measure_union_le _ _
    _ ≤ _ := by
        gcongr
        exact measure_biUnion_finset_le _ _

/-! ## 2–3. Advantages -/

/-- The union bound read in `ℝ` under a finite measure. -/
theorem bad_toReal_le {Ω PK SK ER : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (KeysOK : PK → SK → Prop) (GoodE : PK → SK → ER → Prop)
    (pk : Ω → PK) (sk : Ω → SK) (tape : Ω → ℕ → ER) (q : ℕ) :
    (μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))}).toReal ≤
      (μ {ω | ¬ KeysOK (pk ω) (sk ω)}).toReal +
        ∑ i ∈ Finset.range q, (μ {ω | ¬ GoodE (pk ω) (sk ω) (tape ω i)}).toReal := by
  have hs : ∑ i ∈ Finset.range q, μ {ω | ¬ GoodE (pk ω) (sk ω) (tape ω i)} ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => measure_ne_top μ _
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _),
    ← ENNReal.toReal_add (measure_ne_top μ _) hs]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, hs⟩)
    (bad_le_sum μ KeysOK GoodE pk sk tape q)

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
        ∑ i ∈ Finset.range q, (μ {ω | ¬ S.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := by
  have h := Validation.IndCpaDProfile.adv_le S hC μ pk sk tape coins A q hq
  have h2 := bad_toReal_le μ S.KeysOK S.GoodE pk sk tape q
  linarith

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
        (μ {ω | gameCPA false (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true}).toReal| := by
  rw [Validation.IndCpaD.prob_eq S hC μ pk sk tape coins A true hgood,
    Validation.IndCpaD.prob_eq S hC μ pk sk tape coins A false hgood]

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
        ∑ i ∈ Finset.range q, (μ {ω | ¬ D.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := by
  have h := Validation.IndCpaDLM.advLM_le D mk hmk adm dec stepF hI hC μ pk sk tape coins A q hq
  have h2 := bad_toReal_le μ D.KeysOK D.GoodE pk sk tape q
  linarith

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
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal| := by
  rw [Validation.IndCpaDLM.probLM_eq D mk hmk adm dec stepF hI hC μ pk sk tape coins A true hgood,
    Validation.IndCpaDLM.probLM_eq D mk hmk adm dec stepF hI hC μ pk sk tape coins A false hgood]

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
        ∑ i ∈ Finset.range q, (μ {ω | ¬ D.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := 
  advLM_le_sum D mk hmk adm D.decBFV stepF hI
    (Validation.IndCpaDLM.correct_interp_bfv D henc prof adm hadm stepF hev) μ pk sk tape coins A q hq

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
        ∑ i ∈ Finset.range q, (μ {ω | ¬ D.GoodE (pk ω) (sk ω) (tape ω i)}).toReal) := 
  advLM_le_sum D mk hmk adm D.decBGV stepF hI
    (Validation.IndCpaDLM.correct_interp_bgv D henc prof adm hadm stepF hev) μ pk sk tape coins A q hq

/-! ## 4. Coefficient tails -/

/-- **A polynomial outside its bound has a coefficient outside it**, in measure. -/
theorem normInf_bad_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (f : Ω → IntPoly N) (B : ℕ) :
    μ {ω | ¬ normInf (f ω) ≤ B} ≤ ∑ j : Fin N, μ {ω | B < ((f ω).coeff j).natAbs} := by
  calc μ {ω | ¬ normInf (f ω) ≤ B} ≤ μ (⋃ j : Fin N, {ω | B < ((f ω).coeff j).natAbs}) := by
        apply measure_mono
        intro ω hω
        have hω' : ¬ (Finset.univ.sup fun i => ((f ω).coeff i).natAbs) ≤ B := hω
        rw [Finset.sup_le_iff] at hω'
        push Not at hω'
        obtain ⟨j, -, hj⟩ := hω'
        exact Set.mem_iUnion.mpr ⟨j, hj⟩
    _ ≤ _ := measure_iUnion_fintype_le _ _

/-- **Three sampled polynomials within their bounds**: the probability that one is not is at most
the sum of the coefficient tails. -/
theorem goodE3_bad_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (r : Ω → IntPoly N × IntPoly N × IntPoly N) (Bu B1 B2 : ℕ) :
    μ {ω | ¬ (normInf (r ω).1 ≤ Bu ∧ normInf (r ω).2.1 ≤ B1 ∧ normInf (r ω).2.2 ≤ B2)} ≤
      ∑ j : Fin N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) := by
  calc μ {ω | ¬ (normInf (r ω).1 ≤ Bu ∧ normInf (r ω).2.1 ≤ B1 ∧ normInf (r ω).2.2 ≤ B2)}
      ≤ μ ({ω | ¬ normInf (r ω).1 ≤ Bu} ∪ {ω | ¬ normInf (r ω).2.1 ≤ B1} ∪
          {ω | ¬ normInf (r ω).2.2 ≤ B2}) := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        tauto
    _ ≤ μ {ω | ¬ normInf (r ω).1 ≤ Bu} + μ {ω | ¬ normInf (r ω).2.1 ≤ B1} +
          μ {ω | ¬ normInf (r ω).2.2 ≤ B2} :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ (∑ j : Fin N, μ {ω | Bu < ((r ω).1.coeff j).natAbs}) +
          (∑ j : Fin N, μ {ω | B1 < ((r ω).2.1.coeff j).natAbs}) +
          (∑ j : Fin N, μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
        add_le_add (add_le_add (normInf_bad_le μ (fun ω => (r ω).1) Bu)
          (normInf_bad_le μ (fun ω => (r ω).2.1) B1)) (normInf_bad_le μ (fun ω => (r ω).2.2) B2)
    _ = _ := by rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- **The coefficient tails of `bgvData`** (BGV encryption, `Challenge.IndCpaD.ProfileBGVInstances`). -/
theorem goodE_bad_le_bgvData (P : FullParams) (Bk Bu B1 B2 : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bgvData P Bk Bu B1 B2).PK) (sk : Ω → (bgvData P Bk Bu B1 B2).SK)
    (r : Ω → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    μ {ω | ¬ (bgvData P Bk Bu B1 B2).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin P.src.N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
  goodE3_bad_le μ r Bu B1 B2

/-- **The coefficient tails of `bgvKSData`** (BGV with evaluation keys,
`Challenge.IndCpaD.ProfileBGVKS`). -/
theorem goodE_bad_le_bgvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (r : Ω → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    μ {ω | ¬ (bgvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin P.src.N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
  goodE3_bad_le μ r Bu B1 B2

/-- **The coefficient tails of `bfvKSData`** (BFV with evaluation keys,
`Challenge.IndCpaD.LMBFV`; `bfvSealData` is an instance). -/
theorem goodE_bad_le_bfvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).SK)
    (r : Ω → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    μ {ω | ¬ (bfvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin P.src.N, (μ {ω | Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | B2 < ((r ω).2.2.coeff j).natAbs}) :=
  goodE3_bad_le μ r Bu B1 B2

/-- **The coefficient tails of the OpenFHE-shaped BFV data** `dataOf St`
(`Challenge.IndCpaD.ProfileInstances`; the same predicate as `Spec.IndCpaDBFV.GoodE`). -/
theorem goodE_bad_le_dataOf (St : Spec.IndCpaDBFV.Setting) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (pk : Ω → (dataOf St).PK) (sk : Ω → (dataOf St).SK)
    (r : Ω → IntPoly St.base.P.src.N × IntPoly St.base.P.src.N × IntPoly St.base.P.src.N) :
    μ {ω | ¬ (dataOf St).GoodE (pk ω) (sk ω) (r ω)} ≤
      ∑ j : Fin St.base.P.src.N, (μ {ω | St.Bu < ((r ω).1.coeff j).natAbs} +
        μ {ω | St.B1 < ((r ω).2.1.coeff j).natAbs} + μ {ω | St.B2 < ((r ω).2.2.coeff j).natAbs}) :=
  goodE3_bad_le μ r St.Bu St.B1 St.B2

example := (@bad_le_sum : type_of% @Challenge.IndCpaDBad.bad_le_sum)
example := (@adv_le_sum : type_of% @Challenge.IndCpaDBad.adv_le_sum)
example := (@adv_eq : type_of% @Challenge.IndCpaDBad.adv_eq)
example := (@advLM_le_sum : type_of% @Challenge.IndCpaDBad.advLM_le_sum)
example := (@advLM_eq : type_of% @Challenge.IndCpaDBad.advLM_eq)
example := (@advLM_le_sum_bfv : type_of% @Challenge.IndCpaDBad.advLM_le_sum_bfv)
example := (@advLM_le_sum_bgv : type_of% @Challenge.IndCpaDBad.advLM_le_sum_bgv)
example := (@normInf_bad_le : type_of% @Challenge.IndCpaDBad.normInf_bad_le)
example := (@goodE3_bad_le : type_of% @Challenge.IndCpaDBad.goodE3_bad_le)
example := (@goodE_bad_le_bgvData : type_of% @Challenge.IndCpaDBad.goodE_bad_le_bgvData)
example := (@goodE_bad_le_bgvKSData : type_of% @Challenge.IndCpaDBad.goodE_bad_le_bgvKSData)
example := (@goodE_bad_le_bfvKSData : type_of% @Challenge.IndCpaDBad.goodE_bad_le_bfvKSData)
example := (@goodE_bad_le_dataOf : type_of% @Challenge.IndCpaDBad.goodE_bad_le_dataOf)

end Validation.IndCpaDBad
