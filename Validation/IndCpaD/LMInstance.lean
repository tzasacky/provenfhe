import Validation.IndCpaD.LM
import Validation.IndCpaD.ProfileBGVKS

/-!
# Validation.IndCpaD.LMInstance — proofs of the instance pins of `Challenge.IndCpaD.LM`

The step function of `ksEval` reads its operands with `Option.bind`/`Option.map` and writes the
destination with `CtEnv.set` (read through `change` with the bodies of `ksStep` and `exactStep`;
three helper shapes cover every instruction), so it is a local interpreter; its run is `ksRun`;
correctness at `bgvKSSeal` is `correct_ksEval_bgvKSSeal`.
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDLM Challenge.IndCpaDProfile Challenge.Source Challenge.Realize MeasureTheory

section Shapes
variable {P : FullParams} {Pr : Params} {σ σ₂ σ' : Trace.CtEnv P} {ρ ρ₂ : Env Pr} {d a c : Var}

theorem shape1 (F : List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (σ a).map (fun ca => σ.set d (F ca)) = some σ') (hs : Ext σ σ₂) :
    ∃ ct, σ' = σ.set d ct ∧ (σ₂ a).map (fun ca => σ₂.set d (F ca)) = some (σ₂.set d ct) := by
  obtain ⟨ca, hca, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F ca, rfl, by rw [hs a ca hca]; rfl⟩

theorem shape2 (F : List (IntPoly P.src.N) → List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (σ a).bind (fun ca => (σ c).map fun cb => σ.set d (F ca cb)) = some σ')
    (hs : Ext σ σ₂) :
    ∃ ct, σ' = σ.set d ct ∧
      (σ₂ a).bind (fun ca => (σ₂ c).map fun cb => σ₂.set d (F ca cb)) = some (σ₂.set d ct) := by
  obtain ⟨ca, hca, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F ca cb, rfl, by rw [hs a ca hca, hs c cb hcb]; rfl⟩

theorem shapeR (F : Val Pr → List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (ρ a).bind (fun x => (σ a).map fun ca => σ.set d (F x ca)) = some σ')
    (hr : Ext ρ ρ₂) (hs : Ext σ σ₂) :
    ∃ ct, σ' = σ.set d ct ∧
      (ρ₂ a).bind (fun x => (σ₂ a).map fun ca => σ₂.set d (F x ca)) = some (σ₂.set d ct) := by
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ca, hca, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨F x ca, rfl, by rw [hr a x hx, hs a ca hca]; rfl⟩

theorem prog1 (F : List (IntPoly P.src.N) → List (IntPoly P.src.N)) (h : (σ a).isSome) :
    ((σ a).map fun ca => σ.set d (F ca)).isSome := by
  obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h; rw [hca]; rfl

theorem prog2 (F : List (IntPoly P.src.N) → List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (σ a).isSome) (h' : (σ c).isSome) :
    ((σ a).bind fun ca => (σ c).map fun cb => σ.set d (F ca cb)).isSome := by
  obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp h'
  rw [hca]; simp [hcb]

theorem progR (F : Val Pr → List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (h : (ρ a).isSome) (h' : (σ a).isSome) :
    ((ρ a).bind fun x => (σ a).map fun ca => σ.set d (F x ca)).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp h'
  rw [hx]; simp [hca]

end Shapes

theorem ksStep_interpOK (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    InterpOK D (ksStepFn D lay rk gk) := by
  refine ⟨fun pk ρ ρ₂ σ σ₂ i σ' hr hs h => ?_, fun pk ρ σ i ρ' h hd => ?_⟩
  · cases i with
    | add d a c => exact shape2 (fun ca cb => padZip (· + ·) ca cb) h hs
    | sub d a c => exact shape2 (fun ca cb => padZip (· - ·) ca cb) h hs
    | mul d a c => exact shape2 (fun ca cb => tensorParts ca cb) h hs
    | square d a => exact shape1 (fun ca => tensorParts ca ca) h hs
    | mulConst d a k => exact shape1 (fun ca => ca.map (k • ·)) h hs
    | copy d a => exact shape1 (fun ca => ca) h hs
    | toEval d a => exact shape1 (fun ca => ca) h hs
    | toCoeff d a => exact shape1 (fun ca => ca) h hs
    | dropLimbs d a k => exact shape1 (fun ca => ca) h hs
    | automorph d a g => exact shape1 (fun ca => ca.map (automorph g)) h hs
    | addPlain d a c => exact shape2 (fun ca cp => padZip (· + ·) ca cp) h hs
    | subPlain d a c => exact shape2 (fun ca cp => padZip (· - ·) ca cp) h hs
    | mulPlain d a c => exact shape2 (fun ca cp => ca.map (cp.headD 0 * ·)) h hs
    | relin d a =>
      exact shapeR (fun x ca => relinOpenFHE D.Pe lay x.level ca (rk pk)) h hr hs
    | keySwitch d a =>
      exact shapeR (fun x ca => keySwitchOpenFHE D.Pe lay x.level ca (gk pk x.key)) h hr hs
    | modSwitch d a =>
      exact shapeR (fun x ca => ca.map (bgvModSwitchComp D.Pe.src.t D.Pe.src.qs[x.level - 1]!))
        h hr hs
  · have hone : ∀ a, (∃ x, ρ a = some x) → (σ a).isSome := fun a ⟨x, hx⟩ =>
      hd a (by rw [hx]; rfl)
    cases i with
    | add d a c | sub d a c | mul d a c | addPlain d a c | subPlain d a c | mulPlain d a c =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      rcases hy : ρ c with _ | y
      · simp [step, hx, hy] at h
      have h1 := hone a ⟨x, hx⟩
      have h2 := hone c ⟨y, hy⟩
      first
      | exact prog2 (fun ca cb => padZip (· + ·) ca cb) h1 h2
      | exact prog2 (fun ca cb => padZip (· - ·) ca cb) h1 h2
      | exact prog2 (fun ca cb => tensorParts ca cb) h1 h2
      | exact prog2 (fun ca cp => ca.map (cp.headD 0 * ·)) h1 h2
    | square d a | mulConst d a _ | copy d a | toEval d a | toCoeff d a | dropLimbs d a _
    | automorph d a _ =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      have h1 := hone a ⟨x, hx⟩
      first
      | exact prog1 (fun ca => tensorParts ca ca) h1
      | exact prog1 (fun ca => ca.map (_ • ·)) h1
      | exact prog1 (fun ca => ca) h1
      | exact prog1 (fun ca => ca.map (automorph _)) h1
    | relin d a | keySwitch d a | modSwitch d a =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      have h1 := hone a ⟨x, hx⟩
      have h0 : (ρ a).isSome := by rw [hx]; rfl
      first
      | exact progR (fun x ca => relinOpenFHE D.Pe lay x.level ca (rk pk)) h0 h1
      | exact progR (fun x ca => keySwitchOpenFHE D.Pe lay x.level ca (gk pk x.key)) h0 h1
      | exact progR (fun x ca => ca.map (bgvModSwitchComp D.Pe.src.t D.Pe.src.qs[x.level - 1]!))
          h0 h1

theorem irun_ksRun (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) (pk : D.PK) :
    ∀ (body : List Instr) (ρ : Env D.P.src) (σ : Trace.CtEnv D.Pe),
      irun D (ksStepFn D lay rk gk) pk body ρ σ = ksRun D.Pe lay (rk pk) (gk pk) body ρ σ
  | [], _, _ => rfl
  | i :: is, ρ, σ => by
    show (step D.P.src ρ i).bind (fun ρ' => (ksStepFn D lay rk gk pk ρ σ i).bind fun σ' =>
      irun D (ksStepFn D lay rk gk) pk is ρ' σ') =
      (step D.Pe.src ρ i).bind (fun ρ' => (ksStep D.Pe lay (rk pk) (gk pk) ρ σ i).bind fun σ' =>
        ksRun D.Pe lay (rk pk) (gk pk) is ρ' σ')
    congr 1; funext ρ'; congr 1; funext σ'
    exact irun_ksRun D lay rk gk pk is ρ' σ'

theorem interpEval_ks (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    interpEval D (ksStepFn D lay rk gk) =
      fun pk C cs => ksEval D lay (rk pk) (gk pk) C cs := by
  funext pk C cs
  show ((irun D (ksStepFn D lay rk gk) pk (D.prog C).body
      (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] =
    ((ksRun D.Pe lay (rk pk) (gk pk) (D.prog C).body
      (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD []
  rw [irun_ksRun]

theorem correct_lm_bgvKSSeal :
    Correct (freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) := by
  have e : evSeal = fun pk C cs =>
      ksEval bgvKSSealData bgvKSLayout pk.2.2.1 pk.2.2.2 C cs :=
    interpEval_ks bgvKSSealData bgvKSLayout (fun pk => pk.2.2.1) (fun pk => pk.2.2.2)
  rw [e]
  exact Validation.IndCpaDProfile.correct_ksEval_bgvKSSeal

theorem hmkSeal : ∀ p f c, bgvKSSealData.prog (mkSeal p f c) = p ∧
    bgvKSSealData.fresh (mkSeal p f c) = f ∧ bgvKSSealData.pt (mkSeal p f c) = c :=
  fun _ _ _ => ⟨rfl, rfl, rfl⟩

theorem probLM_eq_bgvKSSeal [DecidableEq (M bgvKSSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → bgvKSSealData.PK) (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, bgvKSSealData.KeysOK (pk ω) (sk ω) ∧
      ∀ i, bgvKSSealData.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true} =
      μ {ω | gameCPA (S := freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) b
        (pk ω) (tape ω) (reductionLM mkSeal admSeal evSeal bgvKSSealData.decBGV A (coins ω) (pk ω))
          0 = true} :=
  probLM_eq bgvKSSealData mkSeal hmkSeal admSeal bgvKSSealData.decBGV _
    (ksStep_interpOK bgvKSSealData bgvKSLayout (fun pk => pk.2.2.1) (fun pk => pk.2.2.2))
    correct_lm_bgvKSSeal μ pk sk tape coins A b hgood

theorem advLM_le_bgvKSSeal [DecidableEq (M bgvKSSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → bgvKSSealData.PK) (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool) (q : ℕ)
    (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true}).toReal -
        (μ {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) true
          (pk ω) (tape ω) (reductionLM mkSeal admSeal evSeal bgvKSSealData.decBGV A (coins ω)
            (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) false
          (pk ω) (tape ω) (reductionLM mkSeal admSeal evSeal bgvKSSealData.decBGV A (coins ω)
            (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (bgvKSSealData.KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, bgvKSSealData.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  advLM_le bgvKSSealData mkSeal hmkSeal admSeal bgvKSSealData.decBGV _
    (ksStep_interpOK bgvKSSealData bgvKSLayout (fun pk => pk.2.2.1) (fun pk => pk.2.2.2))
    correct_lm_bgvKSSeal μ pk sk tape coins A q hq

theorem lm_two_stage_kernel :
    admLM mkSeal admSeal lmG0 lmStage1 [("a", true), ("b", true)] = true ∧
      admLM mkSeal admSeal (lmG0.extend lmStage1) lmStage2 [("c", true)] = true := by
  decide +kernel

theorem lm_reject_kernel :
    admLM mkSeal admSeal (lmG0.extend lmStage1)
      ({ lmStage2.1 with inputs := [{ sealDecl "c" with level := 3 }] }, ["c"], fun _ => 0)
      [("c", true)] = false ∧
    admLM mkSeal admSeal (lmG0.extend lmStage1)
      ({ lmStage2.1 with body := lmStage2.1.body ++ [.copy "a" "m"] }, ["c"], fun _ => 0)
      [("c", true)] = false ∧
    admLM mkSeal admSeal (lmG0.extend lmStage1) lmStage2 [("c", false)] = false := by
  decide +kernel

example := (@lm_reject_kernel : type_of% @Challenge.IndCpaDLM.lm_reject_kernel)
example := (@ksStep_interpOK : type_of% @Challenge.IndCpaDLM.ksStep_interpOK)
example := (@interpEval_ks : type_of% @Challenge.IndCpaDLM.interpEval_ks)
example := (@correct_lm_bgvKSSeal : type_of% @Challenge.IndCpaDLM.correct_lm_bgvKSSeal)
example := (@probLM_eq_bgvKSSeal : type_of% @Challenge.IndCpaDLM.probLM_eq_bgvKSSeal)
example := (@advLM_le_bgvKSSeal : type_of% @Challenge.IndCpaDLM.advLM_le_bgvKSSeal)
example := (@lm_two_stage_kernel : type_of% @Challenge.IndCpaDLM.lm_two_stage_kernel)

end Validation.IndCpaDLM
