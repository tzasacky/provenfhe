import Challenge.IndCpaD.LMExact
import Validation.IndCpaD.LMInstance
import Validation.IndCpaD.ProfileBGVInstances

/-!
# Validation.IndCpaD.LMExact — proofs of the pins of `Challenge.IndCpaD.LMExact`

Locality by the shapes of `Validation.IndCpaD.LMInstance`. On a circuit of `exactClass` the
zero-message replay runs (the certificate's `Source.eval` on the actual inputs, zeroed) and the
body has no key or modulus switch, so the interpreter's run is the fold of `exactStep`: its
outputs are `exactEval`'s, and `correct_exactEval` transfers.
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDLM Challenge.IndCpaDProfile Challenge.Source MeasureTheory
open Validation.BFV.SoundAux (zenv zv)

theorem exactStep_interpOK (D : AbsScheme) : InterpOK D (exactStepFn D) := by
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
    | relin d a => exact shape1 (fun ca => ca) h hs
    | keySwitch d a => exact shape1 (fun ca => ca) h hs
    | modSwitch d a => exact shape1 (fun ca => ca) h hs
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
    | automorph d a _ | relin d a | keySwitch d a | modSwitch d a =>
      rcases hx : ρ a with _ | x
      · simp [step, hx] at h
      have h1 := hone a ⟨x, hx⟩
      first
      | exact prog1 (fun ca => tensorParts ca ca) h1
      | exact prog1 (fun ca => ca.map (_ • ·)) h1
      | exact prog1 (fun ca => ca) h1
      | exact prog1 (fun ca => ca.map (automorph _)) h1

/-- On a body without key or modulus switching whose replay runs, the interpreter's run is the
fold of `exactStep`. -/
theorem irun_exact (D : AbsScheme) (pk : D.PK) : ∀ (body : List Instr) (ρ ρf : Env D.P.src)
    (σ : Trace.CtEnv D.Pe), body.all exactInstr = true →
    body.foldlM (step D.P.src) ρ = some ρf →
    irun D (exactStepFn D) pk body ρ σ = body.foldlM (exactStep D.Pe) σ
  | [], _, _, _, _, _ => rfl
  | i :: is, ρ, ρf, σ, hall, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', hstep, hrest⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have he : exactStep' D.Pe σ i = exactStep D.Pe σ i := by
      cases i <;> first | rfl | exact absurd hall.1 Bool.false_ne_true
    show (step D.P.src ρ i).bind (fun ρ' => (exactStep' D.Pe σ i).bind fun σ' =>
      irun D (exactStepFn D) pk is ρ' σ') = _
    rw [hstep, Option.bind_some, he, List.foldlM_cons]
    congr 1; funext σ'
    exact irun_exact D pk is ρ' ρf σ' hall.2 hrest

theorem correct_lm_exact (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget) :
    Spec.IndCpaD.Correct (freshScheme D (exactClass D prof) (interpEval D (exactStepFn D))
      D.decBGV) := by
  have hC := Validation.IndCpaDProfile.correct_exactEval D henc prof
  refine ⟨hC.fresh, fun pk sk hk C hadm ins hins => ?_⟩
  have h := hC.eval pk sk hk C hadm ins hins
  change (if (ins.map fun p => D.enc pk p.1 p.2).length = (D.fresh C).length
    then interpEval D (exactStepFn D) pk C (ins.map fun p => D.enc pk p.1 p.2) else []).map
      (D.decBGV sk) = D.sem C (ins.map Prod.fst)
  change (if (ins.map fun p => D.enc pk p.1 p.2).length = (D.fresh C).length
    then exactEval D C (ins.map fun p => D.enc pk p.1 p.2) else []).map
      (D.decBGV sk) = D.sem C (ins.map Prod.fst) at h
  by_cases hlen : ins.length = (D.fresh C).length
  swap
  · simp only [List.length_map, hlen, ite_false] at h ⊢; exact h
  simp only [List.length_map, hlen, ite_true] at h ⊢
  rw [← h]
  congr 1
  -- the class: the profile class and no key or modulus switch
  change (admBGV D prof C && exactOnly (D.prog C).body) = true at hadm
  rw [Bool.and_eq_true] at hadm
  obtain ⟨hadm, hex⟩ := hadm
  change (D.prog C).body.all exactInstr = true at hex
  obtain ⟨B, outs, hcert, hfit, hpe⟩ := Validation.IndCpaDProfile.admBGV_some hadm
  obtain ⟨hP, hkind, -⟩ := Validation.Profile.certifyProfile?_some hcert
  have ht : 0 < D.P.src.t := by have := hP.plaintext.1; exact lt_of_lt_of_le (by norm_num) this
  obtain ⟨hin, hbd⟩ := Validation.IndCpaDProfile.inputsOK_bgv hkind henc C ht hfit hpe pk sk hk
    ins hins hlen
  obtain ⟨ρ, hρ, -⟩ := Validation.Profile.certifyProfile?_sound D.Pe (prof C) (D.prog C)
    false B outs hcert (D.sec sk) _ _ hin hbd
  obtain ⟨-, hfold, -⟩ := eval_parts hρ
  have hz := foldl_zenv (D.prog C).body
    (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x))
  rw [zenv_initEnv, hfold, Option.map_some] at hz
  show ((irun D (exactStepFn D) pk (D.prog C).body
      (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2)))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] =
    (((D.prog C).body.foldlM (exactStep D.Pe)
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2)))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD []
  rw [irun_exact D pk _ _ _ _ hex hz]

theorem probLM_eq_bgvSealExact [DecidableEq (M bgvSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → bgvSealData.PK) (sk : Ω → bgvSealData.SK) (tape : Ω → ℕ → bgvSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvSealData.PK → LAdv bgvSealData Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, bgvSealData.KeysOK (pk ω) (sk ω) ∧
      ∀ i, bgvSealData.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mkSealExact (exactClass bgvSealData bgvSealProfile)
        (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV b (pk ω) (sk ω)
        (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty bgvSealData) = true} =
      μ {ω | gameCPA (S := freshScheme bgvSealData (exactClass bgvSealData bgvSealProfile)
          (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV) b
        (pk ω) (tape ω) (reductionLM mkSealExact (exactClass bgvSealData bgvSealProfile)
          (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV A (coins ω)
            (pk ω)) 0 = true} :=
  probLM_eq bgvSealData mkSealExact (fun _ _ _ => ⟨rfl, rfl, rfl⟩) _ _ _
    (exactStep_interpOK bgvSealData)
    (correct_lm_exact bgvSealData
      (Validation.IndCpaDProfile.encOK_bgvData bgvSeal 41 1 41 41 (by decide) (by decide))
      bgvSealProfile) μ pk sk tape coins A b hgood

example := (@exactStep_interpOK : type_of% @Challenge.IndCpaDLM.exactStep_interpOK)
example := (@correct_lm_exact : type_of% @Challenge.IndCpaDLM.correct_lm_exact)
example := (@probLM_eq_bgvSealExact : type_of% @Challenge.IndCpaDLM.probLM_eq_bgvSealExact)

end Validation.IndCpaDLM
