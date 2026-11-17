import Challenge.IndCpaD.SanityInstances
import Validation.IndCpaD.ProfileBGVKS
import Validation.IndCpaD.LMBFV
import Validation.IndCpaD.LMAgreeBFV
import Validation.IndCpaD.LMAgree
import Validation.IndCpaD.Sanity

/-!
# Validation.IndCpaD.SanityInstances — proofs of `Challenge.IndCpaD.SanityInstances`

The norm is a `Finset.sup`; the null bad event is an almost-everywhere statement over the finitely
many tape entries; the joint witnesses are the noisy key generations of
`keyGen_noisy_bgvKSSeal` and `bfvKeyGen_noisy_bfvSeal` with all-ones secret state and randomness,
and the correctness conclusion is `Correct.eval` of the proved instances. Locked definitions are
read through `show`/`change` only.
-/

namespace Validation.IndCpaDSanity
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile Challenge.IndCpaDLM Spec.Encrypt MeasureTheory

/-! ## 1. Good randomness -/

theorem normInf_le_iff {N : ℕ} (a : IntPoly N) (B : ℕ) :
    normInf a ≤ B ↔ ∀ j, (a.coeff j).natAbs ≤ B := by
  simp [normInf, Finset.sup_le_iff]

theorem goodE3_iff {N : ℕ} (r : IntPoly N × IntPoly N × IntPoly N) (Bu B1 B2 : ℕ) :
    (normInf r.1 ≤ Bu ∧ normInf r.2.1 ≤ B1 ∧ normInf r.2.2 ≤ B2) ↔
      ∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2 := by
  simp only [normInf_le_iff]
  exact ⟨fun h j => ⟨h.1 j, h.2.1 j, h.2.2 j⟩,
    fun h => ⟨fun j => (h j).1, fun j => (h j).2.1, fun j => (h j).2.2⟩⟩

theorem goodE_bgvData_iff (P : FullParams) (Bk Bu B1 B2 : ℕ) (pk : (bgvData P Bk Bu B1 B2).PK)
    (sk : (bgvData P Bk Bu B1 B2).SK)
    (r : IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    (bgvData P Bk Bu B1 B2).GoodE pk sk r ↔
      ∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2 :=
  goodE3_iff r Bu B1 B2

theorem goodE_bgvKSData_iff (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (pk : (bgvKSData P lay rots Bk Bu B1 B2).PK)
    (sk : (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (r : IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    (bgvKSData P lay rots Bk Bu B1 B2).GoodE pk sk r ↔
      ∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2 :=
  goodE3_iff r Bu B1 B2

theorem goodE_bfvKSData_iff (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (pk : (bfvKSData P lay rots Bk Bu B1 B2).PK)
    (sk : (bfvKSData P lay rots Bk Bu B1 B2).SK)
    (r : IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    (bfvKSData P lay rots Bk Bu B1 B2).GoodE pk sk r ↔
      ∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2 :=
  goodE3_iff r Bu B1 B2

/-! ## 2. Truncated samplers -/

/-- The generic form: keys good almost surely and every coefficient of the first `q` samples
within its bound almost surely give a null bad event, for any predicate `GoodE` implied by the
coefficient bounds. -/
theorem bad_null_generic {Ω PK SK : Type} {N : ℕ} [MeasurableSpace Ω] (μ : Measure Ω)
    (KeysOK : PK → SK → Prop) (GoodE : PK → SK → IntPoly N × IntPoly N × IntPoly N → Prop)
    (Bu B1 B2 : ℕ)
    (hG : ∀ p s r, (∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2) → GoodE p s r)
    (pk : Ω → PK) (sk : Ω → SK) (tape : Ω → ℕ → IntPoly N × IntPoly N × IntPoly N) (q : ℕ)
    (hk : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω))
    (ht : ∀ i < q, ∀ᵐ ω ∂μ, ∀ j, ((tape ω i).1.coeff j).natAbs ≤ Bu ∧
      ((tape ω i).2.1.coeff j).natAbs ≤ B1 ∧ ((tape ω i).2.2.coeff j).natAbs ≤ B2) :
    μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} = 0 := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, i < q → ∀ j, ((tape ω i).1.coeff j).natAbs ≤ Bu ∧
      ((tape ω i).2.1.coeff j).natAbs ≤ B1 ∧ ((tape ω i).2.2.coeff j).natAbs ≤ B2 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i < q
    · filter_upwards [ht i hi] with ω h _ using h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hi
  have h : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i) := by
    filter_upwards [hk, hall] with ω h1 h2
    exact ⟨h1, fun i hi => hG _ _ _ (h2 i hi)⟩
  rwa [ae_iff] at h

theorem bad_null_bgvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (tape : Ω → ℕ → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) (q : ℕ)
    (hk : ∀ᵐ ω ∂μ, (bgvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω))
    (ht : ∀ i < q, ∀ᵐ ω ∂μ, ∀ j, ((tape ω i).1.coeff j).natAbs ≤ Bu ∧
      ((tape ω i).2.1.coeff j).natAbs ≤ B1 ∧ ((tape ω i).2.2.coeff j).natAbs ≤ B2) :
    μ {ω | ¬ ((bgvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω) ∧
      ∀ i < q, (bgvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (tape ω i))} = 0 :=
  bad_null_generic μ _ _ Bu B1 B2
    (fun p s r h => (goodE_bgvKSData_iff P lay rots Bk Bu B1 B2 p s r).2 h) pk sk tape q hk ht

theorem bad_null_bfvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).SK)
    (tape : Ω → ℕ → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) (q : ℕ)
    (hk : ∀ᵐ ω ∂μ, (bfvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω))
    (ht : ∀ i < q, ∀ᵐ ω ∂μ, ∀ j, ((tape ω i).1.coeff j).natAbs ≤ Bu ∧
      ((tape ω i).2.1.coeff j).natAbs ≤ B1 ∧ ((tape ω i).2.2.coeff j).natAbs ≤ B2) :
    μ {ω | ¬ ((bfvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω) ∧
      ∀ i < q, (bfvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (tape ω i))} = 0 :=
  bad_null_generic μ _ _ Bu B1 B2
    (fun p s r h => (goodE_bfvKSData_iff P lay rots Bk Bu B1 B2 p s r).2 h) pk sk tape q hk ht

/-! ## 3. Joint witnesses -/

/-- The number of outputs of `sem` on the right number of messages, for a circuit that replays on
zero messages. -/
theorem sem_length {D : AbsScheme} {C : D.Circ}
    (hz : (Source.eval D.P.src (D.prog C) fun _ => .exact 0).isSome)
    (ms : List (M D)) (hl : ms.length = (D.fresh C).length) :
    (D.sem C ms).length = (D.prog C).outputs.length := by
  obtain ⟨ρz, hρz⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨hok, hf, hout⟩ := Validation.IndCpaDLM.eval_parts hρz
  obtain ⟨ρm, hfm, hz'⟩ := Validation.IndCpaDLM.foldl_of_zero (D.prog C)
    (fun x => .exact (D.msg C ms x)) ρz hf
  have hem : Source.eval D.P.src (D.prog C) (fun x => .exact (D.msg C ms x)) = some ρm := by
    refine Validation.IndCpaDLM.eval_of_parts hok hfm fun o ho => ?_
    have := hout o ho
    rw [← hz', Validation.IndCpaDLM.zenv_apply] at this
    simpa using this
  unfold AbsScheme.sem
  rw [ite_eq_left_of_eq_true _ _ (eq_true hl), hem]
  simp

/-- The all-ones integer polynomial. -/
def ones (N : ℕ) : IntPoly N := ⟨fun _ => 1⟩

theorem ones_ne_zero {N : ℕ} (hN : 0 < N) : ones N ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : IntPoly N => p.coeff ⟨0, hN⟩) h
  exact one_ne_zero (h1 : (1 : ℤ) = 0)

theorem normInf_ones (N : ℕ) : normInf (ones N) ≤ 1 :=
  (normInf_le_iff _ _).2 fun _ => le_refl _

set_option maxRecDepth 100000 in
theorem bgvKSSeal_jointly :
    ∃ (pk : bgvKSSealData.PK) (sk : bgvKSSealData.SK) (r : bgvKSSealData.ER),
      bgvKSSealData.KeysOK pk sk ∧ bgvKSSealData.GoodE pk sk r ∧
      sk.1 ≠ 0 ∧ sk.2 ≠ 0 ∧ r.1 ≠ 0 ∧ r.2.1 ≠ 0 ∧ r.2.2 ≠ 0 ∧
      ksClass bgvKSSealData bgvKSLayout [5] bgvKSSealProfile bgvKSSealCirc = true ∧
      ∀ m₁ m₂ : M bgvKSSealData,
        (ksEval bgvKSSealData bgvKSLayout pk.2.2.1 pk.2.2.2 bgvKSSealCirc
            [bgvKSSealData.enc pk m₁ r, bgvKSSealData.enc pk m₂ r]).map
            (bgvKSSealData.decBGV sk) =
          bgvKSSealData.sem bgvKSSealCirc [m₁, m₂] ∧
        (bgvKSSealData.sem bgvKSSealCirc [m₁, m₂]).length = 1 := by
  have hN : 0 < bgvKSSeal.src.N := by decide
  have hs : SecretOK bgvKSSeal.secretBound (ones bgvKSSeal.src.N) :=
    le_trans (normInf_ones _) (by decide)
  have he : normInf (ones bgvKSSeal.src.N) ≤ 21 := le_trans (normInf_ones _) (by decide)
  have hk := Validation.IndCpaDProfile.keyGen_noisy_bgvKSSeal (ones _) (ones _) 0 hs he []
    (fun _ => [])
  generalize keyGen _ _ _ _ _ _ _ _ _ = pk0 at hk
  refine ⟨_, _, (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N), hk,
    ?_, ones_ne_zero hN, ones_ne_zero hN, ones_ne_zero hN, ones_ne_zero hN, ones_ne_zero hN,
    Validation.IndCpaDProfile.ksClass_bgvKSSeal.1, ?_⟩
  · show normInf (ones bgvKSSeal.src.N) ≤ 1 ∧ normInf (ones bgvKSSeal.src.N) ≤ 21 ∧
      normInf (ones bgvKSSeal.src.N) ≤ 21
    exact ⟨normInf_ones _, he, he⟩
  · intro m₁ m₂
    have hg : ∀ p ∈ [(m₁, (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N)),
        (m₂, (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N))],
        ∀ (pk' : bgvKSSealData.PK) (sk' : bgvKSSealData.SK), bgvKSSealData.GoodE pk' sk' p.2 := by
      intro p hp pk' sk'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;>
        exact (show normInf (ones bgvKSSeal.src.N) ≤ 1 ∧ normInf (ones bgvKSSeal.src.N) ≤ 21 ∧
          normInf (ones bgvKSSeal.src.N) ≤ 21 from ⟨normInf_ones _, he, he⟩)
    have h := Validation.IndCpaDProfile.correct_ksEval_bgvKSSeal.eval pk0
      (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N) hk bgvKSSealCirc
      Validation.IndCpaDProfile.ksClass_bgvKSSeal.1
      [(m₁, (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N)),
        (m₂, (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N))]
      (fun p hp => hg p hp pk0 (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N))
    change (if [bgvKSSealData.enc pk0 m₁ (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N), bgvKSSealData.enc pk0 m₂ (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N)].length =
        (bgvKSSealData.fresh bgvKSSealCirc).length then
          ksEval bgvKSSealData bgvKSLayout pk0.2.2.1 pk0.2.2.2 bgvKSSealCirc
            [bgvKSSealData.enc pk0 m₁ (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N), bgvKSSealData.enc pk0 m₂ (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N, ones bgvKSSeal.src.N)] else []).map
        (bgvKSSealData.decBGV (ones bgvKSSeal.src.N, ones bgvKSSeal.src.N)) = bgvKSSealData.sem bgvKSSealCirc [m₁, m₂] at h
    have hz : (Source.eval bgvKSSealData.P.src (bgvKSSealData.prog bgvKSSealCirc)
        fun _ => .exact 0).isSome := by
      have hc := Validation.IndCpaDProfile.ksClass_bgvKSSeal.1
      change (admBGV bgvKSSealData (fun _ => Spec.Budget.certified bgvKSSeal bgvKSLayout)
        bgvKSSealCirc && _ && _) = true at hc
      simp only [Bool.and_eq_true] at hc
      exact Validation.IndCpaDLM.admBGV_eval hc.1.1
    split at h
    · exact ⟨h, (sem_length hz [m₁, m₂] rfl).trans rfl⟩
    · exact absurd rfl ‹_›

set_option maxRecDepth 100000 in
theorem bfvSeal_jointly :
    ∃ (pk : bfvSealData.PK) (sk : bfvSealData.SK) (r : bfvSealData.ER),
      bfvSealData.KeysOK pk sk ∧ bfvSealData.GoodE pk sk r ∧
      sk.1 ≠ 0 ∧ sk.2 ≠ 0 ∧ r.1 ≠ 0 ∧ r.2.1 ≠ 0 ∧ r.2.2 ≠ 0 ∧
      admBFVSeal (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) = true ∧
      ∀ m₁ m₂ : M bfvSealData,
        (evBFVSeal pk (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2)
            [bfvSealData.enc pk m₁ r, bfvSealData.enc pk m₂ r]).map (bfvSealData.decBFV sk) =
          bfvSealData.sem (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) [m₁, m₂] ∧
        (bfvSealData.sem (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) [m₁, m₂]).length = 1 := by
  have hN : 0 < Challenge.BFV.sealBFV.src.N := by decide
  have hs : SecretOK Challenge.BFV.sealBFV.secretBound (ones Challenge.BFV.sealBFV.src.N) :=
    le_trans (normInf_ones _) (by decide)
  have he : normInf (ones Challenge.BFV.sealBFV.src.N) ≤ 21 := le_trans (normInf_ones _) (by decide)
  have hk := Validation.IndCpaDLM.bfvKeyGen_noisy_bfvSeal (ones _) (ones _) 0 hs he
    (fun _ => []) (fun _ _ => [])
  generalize Challenge.IndCpaDLM.bfvKeyGen _ _ _ _ _ _ _ _ _ = pk0 at hk
  -- the class: the oracle accepts stage 1 on the fresh entries, and agrees with the class there
  have hreach : Reach mkBFVSeal admBFVSeal bfvG0 :=
    Reach.link _ _ (Reach.link _ _ Reach.empty)
  have hdecl : ∀ d ∈ bfvStage1.1.inputs, d.name ∈ bfvStage1.2.1 →
      d = freshDecl bfvSealData d.name := by
    intro d hd _
    change d ∈ [bfvSealDecl "a", bfvSealDecl "b"] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> rfl
  have hadm : admBFVSeal (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) = true := by
    rw [← Validation.IndCpaDLM.admLM_fresh_bfvSeal bfvG0 hreach bfvStage1
      [("a", true), ("b", true)] rfl rfl (by decide) (by decide) hdecl (by decide)]
    exact Validation.IndCpaDLM.lm_two_stage_bfv_kernel.2.1
  refine ⟨_, _, (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N,
    ones Challenge.BFV.sealBFV.src.N), hk,
    ?_, ones_ne_zero hN, ones_ne_zero hN, ones_ne_zero hN, ones_ne_zero hN, ones_ne_zero hN,
    hadm, ?_⟩
  · show normInf (ones Challenge.BFV.sealBFV.src.N) ≤ 1 ∧
      normInf (ones Challenge.BFV.sealBFV.src.N) ≤ 21 ∧
      normInf (ones Challenge.BFV.sealBFV.src.N) ≤ 21
    exact ⟨normInf_ones _, he, he⟩
  · intro m₁ m₂
    have hg : ∀ p ∈ [(m₁, (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N,
          ones Challenge.BFV.sealBFV.src.N)),
        (m₂, (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N,
          ones Challenge.BFV.sealBFV.src.N))],
        ∀ (pk' : bfvSealData.PK) (sk' : bfvSealData.SK), bfvSealData.GoodE pk' sk' p.2 := by
      intro p hp pk' sk'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;>
        exact (show normInf (ones Challenge.BFV.sealBFV.src.N) ≤ 1 ∧
          normInf (ones Challenge.BFV.sealBFV.src.N) ≤ 21 ∧
          normInf (ones Challenge.BFV.sealBFV.src.N) ≤ 21 from ⟨normInf_ones _, he, he⟩)
    have h := Validation.IndCpaDLM.correct_lm_bfvSeal.eval pk0
      (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N) hk
      (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) hadm
      [(m₁, (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N,
          ones Challenge.BFV.sealBFV.src.N)),
        (m₂, (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N,
          ones Challenge.BFV.sealBFV.src.N))]
      (fun p hp => hg p hp pk0 (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N))
    change (if [bfvSealData.enc pk0 m₁ (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N), bfvSealData.enc pk0 m₂ (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N)].length =
        (bfvSealData.fresh (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2)).length then
          evBFVSeal pk0 (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2)
            [bfvSealData.enc pk0 m₁ (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N), bfvSealData.enc pk0 m₂ (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N)] else []).map
        (bfvSealData.decBFV (ones Challenge.BFV.sealBFV.src.N, ones Challenge.BFV.sealBFV.src.N)) = bfvSealData.sem (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2)
          [m₁, m₂] at h
    have hz : (Source.eval bfvSealData.P.src
        (bfvSealData.prog (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2))
        fun _ => .exact 0).isSome := by
      have hc : (admBFV bfvSealData (fun _ _ => bfvSealBudget)
          (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) &&
          bfvSide bfvSealData.Pe bfvSealLayout &&
          bfvNeed bfvSealData.Pe bfvSealLayout [5] bfvSealBudget
            (bfvSealData.prog (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2)).body
            (initEnv bfvSealData.P.src
              (bfvSealData.prog (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2))
              fun _ => .exact 0)) = true := hadm
      simp only [Bool.and_eq_true] at hc
      exact Validation.IndCpaDLM.admBFV_eval hc.1.1
    split at h
    · exact ⟨h, (sem_length hz [m₁, m₂] rfl).trans rfl⟩
    · exact absurd rfl ‹_›

/-! ## 4. The public key -/

theorem bgvKSData_pk_has_gadget_keys (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (pk : (bgvKSData P lay rots Bk Bu B1 B2).PK)
    (sk : (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (hk : (bgvKSData P lay rots Bk Bu B1 B2).KeysOK pk sk) :
    Budget.GadgetKeysOK P lay P.src.qs.length .square sk.1 pk.2.2.1 ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) sk.1 (pk.2.2.2 g) := by
  obtain ⟨_, _, _, h1, h2⟩ := hk
  exact ⟨h1, h2⟩

theorem irun_exact_pk (D : AbsScheme) (pk pk' : D.PK) :
    ∀ (body : List Instr) (ρ : Env D.P.src) (σ : Trace.CtEnv D.Pe),
      irun D (exactStepFn D) pk body ρ σ = irun D (exactStepFn D) pk' body ρ σ
  | [], _, _ => rfl
  | i :: is, ρ, σ => by
    show ((step D.P.src ρ i).bind fun ρ' => (exactStep' D.Pe σ i).bind fun σ' =>
        irun D (exactStepFn D) pk is ρ' σ') =
      ((step D.P.src ρ i).bind fun ρ' => (exactStep' D.Pe σ i).bind fun σ' =>
        irun D (exactStepFn D) pk' is ρ' σ')
    congr 1
    funext ρ'
    congr 1
    funext σ'
    exact irun_exact_pk D pk pk' is ρ' σ'

theorem exactEval_ignores_pk (D : AbsScheme) (pk pk' : D.PK) (C : D.Circ) (cs : List (CT D)) :
    interpEval D (exactStepFn D) pk C cs = interpEval D (exactStepFn D) pk' C cs := by
  show ((irun D (exactStepFn D) pk (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
        fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] =
    ((irun D (exactStepFn D) pk' (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
        fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD []
  rw [irun_exact_pk D pk pk']

theorem bgvData_pk (P : FullParams) (Bk Bu B1 B2 : ℕ) :
    (bgvData P Bk Bu B1 B2).PK = (IntPoly P.src.N × IntPoly P.src.N) ∧
      ∀ (pk : IntPoly P.src.N × IntPoly P.src.N) m r, (bgvData P Bk Bu B1 B2).enc pk m r =
        (P.src.qs.length, Spec.Encrypt.encrypt P.src.t pk.1 pk.2 (liftMsg m) r.1 r.2.1 r.2.2) :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-! ## 5. Measurability at an instance -/

theorem bgvKSSeal_events_measurable [DecidableEq (M bgvKSSealData)] {Ω Coins : Type}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (pk : Ω → bgvKSSealData.PK) (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool) (b : Bool)
    (q : ℕ) :
    MeasurableSet {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true} ∧
      MeasurableSet {ω | ¬ (bgvKSSealData.KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, bgvKSSealData.GoodE (pk ω) (sk ω) (tape ω i))} :=
  ⟨countable_measurableSet _, countable_measurableSet _⟩

example := (@normInf_le_iff : type_of% @Challenge.IndCpaDSanity.normInf_le_iff)
example := (@goodE_bgvData_iff : type_of% @Challenge.IndCpaDSanity.goodE_bgvData_iff)
example := (@goodE_bgvKSData_iff : type_of% @Challenge.IndCpaDSanity.goodE_bgvKSData_iff)
example := (@goodE_bfvKSData_iff : type_of% @Challenge.IndCpaDSanity.goodE_bfvKSData_iff)
example := (@bad_null_bgvKSData : type_of% @Challenge.IndCpaDSanity.bad_null_bgvKSData)
example := (@bad_null_bfvKSData : type_of% @Challenge.IndCpaDSanity.bad_null_bfvKSData)
example := (@bgvKSSeal_jointly : type_of% @Challenge.IndCpaDSanity.bgvKSSeal_jointly)
example := (@bfvSeal_jointly : type_of% @Challenge.IndCpaDSanity.bfvSeal_jointly)
example := (@bgvKSData_pk_has_gadget_keys :
  type_of% @Challenge.IndCpaDSanity.bgvKSData_pk_has_gadget_keys)
example := (@exactEval_ignores_pk : type_of% @Challenge.IndCpaDSanity.exactEval_ignores_pk)
example := (@bgvData_pk : type_of% @Challenge.IndCpaDSanity.bgvData_pk)
example := (@bgvKSSeal_events_measurable :
  type_of% @Challenge.IndCpaDSanity.bgvKSSeal_events_measurable)

end Validation.IndCpaDSanity
