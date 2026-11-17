import Challenge.IndCpaD.LMBFV
import Challenge.IndCpaD.LMExact
import Challenge.IndCpaD.Sanity
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Challenge.IndCpaD.SanityInstances — good randomness is exactly the coefficient bounds, and the hypotheses of the instances hold jointly   (LOCKED statements; proofs in `Validation/IndCpaD/SanityInstances.lean`)

1. **`GoodE` is exactly "every coefficient within its bound"** (`normInf_le_iff`,
   `goodE_bgvData_iff`, `goodE_bgvKSData_iff`, `goodE_bfvKSData_iff`): the converse of the tail
   statements of `Challenge.IndCpaD.BadEvent`.
2. **Samplers truncated at the declared bounds have a null bad event** (`bad_null_bgvKSData`,
   `bad_null_bfvKSData`): under any measure for which the keys are good almost surely and, for
   each of the first `q` encryptions, every coefficient of the three sampled polynomials is within
   its bound almost surely, the bad event of the reduction has measure zero, so the advantage
   bound holds with no loss.
3. **Every hypothesis of the BGV instance with key switching holds at once, at `N = 2¹³`, with
   non-zero keys and randomness** (`bgvKSSeal_jointly`): one public key, one secret state and one
   encryption randomness, all non-zero, such that the keys are good, the randomness is good, a
   circuit with a product, a relinearization, a rotation, a modulus switch and a plaintext
   addition is in the class, and the textbook decryptions of the evaluator's outputs on two
   encryptions of any two messages are what the program computes (one output: the conclusion
   is not about an empty list). The BFV counterpart
   (`bfvSeal_jointly`) has the product-and-relinearization circuit of stage 1.
4. **The public key the IND-CPA assumption is about** (`bgvKSData_pk_has_gadget_keys`,
   `exactEval_ignores_pk`, `bgvData_pk`): with key switching, good keys put gadget encryptions
   of `s²` and of every `σ_g(s)`, `g ∈ rots`, into the public key, so the assumption of the
   reduction includes circular security; the exact-operation evaluator of
   `Challenge.IndCpaD.LMExact` reads nothing from the public key, and the public key of
   `bgvData` is the encryption key `(b, a)` alone, so for that instance the reduction is to
   IND-CPA of plain public-key encryption.
5. **Measurability at an instance** (`bgvKSSeal_events_measurable`): on a countable sample space
   the events of `advLM_le_bgvKSSeal` are measurable, whatever the adversary.
-/

namespace Challenge.IndCpaDSanity
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile Challenge.IndCpaDLM Spec.Encrypt MeasureTheory

/-! ## 1. Good randomness is the coefficient bounds -/

/-- **The infinity norm is at most `B` exactly when every coefficient is.** -/
theorem normInf_le_iff {N : ℕ} (a : IntPoly N) (B : ℕ) :
    normInf a ≤ B ↔ ∀ j, (a.coeff j).natAbs ≤ B := sorry

/-- **`GoodE` of `bgvData` is the coefficient bounds.** -/
theorem goodE_bgvData_iff (P : FullParams) (Bk Bu B1 B2 : ℕ) (pk : (bgvData P Bk Bu B1 B2).PK)
    (sk : (bgvData P Bk Bu B1 B2).SK)
    (r : IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    (bgvData P Bk Bu B1 B2).GoodE pk sk r ↔
      ∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2 := sorry

/-- **`GoodE` of `bgvKSData` is the coefficient bounds.** -/
theorem goodE_bgvKSData_iff (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (pk : (bgvKSData P lay rots Bk Bu B1 B2).PK)
    (sk : (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (r : IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    (bgvKSData P lay rots Bk Bu B1 B2).GoodE pk sk r ↔
      ∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2 := sorry

/-- **`GoodE` of `bfvKSData` is the coefficient bounds.** -/
theorem goodE_bfvKSData_iff (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (pk : (bfvKSData P lay rots Bk Bu B1 B2).PK)
    (sk : (bfvKSData P lay rots Bk Bu B1 B2).SK)
    (r : IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) :
    (bfvKSData P lay rots Bk Bu B1 B2).GoodE pk sk r ↔
      ∀ j, (r.1.coeff j).natAbs ≤ Bu ∧ (r.2.1.coeff j).natAbs ≤ B1 ∧
        (r.2.2.coeff j).natAbs ≤ B2 := sorry

/-! ## 2. Truncated samplers -/

/-- **BGV with key switching: truncated samplers give a null bad event.** -/
theorem bad_null_bgvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (tape : Ω → ℕ → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) (q : ℕ)
    (hk : ∀ᵐ ω ∂μ, (bgvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω))
    (ht : ∀ i < q, ∀ᵐ ω ∂μ, ∀ j, ((tape ω i).1.coeff j).natAbs ≤ Bu ∧
      ((tape ω i).2.1.coeff j).natAbs ≤ B1 ∧ ((tape ω i).2.2.coeff j).natAbs ≤ B2) :
    μ {ω | ¬ ((bgvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω) ∧
      ∀ i < q, (bgvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (tape ω i))} = 0 := sorry

/-- **BFV with key switching: truncated samplers give a null bad event.** -/
theorem bad_null_bfvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).PK) (sk : Ω → (bfvKSData P lay rots Bk Bu B1 B2).SK)
    (tape : Ω → ℕ → IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N) (q : ℕ)
    (hk : ∀ᵐ ω ∂μ, (bfvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω))
    (ht : ∀ i < q, ∀ᵐ ω ∂μ, ∀ j, ((tape ω i).1.coeff j).natAbs ≤ Bu ∧
      ((tape ω i).2.1.coeff j).natAbs ≤ B1 ∧ ((tape ω i).2.2.coeff j).natAbs ≤ B2) :
    μ {ω | ¬ ((bfvKSData P lay rots Bk Bu B1 B2).KeysOK (pk ω) (sk ω) ∧
      ∀ i < q, (bfvKSData P lay rots Bk Bu B1 B2).GoodE (pk ω) (sk ω) (tape ω i))} = 0 := sorry

/-! ## 3. Joint non-vacuity at `N = 2¹³` -/

/-- **BGV with key switching at `bgvKSSeal`: every hypothesis at once, non-zero witnesses**, and
the correctness conclusion on the circuit `bgvKSSealCirc` for every pair of messages. -/
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
        (bgvKSSealData.sem bgvKSSealCirc [m₁, m₂]).length = 1 := sorry

/-- **BFV with key switching at `sealBFV`: every hypothesis at once, non-zero witnesses**, and
the correctness conclusion on the product-and-relinearization circuit of stage 1. -/
theorem bfvSeal_jointly :
    ∃ (pk : bfvSealData.PK) (sk : bfvSealData.SK) (r : bfvSealData.ER),
      bfvSealData.KeysOK pk sk ∧ bfvSealData.GoodE pk sk r ∧
      sk.1 ≠ 0 ∧ sk.2 ≠ 0 ∧ r.1 ≠ 0 ∧ r.2.1 ≠ 0 ∧ r.2.2 ≠ 0 ∧
      admBFVSeal (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) = true ∧
      ∀ m₁ m₂ : M bfvSealData,
        (evBFVSeal pk (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2)
            [bfvSealData.enc pk m₁ r, bfvSealData.enc pk m₂ r]).map (bfvSealData.decBFV sk) =
          bfvSealData.sem (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) [m₁, m₂] ∧
        (bfvSealData.sem (mkBFVSeal bfvStage1.1 bfvStage1.2.1 bfvStage1.2.2) [m₁, m₂]).length = 1 :=
    sorry

/-! ## 4. The public key -/

/-- **With key switching the public key contains gadget encryptions of functions of the
secret**, whenever the keys are good. -/
theorem bgvKSData_pk_has_gadget_keys (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (pk : (bgvKSData P lay rots Bk Bu B1 B2).PK)
    (sk : (bgvKSData P lay rots Bk Bu B1 B2).SK)
    (hk : (bgvKSData P lay rots Bk Bu B1 B2).KeysOK pk sk) :
    Budget.GadgetKeysOK P lay P.src.qs.length .square sk.1 pk.2.2.1 ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) sk.1 (pk.2.2.2 g) := sorry

/-- **The exact-operation evaluator reads nothing from the public key.** -/
theorem exactEval_ignores_pk (D : AbsScheme) (pk pk' : D.PK) (C : D.Circ) (cs : List (CT D)) :
    interpEval D (exactStepFn D) pk C cs = interpEval D (exactStepFn D) pk' C cs := sorry

/-- **The public key of `bgvData` is the encryption key `(b, a)` alone**, and its encryption
is `Spec.Encrypt.encrypt` of `liftMsg m` under it at the top level. -/
theorem bgvData_pk (P : FullParams) (Bk Bu B1 B2 : ℕ) :
    (bgvData P Bk Bu B1 B2).PK = (IntPoly P.src.N × IntPoly P.src.N) ∧
      ∀ (pk : IntPoly P.src.N × IntPoly P.src.N) m r, (bgvData P Bk Bu B1 B2).enc pk m r =
        (P.src.qs.length, Spec.Encrypt.encrypt P.src.t pk.1 pk.2 (liftMsg m) r.1 r.2.1 r.2.2) :=
  sorry

/-! ## 5. Measurability at an instance -/

/-- **For a countable sample space the events of the reduction at `bgvKSSeal` are measurable**
(the game with evaluation on earlier results and the bad event of `advLM_le_bgvKSSeal`), for every
key, randomness and coin map and every adversary: on a countable sample space with measurable
singletons every event is measurable, in particular those of `advLM_le_bgvKSSeal`. -/
theorem bgvKSSeal_events_measurable [DecidableEq (M bgvKSSealData)] {Ω Coins : Type}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (pk : Ω → bgvKSSealData.PK) (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool) (b : Bool)
    (q : ℕ) :
    MeasurableSet {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true} ∧
      MeasurableSet {ω | ¬ (bgvKSSealData.KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, bgvKSSealData.GoodE (pk ω) (sk ω) (tape ω i))} := sorry

end Challenge.IndCpaDSanity
