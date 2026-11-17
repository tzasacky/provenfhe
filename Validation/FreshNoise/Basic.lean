import Validation.FreshNoise.Tail
import Validation.Headline.Noise
import FHE.KeySwitch.Step
import Validation.Decrypt
import Validation.Trace

/-!
# Validation.FreshNoise.Basic — a fresh encryption encrypts; the noise headline with fresh inputs

Proofs of `Challenge.FreshNoise.phase_encrypt`, `encrypt_encrypts`, `liftMsg_stored`,
`centered_stored`, `encrypt_stored_exceeds`, `freshError_worst`,
`freshError_worst_attained`, `fresh_sound`, `fresh_certified`, `fresh_certified_kappa`, and of the
certificate statements `freshOK?_spec`, `outputKey?_eq`, `certified_decrypts`,
`fresh_worst_decrypts`, `fresh_kappa_decrypts`.
-/

namespace Validation.FreshNoise
open Spec NPoly Scheme Source Correct Spec.Encrypt Challenge.Headline MeasureTheory ProbabilityTheory
open Challenge.FreshNoise
open Validation.Ring Validation.Scheme

variable {N : ℕ}

/-! ## 1. The phase of a fresh encryption -/

theorem ofInt_smul' (Q : ℕ) (c : ℤ) (a : IntPoly N) :
    ofInt Q (c • a) = (c : ZMod Q) • ofInt Q a := by
  ext i; simp

theorem phase_encrypt (t Q : ℕ) (s e b a p u e₁ e₂ : IntPoly N)
    (hpk : PublicKeyOK t Q s e b a) :
    phase (ofInt Q s) ((encrypt t b a p u e₁ e₂).map (ofInt Q)) =
      ofInt Q (p + (t : ℤ) • freshError s e u e₁ e₂) := by
  have hpk' : ofInt Q (b + a * s) = ofInt Q ((t : ℤ) • e) := hpk
  show phase (ofInt Q s) ([b * u + (t : ℤ) • e₁ + p, a * u + (t : ℤ) • e₂].map (ofInt Q)) =
    ofInt Q (p + (t : ℤ) • (e * u + e₁ + e₂ * s))
  rw [phase_map_ofInt_two]
  simp only [ofInt_add, ofInt_mul, ofInt_smul'] at hpk' ⊢
  apply eq_of_neZero; intro
  simp only [smul_eq_const_mul] at hpk' ⊢
  have hb : ofInt Q b = const ((t : ℤ) : ZMod Q) * ofInt Q e - ofInt Q a * ofInt Q s :=
    eq_sub_of_add_eq hpk'
  rw [hb]; ring

theorem encrypt_encrypts (t Q Bp ε : ℕ) (ht : 2 ≤ t) (s e b a p u e₁ e₂ : IntPoly N)
    (hpk : PublicKeyOK t Q s e b a) (hp : normInf p ≤ Bp)
    (hε : normInf (freshError s e u e₁ e₂) ≤ ε) (hQ : 2 * freshNoise t Bp ε < Q) :
    BGVEncrypts t (freshNoise t Bp ε) s ((encrypt t b a p u e₁ e₂).map (ofInt Q)) (ofInt t p) := by
  have _ := ht
  refine bgvEncrypts_of_phase (p + (t : ℤ) • freshError s e u e₁ e₂)
    (Validation.FreshNoise.phase_encrypt t Q s e b a p u e₁ e₂ hpk) ?_ hQ ?_
  · intro i
    have h1 : |p.coeff i| ≤ (Bp : ℤ) := (normInf_le_iff _ _).mp hp i
    have h2 : |(freshError s e u e₁ e₂).coeff i| ≤ (ε : ℤ) := (normInf_le_iff _ _).mp hε i
    have h3 : (p + (t : ℤ) • freshError s e u e₁ e₂).coeff i =
        p.coeff i + (t : ℤ) * (freshError s e u e₁ e₂).coeff i := rfl
    have h4 : ((freshNoise t Bp ε : ℕ) : ℤ) = (Bp : ℤ) + t * ε := by
      unfold freshNoise
      rw [Nat.cast_add, Nat.cast_mul]
    rw [h3, h4]
    have h7 : |(t : ℤ) * (freshError s e u e₁ e₂).coeff i| ≤ t * ε := by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg t)]
      exact mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg t)
    exact (abs_add_le _ _).trans (add_le_add h1 h7)
  · ext i
    show (((p.coeff i + (t : ℤ) * (freshError s e u e₁ e₂).coeff i : ℤ)) : ZMod t) =
      ((p.coeff i : ℤ) : ZMod t)
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero]

theorem liftMsg_stored (t : ℕ) (ht : 0 < t) (m : Poly t N) :
    ofInt t (liftMsg m) = m ∧ normInf (liftMsg m) ≤ t - 1 := by
  have : NeZero t := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · ext i
    show ((((m.coeff i).val : ℤ)) : ZMod t) = m.coeff i
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · rw [normInf_le_iff]
    intro i
    show |((m.coeff i).val : ℤ)| ≤ ((t - 1 : ℕ) : ℤ)
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    have := ZMod.val_lt (m.coeff i)
    omega

theorem centered_stored (t : ℕ) (ht : 0 < t) (m : Poly t N) :
    ofInt t (centered m) = m ∧ normInf (centered m) ≤ t / 2 := by
  have : NeZero t := ⟨by omega⟩
  refine ⟨ofInt_centered m, ?_⟩
  unfold normInf
  exact Finset.sup_le fun i _ => ZMod.natAbs_valMinAbs_le (m.coeff i)

theorem freshError_zero : freshError (0 : IntPoly N) 0 0 0 0 = 0 := by
  apply eq_of_neZero; intro
  unfold freshError
  simp

/-- The norm of a one-coefficient polynomial. -/
theorem normInf_const1_le (c : ℤ) (B : ℕ) (h : |c| ≤ (B : ℤ)) :
    normInf (⟨fun _ => c⟩ : IntPoly 1) ≤ B := by
  rw [normInf_le_iff]
  exact fun _ => h

theorem encrypt_stored_exceeds :
    PublicKeyOK 17 65537 (0 : IntPoly 1) 0 0 0 ∧
    ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1) = ofInt 17 (⟨fun _ => 11⟩ : IntPoly 1) ∧
    ¬ BGVEncrypts 17 (freshNoise 17 (17 - 1) 0) (0 : IntPoly 1)
        ((encrypt 17 0 0 (⟨fun _ => -40⟩ : IntPoly 1) 0 0 0).map (ofInt 65537))
        (ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (freshNoise 17 40 0) (0 : IntPoly 1)
        ((encrypt 17 0 0 (⟨fun _ => -40⟩ : IntPoly 1) 0 0 0).map (ofInt 65537))
        (ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (freshNoise 17 (17 - 1) 0) (0 : IntPoly 1)
        ((encrypt 17 0 0 (⟨fun _ => 11⟩ : IntPoly 1) 0 0 0).map (ofInt 65537))
        (ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1)) := by
  have hpk : PublicKeyOK 17 65537 (0 : IntPoly 1) 0 0 0 := by
    show ofInt 65537 ((0 : IntPoly 1) + 0 * 0) = ofInt 65537 (((17 : ℕ) : ℤ) • (0 : IntPoly 1))
    rw [smul_zero, mul_zero, add_zero]
  have hmsg : ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1) = ofInt 17 (⟨fun _ => 11⟩ : IntPoly 1) := by
    ext i
    show (((-40 : ℤ)) : ZMod 17) = (((11 : ℤ)) : ZMod 17)
    decide
  have hfe : normInf (freshError (0 : IntPoly 1) 0 0 0 0) ≤ 0 := by
    rw [freshError_zero, normInf_zero]
  have hn40 : freshNoise 17 40 0 = 40 := by unfold freshNoise; norm_num
  have hn16 : freshNoise 17 (17 - 1) 0 = 16 := by unfold freshNoise; norm_num
  have h40 := Validation.FreshNoise.encrypt_encrypts 17 65537 40 0 (by norm_num)
    (0 : IntPoly 1) 0 0 0 ⟨fun _ => -40⟩ 0 0 0 hpk (normInf_const1_le _ _ (by norm_num)) hfe
    (by rw [hn40]; norm_num)
  have h11 := Validation.FreshNoise.encrypt_encrypts 17 65537 (17 - 1) 0 (by norm_num)
    (0 : IntPoly 1) 0 0 0 ⟨fun _ => 11⟩ 0 0 0 hpk (normInf_const1_le _ _ (by norm_num)) hfe
    (by rw [hn16]; norm_num)
  refine ⟨hpk, hmsg, ?_, h40, hmsg ▸ h11⟩
  intro hbad
  have hc : centeredPhase (0 : IntPoly 1)
      ((encrypt 17 0 0 (⟨fun _ => -40⟩ : IntPoly 1) 0 0 0).map (ofInt 65537)) =
      ⟨fun _ => -40⟩ := by
    rw [centeredPhase, Validation.FreshNoise.phase_encrypt 17 65537 0 0 0 0 _ 0 0 0 hpk,
      freshError_zero, smul_zero, add_zero]
    apply centered_ofInt
    intro i
    show 2 * |(-40 : ℤ)| < ((65537 : ℕ) : ℤ)
    norm_num
  have h2 := (normInf_le_iff _ _).mp hbad.2 0
  rw [hc, hn16] at h2
  have h3 : |(-40 : ℤ)| ≤ ((16 : ℕ) : ℤ) := h2
  norm_num at h3

/-! ## 2. The worst case -/

theorem freshError_worst (s e u e₁ e₂ : IntPoly N) (Bs Bk Bu B1 B2 : ℕ) (hs : normInf s ≤ Bs)
    (he : normInf e ≤ Bk) (hu : normInf u ≤ Bu) (h1 : normInf e₁ ≤ B1) (h2 : normInf e₂ ≤ B2) :
    normInf (freshError s e u e₁ e₂) ≤ worstError N Bs Bk Bu B1 B2 := by
  rw [normInf_le_iff]
  intro k
  have ha := abs_coeff_mul_le_N e u Bk Bu ((normInf_le_iff _ _).mp he) ((normInf_le_iff _ _).mp hu) k
  have hb := abs_coeff_mul_le_N e₂ s B2 Bs ((normInf_le_iff _ _).mp h2) ((normInf_le_iff _ _).mp hs) k
  have hc := (normInf_le_iff _ _).mp h1 k
  have h3 : (freshError s e u e₁ e₂).coeff k = (e * u).coeff k + e₁.coeff k + (e₂ * s).coeff k := rfl
  have h4 : ((worstError N Bs Bk Bu B1 B2 : ℕ) : ℤ) =
      (N : ℤ) * Bk * Bu + B1 + (N : ℤ) * B2 * Bs := by
    unfold worstError; push_cast; ring
  rw [h3, h4]
  calc |(e * u).coeff k + e₁.coeff k + (e₂ * s).coeff k|
      ≤ |(e * u).coeff k + e₁.coeff k| + |(e₂ * s).coeff k| := abs_add_le _ _
    _ ≤ |(e * u).coeff k| + |e₁.coeff k| + |(e₂ * s).coeff k| := by
        gcongr; exact abs_add_le _ _
    _ ≤ (N : ℤ) * Bk * Bu + B1 + (N : ℤ) * B2 * Bs := by linarith

/-- The top coefficient of a product of all-constant polynomials. -/
theorem coeff_constPoly_mul_top (hN : 0 < N) (A B : ℤ) :
    ((⟨fun _ => A⟩ : IntPoly N) * ⟨fun _ => B⟩).coeff ⟨N - 1, by omega⟩ = N * (A * B) := by
  rw [coeff_mul']
  have : ∀ i : Fin N, (if h : i.val ≤ N - 1 then A * B else -(A * B)) = A * B := by
    intro i
    have := i.isLt
    exact dite_eq_left (by omega)
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem normInf_constPoly_le (B : ℕ) : normInf (⟨fun _ => (B : ℤ)⟩ : IntPoly N) ≤ B := by
  rw [normInf_le_iff]
  intro i
  show |(B : ℤ)| ≤ B
  rw [abs_of_nonneg (Int.natCast_nonneg B)]

theorem freshError_worst_attained (hN : 0 < N) (Bs Bk Bu B1 B2 : ℕ) :
    normInf (freshError (⟨fun _ => (Bs : ℤ)⟩ : IntPoly N) ⟨fun _ => Bk⟩ ⟨fun _ => Bu⟩
      ⟨fun _ => B1⟩ ⟨fun _ => B2⟩) = worstError N Bs Bk Bu B1 B2 := by
  apply le_antisymm
  · exact Validation.FreshNoise.freshError_worst _ _ _ _ _ Bs Bk Bu B1 B2
      (normInf_constPoly_le Bs) (normInf_constPoly_le Bk) (normInf_constPoly_le Bu)
      (normInf_constPoly_le B1) (normInf_constPoly_le B2)
  · have h := abs_coeff_le_normInf (freshError (⟨fun _ => (Bs : ℤ)⟩ : IntPoly N) ⟨fun _ => Bk⟩
      ⟨fun _ => Bu⟩ ⟨fun _ => B1⟩ ⟨fun _ => B2⟩) ⟨N - 1, by omega⟩
    have h3 : (freshError (⟨fun _ => (Bs : ℤ)⟩ : IntPoly N) ⟨fun _ => Bk⟩
        ⟨fun _ => Bu⟩ ⟨fun _ => B1⟩ ⟨fun _ => B2⟩).coeff ⟨N - 1, by omega⟩ =
        ((⟨fun _ => (Bk : ℤ)⟩ : IntPoly N) * ⟨fun _ => Bu⟩).coeff ⟨N - 1, by omega⟩ + B1 +
          ((⟨fun _ => (B2 : ℤ)⟩ : IntPoly N) * ⟨fun _ => Bs⟩).coeff ⟨N - 1, by omega⟩ := rfl
    rw [h3, coeff_constPoly_mul_top hN, coeff_constPoly_mul_top hN] at h
    have h4 : ((worstError N Bs Bk Bu B1 B2 : ℕ) : ℤ) =
        (N : ℤ) * ((Bk : ℤ) * Bu) + B1 + (N : ℤ) * ((B2 : ℤ) * Bs) := by
      unfold worstError; push_cast; ring
    have h5 : (0 : ℤ) ≤ (N : ℤ) * ((Bk : ℤ) * Bu) + B1 + (N : ℤ) * ((B2 : ℤ) * Bs) := by
      rw [← h4]; exact Int.natCast_nonneg _
    rw [abs_of_nonneg h5, ← h4] at h
    exact_mod_cast h

/-! ## 4. The noise headline with fresh encryptions as inputs -/

theorem modulus_dvd_full (Pr : Source.Params) (ℓ : ℕ) :
    Pr.modulus ℓ ∣ Pr.modulus Pr.qs.length := by
  unfold Source.Params.modulus
  rw [List.take_length]
  exact ⟨_, (List.prod_take_mul_prod_drop Pr.qs ℓ).symm⟩

/-- The clauses of `freshOK?`. -/
theorem freshOK?_iff (P : FullParams) (prog : Program) (fresh : List Var) :
    freshOK? P prog fresh = true ↔
      (fresh ≠ [] ∧ (∀ x ∈ fresh, ∃ d ∈ prog.inputs, d.name = x)) ∧
      ∀ d ∈ prog.inputs,
        (d.name ∈ fresh → d.parts = 2 ∧ d.key = 1 ∧ prog.boundOf d.name = none ∧
          2 * P.inputNoise < P.src.modulus d.level) ∧
        (d.name ∉ fresh → d.parts = 1 ∧ ∃ bd, prog.boundOf d.name = some bd ∧ bd ≤ P.inputNoise) := by
  unfold freshOK?
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    List.any_eq_true, beq_iff_eq]
  refine and_congr Iff.rfl (forall_congr' fun d => forall_congr' fun _ => ?_)
  by_cases hx : d.name ∈ fresh
  · simp only [hx, ite_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Option.isNone_iff_eq_none, not_true_eq_false, false_imp_iff, and_true, true_imp_iff]
    tauto
  · simp only [hx, ite_false, Bool.and_eq_true, beq_iff_eq, false_imp_iff, true_and,
      not_false_eq_true, true_imp_iff]
    refine and_congr Iff.rfl ?_
    cases prog.boundOf d.name <;> simp

theorem freshOK?_spec (P : FullParams) (prog : Program) (fresh : List Var)
    (h : freshOK? P prog fresh = true) :
    fresh ≠ [] ∧ ∀ x ∈ fresh, (∃ d ∈ prog.inputs, d.name = x) ∧ prog.boundOf x = none := by
  obtain ⟨⟨hne, hin⟩, hall⟩ := (freshOK?_iff P prog fresh).mp h
  refine ⟨hne, fun x hx => ⟨hin x hx, ?_⟩⟩
  obtain ⟨d, hd, rfl⟩ := hin x hx
  exact ((hall d hd).1 hx).2.2.1

/-- The declared bounds hold of every input: of the fresh ones because they declare none. -/
theorem fresh_boundsOK (P : FullParams) (prog : Program) (fresh : List Var)
    (hfresh : freshOK? P prog fresh = true) (Bp : ℕ) (s b a : IntPoly P.src.N)
    (u e₁ e₂ p : Var → IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N))
    (hin : FreshInputs P prog fresh Bp s b a u e₁ e₂ p m cts) :
    Trace.BoundsOK P s prog (fun x => .exact (m x)) cts := by
  intro x d bd hd hbo
  by_cases hx : x ∈ fresh
  · rw [((freshOK?_spec P prog fresh hfresh).2 x hx).2] at hbo
    exact absurd hbo (by simp)
  · exact hin.2 x d bd hx hd hbo

/-- The inputs of a program whose fresh inputs are good encryptions meet `InputsOK`. -/
theorem fresh_inputsOK (P : FullParams) (prog : Program) (Bp ε : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hnoise : freshNoise P.src.t Bp ε ≤ P.inputNoise)
    (fresh : List Var) (hfresh : freshOK? P prog fresh = true)
    (s e b a : IntPoly P.src.N)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly P.src.N)
    (hgood : ∀ x ∈ fresh, normInf (freshError s e (u x) (e₁ x) (e₂ x)) ≤ ε)
    (p : Var → IntPoly P.src.N)
    (m : Var → Poly P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hfr : ∀ x ∈ fresh, cts x = encrypt P.src.t b a (p x) (u x) (e₁ x) (e₂ x) ∧
      ofInt P.src.t (p x) = m x ∧ normInf (p x) ≤ Bp)
    (hb : Trace.BoundsOK P s prog (fun x => .exact (m x)) cts) :
    InputsOK P s prog (fun x => .exact (m x)) cts := by
  intro x d hd
  have hn : d.name = x := by simpa using List.find?_some hd
  have hmem : d ∈ prog.inputs := List.mem_of_find?_eq_some hd
  have hd' := ((freshOK?_iff P prog fresh).mp hfresh).2 d hmem
  rw [hn] at hd'
  by_cases hx : x ∈ fresh
  · obtain ⟨hparts, hkey, -, hQ⟩ := hd'.1 hx
    have ht : 2 ≤ P.src.t := (hP.plaintext).1
    have hpk' : PublicKeyOK P.src.t (P.src.modulus d.level) s e b a :=
      Validation.Source.ofInt_eq_of_dvd (modulus_dvd_full P.src d.level) hpk
    obtain ⟨hct, hpm, hpB⟩ := hfr x hx
    have henc := Validation.FreshNoise.encrypt_encrypts P.src.t (P.src.modulus d.level) Bp ε ht
      s e b a (p x) (u x) (e₁ x) (e₂ x) hpk' hpB (hgood x hx) (by omega)
    rw [hpm] at henc
    rw [Validation.Source.encrypts_bgv_iff P hk]
    refine ⟨?_, m x, by show Msg.exact (m d.name) = _; rw [hn], ?_⟩
    · rw [hct]; exact hparts.symm
    · show BGVEncrypts P.src.t P.inputNoise (automorph d.key s)
        ((cts x).map (ofInt (P.src.modulus d.level))) (m x)
      rw [hkey, FHE.KeySwitch.automorph_one, hct]
      exact ⟨henc.1, henc.2.trans hnoise⟩
  · obtain ⟨-, bd, hbo, hle⟩ := hd'.2 hx
    exact Validation.Headline.NoiseAux.encrypts_mono hk (hb x d bd hd hbo) hle

theorem fresh_sound (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp ε : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hnoise : freshNoise P.src.t Bp ε ≤ P.inputNoise)
    (fresh : List Var) (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (s e b a : IntPoly P.src.N)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly P.src.N)
    (hgood : ∀ x ∈ fresh, normInf (freshError s e (u x) (e₁ x) (e₂ x)) ≤ ε)
    (p : Var → IntPoly P.src.N)
    (m : Var → Poly P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : FreshInputs P prog fresh Bp s b a u e₁ e₂ p m cts) :
    OutputsExact P E prog B s m cts := by
  have hb := fresh_boundsOK P prog fresh hfresh Bp s b a u e₁ e₂ p m cts hin
  exact Validation.Headline.NoiseAux.refAnalyze_sound P E prog B hP hk h s
    (fun x => .exact (m x)) cts
    (fresh_inputsOK P prog Bp ε hP hk hnoise fresh hfresh s e b a hpk u e₁ e₂ hgood p m cts
      hin.1 hb)
    hb

/-- Union bound over a list (the sets need not be measurable). -/
theorem measureReal_biUnion_list_le {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : ι → Set Ω) (c : ℝ) :
    ∀ l : List ι, (∀ x ∈ l, μ.real (S x) ≤ c) → μ.real (⋃ x ∈ l, S x) ≤ l.length * c
  | [], _ => by simp
  | y :: l, h => by
      have ih := measureReal_biUnion_list_le μ S c l fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hy := h y List.mem_cons_self
      have hU : (⋃ x ∈ y :: l, S x) = S y ∪ ⋃ x ∈ l, S x := by
        ext ω; simp
      rw [hU]
      have := measureReal_union_le (μ := μ) (S y) (⋃ x ∈ l, S x)
      rw [List.length_cons]
      push_cast
      linarith

theorem fresh_certified (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp ε D : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hnoise : freshNoise P.src.t Bp (ε + D) ≤ P.inputNoise)
    (fresh : List Var) (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (Bk Bu B1 B2 mn md : ℕ)
    (hD : (mn : ℝ) / md * (P.src.N * Bk + 1 + P.src.N * P.secretBound : ℕ) ≤ D)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤
      fresh.length * (2 * P.src.N *
        Real.exp (-(ε : ℝ) ^ 2 / (2 * (varProxy P.src.N P.secretBound Bk Bu B1 B2 : ℝ)))) := by
  have hN : 0 < P.src.N := by
    obtain ⟨k, hk'⟩ := hP.N_pow2
    rw [hk']; exact Nat.pos_of_ne_zero (by positivity)
  have hsub : {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ⊆
      ⋃ x ∈ fresh, {ω | (ε : ℝ) +
        (mn : ℝ) / md * (P.src.N * Bk + 1 + P.src.N * P.secretBound : ℕ) ≤
          (normInf (freshError s e (u x ω) (e₁ x ω) (e₂ x ω)) : ℝ)} := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hne
    obtain ⟨p, m, cts, hin, hno⟩ := hω
    refine hno (Validation.FreshNoise.fresh_sound P E prog B Bp (ε + D) hP hk hnoise fresh hfresh h
      s e b a hpk (fun x => u x ω) (fun x => e₁ x ω) (fun x => e₂ x ω) ?_ p m cts hin)
    intro x hx
    have h1 := hne x hx
    have h2 : (normInf (freshError s e (u x ω) (e₁ x ω) (e₂ x ω)) : ℝ) < ((ε + D : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2.le
  refine (measureReal_mono hsub (measure_ne_top μ _)).trans ?_
  refine measureReal_biUnion_list_le μ _ _ fresh fun x hx => ?_
  exact Validation.FreshNoise.freshError_tail μ hN s e P.secretBound Bk Bu B1 B2 mn md hs he
    (u x) (e₁ x) (e₂ x) (hsamp x hx) (ε : ℝ) (Nat.cast_nonneg ε)

theorem fresh_certified_kappa (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp κ : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (Bk Bu B1 B2 mn md : ℕ)
    (hV : 0 < varProxy P.src.N P.secretBound Bk Bu B1 B2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxy P.src.N P.secretBound Bk Bu B1 B2)
        (fresh.length * (2 * P.src.N)) κ +
      meanDrift (P.src.N * Bk + 1 + P.src.N * P.secretBound) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  have h1 := Validation.FreshNoise.fresh_certified P E prog B Bp _ _ hP hk hnoise fresh hfresh h
    Bk Bu B1 B2 mn md (Validation.FreshNoise.meanDrift_spec _ mn md hmd) s e b a hs he hpk
    μ u e₁ e₂ hsamp
  have h2 := Validation.FreshNoise.epsFor_spec (varProxy P.src.N P.secretBound Bk Bu B1 B2)
    (fresh.length * (2 * P.src.N)) κ hV
  push_cast at h2
  refine h1.trans (le_trans (le_of_eq ?_) h2)
  ring

/-! ## 7. The certificates: decryption under the secret key itself -/

open Validation.Headline.NoiseAux in
/-- The key of an output is the same for all messages (as `Validation.Decrypt.outputLevel?_eq`). -/
theorem outputKey?_eq (P : Params) (hk : P.kind = .bgv) (prog : Program)
    (msgs : Var → Msg P.t P.N) (ρ : Env P) (h : eval P prog msgs = some ρ) (o : Var) (v : Val P)
    (ho : ρ o = some v) : outputKey? P prog o = some v.key := by
  simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, guard, Option.pure_def] at h
  obtain ⟨_, h1, _, h2, ρ', h3, _, h4, h5⟩ := h
  have hd : (prog.inputs.all fun dcl => dcl.ok P) = true := by by_contra hc; simp [hc] at h1
  have hf : (prog.inputs.all fun dcl => (msgs dcl.name).fits P.kind) = true := by
    by_contra hc; simp [hc] at h2
  have hout : (prog.outputs.all fun o => (ρ' o).isSome) = true := by by_contra hc; simp [hc] at h4
  cases h5
  have hρ0 : AllExact (initEnv P prog msgs) := by
    intro x w hw
    simp only [initEnv, Option.map_eq_some_iff] at hw
    obtain ⟨d, hd', rfl⟩ := hw
    have hn : d.name = x := by simpa using List.find?_some hd'
    have := List.all_eq_true.mp hf d (List.mem_of_find?_eq_some hd')
    rw [hn, hk] at this
    dsimp only
    cases hmx : msgs x with
    | exact m => exact ⟨m, rfl⟩
  have hz0 : zenv (initEnv P prog msgs) = initEnv P prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  have hfold := Validation.Decrypt.foldlM_zenv hk prog.body _ hρ0
  rw [hz0, h3, Option.map_some] at hfold
  have hev : eval P prog (fun _ => .exact 0) = some (zenv ρ) := by
    have hfz : (prog.inputs.all fun dcl =>
        ((fun _ => .exact 0 : Var → Msg P.t P.N) dcl.name).fits P.kind) = true := by
      rw [List.all_eq_true]; intro dcl _; rw [hk]; rfl
    have hoz : (prog.outputs.all fun o => (zenv ρ o).isSome) = true := by
      simpa [zenv] using hout
    simp only [eval, hd, hfz, hfold, hoz, guard, Option.bind_eq_bind, ite_true,
      Option.pure_def, Option.bind_some]
  simp only [outputKey?, hev, Option.bind_eq_bind, Option.bind_some, zenv, ho, Option.map_some,
    Option.pure_def, zv]

/-- From the noise headline's conclusion and `certOK?` to decryption with `s`. -/
theorem outputsDecrypt_of_encrypts (P : FullParams) (E : Trace.Budget) (prog : Program) (B : ℕ)
    (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hc : certOK? P prog B switched = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N))
    (h : ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct) :
    OutputsDecrypt P E prog switched s msgs cts := by
  obtain ⟨ρ, hev, hrun⟩ := h
  simp only [certOK?, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hkeys, hdec⟩ := hc
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, hv, hct, henc⟩ := hrun σ hσ o ho
  have hkey : v.key = 1 := by
    have h1 := List.all_eq_true.mp hkeys o ho
    rw [outputKey?_eq P.src hk prog msgs ρ hev o v hv] at h1
    simpa using h1
  obtain ⟨m, hm, hdm⟩ := Validation.Trace.encrypts_bgv_decrypts P hk s B v ct henc
  rw [hkey, FHE.KeySwitch.automorph_one] at hdm
  refine ⟨v, ct, m, hv, hct, hm, hkey, hdm, fun hsw => ?_⟩
  have hd : Decrypt.decryptAllOK? P.src prog B = true := by
    rcases hdec with hdec | hdec
    · rw [hsw] at hdec; exact absurd hdec (by simp)
    · exact hdec
  have hlev := Validation.Decrypt.outputLevel?_eq P.src hk prog msgs ρ hev o v hv
  have hdo : Decrypt.decryptOK? P.src v.level B = true := by
    have := List.all_eq_true.mp hd o ho
    rw [hlev] at this
    exact this
  obtain ⟨m', hm', hsd⟩ := Validation.Decrypt.decrypt_switched P hk hP s B v ct henc hdo
  rw [hkey, FHE.KeySwitch.automorph_one] at hsd
  have : m' = m := by rw [hm] at hm'; exact (Msg.exact.inj hm').symm
  rw [this] at hsd
  exact hsd

theorem certified_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program) (B : ℕ)
    (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    OutputsDecrypt P E prog switched s msgs cts :=
  outputsDecrypt_of_encrypts P E prog B switched hP hk hc s msgs cts
    (Validation.Headline.NoiseAux.refAnalyze_sound P E prog B hP hk h s msgs cts hin hb)

theorem fresh_worst_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp : ℕ)
    (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (Bk Bu B1 B2 : ℕ)
    (hnoise : freshNoise P.src.t Bp (worstError P.src.N P.secretBound Bk Bu B1 B2) ≤
      P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly P.src.N)
    (hrand : ∀ x ∈ fresh, normInf (u x) ≤ Bu ∧ normInf (e₁ x) ≤ B1 ∧ normInf (e₂ x) ≤ B2)
    (p : Var → IntPoly P.src.N)
    (m : Var → Poly P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : FreshInputs P prog fresh Bp s b a u e₁ e₂ p m cts) :
    OutputsDecrypt P E prog switched s (fun x => .exact (m x)) cts :=
  outputsDecrypt_of_encrypts P E prog B switched hP hk hc s _ cts
    (Validation.FreshNoise.fresh_sound P E prog B Bp _ hP hk hnoise fresh hfresh h s e b a hpk
      u e₁ e₂
      (fun x hx => Validation.FreshNoise.freshError_worst s e (u x) (e₁ x) (e₂ x) P.secretBound
        Bk Bu B1 B2 hs he (hrand x hx).1 (hrand x hx).2.1 (hrand x hx).2.2)
      p m cts hin)

theorem fresh_kappa_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp κ : ℕ)
    (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (Bk Bu B1 B2 mn md : ℕ)
    (hV : 0 < varProxy P.src.N P.secretBound Bk Bu B1 B2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxy P.src.N P.secretBound Bk Bu B1 B2)
        (fresh.length * (2 * P.src.N)) κ +
      meanDrift (P.src.N * Bk + 1 + P.src.N * P.secretBound) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | DecryptFails P E prog switched fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  have hsub : {ω | DecryptFails P E prog switched fresh Bp s b a u e₁ e₂ ω} ⊆
      {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} := by
    rintro ω ⟨p, m, cts, hin, hno⟩
    exact ⟨p, m, cts, hin, fun hex =>
      hno (outputsDecrypt_of_encrypts P E prog B switched hP hk hc s _ cts hex)⟩
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (Validation.FreshNoise.fresh_certified_kappa P E prog B Bp κ hP hk fresh Bk Bu B1 B2 mn md
      hV hmd hnoise hfresh h s e b a hs he hpk μ u e₁ e₂ hsamp)

end Validation.FreshNoise
