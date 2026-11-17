import Challenge.Budget
import FHE.KeySwitch.Gadget
import Validation.Trace
import Validation.Switch

/-!
# Validation.Budget.Basic — side conditions, the gadget identity, budget comparisons, modulus switching

Proofs of the pins of `Challenge/Budget.lean` that do not need the key-switching algorithm.
-/

namespace Validation.Budget
open Spec NPoly Scheme Source Correct Spec.Budget Challenge.Headline

/-! ## General helpers -/

theorem pairwiseCoprime?_sound : ∀ (ps : List ℕ), pairwiseCoprime? ps = true →
    ps.Pairwise Nat.Coprime
  | [], _ => List.Pairwise.nil
  | p :: ps, h => by
    simp only [pairwiseCoprime?, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    exact List.Pairwise.cons (fun q hq => h.1 q hq) (pairwiseCoprime?_sound ps h.2)

/-- Cutting a list into consecutive chunks of sizes `ss`: the product of the chunk products is
the product of the first `ss.sum` elements. -/
theorem prod_chunks (ss : List ℕ) : ∀ (l : List ℕ),
    ((List.range ss.length).map fun j =>
      ((l.drop (ss.take j).sum).take (ss.getD j 0)).prod).prod = (l.take ss.sum).prod := by
  induction ss with
  | nil => intro l; simp
  | cons s ss ih =>
    intro l
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    have := ih (l.drop s)
    simp only [List.drop_drop] at this
    simp only [List.take_zero, List.sum_nil, List.drop_zero, List.getD_cons_zero, List.sum_cons,
      Function.comp_def, List.take_succ_cons, List.getD_cons_succ]
    rw [this, List.take_add, List.prod_append]

theorem sum_take_succ_le (ss : List ℕ) (j : ℕ) :
    (ss.take j).sum + ss.getD j 0 ≤ ss.sum := by
  induction ss generalizing j with
  | nil => simp
  | cons s ss ih =>
    cases j with
    | zero => simp
    | succ j =>
      have := ih j
      simp only [List.take_succ_cons, List.sum_cons, List.getD_cons_succ]
      omega

theorem two_le_prod_of_ne_nil : ∀ (l : List ℕ), l ≠ [] → (∀ q ∈ l, 2 ≤ q) → 2 ≤ l.prod
  | [], h, _ => absurd rfl h
  | q :: l, _, h => by
    rw [List.prod_cons]
    have h1 : 2 ≤ q := h q (by simp)
    have h2 : 0 < l.prod := List.prod_pos (fun x hx => by
      have := h x (List.mem_cons_of_mem _ hx); omega)
    calc 2 ≤ q * 1 := by omega
      _ ≤ q * l.prod := Nat.mul_le_mul_left _ h2

theorem sum_zipWith_le (f g : ℕ → ℕ → ℕ) : ∀ (l₁ l₂ : List ℕ),
    (∀ a, ∀ b ∈ l₂, f a b ≤ g a b) →
    (List.zipWith f l₁ l₂).sum ≤ (List.zipWith g l₁ l₂).sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [List.zipWith_cons_cons, List.sum_cons]
    exact Nat.add_le_add (h a b (by simp))
      (sum_zipWith_le f g l₁ l₂ fun a b hb => h a b (List.mem_cons_of_mem _ hb))

theorem le_foldl_max : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem mul_le_two_mul_pred (n Q : ℕ) (hQ : 2 ≤ Q) : n * Q ≤ 2 * (n * (Q - 1)) := by
  have : Q ≤ 2 * (Q - 1) := by omega
  calc n * Q ≤ n * (2 * (Q - 1)) := Nat.mul_le_mul_left _ this
    _ = 2 * (n * (Q - 1)) := by ring

/-- For a usable layout every digit modulus is a product of at least one prime. -/
theorem two_le_digitModulus (P : FullParams) (hP : SchemeParamsOK P) (lay : KSLayout) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) (j : ℕ)
    (hj : j < (lay.sizes ℓ).length) : 2 ≤ digitModulus P lay ℓ j := by
  simp only [KSLayout.okAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hlay
  obtain ⟨hsum, hposs⟩ := hlay
  have hle := sum_take_succ_le (lay.sizes ℓ) j
  have hpos : 0 < (lay.sizes ℓ).getD j 0 := by
    have : (lay.sizes ℓ).getD j 0 = (lay.sizes ℓ)[j] := by simp [hj]
    rw [this]; exact hposs _ (List.getElem_mem _)
  unfold digitModulus
  apply two_le_prod_of_ne_nil
  · intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_drop, List.length_nil] at this
    omega
  · intro q hq
    exact (hP.prime q (List.mem_of_mem_take (List.mem_of_mem_drop
      (List.mem_of_mem_take hq)))).two_le

/-- `Qⱼ · Q̂ⱼ = Q`. -/
theorem getElem_mul_prod_eraseIdx (Qs : List ℕ) (j : ℕ) (h : j < Qs.length) :
    Qs[j] * (Qs.eraseIdx j).prod = Qs.prod := by
  induction Qs generalizing j with
  | nil => simp at h
  | cons q Qs ih =>
    cases j with
    | zero => simp
    | succ j =>
      have := ih j (by simpa using h)
      simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.prod_cons]
      rw [← this]; ring

/-! ## Side conditions -/

theorem specialOK?_sound (P : FullParams) (h : specialOK? P = true) : SpecialOK P := by
  simp only [specialOK?, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, pairwiseCoprime?_sound _ h2, h3, h4⟩

/-- Uniform digits are a usable layout at every level. -/
theorem uniformLayout_ok (α : ℕ) (c : Bool) (ℓ : ℕ) : (uniformLayout α c).okAt ℓ = true := by
  simp only [KSLayout.okAt, uniformLayout, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq, List.sum_append, List.sum_replicate, smul_eq_mul, List.mem_append,
    List.mem_replicate]
  constructor
  · have := Nat.div_add_mod' ℓ α
    split_ifs with h <;> simp <;> omega
  · rintro x (⟨h0, rfl⟩ | hx)
    · rcases Nat.eq_zero_or_pos x with rfl | h
      · simp at h0
      · exact h
    · split_ifs at hx with h
      · simp at hx
      · simp only [List.mem_singleton] at hx; omega

/-- A usable layout has as many digit moduli as digits, and their product is the modulus of the
level. -/
theorem digitModuli_prod (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (hlay : lay.okAt ℓ = true) :
    (digitModuli P lay ℓ).length = (lay.sizes ℓ).length ∧
      (digitModuli P lay ℓ).prod = P.src.modulus ℓ := by
  simp only [KSLayout.okAt, Bool.and_eq_true, beq_iff_eq] at hlay
  refine ⟨by simp [digitModuli], ?_⟩
  have := prod_chunks (lay.sizes ℓ) (P.src.qs.take ℓ)
  rw [hlay.1, List.take_take, Nat.min_self] at this
  exact this

/-! ## The gadget -/

/-- **Reconstruction identity.** -/
theorem gadgetFactor_reconstruct (Pm : ℕ) (Qs : List ℕ) (hpos : ∀ q ∈ Qs, 0 < q)
    (hcop : Qs.Pairwise Nat.Coprime) (X : ℤ) (D : ℕ → ℤ)
    (hD : ∀ j (h : j < Qs.length), (Qs[j] : ℤ) ∣ D j - X) :
    ((Qs.prod * Pm : ℕ) : ℤ) ∣
      (∑ j ∈ Finset.range Qs.length, D j * (gadgetFactor Pm Qs j : ℤ)) - Pm * X := by
  set B := FHE.RNS.Basis.ofList Qs hpos hcop with hB
  have hq : ∀ i : Fin Qs.length, B.q i = Qs[i] := fun _ => rfl
  have hhat : ∀ i : Fin Qs.length, B.hat i = (Qs.eraseIdx i).prod := by
    intro i
    have h1 := B.q_mul_hat i
    rw [FHE.RNS.Basis.ofList_prod, ← getElem_mul_prod_eraseIdx Qs i i.2] at h1
    exact Nat.eq_of_mul_eq_mul_left (B.pos i) h1
  have h := B.prod_dvd_sum_sub (fun j => (X : ZMod (B.q j))) X (fun _ => rfl)
    (fun j => D j * ((B.hatInv j).val : ℤ)) (fun j => by
      push_cast
      rw [ZMod.natCast_zmod_val]
      congr 1
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by
        have := hD j j.2
        rw [← dvd_neg, neg_sub] at this; exact this))
  rw [FHE.RNS.Basis.ofList_prod] at h
  have key : (∑ j ∈ Finset.range Qs.length, D j * (gadgetFactor Pm Qs j : ℤ)) - Pm * X =
      (Pm : ℤ) * ((∑ j : Fin Qs.length, D j * ((B.hatInv j).val : ℤ) * B.hat j) - X) := by
    rw [mul_sub, Finset.mul_sum, Finset.sum_range]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hg : gadgetFactor Pm Qs j = Pm * B.hat j * (B.hatInv j).val := by
      simp only [gadgetFactor, FHE.RNS.Basis.hatInv, hhat j]
      have : Qs.getD j 1 = Qs[j] := by simp
      rw [this]
      rfl
    rw [hg]; push_cast; ring
  rw [key, Nat.cast_mul, mul_comm (Qs.prod : ℤ)]
  exact mul_dvd_mul_left _ h

/-! ## Budget comparisons -/

/-- `ksBudget` is at least `ksBoundAt` at every level of the chain. -/
theorem ksBoundAt_le_ksBudget (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) : ksBoundAt P lay ℓ ≤ ksBudget P lay := by
  unfold ksBudget
  apply (le_foldl_max _ 0).2
  refine List.mem_map.mpr ⟨ℓ - 1, List.mem_range.mpr (by omega), ?_⟩
  have : ℓ - 1 + 1 = ℓ := by omega
  rw [this]

/-- The canonical-representative bound is never below the centred one (same digits). -/
theorem ksBoundAt_le_canonical (P : FullParams) (hS : SpecialOK P) (hP : SchemeParamsOK P)
    (sizes : ℕ → List ℕ) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : (KSLayout.mk sizes false).okAt ℓ = true) :
    ksBoundAt P ⟨sizes, false⟩ ℓ ≤ ksBoundAt P ⟨sizes, true⟩ ℓ := by
  have hdm : digitModuli P ⟨sizes, true⟩ ℓ = digitModuli P ⟨sizes, false⟩ ℓ := rfl
  simp only [ksBoundAt, hdm, Bool.false_eq_true, ite_false, ite_true]
  apply Nat.div_le_div_right
  apply Nat.add_le_add
  · apply Nat.mul_le_mul_left
    apply sum_zipWith_le
    intro n Q hQ
    apply mul_le_two_mul_pred
    simp only [digitModuli, List.mem_map, List.mem_range] at hQ
    obtain ⟨j, hj, rfl⟩ := hQ
    exact two_le_digitModulus P hP _ ℓ hℓ hlay j hj
  · apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_left
    rcases Nat.eq_zero_or_pos P.store.special.length with h0 | hpos
    · rw [h0]; simp
    · apply mul_le_two_mul_pred
      unfold specialProd
      apply two_le_prod_of_ne_nil _ _ (fun p hp => (hS.1 p hp).1)
      intro h
      have := congrArg List.length h
      simp only [List.length_map, List.length_nil] at this
      omega

/-! ## Modulus switching -/

theorem msBudgetAt_one (P : FullParams) : msBudgetAt P 1 = msBudgetOne P := by
  simp [msBudgetAt, msBudgetOne]

theorem msBudgetAt_two (P : FullParams) : msBudgetAt P 2 = msBudget P := by
  simp [msBudgetAt, msBudget, List.range_succ]

theorem certified_modSwitchAt (P : FullParams) (lay : KSLayout) (k : ℕ) :
    (certified P lay).modSwitchAt k = msBudgetAt P k := by
  unfold Trace.Budget.modSwitchAt certified
  split_ifs with h1 h2
  · rw [h1, msBudgetAt_one]
  · rw [h2, msBudgetAt_two]
  · rfl

/-- **Modulus switching of any number of components within `msBudgetAt`.** -/
theorem modSwitch_realizable_parts (P : FullParams) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (ℓ k : ℕ) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), msBudgetAt P k ≤ E.modSwitchAt k →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = k → ca.length = k →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := by
  refine ⟨fun ca => ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[ℓ - 1]!), ?_⟩
  intro E hE s hs ρ ρ' σ d a x ca hstep hx ha hl hp hla
  subst hl
  subst hp
  exact Validation.Trace.stepOK_modSwitch_textbook_parts P hk hP E s hs ρ ρ' σ d a x ca hE hstep
    hx ha hla

/-- **Modulus switching within `msBudget`** (two-component ciphertexts). -/
theorem modSwitch_realizable (P : FullParams) (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (ℓ : ℕ) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), msBudget P ≤ E.modSwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = 2 → ca.length = 2 →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := by
  obtain ⟨f, hf⟩ := modSwitch_realizable_parts P hk hP ℓ 2
  refine ⟨f, fun E hE => hf E ?_⟩
  rw [msBudgetAt_two]
  exact hE

/-- **Modulus switching of a one-component value within `msBudgetOne`.** -/
theorem modSwitch_realizable_one (P : FullParams) (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (ℓ : ℕ) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), msBudgetOne P ≤ E.modSwitchOne →
      ∀ (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = 1 → ca.length = 1 →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := by
  refine ⟨fun ca => ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[ℓ - 1]!), ?_⟩
  intro E hE s ρ ρ' σ d a x ca hstep hx ha hl h1 hla
  subst hl
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨hℓ1, h3⟩ := Validation.Trace.guard_bind_eq_some hstep
  have hlt : x.level - 1 < P.src.qs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h3
    simp at h3
  have hℓ : x.level ≤ P.src.qs.length := by omega
  have hgetD : P.src.qs[x.level - 1]? = some P.src.qs[x.level - 1]! := by simp [hlt]
  rw [hgetD, Option.bind_some] at h3
  cases h3
  refine ⟨_, _, Validation.Source.set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla, h1]
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hla
  obtain ⟨hqp, hcop⟩ := Validation.Source.qLast_facts P hP (x.level - 1) hlt
  have hcop' := hcop
  have hQQ : P.src.modulus x.level = P.src.modulus (x.level - 1) * P.src.qs[x.level - 1]! :=
    Validation.Source.modulus_pred _ _ (by omega) hℓ
  refine ⟨x, [c0], ?_⟩
  dsimp only
  rw [show E.modSwitchAt x.parts = E.modSwitchOne from by simp [Trace.Budget.modSwitchAt, h1]]
  generalize P.src.qs[x.level - 1]! = q at hgetD hqp hcop' hQQ ⊢
  have hq0 : 0 < q := hqp.pos
  have : NeZero q := ⟨hq0.ne'⟩
  rw [show [c0].map (Challenge.Source.bgvModSwitchComp P.src.t q) =
    [Challenge.Source.bgvModSwitchComp P.src.t q c0] from rfl,
    Validation.Trace.phaseAt_singleton, Validation.Trace.phaseAt_singleton, hQQ]
  generalize P.src.modulus (x.level - 1) = Q'
  set Φ := centered (ofInt (Q' * q) c0) with hΦ
  refine ⟨⟨fun j => Validation.Switch.corr P.src.t q (Φ.coeff j)⟩, q, hx, ha, hgetD, ?_, ?_, ?_, ?_⟩
  · rw [Validation.Scheme.normInf_le_iff]
    intro j
    refine (Validation.Switch.abs_corr_le P.src.t q _).trans ?_
    have hb : P.src.t * (q / 2) ≤ q * E.modSwitchOne := by
      have h2 : P.src.t ≤ 2 * E.modSwitchOne := by unfold msBudgetOne at hE; omega
      have h3 : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
      calc P.src.t * (q / 2) ≤ (2 * E.modSwitchOne) * (q / 2) := Nat.mul_le_mul_right _ h2
        _ = (2 * (q / 2)) * E.modSwitchOne := by ring
        _ ≤ q * E.modSwitchOne := Nat.mul_le_mul_right _ h3
    exact_mod_cast hb
  · intro j; exact ⟨_, rfl⟩
  · intro j
    exact ⟨_, (Validation.Switch.q_mul_sw hcop' (Φ.coeff j)).symm⟩
  · ext j
    show ((Validation.Switch.sw P.src.t q (c0.coeff j) : ℤ) : ZMod Q') =
      ((Validation.Switch.sw P.src.t q (Φ.coeff j) : ℤ) : ZMod Q')
    apply Validation.Switch.sw_congr hq0 hcop'
    have := congrArg (fun p => p.coeff j) (Validation.Scheme.ofInt_centered (ofInt (Q' * q) c0))
    rw [mul_comm q Q']
    exact this.symm

end Validation.Budget
