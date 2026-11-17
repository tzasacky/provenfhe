import Challenge.Trace
import Validation.Source

/-!
# Validation.Trace — proofs of the pins of `Challenge.Trace`
-/

namespace Validation.Trace
open Spec NPoly Scheme Source Correct
open Validation.Ring Validation.Scheme Validation.Source

/-! ### Helpers -/

theorem guard_bind_eq_some {p : Prop} [Decidable p] {α : Type} {f : Unit → Option α} {r : α}
    (h : (guard p : Option Unit).bind f = some r) : p ∧ f () = some r := by
  by_cases hp : p
  · simp only [guard, hp, ite_true] at h; exact ⟨hp, h⟩
  · simp [guard, hp] at h

end Validation.Trace

namespace Validation.Trace
open Spec NPoly Scheme Source Correct
open Validation.Ring Validation.Scheme Validation.Source

variable (P : FullParams)

/-- `Encrypts`, for BGV, in terms of `Trace.phaseAt`. -/
theorem encrypts_bgv_iff_phase (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (ct : List (IntPoly P.src.N)) :
    Encrypts P s B v ct ↔
      ct.length = v.parts ∧
      ofInt P.src.t (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)) = m ∧
      normInf (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)) ≤ B := by
  rw [encrypts_bgv_iff P hk]
  constructor
  · rintro ⟨hl, m', hm', h1, h2⟩
    rw [hm] at hm'
    cases hm'
    exact ⟨hl, h1, h2⟩
  · rintro ⟨hl, h1, h2⟩
    exact ⟨hl, m, hm, h1, h2⟩

/-- For BGV, a ciphertext that `Encrypts` a value decrypts to its message exactly, by the
decryption function pinned in `Challenge.Scheme`, under the key the value is recorded under. -/
theorem encrypts_bgv_decrypts (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (ct : List (IntPoly P.src.N)) (h : Encrypts P s B v ct) :
    ∃ m, v.msg = .exact m ∧
      bgvDecrypt P.src.t (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) = m := by
  obtain ⟨-, m, hm, h1, -⟩ := (encrypts_bgv_iff P hk s B v ct).mp h
  exact ⟨m, hm, h1⟩

/-- Componentwise addition meets the `add` contract. -/
theorem stepOK_add_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.add d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) (hparts : x.parts = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (List.zipWith (· + ·) ca cb)) (.add d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey⟩, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [List.length_zipWith, hla, hlb, hparts]
  · refine ⟨x, y, ca, cb, hx, hy, ha, hb, ?_⟩
    dsimp only
    rw [← hkey]
    unfold Trace.phaseAt
    rw [map_ofInt_zipWith, phase_zipWith_add _ _ _ (by simp [hla, hlb, hparts])]

/-- The tensor product of two 2-component ciphertexts meets the `mul` contract. -/
theorem stepOK_mul_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.tensor ca cb)) (.mul d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey, -⟩, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  obtain ⟨c0, c1, rfl⟩ := List.length_eq_two.mp hla
  obtain ⟨d0, d1, rfl⟩ := List.length_eq_two.mp hlb
  have ht : Challenge.Source.tensor [c0, c1] [d0, d1] = [c0 * d0, c0 * d1 + c1 * d0, c1 * d1] := rfl
  rw [ht]
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x, h2y]
  · refine ⟨x, y, _, _, hx, hy, ha, hb, ?_⟩
    dsimp only
    rw [← hkey]
    unfold Trace.phaseAt
    simp only [List.map_cons, List.map_nil, ofInt_mul, ofInt_add, phase_three', phase_two']
    apply eq_of_neZero; intro; ring

/-! ### Modulus switching of any number of components -/

section Parts
variable {N : ℕ}

theorem sum_range_pow_succ (x k : ℕ) :
    ((List.range (k + 1)).map fun i => x ^ i).sum =
      1 + x * ((List.range k).map fun i => x ^ i).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, pow_zero,
    ← List.sum_map_mul_left]
  congr 2
  apply List.map_congr_left
  intro i _
  simp [pow_succ, mul_comm]

/-- The division step for any integer phase: if `I ≡ E (mod Q'·q)` and `q · I' = I + D`
coefficientwise, then `I' ≡ e (mod Q')` for an `e` with `q · e = E + D`. -/
theorem divq_gen (Q' q : ℕ) (I I' E D : IntPoly N)
    (hE : ofInt (Q' * q) I = ofInt (Q' * q) E)
    (h : ∀ i, (q : ℤ) * I'.coeff i = I.coeff i + D.coeff i) :
    ∃ e : IntPoly N, ofInt Q' I' = ofInt Q' e ∧
      ∀ i, (q : ℤ) * e.coeff i = E.coeff i + D.coeff i := by
  have hK : ∀ i, ∃ j : ℤ, I.coeff i = E.coeff i + ((Q' * q : ℕ) : ℤ) * j := by
    intro i
    have := congrArg (fun p => p.coeff i) hE
    simp only [coeff_ofInt] at this
    exact exists_eq_add_mul_of_cast_eq this
  choose K hK using hK
  refine ⟨⟨fun i => I'.coeff i - (Q' : ℤ) * K i⟩, ?_, ?_⟩
  · ext i
    simp only [coeff_ofInt]
    push_cast
    simp
  · intro i
    show (q : ℤ) * (I'.coeff i - (Q' : ℤ) * K i) = _
    rw [mul_sub, h i, hK i]
    push_cast
    ring

/-- Linearity of the integer phase in the components, in the form the switch needs. -/
theorem intPhase_switch (q : ℕ) (sk : IntPoly N) (sw dl : IntPoly N → IntPoly N)
    (hdiv : ∀ c : IntPoly N, ∀ i, (q : ℤ) * (sw c).coeff i = c.coeff i + (dl c).coeff i)
    (ca : List (IntPoly N)) (i : Fin N) :
    (q : ℤ) * (intPhase sk (ca.map sw)).coeff i =
      (intPhase sk ca).coeff i + (intPhase sk (ca.map dl)).coeff i := by
  have : NeZero N := ⟨by have := i.isLt; omega⟩
  have key : (q : IntPoly N) * intPhase sk (ca.map sw) = intPhase sk ca + intPhase sk (ca.map dl) := by
    induction ca with
    | nil => simp only [List.map_nil, intPhase]; ring
    | cons c cs ih =>
      have hc : (q : IntPoly N) * sw c = c + dl c := by
        ext i; rw [coeff_natCast_mul, hdiv, coeff_add']
      simp only [List.map_cons, intPhase]
      linear_combination hc + sk * ih
  have := congrArg (fun p => p.coeff i) key
  simpa only [coeff_natCast_mul, coeff_add'] using this

/-- `‖Σ_{i<k} sⁱ·d_i‖∞ ≤ M · Σ_{i<k} Sⁱ` when `‖d_i‖∞ ≤ M` and `‖s‖₁ ≤ S`. -/
theorem abs_coeff_intPhase_le (sk : IntPoly N) (S : ℕ) (M : ℤ)
    (hS : ∑ j, |sk.coeff j| ≤ (S : ℤ)) (hM : 0 ≤ M) :
    ∀ ds : List (IntPoly N), (∀ d ∈ ds, ∀ j, |d.coeff j| ≤ M) →
      ∀ j, |(intPhase sk ds).coeff j| ≤
        M * (((List.range ds.length).map fun i => S ^ i).sum : ℕ)
  | [], _, j => by simp [intPhase]
  | d :: ds, h, j => by
    have ih := abs_coeff_intPhase_le sk S M hS hM ds (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))
    have h0 := h d (List.mem_cons_self ..) j
    set G : ℕ := ((List.range ds.length).map fun i => S ^ i).sum with hG
    have h1 := abs_coeff_mul_le sk (intPhase sk ds) _ ih j
    have hS0 : (0 : ℤ) ≤ ∑ j, |sk.coeff j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hMG : (0 : ℤ) ≤ M * (G : ℤ) := mul_nonneg hM (by positivity)
    have h2 : (∑ j, |sk.coeff j|) * (M * (G : ℤ)) ≤ (S : ℤ) * (M * (G : ℤ)) :=
      mul_le_mul_of_nonneg_right hS hMG
    simp only [intPhase, List.length_cons]
    rw [coeff_add', sum_range_pow_succ, ← hG]
    push_cast
    calc |d.coeff j + (sk * intPhase sk ds).coeff j|
        ≤ |d.coeff j| + |(sk * intPhase sk ds).coeff j| := abs_add_le _ _
      _ ≤ M + (S : ℤ) * (M * (G : ℤ)) := by linarith
      _ = M * (1 + (S : ℤ) * (G : ℤ)) := by ring

/-- If every component vanishes modulo `t`, so does the phase. -/
theorem ofInt_intPhase_eq_zero (t : ℕ) (sk : IntPoly N) : ∀ ds : List (IntPoly N),
    (∀ d ∈ ds, ofInt t d = 0) → ofInt t (intPhase sk ds) = 0
  | [], _ => by simp [intPhase, ofInt_zero]
  | d :: ds, h => by
    simp only [intPhase]
    rw [ofInt_add, ofInt_mul, h d (List.mem_cons_self ..),
      ofInt_intPhase_eq_zero t sk ds (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]
    apply eq_of_neZero; intro; ring

end Parts

/-- **Textbook modulus switching of a value with any number of components** meets the
`modSwitch` contract within `Spec.Budget.msBudgetAt`. -/
theorem stepOK_modSwitch_textbook_parts (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (E : Trace.Budget) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hE : Spec.Budget.msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)))
      (.modSwitch d a) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨hℓ, h3⟩ := guard_bind_eq_some hstep
  have hlt : x.level - 1 < P.src.qs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h3
    simp at h3
  have hℓL : x.level ≤ P.src.qs.length := by omega
  have hgetD : P.src.qs[x.level - 1]? = some P.src.qs[x.level - 1]! := by simp [hlt]
  rw [hgetD, Option.bind_some] at h3
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  obtain ⟨hqp, hcop⟩ := qLast_facts P hP (x.level - 1) hlt
  have hcop' := hcop
  have hQQ : P.src.modulus x.level = P.src.modulus (x.level - 1) * P.src.qs[x.level - 1]! :=
    modulus_pred _ _ (by omega) hℓL
  refine ⟨x, ca, ?_⟩
  dsimp only
  generalize P.src.qs[x.level - 1]! = q at hgetD hqp hcop' hQQ ⊢
  have hq0 : 0 < q := hqp.pos
  have : NeZero q := ⟨hq0.ne'⟩
  unfold Trace.phaseAt
  rw [hQQ]
  generalize hsk : automorph x.key s = sk
  generalize P.src.modulus (x.level - 1) = Q'
  rw [phase_map_ofInt, phase_map_ofInt]
  set Φ := centered (ofInt (Q' * q) (intPhase sk ca)) with hΦ
  have hE' : ofInt (Q' * q) (intPhase sk ca) = ofInt (Q' * q) Φ := by
    rw [hΦ, ofInt_centered]
  let dl : IntPoly P.src.N → IntPoly P.src.N := fun c =>
    ⟨fun i => (P.src.t : ℤ) * ((((-(c.coeff i) : ℤ) : ZMod q) * (P.src.t : ZMod q)⁻¹).valMinAbs)⟩
  have hdiv : ∀ c : IntPoly P.src.N, ∀ i,
      (q : ℤ) * (Challenge.Source.bgvModSwitchComp P.src.t q c).coeff i = c.coeff i + (dl c).coeff i := by
    intro c i
    show (q : ℤ) * ((c.coeff i + (P.src.t : ℤ) * ((((-(c.coeff i) : ℤ) : ZMod q) * (P.src.t : ZMod q)⁻¹).valMinAbs)) / q) = _
    apply Int.mul_ediv_cancel'
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have := ZMod.coe_mul_inv_eq_one P.src.t hcop'
    linear_combination (-(c.coeff i : ZMod q)) * this
  have hdl : ∀ c : IntPoly P.src.N, ∀ i, |(dl c).coeff i| ≤ (P.src.t : ℤ) * ((q / 2 : ℕ) : ℤ) := by
    intro c i
    show |(P.src.t : ℤ) * _| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ P.src.t)]
    exact mul_le_mul_of_nonneg_left (abs_valMinAbs_le _) (by positivity)
  have hdlt : ∀ c : IntPoly P.src.N, ofInt P.src.t (dl c) = 0 := by
    intro c; ext i; simp [dl]
  obtain ⟨e, he, hqe⟩ := divq_gen Q' q (intPhase sk ca)
    (intPhase sk (ca.map (Challenge.Source.bgvModSwitchComp P.src.t q))) Φ
    (intPhase sk (ca.map dl)) hE'
    (intPhase_switch q sk _ dl hdiv ca)
  have hS : (∑ j, |sk.coeff j|) ≤ ((P.src.N * P.secretBound : ℕ) : ℤ) := by
    rw [← hsk]; push_cast
    exact (sum_abs_automorph_le _ _).trans (sum_abs_le s _ ((normInf_le_iff _ _).mp hs))
  refine ⟨intPhase sk (ca.map dl), q, hx, ha, hgetD, ?_, ?_, ?_, ?_⟩
  · -- the bound
    rw [normInf_le_iff]
    intro i
    have hb := abs_coeff_intPhase_le sk (P.src.N * P.secretBound)
      ((P.src.t : ℤ) * ((q / 2 : ℕ) : ℤ)) hS (by positivity) (ca.map dl)
      (fun d' hd' j => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hd'
        exact hdl c j) i
    rw [List.length_map, hla] at hb
    refine hb.trans ?_
    set G : ℕ := ((List.range x.parts).map fun i => (P.src.N * P.secretBound) ^ i).sum with hG
    have h1 : P.src.t * G ≤ 2 * E.modSwitchAt x.parts := by
      have : (P.src.t * G + 1) / 2 ≤ E.modSwitchAt x.parts := hE
      omega
    have h2 : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
    have h3 : P.src.t * (q / 2) * G ≤ q * E.modSwitchAt x.parts := by
      calc P.src.t * (q / 2) * G = (P.src.t * G) * (q / 2) := by ring
        _ ≤ (2 * E.modSwitchAt x.parts) * (q / 2) := Nat.mul_le_mul_right _ h1
        _ = (2 * (q / 2)) * E.modSwitchAt x.parts := by ring
        _ ≤ q * E.modSwitchAt x.parts := Nat.mul_le_mul_right _ h2
    exact_mod_cast h3
  · -- t ∣ δ
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (fun p => p.coeff j) (ofInt_intPhase_eq_zero P.src.t sk (ca.map dl)
      (fun d' hd' => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hd'
        exact hdlt c))
    simpa using this
  · -- q ∣ Φ + δ
    intro j
    exact ⟨e.coeff j, (hqe j).symm⟩
  · -- the new phase
    rw [he]
    congr 1
    ext j
    show e.coeff j = (Φ.coeff j + (intPhase sk (ca.map dl)).coeff j) / q
    rw [← hqe j, Int.mul_ediv_cancel_left _ (by exact_mod_cast hq0.ne')]

theorem msBudgetAt_two_eq : Spec.Budget.msBudgetAt P 2 =
    (P.src.t * (1 + P.src.N * P.secretBound) + 1) / 2 := by
  simp [Spec.Budget.msBudgetAt, List.range_succ]

/-- Textbook t-corrected modulus switching of a 2-component ciphertext meets the `modSwitch`
contract whenever the budget is at least `⌈t · (1 + N · secretBound) / 2⌉`: the two-component
case of `stepOK_modSwitch_textbook_parts`. -/
theorem stepOK_modSwitch_textbook (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (E : Trace.Budget)
    (hE : (P.src.t * (1 + P.src.N * P.secretBound) + 1) / 2 ≤ E.modSwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (h2 : x.parts = 2) (hla : ca.length = 2) :
    Trace.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)))
      (.modSwitch d a) := by
  refine stepOK_modSwitch_textbook_parts P hk hP E s hs ρ ρ' σ d a x ca ?_ hstep hx ha
    (by rw [hla, h2])
  rw [h2, msBudgetAt_two_eq]
  exact hE

end Validation.Trace
/-! ## Mixed numbers of components, plaintext operands, dropped limbs -/

namespace Validation.Trace
open Spec NPoly Scheme Source Correct
open Validation.Ring Validation.Scheme Validation.Source

variable (P : FullParams)

/-- The phase of a one-component value is its component, under every key. -/
theorem phaseAt_singleton (Q key : ℕ) (s c : IntPoly P.src.N) :
    Trace.phaseAt P Q key s [c] = ofInt Q c := by
  unfold Trace.phaseAt
  rw [List.map_cons, List.map_nil, phase_singleton]

theorem stepOK_add_padded (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.add d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· + ·) ca cb)) (.add d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey⟩, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [length_padZip, hla, hlb]
  · refine ⟨x, y, ca, cb, hx, hy, ha, hb, ?_⟩
    dsimp only
    rw [← hkey]
    unfold Trace.phaseAt
    rw [phase_padZip_add]

theorem stepOK_sub_padded (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.sub d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· - ·) ca cb)) (.sub d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey⟩, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [length_padZip, hla, hlb]
  · refine ⟨x, y, ca, cb, hx, hy, ha, hb, ?_⟩
    dsimp only
    rw [← hkey]
    unfold Trace.phaseAt
    rw [phase_padZip_sub]

theorem stepOK_addPlain_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· + ·) ca [c]))
      (.addPlain d a p) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], hx, hy, ha, hp, ?_⟩
    dsimp only
    rw [phaseAt_singleton]
    unfold Trace.phaseAt
    rw [phase_padZip_add, List.map_cons, List.map_nil, phase_singleton]

theorem stepOK_subPlain_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· - ·) ca [c]))
      (.subPlain d a p) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], hx, hy, ha, hp, ?_⟩
    dsimp only
    rw [phaseAt_singleton]
    unfold Trace.phaseAt
    rw [phase_padZip_sub, List.map_cons, List.map_nil, phase_singleton]

theorem stepOK_mulPlain_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.mulPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c * ·))) (.mulPlain d a p) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, y, ca, [c], hx, hy, ha, hp, ?_⟩
    dsimp only
    rw [phaseAt_singleton]
    unfold Trace.phaseAt
    rw [phase_map_mul]

theorem stepOK_dropLimbs_textbook (E : Trace.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (k : ℕ)
    (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.dropLimbs d a k) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d ca) (.dropLimbs d a k) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := guard_bind_eq_some hstep
  cases h2
  refine ⟨_, _, set_self _ _ _, hla, rfl, ?_⟩
  refine ⟨x, ca, hx, ha, ?_⟩
  dsimp only
  unfold Trace.phaseAt
  exact phase_drop P.src x.level k _ ca

/-! ## Every instruction, every number of components -/

theorem stepOK_mul_tensor (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.tensorParts ca cb)) (.mul d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey, h1x, h1y⟩, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · rw [length_tensorParts _ _ (by omega) (by omega), hla, hlb]
  · refine ⟨x, y, ca, cb, hx, hy, ha, hb, ?_⟩
    dsimp only
    rw [← hkey]
    unfold Trace.phaseAt
    rw [phase_tensorParts]

theorem stepOK_square_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.tensorParts ca ca)) (.square d a) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨h1x, h2⟩ := guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · rw [length_tensorParts _ _ (by omega) (by omega), hla]
    show x.parts + x.parts - 1 = 2 * x.parts - 1
    omega
  · refine ⟨x, ca, hx, ha, ?_⟩
    dsimp only
    unfold Trace.phaseAt
    rw [phase_tensorParts]

theorem stepOK_mulConst_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (c : ℤ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mulConst d a c) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c • ·))) (.mulConst d a c) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hstep
  subst hstep
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, ca, hx, ha, ?_⟩
    dsimp only
    unfold Trace.phaseAt
    rw [phase_map_zsmul]

theorem stepOK_copy_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (i : Instr)
    (hi : i = .copy d a ∨ i = .toEval d a ∨ i = .toCoeff d a) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ i = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d ca) i := by
  rcases hi with rfl | rfl | rfl
  all_goals
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hstep
    subst hstep
    exact ⟨_, _, set_self _ _ _, hla, rfl, x, ca, hx, ha, rfl⟩

theorem stepOK_automorph_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (g : ℕ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.automorph d a g) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (ca.map (automorph g))) (.automorph d a g) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨hg, h2⟩ := guard_bind_eq_some hstep
  cases h2
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, ca, hx, ha, ?_⟩
    dsimp only
    unfold Trace.phaseAt
    have hmap : (ca.map (automorph g)).map (ofInt (P.src.modulus x.level)) =
        (ca.map (ofInt (P.src.modulus x.level))).map (automorph g) := by
      simp only [List.map_map]
      congr 1; funext c; exact ofInt_automorph _ g c
    rw [hmap, automorph_mod, ← automorph_automorph hg, ofInt_automorph, phase_automorph hg]

end Validation.Trace
