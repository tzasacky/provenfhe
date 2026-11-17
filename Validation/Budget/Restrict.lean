import Challenge.BudgetRestrict
import Spec.Certify
import Validation.Budget.Basic
import Validation.Budget.KeySwitch

/-!
# Validation.Budget.Restrict — top-level gadget keys serve every level

Proofs of the pins of `Challenge/BudgetRestrict.lean`.

* Lists: `cutSizes` keeps the starts of the digits and shortens them (`cut_take_sum`,
  `cut_getD_le`), so a cut digit is a prefix of the top-level digit and its modulus divides the
  top-level digit modulus (`digitModulus_dvd_of_cut`).
* Gadget: over the level-`ℓ` digit basis, `Q̂ⱼ·[Q̂ⱼ⁻¹]` is `≡ [k = j]` modulo every digit modulus
  `Q'ₖ` both for the top-level and the level-`ℓ` digits (`hatInv_residue`), so their difference
  is divisible by `∏ₖ Q'ₖ = Q_ℓ` (`basis_restrict`).
* Keys: the level-`ℓ` error is the centred representative modulo `Q_ℓ·P` of the top-level error
  (`keyValid_restrict`), never larger, and equal to it when `2·|e| < Q_ℓ·P`.
-/

namespace Validation.Budget
open Spec NPoly Scheme Source Correct Spec.Budget Challenge.Headline
open Challenge.Budget (restrictBadParams restrictBadLayout restrictBadSecret restrictBadKeys
  restrictSizeParams restrictSizeKeys)

/-! ## Cutting a list of digit sizes

`cutSizes` and `restrictsTo` are the trusted definitions `Spec.Budget.cutSizes`,
`Spec.Budget.restrictsTo`. The unfolding lemmas below are proved by `rfl`, so that no equation
lemma of these definitions is generated here (outside `Spec`). -/

theorem cut_nil (n : ℕ) : cutSizes [] n = [] := rfl

theorem cut_cons (s : ℕ) (ss : List ℕ) (n : ℕ) :
    cutSizes (s :: ss) n = if n = 0 then [] else if n ≤ s then [n] else s :: cutSizes ss (n - s) :=
  rfl

theorem restrictsTo_def (lay : KSLayout) (L ℓ : ℕ) :
    restrictsTo lay L ℓ = (lay.okAt L && lay.sizes ℓ == cutSizes (lay.sizes L) ℓ) := rfl

theorem cut_sum : ∀ (S : List ℕ) (n : ℕ), (cutSizes S n).sum = min S.sum n
  | [], n => by simp [cut_nil, cut_cons]
  | s :: ss, n => by
    simp only [cut_cons]
    split_ifs with h0 h1
    · simp; omega
    · simp; omega
    · have := cut_sum ss (n - s)
      simp only [List.sum_cons, this]; omega

theorem cut_pos : ∀ (S : List ℕ) (n : ℕ), (∀ x ∈ S, 0 < x) → ∀ x ∈ cutSizes S n, 0 < x
  | [], n, _ => by simp [cut_nil, cut_cons]
  | s :: ss, n, h => by
    simp only [cut_cons]
    split_ifs with h0 h1
    · simp
    · simp only [List.mem_singleton]; intro x hx; omega
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h x (by simp)
      · exact cut_pos ss (n - s) (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

theorem cut_length_le : ∀ (S : List ℕ) (n : ℕ), (cutSizes S n).length ≤ S.length
  | [], n => by simp [cut_nil, cut_cons]
  | s :: ss, n => by
    simp only [cut_cons]
    split_ifs with h0 h1
    · simp
    · simp
    · have := cut_length_le ss (n - s)
      simp only [List.length_cons]; omega

/-- A cut digit starts where the top-level digit starts. -/
theorem cut_take_sum : ∀ (S : List ℕ) (n k : ℕ), k < (cutSizes S n).length →
    ((cutSizes S n).take k).sum = (S.take k).sum
  | [], n, k, h => by simp [cut_nil, cut_cons] at h
  | s :: ss, n, k, h => by
    simp only [cut_cons] at h ⊢
    split_ifs at h ⊢ with h0 h1
    · simp at h
    · simp at h; subst h; simp
    · cases k with
      | zero => simp
      | succ k =>
        simp only [List.length_cons] at h
        simp only [List.take_succ_cons, List.sum_cons]
        rw [cut_take_sum ss (n - s) k (by omega)]

/-- A cut digit is no longer than the top-level digit. -/
theorem cut_getD_le : ∀ (S : List ℕ) (n k : ℕ), (cutSizes S n).getD k 0 ≤ S.getD k 0
  | [], n, k => by simp [cut_nil, cut_cons]
  | s :: ss, n, k => by
    simp only [cut_cons]
    split_ifs with h0 h1
    · simp
    · cases k with
      | zero => simpa using h1
      | succ k => simp
    · cases k with
      | zero => simp
      | succ k =>
        simp only [List.getD_cons_succ]
        exact cut_getD_le ss (n - s) k

theorem restrictsTo_iff (lay : KSLayout) (L ℓ : ℕ) :
    restrictsTo lay L ℓ = true ↔ lay.okAt L = true ∧ lay.sizes ℓ = cutSizes (lay.sizes L) ℓ := by
  simp [restrictsTo_def]

theorem restrictsTo_okAt (lay : KSLayout) (L ℓ : ℕ) (hℓ : ℓ ≤ L)
    (h : restrictsTo lay L ℓ = true) : lay.okAt ℓ = true := by
  rw [restrictsTo_iff] at h
  obtain ⟨hL, hcut⟩ := h
  simp only [KSLayout.okAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hL ⊢
  rw [hcut, cut_sum, hL.1]
  exact ⟨by omega, cut_pos _ _ hL.2⟩

/-! ## Uniform digits -/

theorem cut_single (L ℓ : ℕ) (h0 : 0 < ℓ) (h : ℓ ≤ L) : cutSizes [L] ℓ = [ℓ] := by
  have h1 : ℓ ≠ 0 := by omega
  simp only [cut_cons, h1, h, ↓reduceIte]

/-- The sizes of `uniformLayout α` at `n` limbs. -/
def uSizes (α n : ℕ) : List ℕ := List.replicate (n / α) α ++ (if n % α = 0 then [] else [n % α])

theorem uSizes_lt (α n : ℕ) (h : n < α) : uSizes α n = if n = 0 then [] else [n] := by
  unfold uSizes
  rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  simp

theorem uSizes_ge (α n : ℕ) (hα : 0 < α) (h : α ≤ n) : uSizes α n = α :: uSizes α (n - α) := by
  unfold uSizes
  rw [Nat.div_eq_sub_div hα h, ← Nat.mod_eq_sub_mod h, List.replicate_succ, List.cons_append]

theorem cut_uSizes (α : ℕ) (hα : 0 < α) : ∀ (ℓ L : ℕ), ℓ ≤ L →
    cutSizes (uSizes α L) ℓ = uSizes α ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro L hℓ
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · rw [uSizes_lt α 0 hα]
      cases uSizes α L <;> simp [cut_nil, cut_cons]
    by_cases hL : L < α
    · have hL0 : L ≠ 0 := by omega
      have hl0 : ℓ ≠ 0 := by omega
      rw [uSizes_lt α L hL, uSizes_lt α ℓ (by omega)]
      simp only [hL0, hl0, ↓reduceIte]
      exact cut_single L ℓ hpos hℓ
    rw [uSizes_ge α L hα (by omega)]
    have hl0 : ℓ ≠ 0 := by omega
    simp only [cut_cons, hl0, ↓reduceIte]
    by_cases h1 : ℓ ≤ α
    · simp only [h1, ↓reduceIte]
      by_cases h2 : ℓ = α
      · subst h2; rw [uSizes_ge ℓ ℓ hα le_rfl, Nat.sub_self, uSizes_lt ℓ 0 hα]; simp
      · rw [uSizes_lt α ℓ (by omega)]; simp; omega
    · simp only [h1, ↓reduceIte]
      rw [uSizes_ge α ℓ hα (by omega), ih (ℓ - α) (by omega) (L - α) (by omega)]

theorem uniformLayout_restrictsTo (α : ℕ) (c : Bool) (L ℓ : ℕ) (hℓ : ℓ ≤ L) :
    restrictsTo (uniformLayout α c) L ℓ = true := by
  rw [restrictsTo_iff]
  refine ⟨uniformLayout_ok α c L, ?_⟩
  show uSizes α ℓ = cutSizes (uSizes α L) ℓ
  rcases Nat.eq_zero_or_pos α with rfl | hα
  · simp only [uSizes, Nat.div_zero, List.replicate_zero, Nat.mod_zero, List.nil_append]
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
    · cases L <;> simp [cut_nil, cut_cons]
    · have hl0 : ℓ ≠ 0 := by omega
      have hL0 : L ≠ 0 := by omega
      simp only [hl0, hL0, ↓reduceIte]
      exact (cut_single L ℓ hℓ0 hℓ).symm
  · exact (cut_uSizes α hα ℓ L hℓ).symm

/-! ## Digit moduli of a cut layout -/

/-- A cut digit is a prefix of the top-level digit, so its modulus divides the top-level one. -/
theorem digitModulus_dvd_of_cut (P : FullParams) (lay : KSLayout) (L ℓ k : ℕ) (hℓ : ℓ ≤ L)
    (hst : ((lay.sizes ℓ).take k).sum = ((lay.sizes L).take k).sum)
    (hsz : (lay.sizes ℓ).getD k 0 ≤ (lay.sizes L).getD k 0) :
    digitModulus P lay ℓ k ∣ digitModulus P lay L k := by
  unfold digitModulus
  rw [hst]
  set a := ((lay.sizes L).take k).sum
  set b' := (lay.sizes ℓ).getD k 0
  set b := (lay.sizes L).getD k 0
  have e1 : P.src.qs.take ℓ = (P.src.qs.take L).take ℓ := by
    rw [List.take_take, min_eq_left hℓ]
  rw [e1, List.drop_take, List.take_take]
  apply List.Sublist.prod_dvd_prod
  have e2 : ((P.src.qs.take L).drop a).take (min b' (ℓ - a)) =
      (((P.src.qs.take L).drop a).take b).take (min b' (ℓ - a)) := by
    rw [List.take_take, min_eq_left (le_trans (min_le_left _ _) hsz)]
  rw [e2]
  exact (List.take_prefix _ _).sublist

/-! ## The gadget restricts -/

open FHE.RNS in
/-- `Q̂ⱼ · [Q̂ⱼ⁻¹]_{Qⱼ} ≡ [k = j]` modulo every divisor of `Qₖ`. -/
theorem hatInv_residue {n : ℕ} (B : Basis n) (j k : Fin n) (d : ℕ) (hd : d ∣ B.q k) :
    (d : ℤ) ∣ ((B.hat j : ℤ) * ((B.hatInv j).val : ℤ)) - (if (k : ℕ) = j then 1 else 0) := by
  split_ifs with h
  · have hkj : k = j := Fin.ext h
    subst hkj
    have hdiv : ((B.q k : ℕ) : ℤ) ∣ (B.hat k : ℤ) * ((B.hatInv k).val : ℤ) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, B.hat_mul_hatInv, sub_self]
    exact (Int.natCast_dvd_natCast.mpr hd).trans hdiv
  · have hkj : k ≠ j := fun e => h (congrArg Fin.val e)
    rw [sub_zero]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (hd.trans (B.q_dvd_hat hkj))) _

open FHE.RNS in
/-- Digit bases `B` (top level) and `B'` (level `ℓ`) with `B'.q k ∣ B.q k`: the CRT coefficients
of digit `j` agree modulo `∏ B'.q`. -/
theorem basis_restrict {n m : ℕ} (B : Basis n) (B' : Basis m) (hmn : m ≤ n)
    (hdvd : ∀ k : Fin m, B'.q k ∣ B.q ⟨k, by omega⟩) (j : Fin m) :
    (B'.prod : ℤ) ∣ ((B.hat ⟨j, by omega⟩ : ℤ) * ((B.hatInv ⟨j, by omega⟩).val : ℤ)) -
      ((B'.hat j : ℤ) * ((B'.hatInv j).val : ℤ)) := by
  apply B'.prod_dvd_of_forall
  intro k
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 := hatInv_residue B ⟨j, by omega⟩ ⟨k, by omega⟩ (B'.q k) (hdvd k)
  have h2 := hatInv_residue B' j k (B'.q k) dvd_rfl
  have := dvd_sub h1 h2
  simp only at this
  rwa [sub_sub_sub_cancel_right] at this

theorem gadgetFactor_restrict (P : FullParams) (lay : KSLayout) (hP : SchemeParamsOK P)
    (Pm ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (j : ℕ) (hj : j < (lay.sizes ℓ).length) :
    ((P.src.modulus ℓ * Pm : ℕ) : ℤ) ∣
      (gadgetFactor Pm (digitModuli P lay P.src.qs.length) j : ℤ) -
        (gadgetFactor Pm (digitModuli P lay ℓ) j : ℤ) := by
  have hℓok := restrictsTo_okAt lay _ ℓ hℓ hlay
  rw [restrictsTo_iff] at hlay
  obtain ⟨hL, hcut⟩ := hlay
  have hlen : (lay.sizes ℓ).length ≤ (lay.sizes P.src.qs.length).length := by
    rw [hcut]; exact cut_length_le _ _
  set BL := (FHE.KeySwitch.layoutDigits lay P.src.qs.length hL).basis
    (FHE.KeySwitch.schemeLevelBasis P hP P.src.qs.length le_rfl) with hBL
  set Bl := (FHE.KeySwitch.layoutDigits lay ℓ hℓok).basis
    (FHE.KeySwitch.schemeLevelBasis P hP ℓ hℓ) with hBl
  have hqL : ∀ k : Fin (lay.sizes P.src.qs.length).length,
      BL.q k = digitModulus P lay P.src.qs.length k := fun k =>
    FHE.KeySwitch.digitsOfSizes_basis_q P.src.qs _ le_rfl (FHE.KeySwitch.scheme_qs_pos P hP)
      (FHE.KeySwitch.scheme_qs_coprime P hP) _ (FHE.KeySwitch.okAt_sum hL) k
  have hql : ∀ k : Fin (lay.sizes ℓ).length, Bl.q k = digitModulus P lay ℓ k := fun k =>
    FHE.KeySwitch.digitsOfSizes_basis_q P.src.qs _ hℓ (FHE.KeySwitch.scheme_qs_pos P hP)
      (FHE.KeySwitch.scheme_qs_coprime P hP) _ (FHE.KeySwitch.okAt_sum hℓok) k
  have hst : ∀ k : ℕ, k < (lay.sizes ℓ).length →
      ((lay.sizes ℓ).take k).sum = ((lay.sizes P.src.qs.length).take k).sum := by
    intro k hk; rw [hcut] at hk ⊢; exact cut_take_sum _ _ _ hk
  have hsz : ∀ k : ℕ, (lay.sizes ℓ).getD k 0 ≤ (lay.sizes P.src.qs.length).getD k 0 := by
    intro k; rw [hcut]; exact cut_getD_le _ _ _
  have hdvd : ∀ k : Fin (lay.sizes ℓ).length,
      Bl.q k ∣ BL.q ⟨k, Nat.lt_of_lt_of_le k.2 hlen⟩ := by
    intro k
    rw [hql k]
    refine (digitModulus_dvd_of_cut P lay _ ℓ k hℓ ?_ ?_).trans
      (hqL ⟨k, Nat.lt_of_lt_of_le k.2 hlen⟩).symm.dvd
    · exact hst k k.2
    · exact hsz k
  have hres := basis_restrict BL Bl hlen hdvd ⟨j, hj⟩
  have hprod : Bl.prod = P.src.modulus ℓ := by
    rw [hBl, FHE.KeySwitch.Digits.basis_prod, FHE.KeySwitch.schemeLevelBasis_prod]
  rw [hprod] at hres
  rw [FHE.KeySwitch.digitModuli_eq P hP lay _ le_rfl hL,
    FHE.KeySwitch.digitModuli_eq P hP lay ℓ hℓ hℓok]
  have gL := FHE.KeySwitch.gadgetFactor_ofFn BL Pm ⟨j, lt_of_lt_of_le hj hlen⟩
  have gl := FHE.KeySwitch.gadgetFactor_ofFn Bl Pm ⟨j, hj⟩
  simp only at gL gl
  rw [gL, gl]
  push_cast
  have e : (Pm : ℤ) * BL.hat ⟨j, lt_of_lt_of_le hj hlen⟩ *
        ((BL.hatInv ⟨j, lt_of_lt_of_le hj hlen⟩).val : ℤ) -
      (Pm : ℤ) * Bl.hat ⟨j, hj⟩ * ((Bl.hatInv ⟨j, hj⟩).val : ℤ) =
      ((BL.hat ⟨j, lt_of_lt_of_le hj hlen⟩ : ℤ) *
          ((BL.hatInv ⟨j, lt_of_lt_of_le hj hlen⟩).val : ℤ) -
        (Bl.hat ⟨j, hj⟩ : ℤ) * ((Bl.hatInv ⟨j, hj⟩).val : ℤ)) * Pm := by ring
  rw [e]
  exact mul_dvd_mul_right hres _

/-! ## The keys restrict -/

/-- The centred representative modulo `M` of an integer is never larger than the integer. -/
theorem natAbs_valMinAbs_intCast_le (M : ℕ) (z : ℤ) :
    ((z : ZMod M).valMinAbs).natAbs ≤ z.natAbs := by
  rcases M with _ | M
  · rfl
  · exact ZMod.natAbs_min_of_le_div_two (M + 1) _ z (ZMod.coe_valMinAbs _)
      (ZMod.natAbs_valMinAbs_le _)

/-- A multiple of `t` of size at most `B` has size at most `⌊B/t⌋·t`. -/
theorem natAbs_le_div_mul_of_dvd (t B : ℕ) (z : ℤ) (hz : (t : ℤ) ∣ z) (hB : z.natAbs ≤ B) :
    z.natAbs ≤ B / t * t := by
  obtain ⟨k, rfl⟩ := hz
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hB ⊢
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [mul_comm]
    exact Nat.mul_le_mul_right _ ((Nat.le_div_iff_mul_le ht).mpr (by rw [mul_comm]; exact hB))

/-- The coefficient of the error of a key requirement written with integer representatives. -/
theorem keyErr_coeff {N : ℕ} (M g : ℕ) (b a s T : IntPoly N) (i : Fin N) :
    (centered (ofInt M b + ofInt M a * ofInt M s - const ((g : ℕ) : ZMod M) * ofInt M T)).coeff i
      = (((b.coeff i + (a * s).coeff i - g * T.coeff i : ℤ)) : ZMod M).valMinAbs := by
  rw [Validation.Scheme.coeff_centered]
  congr 1
  have hc : const ((g : ℕ) : ZMod M) = ofInt M (const (g : ℤ) : IntPoly N) := by
    rw [Validation.Scheme.ofInt_const]; simp
  rw [hc, ← Validation.Scheme.ofInt_mul, ← Validation.Scheme.ofInt_mul,
    ← Validation.Scheme.ofInt_add, ← Validation.Scheme.ofInt_sub, Validation.Scheme.coeff_ofInt]
  simp [Validation.Scheme.coeff_const_mul]

/-- **One key restricts.** A key valid modulo `M'` for the factor `g'` is valid modulo `M ∣ M'`
for any factor `g ≡ g' (mod M)`, with the same bound; for BGV provided `2·(⌊B/t⌋·t) < M`. -/
theorem keyValid_restrict {N : ℕ} {kind : Kind} {t B : ℕ} {s : IntPoly N} (tgt : KeyTarget)
    {M M' g g' : ℕ} (hM : M ∣ M') (hg : (M : ℤ) ∣ (g' : ℤ) - g)
    (hB : kind = .bgv → 2 * (B / t * t) < M) (b a : IntPoly N)
    (h : KeyValid kind t B s ⟨M', const ((g' : ℕ) : ZMod M'), tgt⟩ (ofInt M' b) (ofInt M' a)) :
    KeyValid kind t B s ⟨M, const ((g : ℕ) : ZMod M), tgt⟩ (ofInt M b) (ofInt M a) := by
  unfold KeyValid at h ⊢
  simp only at h ⊢
  obtain ⟨hn, hd⟩ := h
  set T := tgt.eval s
  -- the top-level error and the level error, coefficientwise
  have hcoef : ∀ i : Fin N,
      (centered (ofInt M b + ofInt M a * ofInt M s - const ((g : ℕ) : ZMod M) * ofInt M T)).coeff i
        = ((((centered (ofInt M' b + ofInt M' a * ofInt M' s -
            const ((g' : ℕ) : ZMod M') * ofInt M' T)).coeff i : ℤ)) : ZMod M).valMinAbs := by
    intro i
    rw [keyErr_coeff, keyErr_coeff]
    congr 1
    set x' : ℤ := b.coeff i + (a * s).coeff i - g' * T.coeff i
    have h1 : ((((x' : ZMod M')).valMinAbs : ℤ) : ZMod M') = (x' : ZMod M') :=
      ZMod.coe_valMinAbs _
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have h2 : (M : ℤ) ∣ x' - ((x' : ZMod M')).valMinAbs :=
      (Int.natCast_dvd_natCast.mpr hM).trans h1
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h3 : (M : ℤ) ∣ (x' - ((x' : ZMod M')).valMinAbs) +
        ((g' : ℤ) - g) * T.coeff i := dvd_add h2 (Dvd.dvd.mul_right hg _)
    have e : (x' - ((x' : ZMod M')).valMinAbs) + ((g' : ℤ) - g) * T.coeff i =
        (b.coeff i + (a * s).coeff i - g * T.coeff i) - ((x' : ZMod M')).valMinAbs := by
      simp only [x']; ring
    rw [e] at h3
    exact dvd_sub_comm.mp h3
  set e := centered (ofInt M' b + ofInt M' a * ofInt M' s - const ((g' : ℕ) : ZMod M') * ofInt M' T)
  refine ⟨?_, ?_⟩
  · rw [Validation.Scheme.normInf_le_iff] at hn ⊢
    intro i
    rw [hcoef i]
    have := natAbs_valMinAbs_intCast_le M (e.coeff i)
    have h2 := hn i
    rw [Int.abs_eq_natAbs] at h2 ⊢
    omega
  · intro hk i
    have hsmall : 2 * |e.coeff i| < M := by
      have h1 := Validation.Scheme.abs_coeff_le_normInf e i
      have h0 : (e.coeff i).natAbs ≤ normInf e := by
        have := h1; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
      have h2 := natAbs_le_div_mul_of_dvd t B (e.coeff i) (hd hk i) (by omega)
      have h3 := hB hk
      rw [Int.abs_eq_natAbs]
      omega
    rw [hcoef i, Validation.Scheme.valMinAbs_intCast_of_small hsmall]
    exact hd hk i

theorem gadgetKeys_restrict (P : FullParams) (lay : KSLayout) (tgt : KeyTarget)
    (hP : SchemeParamsOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (hB : P.src.kind = .bgv →
      2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P lay P.src.qs.length tgt s keys) :
    GadgetKeysOK P lay ℓ tgt s (keys.take (lay.sizes ℓ).length) := by
  obtain ⟨hlenK, hval⟩ := hkeys
  have hcut := ((restrictsTo_iff lay _ ℓ).mp hlay).2
  have hlen : (lay.sizes ℓ).length ≤ (lay.sizes P.src.qs.length).length := by
    rw [hcut]; exact cut_length_le _ _
  have hlt : (keys.take (lay.sizes ℓ).length).length = (lay.sizes ℓ).length := by
    rw [List.length_take]; omega
  refine ⟨hlt, fun j hj => ?_⟩
  have hjK : j < keys.length := by omega
  have hj' : j < (lay.sizes ℓ).length := by omega
  rw [List.getElem_take]
  have hM : P.src.modulus ℓ * specialProd P ∣ P.src.modulus P.src.qs.length * specialProd P := by
    apply Nat.mul_dvd_mul_right
    unfold Source.Params.modulus
    have : P.src.qs.take ℓ = (P.src.qs.take P.src.qs.length).take ℓ := by
      rw [List.take_take, min_eq_left hℓ]
    rw [this]
    exact (List.take_prefix _ _).sublist.prod_dvd_prod
  exact keyValid_restrict tgt hM
    (gadgetFactor_restrict P lay hP (specialProd P) ℓ hℓ hlay j hj') hB _ _ (hval j hjK)

theorem gadgetKeys_restrict_uniform (P : FullParams) (α : ℕ) (c : Bool) (tgt : KeyTarget)
    (hP : SchemeParamsOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hB : P.src.kind = .bgv →
      2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P (uniformLayout α c) P.src.qs.length tgt s keys) :
    GadgetKeysOK P (uniformLayout α c) ℓ tgt s
      (keys.take ((uniformLayout α c).sizes ℓ).length) :=
  gadgetKeys_restrict P (uniformLayout α c) tgt hP ℓ hℓ
    (uniformLayout_restrictsTo α c _ ℓ hℓ) hB s keys hkeys

/-! ## Realizability with one top-level key set -/

theorem relin_realizable_top (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (hB : 2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        GadgetKeysOK P lay P.src.qs.length .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca (keys.take (lay.sizes ℓ).length)))
          (.relin d a) := by
  obtain ⟨f, hf⟩ := relin_realizable P lay hk hP hS ℓ h1 hℓ
    (restrictsTo_okAt lay _ ℓ hℓ hlay)
  exact ⟨f, fun E hE s hs keys hkeys => hf E hE s hs _
    (gadgetKeys_restrict P lay .square hP ℓ hℓ hlay (fun _ => hB) s keys hkeys)⟩

theorem keySwitch_realizable_top (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (hB : 2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        GadgetKeysOK P lay P.src.qs.length (.galois x.key) s keys →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca (keys.take (lay.sizes ℓ).length)))
          (.keySwitch d a) := by
  obtain ⟨f, hf⟩ := keySwitch_realizable P lay hk hP hS ℓ h1 hℓ
    (restrictsTo_okAt lay _ ℓ hℓ hlay)
  exact ⟨f, fun E hE s hs ρ ρ' σ d a x ca hstep hx hca hl hlen keys hkeys =>
    hf E hE s hs ρ ρ' σ d a x ca hstep hx hca hl hlen _
      (gadgetKeys_restrict P lay (.galois x.key) hP ℓ hℓ hlay (fun _ => hB) s keys hkeys)⟩

/-! ## The discrimination pins (kernel evaluation) -/

theorem gadgetKeys_restrict_needs_restrictsTo :
    ¬ (GadgetKeysOK restrictBadParams restrictBadLayout 3 .square restrictBadSecret
          restrictBadKeys →
        GadgetKeysOK restrictBadParams restrictBadLayout 2 .square restrictBadSecret
          (restrictBadKeys.take 2)) := by
  have h : GadgetKeysOK restrictBadParams restrictBadLayout 3 .square restrictBadSecret
        restrictBadKeys ∧
      ¬ GadgetKeysOK restrictBadParams restrictBadLayout 2 .square restrictBadSecret
        (restrictBadKeys.take 2) := by
    unfold GadgetKeysOK KeyValid
    decide +kernel
  exact fun hi => h.2 (hi h.1)

theorem gadgetKeys_restrict_needs_size_bgv :
    ¬ (GadgetKeysOK restrictSizeParams (uniformLayout 1) 2 .square 0 restrictSizeKeys →
        GadgetKeysOK restrictSizeParams (uniformLayout 1) 1 .square 0
          (restrictSizeKeys.take 1)) := by
  have h : GadgetKeysOK restrictSizeParams (uniformLayout 1) 2 .square 0 restrictSizeKeys ∧
      ¬ GadgetKeysOK restrictSizeParams (uniformLayout 1) 1 .square 0
        (restrictSizeKeys.take 1) := by
    unfold GadgetKeysOK KeyValid
    decide +kernel
  exact fun hi => h.2 (hi h.1)

/-! ## The checks of `Spec.Certify` (helper lemmas, not pins)

`Spec.Certify.layoutOK?` and `Spec.Certify.keysRestrict?` decide the two hypotheses of
`gadgetKeys_restrict` at every level of the chain. The unfolding lemmas are proved by `rfl`, so
that no equation lemma of the trusted definitions is generated here. -/

theorem layoutOK?_def (P : FullParams) (lay : KSLayout) :
    Spec.Certify.layoutOK? P lay =
      (List.range P.src.qs.length).all fun i => restrictsTo lay P.src.qs.length (i + 1) := rfl

theorem keysRestrict?_def (P : FullParams) :
    Spec.Certify.keysRestrict? P =
      decide (2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus 1 * specialProd P) := rfl

/-- An accepted layout restricts from the top level to every level of the chain. -/
theorem layoutOK?_restricts (P : FullParams) (lay : KSLayout)
    (h : Spec.Certify.layoutOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    restrictsTo lay P.src.qs.length ℓ = true := by
  rw [layoutOK?_def, List.all_eq_true] at h
  have := h (ℓ - 1) (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h1] at this

/-- Uniform digits are accepted, for every digit size and either choice of representatives. -/
theorem layoutOK?_uniform (P : FullParams) (α : ℕ) (c : Bool) :
    Spec.Certify.layoutOK? P (uniformLayout α c) = true := by
  rw [layoutOK?_def, List.all_eq_true]
  intro i hi
  exact uniformLayout_restrictsTo α c _ (i + 1) (by have := List.mem_range.mp hi; omega)

/-- The modulus of level `1` is at most the modulus of every level `ℓ ≥ 1` (positive primes). -/
theorem modulus_one_le (P : FullParams) (hP : SchemeParamsOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) :
    P.src.modulus 1 ≤ P.src.modulus ℓ := by
  show (P.src.qs.take 1).prod ≤ (P.src.qs.take ℓ).prod
  have hsplit : P.src.qs.take ℓ = P.src.qs.take 1 ++ (P.src.qs.take ℓ).drop 1 := by
    conv_lhs => rw [← List.take_append_drop 1 (P.src.qs.take ℓ)]
    rw [List.take_take, Nat.min_eq_left h1]
  rw [hsplit, List.prod_append]
  apply Nat.le_mul_of_pos_right
  apply List.prod_pos
  intro q hq
  exact (hP.prime q (List.mem_of_mem_take (List.mem_of_mem_drop hq))).pos

/-- The size condition checked at the smallest modulus holds at every level of the chain. -/
theorem keysRestrict?_level (P : FullParams) (h : Spec.Certify.keysRestrict? P = true)
    (hP : SchemeParamsOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (_hℓ : ℓ ≤ P.src.qs.length) :
    2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P := by
  rw [keysRestrict?_def, decide_eq_true_eq] at h
  exact lt_of_lt_of_le h (Nat.mul_le_mul_right _ (modulus_one_le P hP ℓ h1))

end Validation.Budget
