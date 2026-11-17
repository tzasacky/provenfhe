import Validation.BFVDecrypt.CRT

/-!
# Validation.BFVDecrypt.Int — the 64-bit integer accumulation does not wrap
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV FHE.Float Challenge.BFVDecrypt

theorem sum_map_flatMap' {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem foldl_addFast {β : Type} (g : β → ℕ) :
    ∀ (L : List β) (s : ℕ), s + (L.map g).sum < 2 ^ 64 →
      L.foldl (fun s w => addFast s (g w)) s = s + (L.map g).sum
  | [], s, _ => by simp
  | w :: L, s, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have e : addFast s (g w) = s + g w := Nat.mod_eq_of_lt (by omega)
    rw [e, foldl_addFast g L (s + g w) (by omega)]
    ring

/-- The machine product of a datum. -/
def mprod (t : ℕ) (qs : List ℕ) (d : D) : ℕ :=
  if pathReduce t qs then modMulConst d.1 d.2.1 t else mulFast d.1 d.2.1

/-- The exact product of a datum (reduced mod `t` on the reduced paths). -/
def eprod (t : ℕ) (qs : List ℕ) (d : D) : ℕ :=
  if pathReduce t qs then d.1 * d.2.1 % t else d.1 * d.2.1

theorem intSum_eq_fold (A : Arith) (t : ℕ) (qs xs : List ℕ) :
    intSum t qs (allWords qs (tables A t qs) xs) =
      (spec t qs xs).foldl (fun s d => addFast s (mprod t qs d)) 0 := by
  rw [allWords_eq, intSum, List.foldl_map]
  rfl

theorem spec_int_lt {t : ℕ} {qs xs : List ℕ} (ht : 0 < t) : ∀ d ∈ spec t qs xs, d.2.1 < t := by
  intro d hd
  unfold spec at hd
  obtain ⟨p, _, hdp⟩ := List.mem_flatMap.mp hd
  unfold wspec at hdp
  split at hdp <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
  · rcases hdp with rfl | rfl <;> exact Nat.mod_lt _ ht
  · subst hdp; exact Nat.mod_lt _ ht

theorem sum_le_len_mul {β : Type} (L : List β) (g : β → ℕ) (c : ℕ) (h : ∀ b ∈ L, g b ≤ c) :
    (L.map g).sum ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a List.mem_cons_self
    have := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    nlinarith

theorem sum_prod_le_gen (t : ℕ) : ∀ (L : List D), (∀ d ∈ L, d.1 < cap d ∧ d.2.1 < t) →
    (L.map fun d => d.1 * d.2.1).sum ≤ (L.map cap).sum * (t - 1)
  | [], _ => by simp
  | d :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    have ih := sum_prod_le_gen t L fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨h1, h2⟩ := h d List.mem_cons_self
    have : d.1 * d.2.1 ≤ cap d * (t - 1) := Nat.mul_le_mul h1.le (by omega)
    nlinarith

/-- The words, against their caps and the plaintext modulus. -/
theorem sum_prod_le {t : ℕ} {qs xs : List ℕ} (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) :
    ((spec t qs xs).map fun d => d.1 * d.2.1).sum ≤ (caps qs).sum * (t - 1) := by
  have ht : 0 < t := by have := (params hp).1; omega
  rw [← caps_eq t qs xs hx.length_eq]
  exact sum_prod_le_gen t _ fun d hd => ⟨(spec_dok hp hx d hd).1, spec_int_lt ht d hd⟩

theorem len_lt_sizeQMSB (qs : List ℕ) : qs.length < 2 ^ sizeQMSB qs := Nat.lt_size_self _

theorem t_lt_msb (t : ℕ) : t < 2 ^ msb t := Nat.lt_size_self _

theorem caps_sum_nonsplit {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true)
    (hs : pathSplit qs = false) : (caps qs).sum < 2 ^ (sizeQMSB qs + qMSB qs) := by
  obtain ⟨hq, _, _⟩ := qMSB_facts hp
  have hk := len_lt_sizeQMSB qs
  have hc : caps qs = qs := by
    unfold caps wordCaps; simp [hs]
  rw [hc, pow_add]
  have := sum_le_len_mul qs id (2 ^ qMSB qs - 1) (fun q h => by
    have := hq q h; simp only [id]; omega)
  rw [List.map_id] at this
  have h1 : qs.length * (2 ^ qMSB qs - 1) < 2 ^ sizeQMSB qs * 2 ^ qMSB qs := by
    have : 0 < 2 ^ qMSB qs := by positivity
    calc qs.length * (2 ^ qMSB qs - 1) < qs.length * 2 ^ qMSB qs + 1 := by
          have := Nat.mul_le_mul_left qs.length (show 2 ^ qMSB qs - 1 ≤ 2 ^ qMSB qs by omega)
          omega
      _ ≤ 2 ^ sizeQMSB qs * 2 ^ qMSB qs := by
          have := Nat.mul_le_mul_right (2 ^ qMSB qs) (show qs.length + 1 ≤ 2 ^ sizeQMSB qs by omega)
          nlinarith
  omega

theorem caps_sum_split {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true)
    (hs : pathSplit qs = true) : (caps qs).sum < 3 * 2 ^ (sizeQMSB qs + qMSBHf qs) := by
  obtain ⟨hq, _, _⟩ := qMSB_facts hp
  have hk := len_lt_sizeQMSB qs
  set h := qMSBHf qs
  have hqh : qMSB qs ≤ 2 * h + 1 := by simp only [h, qMSBHf]; omega
  have hlimb : ∀ q ∈ qs, (wordCaps qs q).sum ≤ 3 * 2 ^ h := by
    intro q hqm
    have hql := hq q hqm
    have e : wordCaps qs q = [min (2 ^ h) q, (q - 1) / 2 ^ h + 1] := by
      unfold wordCaps; simp [hs, h]
    rw [e]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    have h1 : min (2 ^ h) q ≤ 2 ^ h := min_le_left _ _
    have h2 : (q - 1) / 2 ^ h < 2 ^ (h + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      have : 2 ^ qMSB qs ≤ 2 ^ (h + 1 + h) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
    omega
  unfold caps
  rw [sum_map_flatMap' qs (wordCaps qs)]
  have := sum_le_len_mul qs (fun q => (wordCaps qs q).sum) (3 * 2 ^ h) hlimb
  rw [pow_add]
  have h3 : 0 < 2 ^ h := by positivity
  nlinarith

/-- On the unreduced paths, `Σ caps · (t − 1) < 2⁶³`: the thresholds of the inner tests. -/
theorem unreduced_bound {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true)
    (hr : pathReduce t qs = false) : (caps qs).sum * (t - 1) < 2 ^ 63 := by
  have ht := t_lt_msb t
  have ht1 : t - 1 < 2 ^ msb t := by omega
  unfold pathReduce at hr
  cases hs : pathSplit qs
  · have hc := caps_sum_nonsplit hp hs
    have hthr : sizeQMSB qs + qMSB qs + msb t ≤ 62 := by
      split at hr <;> simp [hs] at hr <;> omega
    calc (caps qs).sum * (t - 1) ≤ (caps qs).sum * 2 ^ msb t := Nat.mul_le_mul_left _ ht1.le
      _ < 2 ^ (sizeQMSB qs + qMSB qs) * 2 ^ msb t :=
          Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = 2 ^ (sizeQMSB qs + qMSB qs + msb t) := by rw [← pow_add]
      _ ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hthr
      _ < 2 ^ 63 := by norm_num
  · have hc := caps_sum_split hp hs
    have hthr : sizeQMSB qs + qMSBHf qs + msb t ≤ 61 := by
      split at hr <;> simp [hs] at hr <;> omega
    calc (caps qs).sum * (t - 1) ≤ (caps qs).sum * 2 ^ msb t := Nat.mul_le_mul_left _ ht1.le
      _ < 3 * 2 ^ (sizeQMSB qs + qMSBHf qs) * 2 ^ msb t :=
          Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = 3 * 2 ^ (sizeQMSB qs + qMSBHf qs + msb t) := by rw [pow_add]; ring
      _ ≤ 3 * 2 ^ 61 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hthr)
      _ < 2 ^ 63 := by norm_num

theorem eprod_sum_lt {t : ℕ} {qs xs : List ℕ} (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) : ((spec t qs xs).map (eprod t qs)).sum < 2 ^ 63 := by
  obtain ⟨ht2, ht50, _, hk, _, _⟩ := params hp
  cases hr : pathReduce t qs
  · have := sum_prod_le hp hx
    have := unreduced_bound hp hr
    have e : (spec t qs xs).map (eprod t qs) = (spec t qs xs).map fun d => d.1 * d.2.1 := by
      apply List.map_congr_left; intro d _; simp [eprod, hr]
    rw [e]; omega
  · have h1 := sum_le_len_mul (spec t qs xs) (eprod t qs) (t - 1) (fun d _ => by
      simp only [eprod, hr, if_true]; have := Nat.mod_lt (d.1 * d.2.1) (show 0 < t by omega); omega)
    have h2 := spec_length (t := t) hx.length_eq
    have h3 : (spec t qs xs).length * (t - 1) ≤ 256 * 2 ^ 50 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

theorem mprod_eq {t : ℕ} {qs xs : List ℕ} (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) : ∀ d ∈ spec t qs xs, mprod t qs d = eprod t qs d := by
  intro d hd
  unfold mprod eprod modMulConst mulFast
  split
  · rfl
  · rename_i hr
    simp only [Bool.not_eq_true] at hr
    apply Nat.mod_eq_of_lt
    have := sum_prod_le hp hx
    have := unreduced_bound hp hr
    have hle : d.1 * d.2.1 ≤ ((spec t qs xs).map fun d => d.1 * d.2.1).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hd)
    omega

/-- `intSum` is the exact sum of the (reduced) products, below `2⁶³`. -/
theorem intSum_value (A : Arith) {t : ℕ} {qs xs : List ℕ} (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) :
    intSum t qs (allWords qs (tables A t qs) xs) = ((spec t qs xs).map (eprod t qs)).sum := by
  rw [intSum_eq_fold]
  have hlt := eprod_sum_lt hp hx
  have e : (spec t qs xs).map (mprod t qs) = (spec t qs xs).map (eprod t qs) :=
    List.map_congr_left (mprod_eq hp hx)
  rw [foldl_addFast (mprod t qs) _ 0 (by rw [e]; omega), e, zero_add]

/-- `Challenge.BFVDecrypt.intSum_no_wrap`. -/
theorem intSum_no_wrap (t : ℕ) (qs xs : List ℕ) (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) : NoWrap t qs xs := by
  unfold NoWrap
  dsimp only
  have hv := intSum_value Spec.Float.exact hp hx
  have hlt := eprod_sum_lt hp hx
  rw [allWords_eq] at hv ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro hr w hw
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
    have := sum_prod_le hp hx
    have := unreduced_bound hp hr
    have hle : d.1 * d.2.1 ≤ ((spec t qs xs).map fun d => d.1 * d.2.1).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hd)
    simp only [toW]; omega
  · rw [hv, List.map_map]
    congr 2
  · rw [hv]; exact hlt

end Validation.BFVDecrypt
