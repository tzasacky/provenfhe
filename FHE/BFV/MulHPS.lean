import Challenge.BFVMul.HPS
import FHE.RNS.Basis
import Validation.BFV.Textbook

/-!
# FHE.BFV.MulHPS — the idealised HPS multiplication computes the textbook product

`Challenge.BFVMul.hpsMul` (limb by limb: exact base extension, limb-wise tensor product, RNS
scale-and-round, exact base switch back) is proved equal, coefficient by coefficient modulo `Q`,
to the textbook `Challenge.BFV.bfvMul`, under the side condition `hpsAuxOK?`:

* `hpsMul_eq`: `hpsMul t qs ps c d = (bfvMul t Q c d).map (· mod Q)` (representatives in
  `[0, Q)`), `Q = qs.prod`;
* `hpsMul_congr_bfvMul`: the same after `ofInt Q`.

The scalar facts, on the residues of one integer:

* `switch1_eq`, `switchVal_eq_valMinAbs`, `switchVal_eq_self`: the exact base switch computes
  the residues of the representative in `[-Q/2, Q/2)`, which is `ZMod.valMinAbs` for odd `Q`
  and the value itself when `2·|x| < Q`;
* `scale1_eq`: the HPS scaling formula computes `⌊t·x/Q⌉ mod pⱼ` from the residues of `x`,
  with no size condition on `x`.

The CRT core is `FHE.RNS.Basis.prod_dvd_sum_sub` at `Basis.ofList` (`crt_dvd`).
-/

namespace FHE.BFV.MulHPS
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS

/-! ### Lists -/

theorem zipWith_map_self {α β γ : Type} (f : α → β → γ) (g : α → β) (l : List α) :
    List.zipWith f l (l.map g) = l.map fun a => f a (g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem zipWith_map_map {α β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map fun a => f (g a) (h a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem map_zip_self {α β : Type} (g : α → β) (l : List α) :
    (l.map g).zip l = l.map fun a => (g a, a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem map_zip_map {α β γ : Type} (g : α → β) (h : α → γ) (l : List α) :
    (l.map g).zip (l.map h) = l.map fun a => (g a, h a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_map_modEq {α : Type} (n : ℤ) (l : List α) (f g : α → ℤ)
    (h : ∀ a, f a ≡ g a [ZMOD n]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n] := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa using Int.ModEq.add (h a) ih

/-- Termwise `s·f = r·g + h` sums to the same identity. -/
theorem sum_map_combo {α : Type} (l : List α) (f g h : α → ℤ) (r s : ℤ)
    (H : ∀ a ∈ l, s * f a = r * g a + h a) :
    s * (l.map f).sum = r * (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih fun b hb => H b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, mul_add]
    linarith

theorem prod_odd (qs : List ℕ) (h : ∀ q ∈ qs, q % 2 = 1) : qs.prod % 2 = 1 := by
  induction qs with
  | nil => rfl
  | cons a l ih =>
    rw [List.prod_cons, Nat.mul_mod, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem prod_pos' (qs : List ℕ) (h : ∀ q ∈ qs, 0 < q) : 0 < qs.prod := List.prod_pos h

/-! ### Rounding -/

/-- `a − b·⌊a/b⌉ ∈ [-b/2, b/2)`. -/
theorem roundDiv_bounds (a : ℤ) (b : ℕ) (hb : 0 < b) :
    -(b : ℤ) ≤ 2 * (a - roundDiv a b * b) ∧ 2 * (a - roundDiv a b * b) < b := by
  unfold roundDiv
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have h1 := Int.emod_add_mul_ediv (2 * a + b) (2 * b)
  have h2 := Int.emod_nonneg (2 * a + b) (show (2 * (b : ℤ)) ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos (2 * a + b) (show (0 : ℤ) < 2 * b by omega)
  constructor <;> linarith

theorem roundDiv_mul_add (a c : ℤ) (b : ℕ) (hb : 0 < b) :
    roundDiv (b * c + a) b = c + roundDiv a b := by
  unfold roundDiv
  have hb' : (2 * (b : ℤ)) ≠ 0 := by
    have : (0 : ℤ) < b := by exact_mod_cast hb
    omega
  have e : 2 * ((b : ℤ) * c + a) + b = (2 * a + b) + (2 * b) * c := by ring
  rw [e, Int.add_mul_ediv_left _ _ hb']
  ring

/-! ### Inverses and the CRT -/

theorem cast_invMod (a m : ℕ) (hm : 0 < m) : ((invMod a m : ℤ) : ZMod m) = (a : ZMod m)⁻¹ := by
  have : NeZero m := ⟨hm.ne'⟩
  show ((((a : ZMod m)⁻¹).val : ℤ) : ZMod m) = _
  simp

/-- **CRT, list form** (from `Basis.prod_dvd_sum_sub`): for integers `g q ≡ X·(Q/q)⁻¹ (mod q)`,
`Σ_q g q · (Q/q) ≡ X (mod Q)`. -/
theorem crt_dvd (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime)
    (X : ℤ) (g : ℕ → ℤ)
    (hg : ∀ q ∈ qs, (g q : ZMod q) = (X : ZMod q) * ((qs.prod / q : ℕ) : ZMod q)⁻¹) :
    (qs.prod : ℤ) ∣ (qs.map fun q => g q * ((qs.prod / q : ℕ) : ℤ)).sum - X := by
  have hh : ∀ i : Fin qs.length, (Basis.ofList qs hpos hcop).hat i = qs.prod / qs[i.1] :=
    fun i => by rw [Basis.hat_eq_div, Basis.ofList_prod]; rfl
  have h := (Basis.ofList qs hpos hcop).prod_dvd_sum_sub
    (fun i => (X : ZMod ((Basis.ofList qs hpos hcop).q i))) X (fun _ => rfl) (fun i => g qs[i.1])
    (fun i => by
      show (g qs[i.1] : ZMod qs[i.1]) = (X : ZMod qs[i.1]) * (Basis.ofList qs hpos hcop).hatInv i
      rw [hg _ (List.getElem_mem _)]
      unfold Basis.hatInv
      rw [hh]
      rfl)
  rw [Basis.ofList_prod] at h
  rw [← Fin.sum_univ_fun_getElem]
  simpa only [hh] using h

/-! ### Exact base switch -/

/-- The integer whose residues `switch1` computes: `S − ⌊S/Q⌉·Q` with
`S = Σ_q [x_q·(Q/q)⁻¹]_q·(Q/q)`. -/
def switchVal (qs : List ℕ) (X : ℤ) : ℤ :=
  (qs.map fun q => (X % q * invMod (qs.prod / q) q % q) * ((qs.prod / q : ℕ) : ℤ)).sum -
    roundDiv (qs.map fun q => (X % q * invMod (qs.prod / q) q % q) * ((qs.prod / q : ℕ) : ℤ)).sum
      qs.prod * qs.prod

theorem digits_map (qs : List ℕ) (g : ℕ → ℤ) :
    digits qs (qs.map g) = qs.map fun q => g q * invMod (qs.prod / q) q % q :=
  zipWith_map_self _ _ _

/-- `switch1` on the residues of `X` is `switchVal qs X mod p`. -/
theorem switch1_eq (qs : List ℕ) (X : ℤ) (p : ℕ) :
    switch1 qs (qs.map fun q : ℕ => X % q) p = switchVal qs X % p := by
  unfold switch1 overflow switchVal
  simp only [digits_map, zipWith_map_self]
  refine Int.ModEq.sub (sum_map_modEq _ _ _ _ fun q => Int.ModEq.mul_left _ ?_)
    (Int.ModEq.mul_left _ ?_)
  · rw [Int.natCast_mod]; exact Int.mod_modEq _ _
  · rw [Int.natCast_mod]; exact Int.mod_modEq _ _

theorem crtSum_dvd (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime)
    (X : ℤ) : (qs.prod : ℤ) ∣
      (qs.map fun q => (X % q * invMod (qs.prod / q) q % q) * ((qs.prod / q : ℕ) : ℤ)).sum - X :=
  crt_dvd qs hpos hcop X (fun q => X % q * invMod (qs.prod / q) q % q) fun q hq => by
    rw [ZMod.intCast_mod, Int.cast_mul, ZMod.intCast_mod, cast_invMod _ _ (hpos q hq)]

theorem switchVal_dvd (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime)
    (X : ℤ) : (qs.prod : ℤ) ∣ switchVal qs X - X := by
  have h := crtSum_dvd qs hpos hcop X
  unfold switchVal
  have h2 : (qs.prod : ℤ) ∣ roundDiv (qs.map fun q =>
      (X % q * invMod (qs.prod / q) q % q) * ((qs.prod / q : ℕ) : ℤ)).sum qs.prod * qs.prod :=
    Dvd.intro_left _ rfl
  have := dvd_sub h h2
  convert this using 1
  ring

theorem switchVal_bounds (qs : List ℕ) (hQ : 0 < qs.prod) (X : ℤ) :
    -(qs.prod : ℤ) ≤ 2 * switchVal qs X ∧ 2 * switchVal qs X < qs.prod :=
  roundDiv_bounds _ _ hQ

/-- For odd `Q` the base switch lifts to the centred representative `ZMod.valMinAbs`. -/
theorem switchVal_eq_valMinAbs (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (hodd : qs.prod % 2 = 1) (X : ℤ) :
    switchVal qs X = (X : ZMod qs.prod).valMinAbs := by
  have : NeZero qs.prod := ⟨by omega⟩
  obtain ⟨h1, h2⟩ := switchVal_bounds qs (by omega) X
  symm
  rw [ZMod.valMinAbs_spec]
  refine ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (switchVal_dvd qs hpos hcop X), ?_, ?_⟩
  · omega
  · omega

/-- A value with `2·|X| < Q` is switched exactly. -/
theorem switchVal_eq_self (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (X : ℤ) (hX : 2 * |X| < qs.prod) :
    switchVal qs X = X := by
  have hQ : 0 < qs.prod := prod_pos' qs hpos
  obtain ⟨h1, h2⟩ := switchVal_bounds qs hQ X
  have hd := switchVal_dvd qs hpos hcop X
  have hlt : |switchVal qs X - X| < (qs.prod : ℤ) := by
    rw [abs_lt]
    have := abs_lt.mp (show |X| < (qs.prod : ℤ) by
      have := abs_nonneg X
      omega)
    rcases abs_cases X with ⟨hx, _⟩ | ⟨hx, _⟩ <;> constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega

theorem reconstruct_sum (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime)
    (X : ℤ) :
    (qs.map fun q => (X % q * invMod (qs.prod / q) q % q) * ((qs.prod / q : ℕ) : ℤ)).sum % qs.prod
      = X % qs.prod :=
  (Int.modEq_iff_dvd.mpr (crtSum_dvd qs hpos hcop X)).symm

/-! ### Scale and round -/

/-- **The HPS scaling formula is exact**: from the residues of any integer `T` modulo
`qs ++ ps`, `scale1` computes `⌊t·T/Q⌉ mod pⱼ`. -/
theorem scale1_eq (t : ℕ) (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (T : ℤ) (j : Fin ps.length) :
    scale1 t qs ps (qs.map fun q : ℕ => T % q) ps[j.1] (T % ps[j.1]) =
      roundDiv (t * T) qs.prod % ps[j.1] := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  -- the CRT sum over the whole basis
  have hW := crt_dvd (qs ++ ps) hpos hcop T
    (fun m => T % m * invMod (qs.prod * ps.prod / m) m) (fun m hm => by
      rw [Int.cast_mul, ZMod.intCast_mod, cast_invMod _ _ (hpos m hm), List.prod_append])
  rw [List.map_append, List.sum_append] at hW
  obtain ⟨u, hu⟩ := hW
  -- the `qs` part
  have hq := sum_map_combo qs
    (fun q : ℕ => T % q * invMod (qs.prod * ps.prod / q) q * (((qs ++ ps).prod / q : ℕ) : ℤ))
    (fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q / q))
    (fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
      ((qs.prod / q : ℕ) : ℤ))
    qs.prod t (fun q hq => by
      obtain ⟨k, hk⟩ := List.dvd_prod hq
      have hq0 := hposq q hq
      have hdiv : qs.prod / q = k := by rw [hk, Nat.mul_div_cancel_left _ hq0]
      have hdiv2 : (qs ++ ps).prod / q = k * ps.prod := by
        rw [List.prod_append, hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ hq0]
      have hkZ : (qs.prod : ℤ) = q * k := by exact_mod_cast hk
      have hθ := Int.emod_add_mul_ediv ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q) q
      rw [hdiv, hdiv2, Nat.cast_mul]
      linear_combination (-(T % q * k)) * hθ +
        (-(T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q / q))) * hkZ)
  -- the `ps` part
  have hp := sum_map_combo ps
    (fun p : ℕ => T % p * invMod (qs.prod * ps.prod / p) p * (((qs ++ ps).prod / p : ℕ) : ℤ))
    (fun p : ℕ => T % p * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / p) p / p))
    (fun _ => 0) qs.prod t (fun p hp => by
      obtain ⟨k, hk⟩ := List.dvd_prod hp
      have hp0 := hposp p hp
      have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
      have hdiv2 : (qs ++ ps).prod / p = qs.prod * k := by
        rw [List.prod_append, hk, Nat.mul_left_comm, Nat.mul_div_cancel_left _ hp0]
      have hkZ : (ps.prod : ℤ) = p * k := by exact_mod_cast hk
      have e : (t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / p) p =
          p * (t * k * invMod (qs.prod * ps.prod / p) p) := by rw [hkZ]; ring
      rw [hdiv2, e, Int.mul_ediv_cancel_left _ hp0', Nat.cast_mul]
      ring)
  simp only [List.map_const', List.sum_replicate, smul_zero, add_zero] at hp
  -- `t·T = Q·(A₁ + A₂ − t·P·u) + F`
  have hT : (t : ℤ) * T = (qs.prod : ℤ) *
      ((qs.map fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q / q)).sum
        + ((ps.map fun p : ℕ =>
            T % p * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / p) p / p)).sum
          - t * ps.prod * u)) +
      (qs.map fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
        ((qs.prod / q : ℕ) : ℤ)).sum := by
    simp only [List.prod_append] at hu hq hp
    rw [Nat.cast_mul] at hu
    linear_combination hq + hp - (t : ℤ) * hu
  rw [hT, roundDiv_mul_add _ _ _ hQ]
  -- the list forms in `scale1`
  unfold scale1 theta
  simp only [map_zip_self, zipWith_map_map]
  -- only the `j`-th term of the `ps` part survives modulo `pⱼ`
  have hpj : (ps[j.1] : ℤ) ∣ (ps.prod : ℤ) := by
    exact_mod_cast List.dvd_prod (List.getElem_mem j.2)
  have hrest : ((ps.map fun p : ℕ =>
        T % p * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / p) p / p)).sum
      - t * ps.prod * u) ≡
      T % ps[j.1] * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / ps[j.1]) ps[j.1] / ps[j.1]
        % ps[j.1]) [ZMOD ps[j.1]] := by
    rw [← Fin.sum_univ_fun_getElem, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have h1 : (ps[j.1] : ℤ) ∣ ∑ i ∈ Finset.univ.erase j,
        T % ps[i.1] * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / ps[i.1]) ps[i.1]
          / ps[i.1]) := by
      refine Finset.dvd_sum fun i hi => ?_
      have hij : j ≠ i := (Finset.mem_erase.mp hi).1.symm
      have hd : ps[j.1] ∣ ps.prod / ps[i.1] := by
        have := (Basis.ofList ps hposp hcopp).q_dvd_hat hij
        rwa [Basis.hat_eq_div, Basis.ofList_prod] at this
      have hpi : ps[i.1] ∣ ps.prod := List.dvd_prod (List.getElem_mem i.2)
      have hi0 : (ps[i.1] : ℤ) ≠ 0 := by
        exact_mod_cast (hposp _ (List.getElem_mem i.2)).ne'
      have hPe : (ps.prod : ℤ) = ps[i.1] * ((ps.prod / ps[i.1] : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' hpi).symm
      have e : (t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / ps[i.1]) ps[i.1] =
          ps[i.1] * (t * ((ps.prod / ps[i.1] : ℕ) : ℤ) *
            invMod (qs.prod * ps.prod / ps[i.1]) ps[i.1]) := by
        conv_lhs => rw [hPe]
        ring
      rw [e, Int.mul_ediv_cancel_left _ hi0]
      have hd' : (ps[j.1] : ℤ) ∣ ((ps.prod / ps[i.1] : ℕ) : ℤ) := by exact_mod_cast hd
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left hd' _) _) _
    have h2 : (ps[j.1] : ℤ) ∣ (t : ℤ) * ps.prod * u :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_left hpj _) _
    have h3 : T % ps[j.1] * ((t : ℤ) * ps.prod *
          invMod (qs.prod * ps.prod / ps[j.1]) ps[j.1] / ps[j.1]) ≡
        T % ps[j.1] * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / ps[j.1]) ps[j.1] / ps[j.1]
          % ps[j.1]) [ZMOD ps[j.1]] :=
      Int.ModEq.mul_left _ (Int.mod_modEq _ _).symm
    have h4 : (∑ i ∈ Finset.univ.erase j,
        T % ps[i.1] * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / ps[i.1]) ps[i.1]
          / ps[i.1])) - t * ps.prod * u ≡ 0 [ZMOD ps[j.1]] :=
      (Int.modEq_zero_iff_dvd.mpr (dvd_sub h1 h2))
    have := Int.ModEq.add h3 h4
    rw [add_zero] at this
    rw [add_sub_assoc]
    exact this
  refine Int.ModEq.add (Int.ModEq.add ?_ hrest.symm) (Int.ModEq.refl _)
  exact sum_map_modEq _ _ _ _ fun q => Int.ModEq.mul_left _ (Int.mod_modEq _ _)

/-! ### Polynomials -/

variable {N : ℕ}

/-- Coefficients reduced into `[0, m)`. -/
def modPoly (m : ℕ) (a : IntPoly N) : IntPoly N := ⟨fun i => a.coeff i % m⟩

/-- The two-component case of the locked `Challenge.Source.tensor`, by `rfl` (no equation lemma
of the locked definition is realised here). -/
theorem source_tensor_two (c₀ c₁ d₀ d₁ : IntPoly N) :
    Challenge.Source.tensor [c₀, c₁] [d₀, d₁] = [c₀ * d₀, c₀ * d₁ + c₁ * d₀, c₁ * d₁] :=
  rfl

/-- The two-component case of the locked `HPS.tensor`, by `rfl`. -/
theorem hps_tensor_two (ms : List ℕ) (c₀ c₁ d₀ d₁ : List (IntPoly N)) :
    HPS.tensor ms [c₀, c₁] [d₀, d₁] =
      [mulLimbs ms c₀ d₀, addLimbs ms (mulLimbs ms c₀ d₁) (mulLimbs ms c₁ d₀), mulLimbs ms c₁ d₁] :=
  rfl

theorem residues_eq (x : List (IntPoly N)) (i : Fin N) : residues x i = x.map (·.coeff i) :=
  rfl

theorem toLimbs_eq (ms : List ℕ) (a : IntPoly N) : toLimbs ms a = ms.map fun m => modPoly m a :=
  rfl

theorem ofInt_modPoly (m : ℕ) (a : IntPoly N) : ofInt m (modPoly m a) = ofInt m a := by
  ext i
  exact ZMod.intCast_mod _ _

theorem modPoly_congr {m : ℕ} {a b : IntPoly N} (h : ofInt m a = ofInt m b) :
    modPoly m a = modPoly m b := by
  ext i
  have := congrArg (fun p => p.coeff i) h
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp this

theorem residues_toLimbs (ms : List ℕ) (a : IntPoly N) (i : Fin N) :
    residues (toLimbs ms a) i = ms.map fun m : ℕ => a.coeff i % m := by
  rw [residues_eq, toLimbs_eq, List.map_map]
  rfl

theorem mulLimbs_toLimbs (ms : List ℕ) (a b : IntPoly N) :
    mulLimbs ms (toLimbs ms a) (toLimbs ms b) = toLimbs ms (a * b) := by
  unfold mulLimbs
  rw [toLimbs_eq, toLimbs_eq, toLimbs_eq, map_zip_map, zipWith_map_self]
  refine List.map_congr_left fun m _ => ?_
  show modPoly m (modPoly m a * modPoly m b) = modPoly m (a * b)
  apply modPoly_congr
  rw [ofInt_mul, ofInt_modPoly, ofInt_modPoly, ofInt_mul]

theorem addLimbs_toLimbs (ms : List ℕ) (a b : IntPoly N) :
    addLimbs ms (toLimbs ms a) (toLimbs ms b) = toLimbs ms (a + b) := by
  unfold addLimbs
  rw [toLimbs_eq, toLimbs_eq, toLimbs_eq, map_zip_map, zipWith_map_self]
  refine List.map_congr_left fun m _ => ?_
  show modPoly m (modPoly m a + modPoly m b) = modPoly m (a + b)
  apply modPoly_congr
  rw [ofInt_add, ofInt_modPoly, ofInt_modPoly, ofInt_add]

theorem tensor_toLimbs (ms : List ℕ) (a₀ a₁ b₀ b₁ : IntPoly N) :
    HPS.tensor ms [toLimbs ms a₀, toLimbs ms a₁] [toLimbs ms b₀, toLimbs ms b₁] =
      (Challenge.Source.tensor [a₀, a₁] [b₀, b₁]).map (toLimbs ms) := by
  simp only [hps_tensor_two, source_tensor_two, mulLimbs_toLimbs, addLimbs_toLimbs,
    List.map_cons, List.map_nil]

/-- The base switch of the limbs of `a` gives the limbs of `b`, where `b` has the switched
values as coefficients. -/
theorem switchBasis_toLimbs (qs ps : List ℕ) (a b : IntPoly N)
    (h : ∀ i, switchVal qs (a.coeff i) = b.coeff i) :
    switchBasis qs ps (toLimbs qs a) = toLimbs ps b := by
  unfold switchBasis
  rw [toLimbs_eq ps]
  refine List.map_congr_left fun p _ => ?_
  ext i
  show switch1 qs (residues (toLimbs qs a) i) p = b.coeff i % p
  rw [residues_toLimbs, switch1_eq, h]

/-- **Base extension**: the limbs modulo `qs ++ ps` of the centred representative. -/
theorem expand_toLimbs (qs ps : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (hodd : qs.prod % 2 = 1) (a : IntPoly N) :
    expand qs ps (toLimbs qs a) = toLimbs (qs ++ ps) (centered (ofInt qs.prod a)) := by
  unfold expand
  have hc : ∀ i, switchVal qs (a.coeff i) = (centered (ofInt qs.prod a)).coeff i := fun i =>
    switchVal_eq_valMinAbs qs hpos hcop hodd _
  rw [switchBasis_toLimbs qs ps a _ hc, toLimbs_eq (qs ++ ps), List.map_append]
  congr 1
  rw [toLimbs_eq]
  refine List.map_congr_left fun q hq => ?_
  apply modPoly_congr
  ext i
  show ((a.coeff i : ℤ) : ZMod q) = (((centered (ofInt qs.prod a)).coeff i : ℤ) : ZMod q)
  rw [← hc i, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact dvd_trans (by exact_mod_cast List.dvd_prod hq) (switchVal_dvd qs hpos hcop _)

/-- **Scale and round**: the limbs modulo `ps` of the textbook `⌊t·T/Q⌉`. -/
theorem scaleRound_toLimbs (t : ℕ) (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (T : IntPoly N) :
    HPS.scaleRound t qs ps (toLimbs (qs ++ ps) T) =
      toLimbs ps (Challenge.BFV.scaleRound t qs.prod T) := by
  unfold HPS.scaleRound
  have e : toLimbs (qs ++ ps) T = toLimbs qs T ++ toLimbs ps T := List.map_append
  have hl : (toLimbs qs T).length = qs.length := List.length_map _
  rw [e, List.take_left' hl, List.drop_left' hl]
  apply List.ext_getElem
  · simp [toLimbs_eq]
  · intro n h1 h2
    have hn : n < ps.length := by simpa [toLimbs_eq] using h2
    simp only [List.getElem_zipWith, toLimbs_eq, List.getElem_map]
    ext i
    show scale1 t qs ps (residues (toLimbs qs T) i) ps[n] (T.coeff i % ps[n]) =
      roundDiv (t * T.coeff i) qs.prod % ps[n]
    rw [residues_toLimbs]
    exact scale1_eq t qs ps hpos hcop (T.coeff i) ⟨n, hn⟩

theorem reconstruct_toLimbs (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (a : IntPoly N) :
    reconstruct qs (toLimbs qs a) = modPoly qs.prod a := by
  ext i
  show (List.zipWith (fun q yi => yi * ((qs.prod / q : ℕ) : ℤ)) qs
    (digits qs (residues (toLimbs qs a) i))).sum % qs.prod = a.coeff i % qs.prod
  rw [residues_toLimbs, digits_map, zipWith_map_self]
  exact reconstruct_sum qs hpos hcop _

/-! ### The side condition -/

theorem hpsAuxOK_def (t N : ℕ) (qs ps : List ℕ) :
    hpsAuxOK? t N qs ps =
      ((qs ++ ps).all (fun m => decide (0 < m)) &&
        decide ((qs ++ ps).Pairwise Nat.Coprime) &&
        qs.all (fun q => decide (q % 2 = 1)) &&
        decide (t * N * (qs.prod - 1) * (qs.prod - 1) + qs.prod < ps.prod * qs.prod)) :=
  rfl

theorem hpsAuxOK_iff (t N : ℕ) (qs ps : List ℕ) :
    hpsAuxOK? t N qs ps = true ↔
      (∀ m ∈ qs ++ ps, 0 < m) ∧ (qs ++ ps).Pairwise Nat.Coprime ∧ (∀ q ∈ qs, q % 2 = 1) ∧
        t * N * (qs.prod - 1) * (qs.prod - 1) + qs.prod < ps.prod * qs.prod := by
  simp only [hpsAuxOK_def, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

/-- The scaled tensor product fits in the centred range of `P`. -/
theorem scaled_small (t Q P : ℕ) (hodd : Q % 2 = 1)
    (hsize : t * N * (Q - 1) * (Q - 1) + Q < P * Q) (T : IntPoly N)
    (hT : ∀ i, |T.coeff i| ≤ 2 * (N * ((Q / 2 : ℕ) : ℤ) * ((Q / 2 : ℕ) : ℤ))) (i : Fin N) :
    2 * |(Challenge.BFV.scaleRound t Q T).coeff i| < P := by
  have hQ : 0 < Q := by omega
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hr := Validation.BFV.two_abs_roundDiv_sub_le (t * T.coeff i) Q hQ
  show 2 * |roundDiv (t * T.coeff i) Q| < P
  set r := roundDiv (t * T.coeff i) Q
  have hh : 2 * ((Q / 2 : ℕ) : ℤ) = Q - 1 := by omega
  have hsz : (t : ℤ) * N * (Q - 1) * (Q - 1) + Q < P * Q := by
    have : ((Q - 1 : ℕ) : ℤ) = Q - 1 := by omega
    rw [← this]
    exact_mod_cast hsize
  have h1 : (Q : ℤ) * |r| ≤ |(Q : ℤ) * r - t * T.coeff i| + t * |T.coeff i| := by
    have e : (Q : ℤ) * |r| = |(Q : ℤ) * r| := by rw [abs_mul, abs_of_pos hQ']
    have e2 : (t : ℤ) * |T.coeff i| = |(t : ℤ) * T.coeff i| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)]
    rw [e, e2]
    have := abs_add_le ((Q : ℤ) * r - t * T.coeff i) (t * T.coeff i)
    simpa using this
  have h2 : (t : ℤ) * |T.coeff i| ≤ t * (2 * (N * ((Q / 2 : ℕ) : ℤ) * ((Q / 2 : ℕ) : ℤ))) :=
    mul_le_mul_of_nonneg_left (hT i) (by positivity)
  have h3 : 4 * ((t : ℤ) * (2 * (N * ((Q / 2 : ℕ) : ℤ) * ((Q / 2 : ℕ) : ℤ)))) =
      2 * (t * N * (Q - 1) * (Q - 1)) := by
    rw [← hh]; ring
  have h4 : (Q : ℤ) * (2 * |r|) < Q * P := by nlinarith
  exact lt_of_mul_lt_mul_left h4 hQ'.le

theorem abs_centered_le {Q : ℕ} (hQ : 0 < Q) (a : Poly Q N) (i : Fin N) :
    |(centered a).coeff i| ≤ ((Q / 2 : ℕ) : ℤ) :=
  Validation.BFV.abs_le_half (Validation.BFV.two_abs_valMinAbs_le hQ _)

/-! ### The theorem -/

/-- **HPS multiplication is the textbook multiplication**, with representatives in `[0, Q)`:
under `hpsAuxOK?`, for two-component operands, limb-level `hpsMul` equals `bfvMul` at
`Q = qs.prod` reduced modulo `Q` coefficient by coefficient. -/
theorem hpsMul_eq (t : ℕ) (qs ps : List ℕ) (haux : hpsAuxOK? t N qs ps = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    hpsMul t qs ps c d = (Challenge.BFV.bfvMul t qs.prod c d).map (modPoly qs.prod) := by
  obtain ⟨hpos, hcop, hodd, hsize⟩ := (hpsAuxOK_iff t N qs ps).mp haux
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hQodd := prod_odd qs hodd
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  unfold hpsMul Challenge.BFV.bfvMul
  simp only [List.map_cons, List.map_nil, expand_toLimbs qs ps hposq hcopq hQodd, tensor_toLimbs,
    List.map_map]
  refine List.map_congr_left fun T hT => ?_
  have hb : ∀ i, |T.coeff i| ≤
      2 * (N * ((qs.prod / 2 : ℕ) : ℤ) * ((qs.prod / 2 : ℕ) : ℤ)) := by
    intro i
    have hnn : (0 : ℤ) ≤ N * ((qs.prod / 2 : ℕ) : ℤ) * ((qs.prod / 2 : ℕ) : ℤ) := by positivity
    have hm : ∀ a b : Poly qs.prod N, |(centered a * centered b).coeff i| ≤
        N * ((qs.prod / 2 : ℕ) : ℤ) * ((qs.prod / 2 : ℕ) : ℤ) := fun a b =>
      abs_coeff_mul_le_N _ _ _ _ (abs_centered_le hQ a) (abs_centered_le hQ b) i
    simp only [source_tensor_two, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl
    · linarith [hm (ofInt qs.prod a₀) (ofInt qs.prod b₀)]
    · rw [coeff_add']
      have := abs_add_le ((centered (ofInt qs.prod a₀) * centered (ofInt qs.prod b₁)).coeff i)
        ((centered (ofInt qs.prod a₁) * centered (ofInt qs.prod b₀)).coeff i)
      linarith [hm (ofInt qs.prod a₀) (ofInt qs.prod b₁), hm (ofInt qs.prod a₁) (ofInt qs.prod b₀)]
    · linarith [hm (ofInt qs.prod a₁) (ofInt qs.prod b₁)]
  show reconstruct qs (switchBasis ps qs (HPS.scaleRound t qs ps (toLimbs (qs ++ ps) T))) =
    modPoly qs.prod (Challenge.BFV.scaleRound t qs.prod T)
  rw [scaleRound_toLimbs t qs ps hpos hcop,
    switchBasis_toLimbs ps qs _ _ (fun i => switchVal_eq_self ps hposp hcopp _
      (scaled_small t qs.prod ps.prod hQodd hsize T hb i)),
    reconstruct_toLimbs qs hposq hcopq]

/-- **HPS multiplication is congruent to the textbook multiplication modulo `Q`**, component by
component. -/
theorem hpsMul_congr_bfvMul (t : ℕ) (qs ps : List ℕ) (haux : hpsAuxOK? t N qs ps = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    (hpsMul t qs ps c d).map (ofInt qs.prod) =
      (Challenge.BFV.bfvMul t qs.prod c d).map (ofInt qs.prod) := by
  rw [hpsMul_eq t qs ps haux c d hc hd, List.map_map]
  exact List.map_congr_left fun a _ => ofInt_modPoly _ _

end FHE.BFV.MulHPS
