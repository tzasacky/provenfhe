import Challenge.BFVMul.Float
import FHE.BFV.MulHPS

/-!
# FHE.BFV.FloatScalar — base switch and scaling with sums within a tolerance (scalar facts)

The two facts about one integer on which the floating-point HPS-family multiplications
(`Challenge.BFVMul.Float`) rest, for every `S : Fl.Sums` with `Fl.SumsOK S`:

* `switch1_eq`, `switchVal_dvd`, `switchVal_bound`: `Fl.switch1 S qs` computes the residues of a
  representative `switchVal S qs X ≡ X (mod Q)` with `|·| ≤ Q/2 + Q·doubleSw k/2⁵³`;
* `scale1_tol`: `Fl.scale1 S t qs ps` computes the residues of an integer `R` with
  `|R − t·T/Q| ≤ 1/2 + doubleSr qs/2⁵³`.

They are the tolerant counterparts of `FHE.BFV.MulHPS.switch1_eq`, `switchVal_bounds`, `scale1_eq`.
-/

namespace FHE.BFV.FloatScalar
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Spec.BudgetBFV
open FHE.BFV.MulHPS

/-! ### Lists and the exact sums -/

theorem zip_map_self {α β : Type} (g : α → β) (l : List α) :
    l.zip (l.map g) = l.map fun a => (a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem zip_zip_map {α β γ : Type} (g : α → β) (h : α → γ) (l : List α) :
    (l.zip (l.map g)).zip (l.map h) = l.map fun a => ((a, g a), h a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem reduced_map (qs : List ℕ) (g : ℕ → ℤ) (h : ∀ q ∈ qs, 0 ≤ g q ∧ g q < (q : ℤ)) :
    Fl.Reduced qs (qs.map g) := by
  intro p hp
  rw [zip_map_self, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact h q hq

theorem exactSw_map (qs : List ℕ) (g : ℕ → ℤ) :
    Fl.exactSw qs (qs.map g) = 1 / 2 + (qs.map fun q : ℕ => (g q : ℚ) / (q : ℚ)).sum := by
  unfold Fl.exactSw
  rw [zip_map_self, List.map_map]
  rfl

theorem exactSr_map (qs : List ℕ) (n g : ℕ → ℤ) :
    Fl.exactSr qs (qs.map n) (qs.map g) =
      1 / 2 + (qs.map fun q : ℕ => (g q : ℚ) * (n q : ℚ) / (q : ℚ)).sum := by
  unfold Fl.exactSr
  rw [zip_zip_map, List.map_map]
  rfl

theorem fracNums_eq (t : ℕ) (qs ps : List ℕ) :
    Fl.fracNums t qs ps =
      qs.map fun q : ℕ => (t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q := by
  unfold Fl.fracNums theta
  rw [map_zip_self, List.map_map]
  rfl

/-- `Σ f q·(Q/q) = Q·Σ f q/q` for divisors `q` of `Q`. -/
theorem cast_sum_hat (l : List ℕ) (Q : ℕ) (h : ∀ q ∈ l, 0 < q ∧ q ∣ Q) (f : ℕ → ℤ) :
    (((l.map fun q : ℕ => f q * ((Q / q : ℕ) : ℤ)).sum : ℤ) : ℚ) =
      (Q : ℚ) * (l.map fun q : ℕ => (f q : ℚ) / (q : ℚ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, k, hk⟩ := h a List.mem_cons_self
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add]
    rw [ih']
    congr 1
    have hd : Q / a = k := by rw [hk, Nat.mul_div_cancel_left _ ha]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hQ : (Q : ℚ) = a * k := by exact_mod_cast hk
    rw [hd, hQ]
    push_cast
    field_simp

theorem floatDen_pos : 0 < floatDen := by unfold floatDen; positivity

/-- The common core of the two tolerant facts: if `n = ⌊s⌋` with `s` within `w/2⁵³` of
`e = 1/2 + Σ/Q`, then `|Σ − n·Q| ≤ Q/2 + Q·w/2⁵³`. -/
theorem floor_core (Q w : ℕ) (hQ : 0 < Q) (Sg n : ℤ) (s e : ℚ) (hn : n = ⌊s⌋)
    (hs : |s - e| ≤ (w : ℚ) / (floatDen : ℚ)) (hSg : (Sg : ℚ) = (Q : ℚ) * (e - 1 / 2)) :
    2 * (floatDen : ℤ) * |Sg - n * Q| ≤ (Q : ℤ) * ((floatDen : ℤ) + 2 * (w : ℤ)) := by
  have hF : (0 : ℚ) < (floatDen : ℚ) := by exact_mod_cast floatDen_pos
  have hQ' : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQ
  have h1 : (n : ℚ) ≤ s := by rw [hn]; exact Int.floor_le s
  have h2 : s < (n : ℚ) + 1 := by rw [hn]; exact Int.lt_floor_add_one s
  obtain ⟨h3, h4⟩ := abs_le.mp hs
  have hd : |e - 1 / 2 - (n : ℚ)| ≤ 1 / 2 + (w : ℚ) / (floatDen : ℚ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have h5 : 2 * (floatDen : ℚ) * |e - 1 / 2 - (n : ℚ)| ≤ (floatDen : ℚ) + 2 * (w : ℚ) := by
    have h6 := mul_le_mul_of_nonneg_left hd (show (0 : ℚ) ≤ 2 * (floatDen : ℚ) by positivity)
    have h7 : 2 * (floatDen : ℚ) * (1 / 2 + (w : ℚ) / (floatDen : ℚ)) =
        (floatDen : ℚ) + 2 * (w : ℚ) := by
      field_simp
    linarith
  have h8 : ((Sg - n * Q : ℤ) : ℚ) = (Q : ℚ) * (e - 1 / 2 - (n : ℚ)) := by
    push_cast
    rw [hSg]
    ring
  have h9 : ((2 * (floatDen : ℤ) * |Sg - n * Q| : ℤ) : ℚ) ≤
      (((Q : ℤ) * ((floatDen : ℤ) + 2 * (w : ℤ)) : ℤ) : ℚ) := by
    rw [Int.cast_mul, Int.cast_abs, h8, abs_mul, abs_of_pos hQ']
    push_cast
    have := mul_le_mul_of_nonneg_left h5 hQ'.le
    linarith
  exact_mod_cast h9

/-- The integer whose residues `Fl.switch1 S qs` computes on the residues of `X`:
`Σ − S.sw·Q` with `Σ = Σ_q [X·(Q/q)⁻¹]_q·(Q/q)`. -/
def switchVal (S : Fl.Sums) (qs : List ℕ) (X : ℤ) : ℤ :=
  (qs.map fun q => (X % q * invMod (qs.prod / q) q % q) * ((qs.prod / q : ℕ) : ℤ)).sum -
    S.sw qs (qs.map fun q => X % q * invMod (qs.prod / q) q % q) * qs.prod

/-- `Fl.switch1` on the residues of `X` is `switchVal S qs X mod p`. -/
theorem switch1_eq (S : Fl.Sums) (qs : List ℕ) (X : ℤ) (p : ℕ) :
    Fl.switch1 S qs (qs.map fun q : ℕ => X % q) p = switchVal S qs X % p := by
  unfold Fl.switch1 switchVal
  simp only [digits_map, zipWith_map_self]
  refine Int.ModEq.sub (sum_map_modEq _ _ _ _ fun q => Int.ModEq.mul_left _ ?_)
    (Int.ModEq.mul_left _ ?_)
  · rw [Int.natCast_mod]; exact Int.mod_modEq _ _
  · rw [Int.natCast_mod]; exact Int.mod_modEq _ _

/-- The switched representative is congruent to the value modulo `Q`. -/
theorem switchVal_dvd (S : Fl.Sums) (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (X : ℤ) : (qs.prod : ℤ) ∣ switchVal S qs X - X := by
  have h := crtSum_dvd qs hpos hcop X
  unfold switchVal
  have h2 : (qs.prod : ℤ) ∣
      S.sw qs (qs.map fun q : ℕ => X % q * invMod (qs.prod / q) q % q) * qs.prod :=
    Dvd.intro_left _ rfl
  have := dvd_sub h h2
  convert this using 1
  ring

/-- **The switched representative is within `Q/2 + Q·doubleSw k/2⁵³`.** -/
theorem switchVal_bound (S : Fl.Sums) (hS : Fl.SumsOK S) (qs : List ℕ)
    (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime) (hfb : floatBasisOK qs = true)
    (X : ℤ) :
    2 * (floatDen : ℤ) * |switchVal S qs X| ≤
      (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℤ)) := by
  have _ := hcop
  have hQ : 0 < qs.prod := prod_pos' qs hpos
  have hred : Fl.Reduced qs (qs.map fun q : ℕ => X % q * invMod (qs.prod / q) q % q) :=
    reduced_map qs _ fun q hq =>
      have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hpos q hq
      ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩
  obtain ⟨s, hs1, hs2⟩ := hS.1 qs _ hfb hred
  rw [exactSw_map] at hs2
  refine floor_core qs.prod (doubleSw qs.length) hQ _ _ s _ hs1 hs2 ?_
  rw [cast_sum_hat qs qs.prod (fun q hq => ⟨hpos q hq, List.dvd_prod hq⟩)]
  ring

/-- The decomposition behind the HPS scaling formula (the first half of the proof of
`FHE.BFV.MulHPS.scale1_eq`): `t·T = Q·I + Σᵢ [T]_{qᵢ}·(θᵢ mod qᵢ)·(Q/qᵢ)` for an integer `I`. -/
theorem scale_decomp (t : ℕ) (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (T : ℤ) :
    ∃ I : ℤ, (t : ℤ) * T = (qs.prod : ℤ) * I +
      (qs.map fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
        ((qs.prod / q : ℕ) : ℤ)).sum := by
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
  exact ⟨_, hT⟩

/-- `Fl.scale1` is `HPS.scale1` with the exact rounded fractional sum exchanged for `S.sr`. -/
theorem scale1_fl (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (xq : List ℤ) (p : ℕ) (xp : ℤ) :
    Fl.scale1 S t qs ps xq p xp =
      (HPS.scale1 t qs ps xq p xp -
        roundDiv (List.zipWith
          (fun (θ : ℤ × ℕ) xi => xi * (θ.1 % θ.2) * ((qs.prod / θ.2 : ℕ) : ℤ))
          ((theta t qs ps).zip qs) xq).sum qs.prod +
        S.sr qs (Fl.fracNums t qs ps) xq) % p := by
  have key : ∀ a f s m : ℤ, (a + s) % m = ((a + f) % m - f + s) % m := by
    intro a f s m
    have h : (a + f) % m - f + s ≡ (a + f) - f + s [ZMOD m] :=
      ((Int.mod_modEq _ _).sub_right _).add_right _
    rw [h.eq]
    congr 1
    ring
  exact key _ _ _ _

/-- **Scaling with a tolerant fractional sum**: from the residues of any integer `T` modulo
`qs ++ ps`, `Fl.scale1 S` computes the residues modulo every `pⱼ` of one integer `R` with
`2·2⁵³·|Q·R − t·T| ≤ Q·(2⁵³ + 2·doubleSr qs)`. -/
theorem scale1_tol (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfb : floatBasisOK qs = true) (T : ℤ) :
    ∃ R : ℤ,
      (∀ j : Fin ps.length,
        Fl.scale1 S t qs ps (qs.map fun q : ℕ => T % q) ps[j.1] (T % ps[j.1]) = R % ps[j.1]) ∧
      2 * (floatDen : ℤ) * |(qs.prod : ℤ) * R - t * T| ≤
        (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr qs : ℤ)) := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  obtain ⟨I, hI⟩ := scale_decomp t qs ps hpos hcop T
  have hred1 : Fl.Reduced qs (Fl.fracNums t qs ps) := by
    rw [fracNums_eq]
    exact reduced_map qs _ fun q hq =>
      have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hposq q hq
      ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩
  have hred2 : Fl.Reduced qs (qs.map fun q : ℕ => T % q) :=
    reduced_map qs _ fun q hq =>
      have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hposq q hq
      ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩
  obtain ⟨s, hs1, hs2⟩ := hS.2 qs _ _ hfb hred1 hred2
  refine ⟨I + S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q), fun j => ?_, ?_⟩
  · have h := scale1_eq t qs ps hpos hcop T j
    rw [hI, roundDiv_mul_add _ _ _ hQ] at h
    have hz : List.zipWith
        (fun (θ : ℤ × ℕ) xi => xi * (θ.1 % θ.2) * ((qs.prod / θ.2 : ℕ) : ℤ))
        ((theta t qs ps).zip qs) (qs.map fun q : ℕ => T % q) =
        qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ) := by
      unfold theta
      simp only [map_zip_self, zipWith_map_map]
    rw [scale1_fl, h, hz]
    have h2 : ((I + roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod) % (ps[j.1] : ℤ) -
        roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod +
        S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q)) ≡
        I + S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q) [ZMOD (ps[j.1] : ℤ)] := by
      have := ((Int.mod_modEq (I + roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod) (ps[j.1] : ℤ)).sub_right
          (roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod)).add_right
          (S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q))
      rwa [add_sub_cancel_right] at this
    exact h2.eq
  · rw [fracNums_eq, exactSr_map] at hs2
    have hc := floor_core qs.prod (doubleSr qs) hQ
      (qs.map fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
        ((qs.prod / q : ℕ) : ℤ)).sum _ s _ hs1 hs2 (by
        rw [cast_sum_hat qs qs.prod (fun q hq => ⟨hposq q hq, List.dvd_prod hq⟩)
          (fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q))]
        simp only [Int.cast_mul]
        ring)
    have e : (qs.prod : ℤ) * (I + S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q)) -
        t * T = -((qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum -
          S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q) * qs.prod) := by
      rw [hI]
      ring
    rw [e, abs_neg]
    exact hc

end FHE.BFV.FloatScalar
