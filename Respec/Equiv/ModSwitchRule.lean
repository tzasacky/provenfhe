import Respec.Equiv.ModSwitch
import Validation.Trace

/-!
# Respec.Equiv.ModSwitchRule — B's `ModSwitchRule .centred`, and any number of components

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Verdicts (PROVED, no `sorry`)

* `modSwitch_centred_parts` : B's ciphertext-level `modSwitch (.ghs .centred) t q Q'` of a
  ciphertext with **any number `k` of components** that encrypts `m` with noise `B` under a
  secret with `‖s‖∞ ≤ Bs` encrypts `q⁻¹·m` with noise at most
  `⌊(B + t·⌊q/2⌋·Σ_{i<k} (N·Bs)ⁱ) / q⌋`, given `t` coprime to `q`, `0 < q` and the no-wrap
  condition `2·B + t·q·Σ_{i<k} (N·Bs)ⁱ < Q'·q` on the numerator. The proof is A's proof of
  `Validation.Trace.stepOK_modSwitch_textbook_parts` (`divq_gen`, `intPhase_switch`,
  `abs_coeff_intPhase_le`, `ofInt_intPhase_eq_zero`) applied to B's switch through
  `ModSwitch.modSwitchElt_eq`.
* `modSwitchRule_centred` : **B's `ModSwitchRule .centred N t ql Q'` holds for all `N`, `t`,
  `ql`, `Q'`** (formerly open): the case `k = 2`, with
  `B' = ⌊(B + t·⌊ql/2⌋·(1 + N·Bs)) / ql⌋ ≤ modSwitchBound (.ghs .centred) N t Bs ql 1 B`.

Not proved here: `ModSwitchRule .canonical` (the correction in `[0, q)`). It is not stated as a
theorem anywhere; A defines no budget for that convention (`Spec/Budget.lean`).
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Respec Respec.BGV Respec.Noise Validation.Ring Validation.Scheme
  Validation.Source Validation.Trace

variable {N : ℕ}

/-- **B's centred modulus switch, any number of components.** -/
theorem modSwitch_centred_parts (t ql Q' : ℕ) (s : IntPoly N) (ct : Ct (Q' * ql) N)
    (m : Poly t N) (Bs B : ℕ) (hcop : Nat.Coprime t ql) (hql : 0 < ql)
    (hs : normInf s ≤ Bs) (h : Encrypts t s ct m B)
    (hnw : 2 * B + t * ql * ((List.range ct.length).map fun i => (N * Bs) ^ i).sum < Q' * ql) :
    Encrypts t s (modSwitch (.ghs .centred) t ql Q' ct) ((((ql : ℕ) : ZMod t)⁻¹) • m)
      ((B + t * (ql / 2) * ((List.range ct.length).map fun i => (N * Bs) ^ i).sum) / ql) := by
  have hQ' : 0 < Q' := Nat.pos_of_ne_zero fun h0 => by
    have : Q' * ql = 0 := by rw [h0, zero_mul]
    omega
  have : NeZero ql := ⟨hql.ne'⟩
  rw [← bgvEncrypts_iff] at h ⊢
  -- integer representatives of the components
  set ca : List (IntPoly N) := ct.map centered with hca
  have hct : ct = ca.map (ofInt (Q' * ql)) := by
    rw [hca, List.map_map]
    conv_lhs => rw [← List.map_id ct]
    apply List.map_congr_left
    intro c _
    exact (ofInt_centered c).symm
  have hlen : ca.length = ct.length := by rw [hca, List.length_map]
  clear_value ca
  have hout : modSwitch (.ghs .centred) t ql Q' ct =
      (ca.map (Challenge.Source.bgvModSwitchComp t ql)).map (ofInt Q') := by
    unfold modSwitch
    conv_lhs => rw [hct]
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro c _
    exact (modSwitchElt_eq t ql Q' hql hQ' hcop c).symm
  set G : ℕ := ((List.range ct.length).map fun i => (N * Bs) ^ i).sum with hG
  set Φ := centeredPhase s ct with hΦ
  have hE' : ofInt (Q' * ql) (intPhase s ca) = ofInt (Q' * ql) Φ := by
    rw [← phase_map_ofInt, ← hct, hΦ, ← phase_eq_ofInt_centeredPhase]
  let dl : IntPoly N → IntPoly N := fun c => ⟨fun i => Validation.Switch.corr t ql (c.coeff i)⟩
  have hdiv : ∀ c : IntPoly N, ∀ i,
      (ql : ℤ) * (Challenge.Source.bgvModSwitchComp t ql c).coeff i =
        c.coeff i + (dl c).coeff i := fun c i => Validation.Switch.q_mul_sw hcop (c.coeff i)
  have hdl : ∀ c : IntPoly N, ∀ i, |(dl c).coeff i| ≤ (t : ℤ) * ((ql / 2 : ℕ) : ℤ) :=
    fun c i => Validation.Switch.abs_corr_le t ql (c.coeff i)
  have hdlt : ∀ c : IntPoly N, ofInt t (dl c) = 0 := by
    intro c; ext i
    show (((t : ℤ) * _ : ℤ) : ZMod t) = 0
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  obtain ⟨e, he, hqe⟩ := divq_gen Q' ql (intPhase s ca)
    (intPhase s (ca.map (Challenge.Source.bgvModSwitchComp t ql))) Φ
    (intPhase s (ca.map dl)) hE' (intPhase_switch ql s _ dl hdiv ca)
  have hS : (∑ j, |s.coeff j|) ≤ ((N * Bs : ℕ) : ℤ) := by
    push_cast
    exact sum_abs_le s _ ((normInf_le_iff _ _).mp hs)
  have hD : ∀ i, |(intPhase s (ca.map dl)).coeff i| ≤ (t : ℤ) * ((ql / 2 : ℕ) : ℤ) * (G : ℕ) := by
    intro i
    have hb := abs_coeff_intPhase_le s (N * Bs) ((t : ℤ) * ((ql / 2 : ℕ) : ℤ)) hS (by positivity)
      (ca.map dl) (fun d' hd' j => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hd'
        exact hdl c j) i
    rwa [List.length_map, hlen] at hb
  have hΦB : ∀ i, |Φ.coeff i| ≤ (B : ℤ) := BGVEncrypts.bound h
  have hql0 : (0 : ℤ) < ql := by exact_mod_cast hql
  have hebound : ∀ i, ql * (e.coeff i).natAbs ≤ B + t * (ql / 2) * G := by
    intro i
    have h1 : |(ql : ℤ) * e.coeff i| ≤ (B : ℤ) + (t : ℤ) * ((ql / 2 : ℕ) : ℤ) * (G : ℕ) := by
      rw [hqe i]; exact (abs_add_le _ _).trans (add_le_add (hΦB i) (hD i))
    rw [abs_mul, abs_of_nonneg hql0.le, ← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  rw [hout]
  refine bgvEncrypts_of_phase e ?_ ?_ ?_ ?_
  · rw [phase_map_ofInt, he]
  · intro i
    rw [← Int.natCast_natAbs]
    have : (e.coeff i).natAbs ≤ (B + t * (ql / 2) * G) / ql := by
      rw [Nat.le_div_iff_mul_le hql, mul_comm]; exact hebound i
    exact_mod_cast this
  · have h1 : (B + t * (ql / 2) * G) / ql * ql ≤ B + t * (ql / 2) * G := Nat.div_mul_le_self _ _
    have h2 : 2 * (ql / 2) ≤ ql := Nat.mul_div_le ql 2
    have h3 : 2 * (t * (ql / 2) * G) ≤ t * ql * G := by
      calc 2 * (t * (ql / 2) * G) = t * G * (2 * (ql / 2)) := by ring
        _ ≤ t * G * ql := Nat.mul_le_mul_left _ h2
        _ = t * ql * G := by ring
    have h4 : 2 * ((B + t * (ql / 2) * G) / ql) * ql < Q' * ql := by
      calc 2 * ((B + t * (ql / 2) * G) / ql) * ql = 2 * ((B + t * (ql / 2) * G) / ql * ql) := by ring
        _ ≤ 2 * (B + t * (ql / 2) * G) := Nat.mul_le_mul_left _ h1
        _ < Q' * ql := by omega
    exact Nat.lt_of_mul_lt_mul_right h4
  · ext i
    rw [coeff_smul']
    show ((e.coeff i : ℤ) : ZMod t) = _
    have hm : ((Φ.coeff i : ℤ) : ZMod t) = m.coeff i :=
      congrArg (fun p => p.coeff i) (BGVEncrypts.msg h)
    have hd0 : (((intPhase s (ca.map dl)).coeff i : ℤ) : ZMod t) = 0 :=
      congrArg (fun p => p.coeff i) (ofInt_intPhase_eq_zero t s (ca.map dl)
        (fun d' hd' => by
          obtain ⟨c, -, rfl⟩ := List.mem_map.mp hd'
          exact hdlt c))
    have h1 := congrArg (Int.cast : ℤ → ZMod t) (hqe i)
    push_cast at h1
    rw [hm, hd0, add_zero] at h1
    have hinv := ZMod.coe_mul_inv_eq_one ql hcop.symm
    linear_combination (-(e.coeff i : ZMod t)) * hinv + ((ql : ZMod t))⁻¹ * h1

/-- **B's `ModSwitchRule .centred`** (two components, GHS/OpenFHE centred correction). -/
theorem modSwitchRule_centred (N t ql Q' : ℕ) : ModSwitchRule .centred N t ql Q' := by
  intro s c0 c1 m Bs B hcop _ hql _ hs h hnw
  have hG : ((List.range [c0, c1].length).map fun i => (N * Bs) ^ i).sum = 1 + N * Bs := by
    simp [List.range_succ]
  have hnw' : 2 * B + t * ql * ((List.range [c0, c1].length).map fun i => (N * Bs) ^ i).sum
      < Q' * ql := by
    rw [hG]; simpa [msDeltaBound2, Lift.bound2] using hnw
  have key := modSwitch_centred_parts t ql Q' s [c0, c1] m Bs B hcop (by omega) hs h hnw'
  rw [hG] at key
  refine ⟨_, ?_, key⟩
  have hl : lsum ((List.range (1 + 1)).map fun i => (N * Bs) ^ i) = 1 + N * Bs := by
    rw [lsum_nat_eq_sum]; simp [List.range_succ]
  unfold modSwitchBound
  rw [hl]
  simp only [msDeltaBound2, Lift.bound2]
  have hq' : (0 : ℚ) < ql := by exact_mod_cast (by omega : 0 < ql)
  rw [le_div_iff₀ hq']
  have h1 : (B + t * (ql / 2) * (1 + N * Bs)) / ql * ql ≤ B + t * (ql / 2) * (1 + N * Bs) :=
    Nat.div_mul_le_self _ _
  have h1' : (((B + t * (ql / 2) * (1 + N * Bs)) / ql : ℕ) : ℚ) * ql ≤
      (B : ℚ) + t * ((ql / 2 : ℕ) : ℚ) * (1 + N * Bs) := by exact_mod_cast h1
  have h2 : ((ql / 2 : ℕ) : ℚ) ≤ (ql : ℚ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self ql 2
  have h3 : (t : ℚ) * ((ql / 2 : ℕ) : ℚ) * (1 + N * Bs) ≤ (t : ℚ) * ((ql : ℚ) / 2) * (1 + N * Bs) := by
    gcongr
  push_cast
  linarith

end Respec.Equiv
