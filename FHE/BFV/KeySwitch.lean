import FHE.KeySwitch.Layout
import Spec.BudgetBFV
import Validation.Budget.Basic

/-!
# FHE.BFV.KeySwitch — plain hybrid key switching from `Spec.Budget` layouts (BFV)

The BFV analogue of `FHE.KeySwitch.layoutKS`: `FHE.KeySwitch.keySwitchPlain` (centred ModUp, plain
rounding in ModDown, no `t`-correction) on the digits of a `Spec.Budget.KSLayout`, at the bases of
`SchemeParamsOK` / `SpecialOK`.

* `ksBoundAt_unit_centred`: `Spec.Budget.ksBoundAt` at `unitPlain P` with centred weights is the
  library's `ksBound` with `t = 1`;
* `ksBound_le_ksBoundAtBFV`: that bound is at most `Spec.BudgetBFV.ksBoundAt P lay ℓ`, whichever
  representatives the layout declares (the canonical bound is the larger one);
* `layoutKSPlain`, `layoutKSPlain_spec`: the algorithm on integer representatives and its contract
  at the `Spec` modulus with error at most `Spec.BudgetBFV.ksBoundAt`, from
  `Spec.Budget.GadgetKeysOK`. The algorithm always uses centred representatives.
-/

namespace FHE.BFV

open Finset Spec Spec.NPoly Spec.Scheme Spec.Source Spec.Trace FHE.RNS FHE.RNS.Basis
  Validation.Ring Validation.Scheme FHE.KeySwitch

section Params

variable (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P)

/-- The `t = 1` bound with centred weights is the library bound of `keySwitchPlain`. -/
theorem ksBoundAt_unit_centred (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    Spec.Budget.ksBoundAt (Spec.BudgetBFV.unitPlain P) ⟨lay.sizes, false⟩ ℓ =
      ksBound P.src.N P.keyNoise P.secretBound 1
        ((P.store.special.map (·.q)).length * (schemeSpecialBasis P hS).prod)
        (schemeSpecialBasis P hS).prod
        (digitWeight (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)) := by
  have hdm : Spec.Budget.digitModuli (Spec.BudgetBFV.unitPlain P) ⟨lay.sizes, false⟩ ℓ =
      List.ofFn ((layoutDigits lay ℓ hlay).basis (schemeLevelBasis P hP ℓ hℓ)).q :=
    digitModuli_eq P hP lay ℓ hℓ hlay
  have hsp : Spec.Budget.specialProd (Spec.BudgetBFV.unitPlain P) =
      (schemeSpecialBasis P hS).prod := (schemeSpecialBasis_prod P hS).symm
  unfold Spec.Budget.ksBoundAt ksBound
  rw [hdm, hsp]
  have hsum := fun w => sum_zipWith_ofFn w (lay.sizes ℓ)
    ((layoutDigits lay ℓ hlay).basis (schemeLevelBasis P hP ℓ hℓ)).q
  simp only [List.length_map, Bool.false_eq_true, ite_false]
  erw [hsum]; rfl

/-- The centred `t = 1` bound is at most the bound of the layout (equal for a centred layout,
smaller for a canonical one). -/
theorem ksBoundAt_unit_centred_le (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P)
    (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) :
    Spec.Budget.ksBoundAt (Spec.BudgetBFV.unitPlain P) ⟨lay.sizes, false⟩ ℓ ≤
      Spec.BudgetBFV.ksBoundAt P lay ℓ := by
  obtain ⟨sizes, canonical⟩ := lay
  cases canonical
  · exact le_rfl
  · have hdm : Spec.Budget.digitModuli (Spec.BudgetBFV.unitPlain P) ⟨sizes, true⟩ ℓ =
        Spec.Budget.digitModuli (Spec.BudgetBFV.unitPlain P) ⟨sizes, false⟩ ℓ := rfl
    simp only [Spec.BudgetBFV.ksBoundAt, Spec.Budget.ksBoundAt, hdm, Bool.false_eq_true,
      ite_false, ite_true]
    apply Nat.div_le_div_right
    apply Nat.add_le_add
    · apply Nat.mul_le_mul_left
      apply Validation.Budget.sum_zipWith_le
      intro n Q hQ
      apply Validation.Budget.mul_le_two_mul_pred
      simp only [Spec.Budget.digitModuli, List.mem_map, List.mem_range] at hQ
      obtain ⟨j, hj, rfl⟩ := hQ
      exact Validation.Budget.two_le_digitModulus P hP ⟨sizes, true⟩ ℓ hℓ hlay j hj
    · apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      rcases Nat.eq_zero_or_pos P.store.special.length with h0 | hpos
      · have h0' : (Spec.BudgetBFV.unitPlain P).store.special.length = 0 := h0
        rw [h0']; simp
      · apply Validation.Budget.mul_le_two_mul_pred
        unfold Spec.Budget.specialProd
        apply Validation.Budget.two_le_prod_of_ne_nil _ _ (fun p hp => (hS.1 p hp).1)
        intro h
        have := congrArg List.length h
        simp only [List.length_map, List.length_nil] at this
        omega

/-- **The library bound of `keySwitchPlain` is within the trusted BFV bound.** -/
theorem ksBound_le_ksBoundAtBFV (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    ksBound P.src.N P.keyNoise P.secretBound 1
        ((P.store.special.map (·.q)).length * (schemeSpecialBasis P hS).prod)
        (schemeSpecialBasis P hS).prod
        (digitWeight (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)) ≤
      Spec.BudgetBFV.ksBoundAt P lay ℓ := by
  rw [← ksBoundAt_unit_centred P hP hS lay ℓ hℓ hlay]
  exact ksBoundAt_unit_centred_le P hP hS lay ℓ hℓ hlay

variable [NeZero P.src.N]

/-- Plain (BFV) hybrid key switching of one component `d` (an integer representative) at
level `ℓ` with the digits of `lay`: centred ModUp and plain rounding in ModDown, whatever
`lay.canonical` says. The keys are integer representatives, one pair per digit (missing ones read
as zero). The result is the pair of centred lifts `(KS(d)₀, KS(d)₁)`. -/
noncomputable def layoutKSPlain (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  let C := schemeLevelBasis P hP ℓ hℓ
  let Bp := schemeSpecialBasis P hS
  let Dg := layoutDigits lay ℓ hlay
  let kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) P.src.N :=
    fun j => ofInt _ (keys.getD j (0, 0)).1
  let ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) P.src.N :=
    fun j => ofInt _ (keys.getD j (0, 0)).2
  let out := keySwitchPlain Dg C Bp (C.toRNS d) kb ka
  (centered (C.combine out.1), centered (C.combine out.2))

/-- **Plain hybrid key switching at a `Spec.Budget` layout.** With `SchemeParamsOK`, `SpecialOK`,
a usable layout, a secret within bound and keys meeting `Spec.Budget.GadgetKeysOK` (of any scheme
kind: only the noise bound of the keys is used):
`KS(d)₀ + KS(d)₁·s ≡ d·tgt(s) + e (mod Q_ℓ)` with `‖e‖∞ ≤ BudgetBFV.ksBoundAt P lay ℓ`. -/
theorem layoutKSPlain_spec (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) (s : IntPoly P.src.N)
    (hs : normInf s ≤ P.secretBound) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys) (d : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (layoutKSPlain P hP hS lay ℓ hℓ hlay d keys).1 +
        ofInt (P.src.modulus ℓ) (layoutKSPlain P hP hS lay ℓ hℓ hlay d keys).2 *
          ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) d * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      normInf e ≤ Spec.BudgetBFV.ksBoundAt P lay ℓ := by
  have hQ := schemeLevelBasis_prod P hP ℓ hℓ
  have hPm := schemeSpecialBasis_prod P hS
  have hcop : ∀ i, Nat.Coprime (schemeSpecialBasis P hS).prod ((schemeLevelBasis P hP ℓ hℓ).q i) :=
    fun i => Nat.coprime_prod_left_iff.mpr fun j _ =>
      hS.2.2.1 _ (List.getElem_mem _) _ (List.getElem_mem _)
  have hkey : ∀ j : Fin (layoutDigits lay ℓ hlay).dnum,
      KeyValid P.src.kind P.src.t P.keyNoise s
        (gadgetReq (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
          (schemeSpecialBasis P hS) tgt j)
        (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
          (keys.getD j (0, 0)).1)
        (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
          (keys.getD j (0, 0)).2) := by
    intro j
    obtain ⟨hlen, hv⟩ := hkeys
    have hj : (j : ℕ) < keys.length := by rw [hlen]; exact j.isLt
    have h := hv j hj
    have hg1 : keys.getD j (0, 0) = keys[(j : ℕ)] := by simp [hj]
    rw [hg1]
    exact keyValid_congr (by rw [hQ, hPm])
      (gadget_eq_gadgetFactor P hP hS lay ℓ hℓ hlay j) tgt _ _ h
  obtain ⟨y0, y1, e, hout, heq, hb⟩ :=
    keySwitchPlain_spec (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
      (schemeSpecialBasis P hS) hcop s hs tgt _ _ hkey
      ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
  refine ⟨e, ?_, hb.trans (ksBound_le_ksBoundAtBFV P hP hS lay ℓ hℓ hlay)⟩
  unfold layoutKSPlain
  exact level_transport _ hQ _ y0 y1 e d _ s hout heq

end Params

end FHE.BFV
