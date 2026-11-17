import FHE.KeySwitch.Canonical
import FHE.KeySwitch.Step
import Spec.Budget

/-!
# FHE.KeySwitch.Layout — hybrid key switching from `Spec.Budget` layouts, without `ParamsOK`

`FHE.KeySwitch.Step` runs hybrid key switching on the bases of `FHE.RNS.Params`, which need
`Spec.ParamsOK` (32-bit primes, roots of unity). The scheme-level statements of `Spec.Budget`
assume only `SchemeParamsOK` and `Spec.Budget.SpecialOK`. This file is the bridge:

* `digitsOfSizes`: the `Digits` of a list of digit sizes (consecutive limbs);
* `schemeLevelBasis`, `schemeSpecialBasis`: the bases from `SchemeParamsOK` / `SpecialOK`;
* `digitModuli_eq`, `gadget_eq_gadgetFactor`: the trusted digit moduli and gadget factor are the
  library's (`Digits.basis`, `gadget`), as integers;
* `ksBoundAt_eq`: the trusted bound is the library's `ksBound` (centred or canonical weights);
* `layoutKS`, `layoutKS_spec`: the algorithm on integer representatives (centred variant, or the
  OpenFHE canonical variant when `lay.canonical`), and its contract at the `Spec` modulus with
  error at most `Spec.Budget.ksBoundAt`, from `Spec.Budget.GadgetKeysOK`.
-/

namespace FHE.KeySwitch

open Finset Spec Spec.NPoly Spec.Scheme Spec.Source Spec.Trace FHE.RNS FHE.RNS.Basis
  Validation.Ring Validation.Scheme

/-! ### Lists -/

theorem sum_take_le_of_le (l : List ℕ) {i j : ℕ} (h : i ≤ j) :
    (l.take i).sum ≤ (l.take j).sum := by
  have e : l.take i = (l.take j).take i := by rw [List.take_take, min_eq_left h]
  have := List.sum_take_add_sum_drop (l.take j) i
  rw [e]; omega

theorem exists_digit (l : List ℕ) (i : ℕ) (hi : i < l.sum) :
    ∃ j, ∃ hj : j < l.length, (l.take j).sum ≤ i ∧ i < (l.take j).sum + l[j] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    by_cases h : i < a
    · exact ⟨0, by simp, by simp, by simpa using h⟩
    · rw [List.sum_cons] at hi
      obtain ⟨j, hj, h1, h2⟩ := ih (i - a) (by omega)
      refine ⟨j + 1, by simpa using hj, ?_, ?_⟩
      · rw [List.take_succ_cons, List.sum_cons]; omega
      · rw [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]; omega

theorem prod_take_drop_eq (l : List ℕ) (a n : ℕ) (h : a + n ≤ l.length) :
    ((l.drop a).take n).prod = ∏ r : Fin n, l[a + r.val]'(by have := r.isLt; omega) := by
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2; simp

theorem sum_zipWith_ofFn (w : ℕ → ℕ → ℕ) (sizes : List ℕ) (f : Fin sizes.length → ℕ) :
    (List.zipWith w sizes (List.ofFn f)).sum = ∑ j : Fin sizes.length, w sizes[(j : ℕ)] (f j) := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp

/-! ### Digits from a list of sizes -/

/-- Consecutive digits: digit `j` is the `sizes[j]` limbs starting at `sizes[0] + ⋯ + sizes[j-1]`. -/
def digitsOfSizes (sizes : List ℕ) (ℓ : ℕ) (h : sizes.sum = ℓ) : Digits ℓ where
  dnum := sizes.length
  size j := sizes[(j : ℕ)]
  emb j r := ⟨(sizes.take j).sum + r, by
    have h1 := List.sum_take_succ sizes j j.isLt
    have h2 := sum_take_le_of_le sizes (i := j + 1) (j := sizes.length) (by omega)
    rw [List.take_length] at h2
    have := r.isLt
    omega⟩
  bij := by
    constructor
    · rintro ⟨j, r⟩ ⟨j', r'⟩ he
      simp only [Fin.mk.injEq] at he
      have key : ∀ (a b : Fin sizes.length) (ra : Fin sizes[(a : ℕ)]) (rb : Fin sizes[(b : ℕ)]), a < b →
          (sizes.take a).sum + ra ≠ (sizes.take b).sum + rb := by
        intro a b ra rb hab
        have h1 := List.sum_take_succ sizes a a.isLt
        have h2 := sum_take_le_of_le sizes (i := a + 1) (j := b) hab
        have := ra.isLt
        have := rb.isLt
        omega
      rcases lt_trichotomy j j' with hlt | heq | hgt
      · exact absurd he (key j j' r r' hlt)
      · subst heq
        have : r = r' := Fin.ext (by omega)
        subst this; rfl
      · exact absurd he.symm (key j' j r' r hgt)
    · intro i
      subst h
      obtain ⟨j, hj, h1, h2⟩ := exists_digit sizes i i.isLt
      exact ⟨⟨⟨j, hj⟩, ⟨i - (sizes.take j).sum, by show _ < sizes[j]; omega⟩⟩,
        Fin.ext (by simp only; omega)⟩

/-- The modulus of digit `j` is the product of its slice of the modulus chain. -/
theorem digitsOfSizes_basis_q (qs : List ℕ) (ℓ : ℕ) (hℓ : ℓ ≤ qs.length)
    (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime) (sizes : List ℕ)
    (h : sizes.sum = ℓ) (j : Fin sizes.length) :
    ((digitsOfSizes sizes ℓ h).basis (Basis.take qs ℓ hℓ hpos hcop)).q j =
      (((qs.take ℓ).drop (sizes.take j).sum).take (sizes.getD j 0)).prod := by
  have hg : sizes.getD j 0 = sizes[(j : ℕ)] := by simp
  have hb : (sizes.take j).sum + sizes[(j : ℕ)] ≤ (qs.take ℓ).length := by
    have h1 := List.sum_take_succ sizes j j.isLt
    have h2 := sum_take_le_of_le sizes (i := j + 1) (j := sizes.length) (by omega)
    rw [List.take_length] at h2
    simp only [List.length_take]
    omega
  rw [hg, prod_take_drop_eq _ _ _ hb]
  show ∏ r : Fin sizes[(j : ℕ)],
    (Basis.take qs ℓ hℓ hpos hcop).q ((digitsOfSizes sizes ℓ h).emb j r) = _
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [List.getElem_take]
  rfl

/-! ### The trusted gadget factor is the library's gadget -/

theorem gadgetFactor_ofFn {n : ℕ} (B : Basis n) (Pm : ℕ) (j : Fin n) :
    Spec.Budget.gadgetFactor Pm (List.ofFn B.q) j = Pm * B.hat j * (B.hatInv j).val := by
  have hq : (List.ofFn B.q).getD j 1 = B.q j := by simp
  have hhat : ((List.ofFn B.q).eraseIdx j).prod = B.hat j := by
    have h1 := List.mul_prod_eraseIdx (l := List.ofFn B.q) (i := j) (by simp)
      (fun _ _ => Commute.all _ _)
    rw [List.prod_ofFn, List.getElem_ofFn] at h1
    exact Nat.eq_of_mul_eq_mul_left (B.pos j) (h1.trans (B.q_mul_hat j).symm)
  unfold Spec.Budget.gadgetFactor
  simp only [hhat]
  rw [hq]
  rfl

/-! ### Transport along equal moduli -/

/-- A key requirement stated with integer representatives does not depend on how its modulus and
its (integer) factor are written. -/
theorem keyValid_congr {N : ℕ} {kind : Kind} {t B : ℕ} {s : IntPoly N} {M M' : ℕ} (hM : M = M')
    {g : ℕ} {g' : ℤ} (hg : (g : ℤ) = g') (tgt : KeyTarget) (b a : IntPoly N)
    (h : KeyValid kind t B s ⟨M, const ((g : ℕ) : ZMod M), tgt⟩ (ofInt M b) (ofInt M a)) :
    KeyValid kind t B s ⟨M', const ((g' : ℤ) : ZMod M'), tgt⟩ (ofInt M' b) (ofInt M' a) := by
  subst hM; subst hg
  have e : (((g : ℤ)) : ZMod M) = (g : ZMod M) := Int.cast_natCast g
  rw [e]; exact h

/-- From the RNS statement of a key-switching theorem to the phase equation at a modulus `Q`
equal to the product of the basis. -/
theorem level_transport {N ℓ : ℕ} [NeZero N] (C : Basis ℓ) {Q : ℕ} (hQ : C.prod = Q)
    (out : RNSPoly C N × RNSPoly C N) (y0 y1 e d T s : IntPoly N)
    (hout : out = (C.toRNS y0, C.toRNS y1))
    (heq : ofInt C.prod (y0 + y1 * s) =
      ofInt C.prod (centered (C.combine (C.toRNS d)) * T + e)) :
    ofInt Q (centered (C.combine out.1)) + ofInt Q (centered (C.combine out.2)) * ofInt Q s =
      ofInt Q d * ofInt Q T + ofInt Q e := by
  subst hQ
  rw [hout, combine_toRNS, combine_toRNS]
  rw [combine_toRNS] at heq
  rw [ofInt_centered, ofInt_centered, ← ofInt_mul, ← ofInt_add, heq, ofInt_add, ofInt_mul,
    ofInt_centered]

/-! ### Bases, digits and the bound from `SchemeParamsOK`, `SpecialOK` and a layout -/

section Params

variable (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P)

theorem scheme_qs_pos (hP : SchemeParamsOK P) : ∀ q ∈ P.src.qs, 0 < q :=
  fun q hq => (hP.prime q hq).pos

theorem scheme_qs_coprime (hP : SchemeParamsOK P) : P.src.qs.Pairwise Nat.Coprime :=
  Basis.pairwise_coprime_of_prime_nodup hP.prime hP.distinct

/-- The ciphertext basis at level `ℓ`, from `SchemeParamsOK`. -/
def schemeLevelBasis (ℓ : ℕ) (h : ℓ ≤ P.src.qs.length) : Basis ℓ :=
  Basis.take P.src.qs ℓ h (scheme_qs_pos P hP) (scheme_qs_coprime P hP)

theorem schemeLevelBasis_prod (ℓ : ℕ) (h : ℓ ≤ P.src.qs.length) :
    (schemeLevelBasis P hP ℓ h).prod = P.src.modulus ℓ :=
  Basis.take_prod _ _ _ _ _

/-- The special basis, from `SpecialOK`. -/
def schemeSpecialBasis : Basis (P.store.special.map (·.q)).length :=
  Basis.ofList _ (fun q hq => by have := hS.1 q hq; omega) hS.2.1

theorem schemeSpecialBasis_prod : (schemeSpecialBasis P hS).prod = Spec.Budget.specialProd P :=
  Basis.ofList_prod _ _ _

theorem okAt_sum {lay : Spec.Budget.KSLayout} {ℓ : ℕ} (h : lay.okAt ℓ = true) :
    (lay.sizes ℓ).sum = ℓ := by
  simp [Spec.Budget.KSLayout.okAt] at h
  exact h.1

/-- The digits of a layout at a level where it is usable. -/
def layoutDigits (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hlay : lay.okAt ℓ = true) : Digits ℓ :=
  digitsOfSizes (lay.sizes ℓ) ℓ (okAt_sum hlay)

/-- The trusted digit moduli are the moduli of the library's digit basis. -/
theorem digitModuli_eq (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    Spec.Budget.digitModuli P lay ℓ =
      List.ofFn ((layoutDigits lay ℓ hlay).basis (schemeLevelBasis P hP ℓ hℓ)).q := by
  apply List.ext_getElem
  · simp [Spec.Budget.digitModuli, layoutDigits, digitsOfSizes]
  · intro i h1 h2
    have hi : i < (lay.sizes ℓ).length := by
      simpa [Spec.Budget.digitModuli] using h1
    rw [List.getElem_ofFn]
    simp only [Spec.Budget.digitModuli, List.getElem_map, List.getElem_range]
    exact (digitsOfSizes_basis_q P.src.qs ℓ hℓ (scheme_qs_pos P hP) (scheme_qs_coprime P hP)
      (lay.sizes ℓ) (okAt_sum hlay) ⟨i, hi⟩).symm

/-- **Gadget agreement**: the factor `Spec.Budget.gadgetReq` asks the keys to encrypt is the
library's gadget entry, as an integer. -/
theorem gadget_eq_gadgetFactor (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) (j : Fin (layoutDigits lay ℓ hlay).dnum) :
    ((Spec.Budget.gadgetFactor (Spec.Budget.specialProd P) (Spec.Budget.digitModuli P lay ℓ) j
        : ℕ) : ℤ) =
      gadget (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS).prod j := by
  rw [digitModuli_eq P hP lay ℓ hℓ hlay, gadgetFactor_ofFn, schemeSpecialBasis_prod]
  simp [gadget]

/-- **The trusted bound is the library bound** (centred weights, or canonical ones). -/
theorem ksBoundAt_eq (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    Spec.Budget.ksBoundAt P lay ℓ =
      if lay.canonical then
        ksBound P.src.N P.keyNoise P.secretBound P.src.t
          (2 * ((P.store.special.map (·.q)).length * ((schemeSpecialBasis P hS).prod - 1)))
          (schemeSpecialBasis P hS).prod
          (canonWeight (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ))
      else
        ksBound P.src.N P.keyNoise P.secretBound P.src.t
          ((P.store.special.map (·.q)).length * (schemeSpecialBasis P hS).prod)
          (schemeSpecialBasis P hS).prod
          (digitWeight (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)) := by
  unfold Spec.Budget.ksBoundAt ksBound
  rw [digitModuli_eq P hP lay ℓ hℓ hlay, schemeSpecialBasis_prod]
  have hsum := fun w => sum_zipWith_ofFn w (lay.sizes ℓ)
    ((layoutDigits lay ℓ hlay).basis (schemeLevelBasis P hP ℓ hℓ)).q
  simp only [List.length_map]
  cases lay.canonical
  · simp only [Bool.false_eq_true, ite_false]
    erw [hsum]; rfl
  · simp only [ite_true]
    erw [hsum]; rfl

/-! ### The algorithm on integer representatives -/

variable [NeZero P.src.N]

/-- Hybrid key switching of one component `d` (an integer representative) at level `ℓ` with the
digits of `lay`: centred ModUp/ModDown, or the canonical (OpenFHE) variant if `lay.canonical`.
The keys are integer representatives, one pair per digit (missing ones read as zero). The result
is the pair of centred lifts `(KS(d)₀, KS(d)₁)`. -/
noncomputable def layoutKS (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  let C := schemeLevelBasis P hP ℓ hℓ
  let Bp := schemeSpecialBasis P hS
  let Dg := layoutDigits lay ℓ hlay
  let kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) P.src.N :=
    fun j => ofInt _ (keys.getD j (0, 0)).1
  let ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) P.src.N :=
    fun j => ofInt _ (keys.getD j (0, 0)).2
  let out := if lay.canonical then keySwitchBGVOpenFHE Dg C Bp P.src.t (C.toRNS d) kb ka
    else keySwitchBGV Dg C Bp P.src.t (C.toRNS d) kb ka
  (centered (C.combine out.1), centered (C.combine out.2))

/-- **Hybrid key switching at a `Spec.Budget` layout.** With `SchemeParamsOK`, `SpecialOK`, a
usable layout, a secret within bound and keys meeting `Spec.Budget.GadgetKeysOK`:
`KS(d)₀ + KS(d)₁·s ≡ d·tgt(s) + e (mod Q_ℓ)` with `t ∣ e` and `‖e‖∞ ≤ ksBoundAt P lay ℓ`. -/
theorem layoutKS_spec (hk : P.src.kind = .bgv) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) (s : IntPoly P.src.N)
    (hs : normInf s ≤ P.secretBound) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys) (d : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (layoutKS P hP hS lay ℓ hℓ hlay d keys).1 +
        ofInt (P.src.modulus ℓ) (layoutKS P hP hS lay ℓ hℓ hlay d keys).2 *
          ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) d * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      (∀ c, (P.src.t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ Spec.Budget.ksBoundAt P lay ℓ := by
  have hQ := schemeLevelBasis_prod P hP ℓ hℓ
  have hPm := schemeSpecialBasis_prod P hS
  have ht : ∀ j, Nat.Coprime P.src.t ((schemeSpecialBasis P hS).q j) := fun j =>
    hS.2.2.2 _ (List.getElem_mem _)
  have hcop : ∀ i, Nat.Coprime (schemeSpecialBasis P hS).prod ((schemeLevelBasis P hP ℓ hℓ).q i) :=
    fun i => Nat.coprime_prod_left_iff.mpr fun j _ =>
      hS.2.2.1 _ (List.getElem_mem _) _ (List.getElem_mem _)
  have hkey : ∀ j : Fin (layoutDigits lay ℓ hlay).dnum,
      KeyValid .bgv P.src.t P.keyNoise s
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
    rw [hk] at h
    have hg1 : keys.getD j (0, 0) = keys[(j : ℕ)] := by simp [hj]
    rw [hg1]
    exact keyValid_congr (by rw [hQ, hPm])
      (gadget_eq_gadgetFactor P hP hS lay ℓ hℓ hlay j) tgt _ _ h
  rw [ksBoundAt_eq P hP hS lay ℓ hℓ hlay]
  unfold layoutKS
  cases hc : lay.canonical
  · obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
      keySwitchBGV_spec (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS) ht hcop s hs tgt _ _ hkey
        ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
    refine ⟨e, ?_, hdvd, by simpa using hb⟩
    simp only [Bool.false_eq_true, ite_false]
    exact level_transport _ hQ _ y0 y1 e d _ s hout heq
  · obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
      keySwitchBGVOpenFHE_spec (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS) ht hcop s hs tgt _ _ hkey
        ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
    refine ⟨e, ?_, hdvd, by simpa using hb⟩
    simp only [ite_true]
    exact level_transport _ hQ _ y0 y1 e d _ s hout heq

end Params

end FHE.KeySwitch
