import Challenge.Realize.OpenFHEBFV
import FHE.Realize.KeySwitch
import FHE.BFV.KeySwitch

/-!
# FHE.Realize.BFV — the locked BFV key-switch transcription: library form and contract

`Challenge.Realize.OpenFHEBFV` transcribes OpenFHE's BFV key switching. This file proves:

* `ksHybrid_toRNS`: HYBRID (`ksHybrid`, the BGV transcription at plaintext modulus `1`) is, limb
  for limb, `FHE.KeySwitch.keySwitchBGVOpenFHE` with `t = 1`, the function the conformance harness
  runs for BGV (`ApproxModDown` with `t = 0` and with `t = 1` compute the same thing: the
  multiplications by `t⁻¹` and `t` are the identity);
* `ksHybrid_spec`: its contract at the `Spec` modulus of the level, within the canonical
  `Spec.BudgetBFV.ksBoundAt` (`lay.canonical = true`), from `FHE.KeySwitch.keySwitchBGVOpenFHE_spec`
  at `t = 1`;
* `ksBV_spec`: BV with digit size 0, from the integer core `FHE.KeySwitch.ks_core` with `P = 1`
  (no special prime) and one limb per digit, within `Spec.BudgetBFV.ksBoundAt` (the centred bound
  is the BV bound; the canonical one is larger);
* `ksBFV_spec`: the dispatch, under `ksDeclOK?`.
-/

namespace FHE.RealizeBFV

open Finset Spec Spec.NPoly Spec.Scheme FHE.RNS FHE.RNS.Basis FHE.KeySwitch
  Validation.Ring Validation.Scheme Challenge.RealizeBFV

section Level

variable (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P) [NeZero P.src.N]
  (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)

/-! ### HYBRID -/

/-- **ModDown with `t = 1` is the transcription's ModDown at `unitPlain P`.** -/
theorem modDownUnit_eq (X : IntPoly P.src.N) :
    bgvModDownPoly (schemeLevelBasis P hP ℓ hℓ) (schemeSpecialBasis P hS) 1
        ((schemeLevelBasis P hP ℓ hℓ).toRNS X) ((schemeSpecialBasis P hS).toRNS X) =
      (schemeLevelBasis P hP ℓ hℓ).toRNS
        (Challenge.Realize.modDownBGV (Spec.BudgetBFV.unitPlain P) X) := by
  rw [FHE.Realize.modDown_eq _ _ (fun _ => Nat.coprime_one_left _)
    (FHE.Realize.special_hcop P hP hS ℓ hℓ) _ (FHE.Realize.specialMods_eq P hS) X]
  unfold Challenge.Realize.modDownBGV
  rw [schemeSpecialBasis_prod]
  rfl

/-- **HYBRID, BFV, is `keySwitchBGVOpenFHE` at `t = 1`**, limb for limb, with the keys read
modulo `Q_ℓ·P`. -/
theorem ksHybrid_toRNS (d : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    keySwitchBGVOpenFHE (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS) 1 ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
        (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2) =
      ((schemeLevelBasis P hP ℓ hℓ).toRNS (ksHybrid P lay ℓ d keys).1,
       (schemeLevelBasis P hP ℓ hℓ).toRNS (ksHybrid P lay ℓ d keys).2) := by
  unfold keySwitchBGVOpenFHE
  rw [FHE.Realize.innerQ_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).1),
    FHE.Realize.innerP_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).1),
    FHE.Realize.innerQ_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).2),
    FHE.Realize.innerP_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).2),
    modDownUnit_eq, modDownUnit_eq]
  rfl

/-- The canonical `t = 1` bound is the library bound of `keySwitchBGVOpenFHE` at `t = 1`. -/
theorem ksBoundAt_unit_canon (hc : lay.canonical = true) :
    Spec.BudgetBFV.ksBoundAt P lay ℓ =
      ksBound P.src.N P.keyNoise P.secretBound 1
        (2 * ((P.store.special.map (·.q)).length * ((schemeSpecialBasis P hS).prod - 1)))
        (schemeSpecialBasis P hS).prod
        (canonWeight (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)) := by
  have hdm : Spec.Budget.digitModuli (Spec.BudgetBFV.unitPlain P) lay ℓ =
      List.ofFn ((layoutDigits lay ℓ hlay).basis (schemeLevelBasis P hP ℓ hℓ)).q :=
    digitModuli_eq P hP lay ℓ hℓ hlay
  have hsp : Spec.Budget.specialProd (Spec.BudgetBFV.unitPlain P) =
      (schemeSpecialBasis P hS).prod := (schemeSpecialBasis_prod P hS).symm
  unfold Spec.BudgetBFV.ksBoundAt Spec.Budget.ksBoundAt ksBound
  rw [hdm, hsp, hc]
  have hsum := fun w => sum_zipWith_ofFn w (lay.sizes ℓ)
    ((layoutDigits lay ℓ hlay).basis (schemeLevelBasis P hP ℓ hℓ)).q
  simp only [List.length_map, ite_true]
  erw [hsum]; rfl

/-- The keys of `GadgetKeysOK` (any scheme kind) are valid for the library's gadget, read as
integer representatives modulo `Q_ℓ·P`. -/
theorem keys_valid (s : IntPoly P.src.N) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys)
    (j : Fin (layoutDigits lay ℓ hlay).dnum) :
    KeyValid P.src.kind P.src.t P.keyNoise s
      (gadgetReq (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS) tgt j)
      (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
        (keys.getD j (0, 0)).1)
      (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
        (keys.getD j (0, 0)).2) := by
  have hQ := schemeLevelBasis_prod P hP ℓ hℓ
  have hPm := schemeSpecialBasis_prod P hS
  obtain ⟨hlen, hv⟩ := hkeys
  have hj : (j : ℕ) < keys.length := by rw [hlen]; exact j.isLt
  have h := hv j hj
  have hg1 : keys.getD j (0, 0) = keys[(j : ℕ)] := by simp [hj]
  rw [hg1]
  exact keyValid_congr (by rw [hQ, hPm])
    (gadget_eq_gadgetFactor P hP hS lay ℓ hℓ hlay j) tgt _ _ h

include hP hS hℓ hlay in
/-- **HYBRID key switching, BFV: contract** at the `Spec` modulus of the level, within the
canonical `Spec.BudgetBFV.ksBoundAt`. -/
theorem ksHybrid_spec (hc : lay.canonical = true) (s : IntPoly P.src.N)
    (hs : normInf s ≤ P.secretBound) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys) (d : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (ksHybrid P lay ℓ d keys).1 +
        ofInt (P.src.modulus ℓ) (ksHybrid P lay ℓ d keys).2 * ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) d * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      normInf e ≤ Spec.BudgetBFV.ksBoundAt P lay ℓ := by
  have hQ := schemeLevelBasis_prod P hP ℓ hℓ
  have hkey : ∀ j : Fin (layoutDigits lay ℓ hlay).dnum,
      KeyValid .bgv 1 P.keyNoise s
        (gadgetReq (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
          (schemeSpecialBasis P hS) tgt j)
        (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
          (keys.getD j (0, 0)).1)
        (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
          (keys.getD j (0, 0)).2) := fun j =>
    ⟨(keys_valid P hP hS lay ℓ hℓ hlay s tgt keys hkeys j).1, fun _ _ => by simp⟩
  obtain ⟨y0, y1, e, hout, heq, -, hb⟩ :=
    keySwitchBGVOpenFHE_spec (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
      (schemeSpecialBasis P hS) (t := 1) (fun _ => Nat.coprime_one_left _)
      (FHE.Realize.special_hcop P hP hS ℓ hℓ) s hs tgt _ _ hkey
      ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
  refine ⟨e, ?_, hb.trans (ksBoundAt_unit_canon P hP hS lay ℓ hℓ hlay hc).ge⟩
  have h := level_transport _ hQ _ y0 y1 e d _ s hout heq
  rw [ksHybrid_toRNS P hP hS lay ℓ hℓ hlay d keys] at h
  simp only [combine_toRNS] at h
  rw [hQ, ofInt_centered, ofInt_centered] at h
  exact h

/-! ### BV -/

theorem specialProd_nil (hsp : P.store.special = []) : (schemeSpecialBasis P hS).prod = 1 := by
  rw [schemeSpecialBasis_prod]
  unfold Spec.Budget.specialProd
  rw [hsp]; rfl

theorem dnum_eq (hsz : lay.sizes ℓ = List.replicate ℓ 1) : (layoutDigits lay ℓ hlay).dnum = ℓ := by
  show (lay.sizes ℓ).length = ℓ
  rw [hsz, List.length_replicate]

theorem size_eq (hsz : lay.sizes ℓ = List.replicate ℓ 1) (j : Fin (layoutDigits lay ℓ hlay).dnum) :
    (layoutDigits lay ℓ hlay).size j = 1 := by
  show (lay.sizes ℓ)[(j : ℕ)] = 1
  simp [hsz]

theorem digitQ_eq (hsz : lay.sizes ℓ = List.replicate ℓ 1)
    (j : Fin (layoutDigits lay ℓ hlay).dnum) :
    ((layoutDigits lay ℓ hlay).basis (schemeLevelBasis P hP ℓ hℓ)).q j = P.src.qs.getD j 0 := by
  have hj : (j : ℕ) < ℓ := by
    have h := j.isLt
    have h2 : (layoutDigits lay ℓ hlay).dnum = ℓ := dnum_eq lay ℓ hlay hsz
    omega
  have h := digitsOfSizes_basis_q P.src.qs ℓ hℓ (scheme_qs_pos P hP) (scheme_qs_coprime P hP)
    (lay.sizes ℓ) (okAt_sum hlay) j
  refine h.trans ?_
  generalize (j : ℕ) = jn at hj ⊢
  rw [hsz]
  have hs1 : ((List.replicate ℓ 1).take jn).sum = jn := by
    rw [List.take_replicate, List.sum_replicate, smul_eq_mul, mul_one, min_eq_left hj.le]
  have hg : (List.replicate ℓ 1).getD jn 0 = 1 := by simp [hj]
  rw [hs1, hg]
  have hjL : jn < (P.src.qs.take ℓ).length := by rw [List.length_take]; omega
  rw [List.drop_eq_getElem_cons hjL]
  simp [List.getD_eq_getElem?_getD, List.getElem_take]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

theorem crtDigit_dvd (q : ℕ) (d : IntPoly P.src.N) (c : Fin P.src.N) :
    (q : ℤ) ∣ (crtDigit q d).coeff c - d.coeff c := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  show ((d.coeff c : ZMod q) : ZMod q) = (((d.coeff c : ZMod q)).valMinAbs : ZMod q)
  rw [ZMod.coe_valMinAbs]

theorem two_mul_normInf_crtDigit (q : ℕ) [NeZero q] (d : IntPoly P.src.N) :
    2 * normInf (crtDigit q d) ≤ q := by
  refine two_mul_normInf_le fun c => ?_
  show 2 * |((d.coeff c : ZMod q)).valMinAbs| ≤ (q : ℤ)
  have h := ZMod.natAbs_valMinAbs_le (d.coeff c : ZMod q)
  rw [Int.abs_eq_natAbs]
  have : 2 * ((d.coeff c : ZMod q)).valMinAbs.natAbs ≤ q := by omega
  exact_mod_cast this

include hP hS hℓ hlay in
/-- **BV key switching (digit size 0): contract** at the `Spec` modulus of the level, within
`Spec.BudgetBFV.ksBoundAt` (whatever `lay.canonical` says), for parameters without special
primes and a layout with one limb per digit at this level. -/
theorem ksBV_spec (hsp : P.store.special = []) (hsz : lay.sizes ℓ = List.replicate ℓ 1)
    (s : IntPoly P.src.N) (hs : normInf s ≤ P.secretBound) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys) (d : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (ksBV P ℓ d keys).1 +
        ofInt (P.src.modulus ℓ) (ksBV P ℓ d keys).2 * ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) d * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      normInf e ≤ Spec.BudgetBFV.ksBoundAt P lay ℓ := by
  set C := schemeLevelBasis P hP ℓ hℓ with hCdef
  set Bp := schemeSpecialBasis P hS with hBpdef
  set Dg := layoutDigits lay ℓ hlay with hDgdef
  have hQ : C.prod = P.src.modulus ℓ := schemeLevelBasis_prod P hP ℓ hℓ
  have hB1 : Bp.prod = 1 := specialProd_nil P hS hsp
  have hdn : Dg.dnum = ℓ := dnum_eq lay ℓ hlay hsz
  have hq : ∀ j, (Dg.basis C).q j = P.src.qs.getD j 0 := digitQ_eq P hP lay ℓ hℓ hlay hsz
  set M := C.prod * Bp.prod with hM
  let kb : Fin Dg.dnum → Poly M P.src.N := fun j => ofInt M (keys.getD j (0, 0)).1
  let ka : Fin Dg.dnum → Poly M P.src.N := fun j => ofInt M (keys.getD j (0, 0)).2
  let D : Fin Dg.dnum → IntPoly P.src.N := fun j => crtDigit (P.src.qs.getD j 0) d
  set E : Fin Dg.dnum → IntPoly P.src.N := fun j => centered (kb j + ka j * ofInt _ s -
    const ((gadget Dg C Bp.prod j : ℤ) : ZMod M) * ofInt _ (tgt.eval s)) with hE
  have hD : ∀ j c, ((Dg.basis C).q j : ℤ) ∣ (D j).coeff c - d.coeff c := fun j c => by
    rw [hq j]; exact crtDigit_dvd P _ d c
  set y0 : IntPoly P.src.N := ∑ j, D j * centered (kb j) with hy0
  set y1 : IntPoly P.src.N := ∑ j, D j * centered (ka j) with hy1
  have h0 : ∀ c, (Bp.prod : ℤ) * y0.coeff c =
      (∑ j, D j * centered (kb j)).coeff c + ((1 : ℕ) : ℤ) * (0 : IntPoly P.src.N).coeff c := by
    intro c; rw [hB1]; simp [hy0]
  have h1 : ∀ c, (Bp.prod : ℤ) * y1.coeff c =
      (∑ j, D j * centered (ka j)).coeff c + ((1 : ℕ) : ℤ) * (0 : IntPoly P.src.N).coeff c := by
    intro c; rw [hB1]; simp [hy1]
  obtain ⟨err, herr, herrc⟩ := ks_core (Q := C.prod) (t := 1) Bp.prod_pos (gadget Dg C Bp.prod) D
    (fun j => centered (kb j)) (fun j => centered (ka j)) E d (tgt.eval s) s y0 y1 0 0
    (gadget_poly Dg C Bp.prod d D hD) (fun j => key_congr Dg C Bp s tgt j (kb j) (ka j)) h0 h1
  have hkey := keys_valid P hP hS lay ℓ hℓ hlay s tgt keys hkeys
  have hDw : ∀ j, 2 * normInf (D j) ≤ digitWeight Dg C j := fun j => by
    have hqpos : 0 < P.src.qs.getD j 0 := by
      rw [← hq j]; exact (Dg.basis C).pos j
    have : NeZero (P.src.qs.getD j 0) := ⟨hqpos.ne'⟩
    unfold digitWeight
    rw [size_eq lay ℓ hlay hsz j, one_mul, hq j]
    exact two_mul_normInf_crtDigit P _ d
  have hb := ks_core_bound (P := Bp.prod) (t := 1)
    (F := (P.store.special.map (·.q)).length * Bp.prod) Bp.prod_pos D E
    (digitWeight Dg C) s 0 0 err hDw (fun j => (hkey j).1) hs (by rw [normInf_zero]; omega)
    (by rw [normInf_zero]; omega) herrc
  refine ⟨err, ?_, hb.trans (FHE.BFV.ksBound_le_ksBoundAtBFV P hP hS lay ℓ hℓ hlay)⟩
  -- the library's sums are `y0`, `y1` modulo `Q`
  have hreidx : ∀ (k : ℕ → IntPoly P.src.N) (kk : Fin Dg.dnum → Poly M P.src.N),
      (∀ j : Fin Dg.dnum, kk j = ofInt M (k j)) →
      ofInt C.prod ((List.ofFn fun i : Fin ℓ =>
          crtDigit (P.src.qs.getD i 0) d * k i).sum) =
        ofInt C.prod (∑ j, D j * centered (kk j)) := by
    intro k kk hkk
    rw [List.sum_ofFn, ofInt_sum, ofInt_sum]
    refine (Fintype.sum_equiv (finCongr hdn) _ _ fun j => ?_).symm
    rw [ofInt_mul, ofInt_mul, hkk j]
    have hdvd : C.prod ∣ M := Nat.dvd_mul_right _ _
    have hl := FHE.Realize.keyLimb_ofInt hdvd (k j)
    unfold keyLimb at hl
    rw [hl]
    rfl
  have e0 := hreidx (fun i => (keys.getD i (0, 0)).1) kb fun _ => rfl
  have e1 := hreidx (fun i => (keys.getD i (0, 0)).2) ka fun _ => rfl
  have hfin : ofInt C.prod (ksBV P ℓ d keys).1 + ofInt C.prod (ksBV P ℓ d keys).2 *
      ofInt C.prod s = ofInt C.prod d * ofInt C.prod (tgt.eval s) + ofInt C.prod err := by
    show ofInt C.prod (List.ofFn _).sum + ofInt C.prod (List.ofFn _).sum * _ = _
    rw [e0, e1, ← ofInt_mul, ← ofInt_add, herr, ofInt_add, ofInt_mul]
  rw [hQ] at hfin
  exact hfin

/-! ### The dispatch -/

omit [NeZero P.src.N] in
include hℓ in
/-- `ksDeclOK?` at a level of the chain gives the layout fact each branch needs. -/
theorem ksDeclOK_at (hdecl : ksDeclOK? P lay = true) (h1 : 1 ≤ ℓ) :
    (P.store.special = [] → lay.sizes ℓ = List.replicate ℓ 1) ∧
      (P.store.special ≠ [] → lay.canonical = true) := by
  unfold ksDeclOK? at hdecl
  by_cases hsp : P.store.special = []
  · rw [if_pos hsp] at hdecl
    refine ⟨fun _ => ?_, fun h => absurd hsp h⟩
    have := List.all_eq_true.mp hdecl (ℓ - 1) (List.mem_range.mpr (by omega))
    rw [Nat.sub_add_cancel h1] at this
    exact beq_iff_eq.mp this
  · rw [if_neg hsp] at hdecl
    exact ⟨fun h => absurd h hsp, fun _ => hdecl⟩

include hP hS hℓ hlay in
/-- **OpenFHE's BFV key switching of one component: contract** at the `Spec` modulus of the
level, within `Spec.BudgetBFV.ksBoundAt`, when the declared layout is the library's. -/
theorem ksBFV_spec (hdecl : ksDeclOK? P lay = true) (h1 : 1 ≤ ℓ) (s : IntPoly P.src.N)
    (hs : normInf s ≤ P.secretBound) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys) (d : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (ksBFV P lay ℓ d keys).1 +
        ofInt (P.src.modulus ℓ) (ksBFV P lay ℓ d keys).2 * ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) d * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      normInf e ≤ Spec.BudgetBFV.ksBoundAt P lay ℓ := by
  obtain ⟨hbv, hhy⟩ := ksDeclOK_at P lay ℓ hℓ hdecl h1
  unfold ksBFV
  by_cases hsp : P.store.special = []
  · rw [if_pos hsp]
    exact ksBV_spec P hP hS lay ℓ hℓ hlay hsp (hbv hsp) s hs tgt keys hkeys d
  · rw [if_neg hsp]
    exact ksHybrid_spec P hP hS lay ℓ hℓ hlay (hhy hsp) s hs tgt keys hkeys d

end Level

end FHE.RealizeBFV
