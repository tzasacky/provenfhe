import Challenge.Realize.OpenFHE
import FHE.KeySwitch.Layout

/-!
# FHE.Realize.KeySwitch — the locked transcription is the library's OpenFHE key switching

`Challenge.Realize.OpenFHE` transcribes OpenFHE's BGV key switching on integer representatives,
with trusted primitives only. This file proves it equal, limb for limb, to the untrusted RNS
functions the conformance harness runs (`FHE.KeySwitch.keySwitchBGVOpenFHE`, and through it
`FHE.Pin.Algo.relinOpenFHE`), on the bases built from `SchemeParamsOK` and `SpecialOK`
(`FHE.KeySwitch.schemeLevelBasis`, `schemeSpecialBasis`) with the digits of the layout
(`layoutDigits`):

* `fbc_ofFn`: the transcription's fast base conversion is `Basis.fbcInt`;
* `digitMods_eq`, `specialMods_eq`: its moduli lists are those of the library's bases;
* `modUpQ_eq`, `modUpP_eq`: canonical ModUp is the RNS form of `modUpDigit`;
* `modDown_eq`: OpenFHE's BGV ModDown of the RNS form of `X` is the RNS form of `modDownBGV X`;
* `ksOpenFHE_toRNS`: the key switch, with keys read modulo `Q_ℓ·P`;
* `ksOpenFHE_ofInt`: the same at the `Spec` modulus, as `layoutKS` (canonical).
-/

namespace FHE.Realize

open Finset Spec Spec.NPoly Spec.Scheme FHE.RNS FHE.RNS.Basis FHE.KeySwitch
  Validation.Ring Validation.Scheme

/-! ### Fast base conversion -/

theorem hat_ofFn {n : ℕ} (B : Basis n) (i : Fin n) :
    ((List.ofFn B.q).eraseIdx i).prod = B.hat i := by
  have h1 := List.mul_prod_eraseIdx (l := List.ofFn B.q) (i := i) (by simp)
    (fun _ _ => Commute.all _ _)
  rw [List.prod_ofFn, List.getElem_ofFn] at h1
  exact Nat.eq_of_mul_eq_mul_left (B.pos i) (h1.trans (B.q_mul_hat i).symm)

theorem fbc_term {m q H Hb : ℕ} (hm : m = q) (hH : H = Hb) (x : (m : ℕ) → ZMod m) :
    ((x m * ((H : ℕ) : ZMod m)⁻¹).val : ℤ) * (H : ℕ) =
      ((x q * ((Hb : ℕ) : ZMod q)⁻¹).val : ℤ) * (Hb : ℕ) := by
  subst hm; subst hH; rfl

/-- The transcription's fast base conversion from the moduli of a basis is `Basis.fbcInt`. -/
theorem fbc_ofFn {n : ℕ} (B : Basis n) (x : (m : ℕ) → ZMod m) :
    Challenge.Realize.fbc (List.ofFn B.q) x = B.fbcInt (fun i => x (B.q i)) := by
  unfold Challenge.Realize.fbc fbcInt
  refine Fintype.sum_equiv (finCongr (List.length_ofFn)) _ _ fun i => ?_
  have hq : (List.ofFn B.q)[(i : ℕ)] = B.q (finCongr List.length_ofFn i) := by simp; rfl
  have hh : ((List.ofFn B.q).eraseIdx i).prod = B.hat (finCongr List.length_ofFn i) :=
    hat_ofFn B (finCongr List.length_ofFn i)
  exact fbc_term (m := (List.ofFn B.q)[i]) hq hh x

/-! ### The moduli lists -/

variable (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P)

theorem specialMods_eq :
    Challenge.Realize.specialMods P = List.ofFn (schemeSpecialBasis P hS).q := by
  unfold Challenge.Realize.specialMods
  simp [schemeSpecialBasis, Basis.ofList]

theorem digitMods_eq (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) (j : Fin (layoutDigits lay ℓ hlay).dnum) :
    Challenge.Realize.digitMods P lay ℓ j =
      List.ofFn ((layoutDigits lay ℓ hlay).sub (schemeLevelBasis P hP ℓ hℓ) j).q := by
  have hsum := okAt_sum hlay
  have hj : (j : ℕ) < (lay.sizes ℓ).length := j.isLt
  have hb : ((lay.sizes ℓ).take j).sum + (lay.sizes ℓ)[(j : ℕ)] ≤ ℓ := by
    have h1 := List.sum_take_succ (lay.sizes ℓ) j hj
    have h2 := sum_take_le_of_le (lay.sizes ℓ) (i := j + 1) (j := (lay.sizes ℓ).length) (by omega)
    rw [List.take_length] at h2
    omega
  have hg : (lay.sizes ℓ).getD j 0 = (lay.sizes ℓ)[(j : ℕ)] := by simp [hj]
  unfold Challenge.Realize.digitMods
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn,
      hg]
    show _ = (lay.sizes ℓ)[(j : ℕ)]
    omega
  · intro r h1 h2
    simp only [List.getElem_take, List.getElem_drop,
      List.getElem_ofFn]
    rfl


/-! ### ModUp, ModDown, keys -/

section RNS

variable {N : ℕ}

/-- **Canonical ModUp is the RNS form of `modUpDigit`'s integer** (ciphertext limbs and special
limbs), for any list of moduli equal to those of the digit's basis. -/
theorem modUp_eq {ℓ k : ℕ} (Dg : Digits ℓ) (C : Basis ℓ) (Bp : Basis k) (d : IntPoly N)
    (j : Fin Dg.dnum) (ms : List ℕ) (hms : ms = List.ofFn (Dg.sub C j).q) :
    modUpQCanon Dg C (C.toRNS d) j =
        C.toRNS ⟨fun c => Challenge.Realize.fbc ms (fun m => (d.coeff c : ZMod m))⟩ ∧
      modUpPCanon Dg C Bp (C.toRNS d) j =
        Bp.toRNS ⟨fun c => Challenge.Realize.fbc ms (fun m => (d.coeff c : ZMod m))⟩ := by
  subst hms
  simp only [fbc_ofFn]
  set S := Dg.sub C j
  set x := digitLimbs Dg C (C.toRNS d) j
  have hx : ∀ c, (fun r => (d.coeff c : ZMod (S.q r))) = S.coeffVec x c := fun c => rfl
  refine ⟨?_, ?_⟩
  · funext i; ext c
    unfold modUpQCanon
    split_ifs with h
    · obtain ⟨r, rfl⟩ := h
      show (d.coeff c : ZMod (C.q (Dg.emb j r))) = ((S.fbcInt _ : ℤ) : ZMod (C.q (Dg.emb j r)))
      rw [hx c]
      exact (S.fbcInt_residue (S.coeffVec x c) r).symm
    · show S.fastBConv C.q (S.coeffVec x c) i = _
      rw [S.fastBConv_eq_intCast, ← hx c]; rfl
  · funext i; ext c
    show S.fastBConv Bp.q (S.coeffVec x c) i = _
    rw [S.fastBConv_eq_intCast, ← hx c]; rfl

/-- **OpenFHE's BGV ModDown of the RNS form of `X`** is the RNS form of
`(X − t·fbc([X·t⁻¹]_P)) / P`, for any list of special moduli equal to those of `Bp`. -/
theorem modDown_eq {ℓ k : ℕ} (C : Basis ℓ) (Bp : Basis k) {t : ℕ}
    (ht : ∀ j, Nat.Coprime t (Bp.q j)) (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i))
    (ps : List ℕ) (hps : ps = List.ofFn Bp.q) (X : IntPoly N) :
    bgvModDownPoly C Bp t (C.toRNS X) (Bp.toRNS X) =
      C.toRNS ⟨fun c => (X.coeff c - (t : ℤ) *
        Challenge.Realize.fbc ps (fun p => (X.coeff c : ZMod p) * (t : ZMod p)⁻¹)) /
          (Bp.prod : ℤ)⟩ := by
  subst hps
  funext i; ext c
  obtain ⟨y, hy, hq, -, -, -⟩ := bgvModDown_spec ht hcop (xq := C.coeffVec (C.toRNS X) c)
    (xp := Bp.coeffVec (Bp.toRNS X) c) (X := X.coeff c) (fun _ => rfl) (fun _ => rfl)
  have hP : (0 : ℤ) < Bp.prod := by exact_mod_cast Bp.prod_pos
  show C.bgvModDown Bp t _ _ i = (((X.coeff c - (t : ℤ) * _) / (Bp.prod : ℤ) : ℤ) : ZMod (C.q i))
  rw [hy i, fbc_ofFn]
  congr 1
  rw [← Int.mul_ediv_cancel_left y hP.ne', hq]
  rfl

/-- A key component stored modulo `M`, read modulo a divisor `q` of `M`. -/
theorem keyLimb_ofInt {M q : ℕ} (hq : q ∣ M) (k : IntPoly N) :
    keyLimb q (ofInt M k) = ofInt q k := by
  ext c
  show ((((k.coeff c : ZMod M)).valMinAbs : ℤ) : ZMod q) = (k.coeff c : ZMod q)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h1 : (M : ℤ) ∣ k.coeff c - ((k.coeff c : ZMod M)).valMinAbs := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.coe_valMinAbs]
  exact (Int.natCast_dvd_natCast.mpr hq).trans h1

end RNS

/-! ### The key switch at a `Spec` level -/

section Level

variable (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P) [NeZero P.src.N]
  (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)

theorem modUpDigit_eq (d : IntPoly P.src.N) (j : Fin (layoutDigits lay ℓ hlay).dnum) :
    modUpQCanon (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        ((schemeLevelBasis P hP ℓ hℓ).toRNS d) j =
      (schemeLevelBasis P hP ℓ hℓ).toRNS (Challenge.Realize.modUpDigit P lay ℓ d j) ∧
    modUpPCanon (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ) (schemeSpecialBasis P hS)
        ((schemeLevelBasis P hP ℓ hℓ).toRNS d) j =
      (schemeSpecialBasis P hS).toRNS (Challenge.Realize.modUpDigit P lay ℓ d j) :=
  modUp_eq _ _ _ d j _ (digitMods_eq P hP lay ℓ hℓ hlay j)

/-- The inner product with keys stored modulo `Q_ℓ·P`, on any modulus dividing `Q_ℓ·P`. -/
theorem ofInt_inner_eq (d : IntPoly P.src.N) (k : ℕ → IntPoly P.src.N) (q : ℕ)
    (hq : q ∣ (schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod) :
    ofInt q (∑ j : Fin (layoutDigits lay ℓ hlay).dnum,
        Challenge.Realize.modUpDigit P lay ℓ d j *
          centered (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
            (k j))) =
      ofInt q (Challenge.Realize.innerKey P lay ℓ d k) := by
  unfold Challenge.Realize.innerKey
  rw [List.sum_ofFn, ofInt_sum, ofInt_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ofInt_mul, ofInt_mul]
  congr 1
  exact keyLimb_ofInt hq (k j)

theorem innerQ_eq (d : IntPoly P.src.N) (k : ℕ → IntPoly P.src.N) :
    innerQCanon (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ) (schemeSpecialBasis P hS)
        ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
        (fun j => ofInt _ (k j)) =
      (schemeLevelBasis P hP ℓ hℓ).toRNS (Challenge.Realize.innerKey P lay ℓ d k) := by
  rw [innerQCanon_eq _ _ _ _ (fun j => Challenge.Realize.modUpDigit P lay ℓ d j)
    (fun j i => by rw [(modUpDigit_eq P hP hS lay ℓ hℓ hlay d j).1]; rfl)]
  funext i
  exact ofInt_inner_eq P hP hS lay ℓ hℓ hlay d k _
    (Nat.dvd_trans ((schemeLevelBasis P hP ℓ hℓ).q_dvd_prod i) (Nat.dvd_mul_right _ _))

theorem innerP_eq (d : IntPoly P.src.N) (k : ℕ → IntPoly P.src.N) :
    innerPCanon (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ) (schemeSpecialBasis P hS)
        ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
        (fun j => ofInt _ (k j)) =
      (schemeSpecialBasis P hS).toRNS (Challenge.Realize.innerKey P lay ℓ d k) := by
  rw [innerPCanon_eq _ _ _ _ (fun j => Challenge.Realize.modUpDigit P lay ℓ d j)
    (fun j i => by rw [(modUpDigit_eq P hP hS lay ℓ hℓ hlay d j).2]; rfl)]
  funext i
  exact ofInt_inner_eq P hP hS lay ℓ hℓ hlay d k _
    (Nat.dvd_trans ((schemeSpecialBasis P hS).q_dvd_prod i) (Nat.dvd_mul_left _ _))

theorem special_ht : ∀ j, Nat.Coprime P.src.t ((schemeSpecialBasis P hS).q j) := fun j =>
  hS.2.2.2 _ (List.getElem_mem _)

theorem special_hcop : ∀ i, Nat.Coprime (schemeSpecialBasis P hS).prod
    ((schemeLevelBasis P hP ℓ hℓ).q i) :=
  fun i => Nat.coprime_prod_left_iff.mpr fun j _ =>
    hS.2.2.1 _ (List.getElem_mem _) _ (List.getElem_mem _)

/-- **The transcription's ModDown is OpenFHE's BGV ModDown**, limb for limb. -/
theorem modDownBGV_eq (X : IntPoly P.src.N) :
    bgvModDownPoly (schemeLevelBasis P hP ℓ hℓ) (schemeSpecialBasis P hS) P.src.t
        ((schemeLevelBasis P hP ℓ hℓ).toRNS X) ((schemeSpecialBasis P hS).toRNS X) =
      (schemeLevelBasis P hP ℓ hℓ).toRNS (Challenge.Realize.modDownBGV P X) := by
  rw [modDown_eq _ _ (special_ht P hS) (special_hcop P hP hS ℓ hℓ) _ (specialMods_eq P hS) X]
  unfold Challenge.Realize.modDownBGV
  rw [schemeSpecialBasis_prod]

/-- **The transcription's key switch is `keySwitchBGVOpenFHE`**, limb for limb: on the RNS form
of `d`, with the keys read modulo `Q_ℓ·P`, the library function returns the RNS form of
`ksOpenFHE P lay ℓ d keys`. -/
theorem ksOpenFHE_toRNS (d : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    keySwitchBGVOpenFHE (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS) P.src.t ((schemeLevelBasis P hP ℓ hℓ).toRNS d)
        (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2) =
      ((schemeLevelBasis P hP ℓ hℓ).toRNS (Challenge.Realize.ksOpenFHE P lay ℓ d keys).1,
       (schemeLevelBasis P hP ℓ hℓ).toRNS (Challenge.Realize.ksOpenFHE P lay ℓ d keys).2) := by
  unfold keySwitchBGVOpenFHE Challenge.Realize.ksOpenFHE
  rw [innerQ_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).1),
    innerP_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).1),
    innerQ_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).2),
    innerP_eq P hP hS lay ℓ hℓ hlay d (fun j => (keys.getD j (0, 0)).2),
    modDownBGV_eq, modDownBGV_eq]

/-- At the `Spec` modulus of the level, the transcription is `layoutKS` with canonical
representatives. -/
theorem ksOpenFHE_ofInt (hc : lay.canonical = true) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ofInt (P.src.modulus ℓ) (Challenge.Realize.ksOpenFHE P lay ℓ d keys).1 =
        ofInt (P.src.modulus ℓ) (layoutKS P hP hS lay ℓ hℓ hlay d keys).1 ∧
      ofInt (P.src.modulus ℓ) (Challenge.Realize.ksOpenFHE P lay ℓ d keys).2 =
        ofInt (P.src.modulus ℓ) (layoutKS P hP hS lay ℓ hℓ hlay d keys).2 := by
  have h := ksOpenFHE_toRNS P hP hS lay ℓ hℓ hlay d keys
  have hQ := schemeLevelBasis_prod P hP ℓ hℓ
  unfold layoutKS
  simp only [hc, ite_true, h, combine_toRNS]
  rw [← hQ, ofInt_centered, ofInt_centered]
  exact ⟨rfl, rfl⟩

end Level

/-- **The transcription's key switch: correctness and worst-case noise** at the `Spec` modulus of
the level, within the canonical `ksBoundAt`. -/
theorem ksOpenFHE_spec (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P)
    [NeZero P.src.N] (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) (hk : P.src.kind = .bgv) (hc : lay.canonical = true)
    (s : IntPoly P.src.N) (hs : normInf s ≤ P.secretBound) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys) (d : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (Challenge.Realize.ksOpenFHE P lay ℓ d keys).1 +
        ofInt (P.src.modulus ℓ) (Challenge.Realize.ksOpenFHE P lay ℓ d keys).2 *
          ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) d * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      (∀ c, (P.src.t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ Spec.Budget.ksBoundAt P lay ℓ := by
  obtain ⟨h1, h2⟩ := ksOpenFHE_ofInt P hP hS lay ℓ hℓ hlay hc d keys
  rw [h1, h2]
  exact layoutKS_spec P hP hS hk lay ℓ hℓ hlay s hs tgt keys hkeys d


end FHE.Realize
