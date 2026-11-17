import FHE.KeySwitch.Hybrid

/-!
# FHE.KeySwitch.Canonical — hybrid key switching with canonical representatives

`FHE.KeySwitch.Hybrid` uses centred representatives in ModUp and ModDown. Libraries use
canonical ones (`[·] ∈ [0, q)`), and the two BGV ModDowns in the wild differ in sign:

| variant | ModUp | ModDown by `P` (BGV) | corresponds to |
|---|---|---|---|
| `keySwitchBGVOpenFHE` | canonical FastBConv | `(X − t·FastBConv([X·t⁻¹]_P)) / P` (`Basis.bgvModDown`) | OpenFHE on a default build (no `WITH_REDUCED_NOISE`): established, see below |
| `keySwitchBGVAddDown` | canonical FastBConv | `(X + t·FastBConv([−X·t⁻¹]_P)) / P` (`bgvModDownK`) | the opposite sign convention (`k = 1`): a source reading only |
| `keySwitchBGV` (`FHE.KeySwitch.Hybrid`) | centred FastBConv | `(X + t·FastBConvC([−X·t⁻¹]_P)) / P` | OpenFHE built `WITH_REDUCED_NOISE`, for odd special primes: a source reading only, see below |

What this rests on, row by row.

* `keySwitchBGVOpenFHE` is OpenFHE's BGV key switching on a build without the CMake option
  `WITH_REDUCED_NOISE` (off by default). Two things are established. (1) Proved: it is equal,
  limb for limb, for every input, key and digit partition, to the key switch of the independent
  re-specification (`Respec.Equiv.keySwitch_openfhe_eq` in `Respec/Equiv/KeySwitch.lean`; the
  header of that file gives the OpenFHE source lines the reading is taken from,
  `ApproxSwitchCRTBasis` in `src/core/include/lattice/hal/default/dcrtpoly-impl.h`). (2) Measured:
  the conformance harness compares it bit for bit with the outputs of OpenFHE v1.6.1's
  relinearization on recorded runs and finds them equal (`harness/openfhe-pin/algo/README.md`,
  check `algo.relin`). OpenFHE v1.6.1's rotation is not this key switch followed by the
  automorphism: it applies the automorphism between the inner product and ModDown; the check
  `algo.rotate` compares that variant (`rotateOpenFHE161` in `FHE/Pin/AlgoOpenFHE.lean`, proved
  within the same bound, `rotateOpenFHE161_spec`) and finds it bit-exact. (2) is an executed
  comparison on those runs, not a proof about OpenFHE's code.
* The centred `keySwitchBGV` corresponds to a `WITH_REDUCED_NOISE` build when every special prime
  is odd: under that hypothesis it is proved equal, limb for limb, to the centred key switch of
  the re-specification (`Respec.Equiv.keySwitch_centred_eq`), whose ModDown is written as OpenFHE
  writes it (subtracting `t·FastBConvC([X·t⁻¹]_P)`). That the re-specification's centred variant
  is what such a build computes is a reading of the source; there is no recorded run of a
  `WITH_REDUCED_NOISE` build. (`Spec.Budget.SpecialOK` requires odd special primes.)
* `keySwitchBGVAddDown`: the sign convention is a reading of one code generator's source and
  nothing more; it has no counterpart in the re-specification and no recorded comparison. (That
  generator also uses only single-limb digits and one special prime; with single-limb digits
  canonical ModUp is just reinterpretation of the stored residue, no overflow.)

Both satisfy the same correctness statement as the centred variant, with
`2‖Dⱼ‖∞ ≤ 2·ℓⱼ·(Qⱼ − 1)` (`canonWeight`) and ModDown error `2‖f‖∞ ≤ 2·k·(P − 1)`:

  `‖e‖∞ ≤ ⌊(N·B_k·Σⱼ 2ℓⱼ(Qⱼ−1) + t·2k(P−1)·(1 + N·B_s)) / (2P)⌋`.
-/

namespace FHE.KeySwitch

open Finset Spec Spec.NPoly Spec.Scheme FHE.RNS FHE.RNS.Basis Validation.Ring Validation.Scheme

variable {N ℓ k : ℕ} (Dg : Digits ℓ) (C : Basis ℓ) (Bp : Basis k)

/-! ### Canonical ModUp -/

/-- Canonical ModUp of digit `j`, ciphertext limbs (copy own limbs). -/
def modUpQCanon (a : RNSPoly C N) (j : Fin Dg.dnum) : RNSPoly C N := fun i =>
  if ∃ r, Dg.emb j r = i then a i
  else (Dg.sub C j).fastBConvPoly C.q (digitLimbs Dg C a j) i

/-- Canonical ModUp of digit `j`, special limbs. -/
def modUpPCanon (a : RNSPoly C N) (j : Fin Dg.dnum) : RNSPoly Bp N :=
  (Dg.sub C j).fastBConvPoly Bp.q (digitLimbs Dg C a j)

/-- `Mⱼ = 2·ℓⱼ·(Qⱼ − 1)` bounds `2‖ModUpⱼ(d)‖∞` (canonical ModUp). -/
def canonWeight (j : Fin Dg.dnum) : ℕ := 2 * (Dg.size j * ((Dg.basis C).q j - 1))

/-- **Canonical ModUp, exact.** The RNS form of `Dⱼ = Σᵣ [xᵣ·q̃ᵣ]·q̂ᵣ ∈ [0, ℓⱼ(Qⱼ−1)]`,
`Dⱼ ≡ d (mod Qⱼ)`. -/
theorem modUpCanon_spec (a : RNSPoly C N) (j : Fin Dg.dnum) :
    ∃ D : IntPoly N, (∀ i, modUpQCanon Dg C a j i = ofInt (C.q i) D) ∧
      (∀ i, modUpPCanon Dg C Bp a j i = ofInt (Bp.q i) D) ∧
      (∀ c, ((Dg.basis C).q j : ℤ) ∣ D.coeff c - (centered (C.combine a)).coeff c) ∧
      2 * normInf D ≤ canonWeight Dg C j := by
  set S := Dg.sub C j
  set x := digitLimbs Dg C a j
  let D : IntPoly N := ⟨fun c => S.fbcInt (S.coeffVec x c)⟩
  have hfbc : ∀ {m : ℕ} (p : Fin m → ℕ) (i : Fin m), S.fastBConvPoly p x i = ofInt (p i) D := by
    intro m p i; ext c; exact S.fastBConv_eq_intCast p _ i
  have hown : ∀ r, a (Dg.emb j r) = ofInt (C.q (Dg.emb j r)) D := by
    intro r; ext c; exact (S.fbcInt_residue (S.coeffVec x c) r).symm
  refine ⟨D, fun i => ?_, fun i => hfbc Bp.q i, fun c => ?_, ?_⟩
  · unfold modUpQCanon
    split_ifs with h
    · obtain ⟨r, rfl⟩ := h; exact hown r
    · exact hfbc C.q i
  · show (S.prod : ℤ) ∣ _
    refine S.prod_dvd_sub_of_residues fun r => ?_
    have h1 := congrArg (fun p => p.coeff c) (hown r)
    have h2 := congrArg (fun p => (p (Dg.emb j r)).coeff c) (C.toRNS_centered_combine a)
    simp only [coeff_ofInt, toRNS] at h1 h2
    exact h1.symm.trans h2.symm
  · refine two_mul_normInf_le fun c => ?_
    have h0 := S.fbcInt_nonneg (S.coeffVec x c)
    have h1 := S.fbcInt_le (S.coeffVec x c)
    have hP : 1 ≤ S.prod := S.prod_pos
    show 2 * |S.fbcInt (S.coeffVec x c)| ≤ ((2 * (Dg.size j * (S.prod - 1)) : ℕ) : ℤ)
    rw [abs_of_nonneg h0]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hP, Nat.cast_one, Nat.cast_ofNat]
    linarith

/-! ### Canonical BGV ModDowns on polynomials -/

/-- BGV ModDown, adding sign: add `t · FastBConv([−xp · t⁻¹]_P; Bp → C)` (canonical), divide by `P`.
For one special prime the correction is `delta = t·[−t⁻¹·c_p]_p`. -/
def bgvModDownK (t : ℕ) (xq : (i : Fin ℓ) → ZMod (C.q i)) (xp : (j : Fin k) → ZMod (Bp.q j)) :
    (i : Fin ℓ) → ZMod (C.q i) :=
  C.modDownWith Bp.prod xq
    (fun i => (t : ZMod (C.q i)) * Bp.fastBConv C.q (fun j => -xp j * (t : ZMod (Bp.q j))⁻¹) i)

/-- Polynomial version of `bgvModDownK`. -/
def bgvModDownKPoly (t : ℕ) (aq : RNSPoly C N) (ap : RNSPoly Bp N) : RNSPoly C N :=
  fun i => ⟨fun c => bgvModDownK C Bp t (C.coeffVec aq c) (Bp.coeffVec ap c) i⟩

/-- Polynomial version of OpenFHE's BGV ModDown `Basis.bgvModDown`. -/
def bgvModDownPoly (t : ℕ) (aq : RNSPoly C N) (ap : RNSPoly Bp N) : RNSPoly C N :=
  fun i => ⟨fun c => C.bgvModDown Bp t (C.coeffVec aq c) (Bp.coeffVec ap c) i⟩

variable {C Bp}

/-- **BGV ModDown, adding sign, exact.** `P·y = X + t·f` with `0 ≤ f ≤ k(P−1)`. -/
theorem bgvModDownKPoly_spec {t : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (X : IntPoly N) :
    ∃ y f : IntPoly N, bgvModDownKPoly C Bp t (C.toRNS X) (Bp.toRNS X) = C.toRNS y ∧
      (∀ c, (Bp.prod : ℤ) * y.coeff c = X.coeff c + t * f.coeff c) ∧
      2 * normInf f ≤ 2 * (k * (Bp.prod - 1)) := by
  have key : ∀ c : Fin N, ∃ y : ℤ,
      (∀ i, bgvModDownK C Bp t (C.coeffVec (C.toRNS X) c) (Bp.coeffVec (Bp.toRNS X) c) i =
        (y : ZMod (C.q i))) ∧
      (Bp.prod : ℤ) * y = X.coeff c + t * Bp.fbcInt
        (fun j => -Bp.coeffVec (Bp.toRNS X) c j * (t : ZMod (Bp.q j))⁻¹) := by
    intro c
    set D := Bp.fbcInt (fun j => -Bp.coeffVec (Bp.toRNS X) c j * (t : ZMod (Bp.q j))⁻¹)
    have hdiv : (Bp.prod : ℤ) ∣ X.coeff c + t * D := by
      rw [← sub_neg_eq_add]
      refine Bp.prod_dvd_sub_of (xp := Bp.coeffVec (Bp.toRNS X) c) (fun _ => rfl) fun j => ?_
      push_cast
      rw [Bp.fbcInt_residue, mul_left_comm, ZMod.coe_mul_inv_eq_one _ (ht j)]
      ring
    refine ⟨(X.coeff c + t * D) / Bp.prod, fun i => ?_, Int.mul_ediv_cancel' hdiv⟩
    exact C.modDownWith_spec hcop (fun _ => rfl)
      (fun i => by rw [Bp.fastBConv_eq_intCast]; push_cast; rfl) hdiv i
  choose y hy hq using key
  refine ⟨⟨y⟩, ⟨fun c => Bp.fbcInt (fun j => -Bp.coeffVec (Bp.toRNS X) c j *
    (t : ZMod (Bp.q j))⁻¹)⟩, ?_, hq, ?_⟩
  · funext i; ext c; exact hy c i
  · refine two_mul_normInf_le fun c => ?_
    have h0 := Bp.fbcInt_nonneg (fun j => -Bp.coeffVec (Bp.toRNS X) c j * (t : ZMod (Bp.q j))⁻¹)
    have h1 := Bp.fbcInt_le (fun j => -Bp.coeffVec (Bp.toRNS X) c j * (t : ZMod (Bp.q j))⁻¹)
    have hP : 1 ≤ Bp.prod := Bp.prod_pos
    show 2 * |Bp.fbcInt _| ≤ ((2 * (k * (Bp.prod - 1)) : ℕ) : ℤ)
    rw [abs_of_nonneg h0]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hP, Nat.cast_one, Nat.cast_ofNat]
    linarith

/-- **OpenFHE BGV ModDown, exact.** `P·y = X + t·f` with `−k(P−1) ≤ f ≤ 0`. -/
theorem bgvModDownPoly_spec {t : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (X : IntPoly N) :
    ∃ y f : IntPoly N, bgvModDownPoly C Bp t (C.toRNS X) (Bp.toRNS X) = C.toRNS y ∧
      (∀ c, (Bp.prod : ℤ) * y.coeff c = X.coeff c + t * f.coeff c) ∧
      2 * normInf f ≤ 2 * (k * (Bp.prod - 1)) := by
  have h := fun c => bgvModDown_spec ht hcop (xq := C.coeffVec (C.toRNS X) c)
    (xp := Bp.coeffVec (Bp.toRNS X) c) (X := X.coeff c) (fun _ => rfl) (fun _ => rfl)
  choose y hy hq h0 h1 _ using h
  refine ⟨⟨y⟩, ⟨fun c => -Bp.fbcInt (fun j => Bp.coeffVec (Bp.toRNS X) c j *
    (t : ZMod (Bp.q j))⁻¹)⟩, ?_, fun c => ?_, ?_⟩
  · funext i; ext c; exact hy c i
  · show _ = _ + _ * -_
    rw [hq c]; ring
  · refine two_mul_normInf_le fun c => ?_
    have hP : 1 ≤ Bp.prod := Bp.prod_pos
    show 2 * |-Bp.fbcInt _| ≤ ((2 * (k * (Bp.prod - 1)) : ℕ) : ℤ)
    rw [abs_neg, abs_of_nonneg (h0 c)]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hP, Nat.cast_one, Nat.cast_ofNat]
    linarith [h1 c]

/-! ### The two canonical algorithms and their theorems -/

variable (C Bp) [NeZero N]

/-- Inner product with canonical ModUp, ciphertext limbs. -/
def innerQCanon (a : RNSPoly C N) (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N :=
  fun i => ∑ j, modUpQCanon Dg C a j i * keyLimb (C.q i) (kb j)

/-- Inner product with canonical ModUp, special limbs. -/
def innerPCanon (a : RNSPoly C N) (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    RNSPoly Bp N :=
  fun i => ∑ j, modUpPCanon Dg C Bp a j i * keyLimb (Bp.q i) (kb j)

/-- **Hybrid key switching, BGV, OpenFHE convention.** -/
def keySwitchBGVOpenFHE (t : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (bgvModDownPoly C Bp t (innerQCanon Dg C Bp a kb) (innerPCanon Dg C Bp a kb),
   bgvModDownPoly C Bp t (innerQCanon Dg C Bp a ka) (innerPCanon Dg C Bp a ka))

/-- **Hybrid key switching, BGV, adding-sign ModDown.** -/
def keySwitchBGVAddDown (t : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (bgvModDownKPoly C Bp t (innerQCanon Dg C Bp a kb) (innerPCanon Dg C Bp a kb),
   bgvModDownKPoly C Bp t (innerQCanon Dg C Bp a ka) (innerPCanon Dg C Bp a ka))

theorem innerQCanon_eq (a : RNSPoly C N) (D : Fin Dg.dnum → IntPoly N)
    (hD : ∀ j i, modUpQCanon Dg C a j i = ofInt (C.q i) (D j))
    (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    innerQCanon Dg C Bp a kb = C.toRNS (∑ j, D j * centered (kb j)) := by
  funext i
  simp only [innerQCanon, toRNS, keyLimb, hD, ofInt_sum, ofInt_mul]

theorem innerPCanon_eq (a : RNSPoly C N) (D : Fin Dg.dnum → IntPoly N)
    (hD : ∀ j i, modUpPCanon Dg C Bp a j i = ofInt (Bp.q i) (D j))
    (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    innerPCanon Dg C Bp a kb = Bp.toRNS (∑ j, D j * centered (kb j)) := by
  funext i
  simp only [innerPCanon, toRNS, keyLimb, hD, ofInt_sum, ofInt_mul]

/-- **OpenFHE-convention BGV hybrid key switching: correctness and worst-case noise.** -/
theorem keySwitchBGVOpenFHE_spec {t Bk Bs : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (a : RNSPoly C N) :
    ∃ y0 y1 e : IntPoly N,
      keySwitchBGVOpenFHE Dg C Bp t a kb ka = (C.toRNS y0, C.toRNS y1) ∧
      ofInt C.prod (y0 + y1 * s) = ofInt C.prod (centered (C.combine a) * tgt.eval s + e) ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (2 * (k * (Bp.prod - 1))) Bp.prod (canonWeight Dg C) := by
  choose D hDQ hDP hDc hDb using modUpCanon_spec Dg C Bp a
  have hP := Bp.prod_pos
  obtain ⟨y0, f0, hy0, h0, hf0⟩ := bgvModDownPoly_spec ht hcop (∑ j, D j * centered (kb j))
  obtain ⟨y1, f1, hy1, h1, hf1⟩ := bgvModDownPoly_spec ht hcop (∑ j, D j * centered (ka j))
  set E : Fin Dg.dnum → IntPoly N := fun j => centered (kb j + ka j * ofInt _ s -
    const ((gadget Dg C Bp.prod j : ℤ) : ZMod (C.prod * Bp.prod)) * ofInt _ (tgt.eval s))
  obtain ⟨err, herr, herrc⟩ := ks_core (Q := C.prod) hP (gadget Dg C Bp.prod) D
    (fun j => centered (kb j)) (fun j => centered (ka j)) E (centered (C.combine a)) (tgt.eval s)
    s y0 y1 f0 f1 (gadget_poly Dg C Bp.prod _ D hDc)
    (fun j => key_congr Dg C Bp s tgt j (kb j) (ka j)) h0 h1
  refine ⟨y0, y1, err, ?_, herr, ?_, ?_⟩
  · simp only [keySwitchBGVOpenFHE, innerQCanon_eq Dg C Bp a D hDQ,
      innerPCanon_eq Dg C Bp a D hDP, hy0, hy1]
  · exact ks_core_dvd (Nat.coprime_prod_right_iff.mpr fun j _ => ht j) D E s f0 f1 err
      (fun j => (hkey j).2 rfl) herrc
  · exact ks_core_bound hP D E (canonWeight Dg C) s f0 f1 err hDb (fun j => (hkey j).1) hs
      hf0 hf1 herrc

/-- **Adding-sign BGV hybrid key switching: correctness and worst-case noise.** -/
theorem keySwitchBGVAddDown_spec {t Bk Bs : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (a : RNSPoly C N) :
    ∃ y0 y1 e : IntPoly N,
      keySwitchBGVAddDown Dg C Bp t a kb ka = (C.toRNS y0, C.toRNS y1) ∧
      ofInt C.prod (y0 + y1 * s) = ofInt C.prod (centered (C.combine a) * tgt.eval s + e) ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (2 * (k * (Bp.prod - 1))) Bp.prod (canonWeight Dg C) := by
  choose D hDQ hDP hDc hDb using modUpCanon_spec Dg C Bp a
  have hP := Bp.prod_pos
  obtain ⟨y0, f0, hy0, h0, hf0⟩ := bgvModDownKPoly_spec ht hcop (∑ j, D j * centered (kb j))
  obtain ⟨y1, f1, hy1, h1, hf1⟩ := bgvModDownKPoly_spec ht hcop (∑ j, D j * centered (ka j))
  set E : Fin Dg.dnum → IntPoly N := fun j => centered (kb j + ka j * ofInt _ s -
    const ((gadget Dg C Bp.prod j : ℤ) : ZMod (C.prod * Bp.prod)) * ofInt _ (tgt.eval s))
  obtain ⟨err, herr, herrc⟩ := ks_core (Q := C.prod) hP (gadget Dg C Bp.prod) D
    (fun j => centered (kb j)) (fun j => centered (ka j)) E (centered (C.combine a)) (tgt.eval s)
    s y0 y1 f0 f1 (gadget_poly Dg C Bp.prod _ D hDc)
    (fun j => key_congr Dg C Bp s tgt j (kb j) (ka j)) h0 h1
  refine ⟨y0, y1, err, ?_, herr, ?_, ?_⟩
  · simp only [keySwitchBGVAddDown, innerQCanon_eq Dg C Bp a D hDQ,
      innerPCanon_eq Dg C Bp a D hDP, hy0, hy1]
  · exact ks_core_dvd (Nat.coprime_prod_right_iff.mpr fun j _ => ht j) D E s f0 f1 err
      (fun j => (hkey j).2 rfl) herrc
  · exact ks_core_bound hP D E (canonWeight Dg C) s f0 f1 err hDb (fun j => (hkey j).1) hs
      hf0 hf1 herrc

end FHE.KeySwitch
