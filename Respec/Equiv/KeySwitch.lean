import Respec.Equiv.Decrypt
import FHE.KeySwitch.Canonical
import FHE.KeySwitch.Layout

/-!
# Respec.Equiv.KeySwitch — items 5 and 11: the RNS algorithms, limb for limb

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Bridge

A's bases are structures (`FHE.RNS.Basis`), B's are functions (`Respec.Basis k = Fin k → ℕ`):
B's basis is `C.q`. A's RNS polynomials are functions of the limb, B's a structure: `toB C a`.
A's digits are a `Digits` structure, B's a map `limb ↦ digit`: `digOf Dg` (`digOf_iff`). A's keys
are one pair of polynomials modulo `Q·P` per digit, B's are limbs: `keyOfA` takes A's per-limb
reductions `keyLimb`.

## Verdicts (PROVED, no `sorry`)

* **Item 11, fast base conversion: EQUAL.** `fastBConvZ_all_canonical` /
  `fastBConvZ_all_centred` : B's `fastBConvZ` on a whole basis is A's `fbcInt` / `fbcIntC`;
  `fastBConvZ_digit_canonical` / `_centred` : on the sub-basis of a digit it is A's `fbcInt` /
  `fbcIntC` of `Digits.sub`. Consequently B's `FastBConvSpec` (checked by B only exhaustively at
  `Q = 105`) holds **for every CRT basis** (`fastBConvSpec_canonical`, `fastBConvSpec_centred`,
  from A's `fastBConv_spec`, `fbcIntC_eq`/`two_mul_abs_fbcIntC_le`).
* **Item 5, ModUp: EQUAL** (`modUp_canonical_eq`, `modUp_centred_eq`): B's `modUp` is A's
  `modUpQCanon`/`modUpPCanon` (canonical) and `modUpQ`/`modUpP` (centred), limb for limb.
* **Item 5, the whole hybrid key switch, canonical: EQUAL** (`keySwitch_openfhe_eq`): B's
  `hybridKeySwitch .canonical (some t)` is A's `keySwitchBGVOpenFHE`, both output polynomials,
  every limb, every input, every key, every digit partition.
* **Item 5, centred: EQUAL for odd special primes** (`keySwitch_centred_eq`): B's
  `hybridKeySwitch .centred (some t)` is A's `keySwitchBGV` when every special prime is odd.
  The two centred ModDowns are written differently: A adds `t·FastBConvC([−X·t⁻¹]_P)`, B (and
  OpenFHE with `WITH_REDUCED_NOISE`) subtracts `t·FastBConvC([X·t⁻¹]_P)`. They agree exactly when
  `valMinAbs (−y) = −valMinAbs y` on every special limb, i.e. away from the tie `y = p/2`
  (`centredModDown_differs`, `centredModDown_differs'`: special modulus `P = 2`, kernel-checked,
  they differ). `Spec.Budget.SpecialOK` requires every special prime to be odd, so the
  hypothesis holds for every `SpecialOK` parameter set (`specialBasis_odd`), and
  `keySwitch_centred_eq_specialOK` is the equality at the special basis
  `FHE.KeySwitch.schemeSpecialBasis P hS`, for every ciphertext basis, digit partition, key and
  input. The witness at `P = 2` is therefore outside `SpecialOK`: it says why the oddness clause
  is there, not that A and B differ on an admitted parameter set.

**Which A variant is OpenFHE?** (source: OpenFHE v1.3.1, commit 7e2eafc,
`src/core/include/lattice/hal/default/dcrtpoly-impl.h:910-948`; re-read in v1.6.1, same code at
l.938-977, `CMakeLists.txt:95`): `ApproxSwitchCRTBasis` uses the
canonical representative `[0, qᵢ)` on the 128-bit path (l.917-936: `ModMulFastConst` output
`ConvertToInt`, accumulated in 128 bits) **and on the default fallback path** (l.946-948:
`MultAccEqNoCheck`, which multiplies the stored `[0, qᵢ)` values). The centred representative is
used only when OpenFHE is built with `WITH_REDUCED_NOISE` (l.943-945, `SwitchModulus`), an option
that is OFF by default (`CMakeLists.txt:80`). (The 128-bit branch is taken only with
`HAVE_INT128`, `NATIVEINT == 64` and OpenMP or clang without NATIVEOPT; the fallback otherwise.)
So: A's `keySwitchBGVOpenFHE` (= B's `.canonical`) is OpenFHE on every build without
`WITH_REDUCED_NOISE`; A's centred `keySwitchBGV` (= B's `.centred`) is OpenFHE built
`WITH_REDUCED_NOISE` (for odd special primes). The fallback path is also canonical unless
`WITH_REDUCED_NOISE` is set.

A's `keySwitchBGVAddDown` (canonical ModUp, ModDown *adding* `t·FastBConv([−X·t⁻¹]_P)`) has no
counterpart in B (B models OpenFHE/SEAL/Lattigo only).
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Respec Validation.Ring Validation.Scheme FHE.KeySwitch

variable {N k l : ℕ}

/-! ### Digits -/

/-- B's digit map of A's digits. -/
noncomputable def digOf (Dg : Digits k) (i : Fin k) : Fin Dg.dnum :=
  ((Equiv.ofBijective _ Dg.bij).symm i).1

theorem digOf_iff (Dg : Digits k) (i : Fin k) (j : Fin Dg.dnum) :
    digOf Dg i = j ↔ ∃ r, Dg.emb j r = i := by
  constructor
  · intro h
    have he := (Equiv.ofBijective _ Dg.bij).apply_symm_apply i
    unfold digOf at h
    revert he h
    generalize (Equiv.ofBijective _ Dg.bij).symm i = p
    obtain ⟨j', r⟩ := p
    intro hdig hrel
    have h' : j' = j := hdig
    cases h'
    exact ⟨r, hrel⟩
  · rintro ⟨r, rfl⟩
    have : (Equiv.ofBijective _ Dg.bij).symm (Dg.emb j r) = ⟨j, r⟩ :=
      (Equiv.ofBijective _ Dg.bij).symm_apply_apply ⟨j, r⟩
    unfold digOf; rw [this]

theorem digitMask_iff (Dg : Digits k) (j : Fin Dg.dnum) (i : Fin k) :
    digitMask (digOf Dg) j i = true ↔ ∃ r, Dg.emb j r = i := by
  unfold digitMask; simp only [decide_eq_true_eq]; exact digOf_iff Dg i j

theorem filter_mask (Dg : Digits k) (j : Fin Dg.dnum) :
    Finset.univ.filter (fun i => digitMask (digOf Dg) j i = true) =
      Finset.univ.image (Dg.emb j) := by
  ext i; simp [digitMask_iff]

/-- Sums over the limbs of a digit. -/
theorem sum_mask {M : Type} [AddCommMonoid M] (Dg : Digits k) (j : Fin Dg.dnum) (F : Fin k → M) :
    (∑ i, if digitMask (digOf Dg) j i = true then F i else 0) = ∑ r, F (Dg.emb j r) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, filter_mask,
    Finset.sum_image (fun a _ b _ h => Dg.emb_injective j h)]

/-- B's masked `Q̂` is A's `hat` of the digit sub-basis. -/
theorem hatM_digit (Dg : Digits k) (C : FHE.RNS.Basis k) (j : Fin Dg.dnum) (r : Fin (Dg.size j)) :
    Respec.Basis.hatM C.q (digitMask (digOf Dg) j) (Dg.emb j r) = (Dg.sub C j).hat r := by
  unfold Respec.Basis.hatM FHE.RNS.Basis.hat
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  have : Finset.univ.filter (fun i => digitMask (digOf Dg) j i = true ∧ i ≠ Dg.emb j r) =
      (Finset.univ.erase r).image (Dg.emb j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase,
      digitMask_iff, and_true]
    constructor
    · rintro ⟨⟨r', rfl⟩, h⟩
      exact ⟨r', fun h' => h (by rw [h']), rfl⟩
    · rintro ⟨r', h, rfl⟩
      exact ⟨⟨r', rfl⟩, fun h' => h (Dg.emb_injective j h')⟩
  rw [this, Finset.prod_image (fun a _ b _ h => Dg.emb_injective j h)]
  rfl

/-- B's `Q̂` on a whole basis is A's `hat`. -/
theorem hatM_all (C : FHE.RNS.Basis k) (i : Fin k) :
    Respec.Basis.hatM C.q Respec.Basis.all i = C.hat i := by
  unfold Respec.Basis.hatM FHE.RNS.Basis.hat Respec.Basis.all
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  congr 1
  ext j; simp

/-! ### Fast base conversion (item 11) -/

theorem fastBConvZ_all_canonical (C : FHE.RNS.Basis k) (x : (i : Fin k) → ZMod (C.q i)) :
    fastBConvZ .canonical C.q Respec.Basis.all x = C.fbcInt x := by
  unfold fastBConvZ FHE.RNS.Basis.fbcInt bconvY
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Respec.Basis.all, ite_true, hatM_all, Lift.rep, FHE.RNS.Basis.hatInv]

theorem fastBConvZ_all_centred (C : FHE.RNS.Basis k) (x : (i : Fin k) → ZMod (C.q i)) :
    fastBConvZ .centred C.q Respec.Basis.all x = C.fbcIntC x := by
  unfold fastBConvZ FHE.RNS.Basis.fbcIntC bconvY
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Respec.Basis.all, ite_true, hatM_all, Lift.rep, FHE.RNS.Basis.hatInv]

theorem fastBConvZ_digit_canonical (Dg : Digits k) (C : FHE.RNS.Basis k) (j : Fin Dg.dnum)
    (x : (i : Fin k) → ZMod (C.q i)) :
    fastBConvZ .canonical C.q (digitMask (digOf Dg) j) x =
      (Dg.sub C j).fbcInt (fun r => x (Dg.emb j r)) := by
  unfold fastBConvZ
  rw [sum_mask Dg j (fun i => Lift.rep .canonical (bconvY C.q (digitMask (digOf Dg) j) x i) *
    (Respec.Basis.hatM C.q (digitMask (digOf Dg) j) i : ℤ))]
  unfold FHE.RNS.Basis.fbcInt bconvY
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [hatM_digit, Lift.rep, FHE.RNS.Basis.hatInv]
  rfl

theorem fastBConvZ_digit_centred (Dg : Digits k) (C : FHE.RNS.Basis k) (j : Fin Dg.dnum)
    (x : (i : Fin k) → ZMod (C.q i)) :
    fastBConvZ .centred C.q (digitMask (digOf Dg) j) x =
      (Dg.sub C j).fbcIntC (fun r => x (Dg.emb j r)) := by
  unfold fastBConvZ
  rw [sum_mask Dg j (fun i => Lift.rep .centred (bconvY C.q (digitMask (digOf Dg) j) x i) *
    (Respec.Basis.hatM C.q (digitMask (digOf Dg) j) i : ℤ))]
  unfold FHE.RNS.Basis.fbcIntC bconvY
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [hatM_digit, Lift.rep, FHE.RNS.Basis.hatInv]
  rfl

/-- **B's `FastBConvSpec .canonical` holds for every nonempty CRT basis** (B checked `Q = 105`). -/
theorem fastBConvSpec_canonical (C : FHE.RNS.Basis k) (hk : 0 < k) (x : ℤ) :
    FastBConvSpec .canonical C.q x := by
  have hspec := C.fastBConv_spec hk C.q (toRes C.q x)
  show ∃ α : Fin k, fastBConvZ .canonical C.q Respec.Basis.all (toRes C.q x) =
    nmod x (Respec.Basis.prod C.q) + (α.val : ℤ) * (Respec.Basis.prod C.q)
  rw [fastBConvZ_all_canonical]
  obtain ⟨-, h0, h1⟩ := hspec
  refine ⟨⟨(C.fbcOverflow (toRes C.q x)).toNat, by omega⟩, ?_⟩
  have hl : ((C.lift (toRes C.q x) : ℕ) : ℤ) = x % (C.prod : ℤ) := by
    unfold FHE.RNS.Basis.lift
    rw [← C.intCast_eq_reconstruct (x := toRes C.q x) (X := x) (fun _ => rfl), ZMod.val_intCast]
  show C.fbcInt (toRes C.q x) = x % (C.prod : ℤ) + (((C.fbcOverflow (toRes C.q x)).toNat : ℕ) : ℤ) * C.prod
  rw [C.fbcInt_eq, hl, Int.toNat_of_nonneg h0]

/-- **B's `FastBConvSpec .centred` holds for every CRT basis.** -/
theorem fastBConvSpec_centred (C : FHE.RNS.Basis k) (x : ℤ) : FastBConvSpec .centred C.q x := by
  show (Respec.Basis.prod C.q : ℤ) ∣ (fastBConvZ .centred C.q Respec.Basis.all (toRes C.q x) - x) ∧
    2 * (fastBConvZ .centred C.q Respec.Basis.all (toRes C.q x)).natAbs ≤ k * Respec.Basis.prod C.q
  rw [fastBConvZ_all_centred]
  refine ⟨C.prod_dvd_fbcIntC_sub _ x (fun _ => rfl), ?_⟩
  have := C.two_mul_abs_fbcIntC_le (toRes C.q x)
  show 2 * (C.fbcIntC (toRes C.q x)).natAbs ≤ k * C.prod
  have h : ((2 * (C.fbcIntC (toRes C.q x)).natAbs : ℕ) : ℤ) ≤ ((k * C.prod : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Int.natCast_natAbs]; exact_mod_cast this
  exact_mod_cast h

/-! ### Polynomials, keys -/

/-- A's RNS polynomial as B's. -/
def toB (C : FHE.RNS.Basis k) (a : FHE.RNS.RNSPoly C N) : RnsPoly C.q N := ⟨a⟩

/-- A's keys (one pair modulo `Q·P` per digit) as B's limb-wise hybrid key. -/
def keyOfA (Dg : Digits k) (C : FHE.RNS.Basis k) (Bp : FHE.RNS.Basis l)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : HybridKey C.q Bp.q Dg.dnum N where
  bQ j := ⟨fun i => keyLimb (C.q i) (kb j)⟩
  bP j := ⟨fun i => keyLimb (Bp.q i) (kb j)⟩
  aQ j := ⟨fun i => keyLimb (C.q i) (ka j)⟩
  aP j := ⟨fun i => keyLimb (Bp.q i) (ka j)⟩

theorem psum_finRange {R : Type} [CommRing R] [NeZero N] {d : ℕ} (f : Fin d → NPoly R N) :
    psum ((List.finRange d).map f) = ∑ j, f j := by
  rw [psum_eq, Fin.sum_univ_def]
  generalize (List.finRange d).map f = L
  suffices ∀ a, L.foldl (· + ·) a = a + L.sum by simpa using this 0
  induction L with
  | nil => intro a; simp
  | cons x L ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-! ### ModUp -/

theorem modUp_canonical_eq (Dg : Digits k) (C : FHE.RNS.Basis k) (Bp : FHE.RNS.Basis l)
    (a : FHE.RNS.RNSPoly C N) (j : Fin Dg.dnum) :
    (∀ i, (modUp .canonical C.q Bp.q (digOf Dg) j (toB C a)).1.limb i = modUpQCanon Dg C a j i) ∧
    (∀ i, (modUp .canonical C.q Bp.q (digOf Dg) j (toB C a)).2.limb i = modUpPCanon Dg C Bp a j i) := by
  constructor
  · intro i
    simp only [modUp, rmk_eq, modUpQCanon]
    by_cases h : digOf Dg i = j
    · rw [if_pos h, if_pos ((digOf_iff Dg i j).mp h)]; rfl
    · rw [if_neg h, if_neg (fun h' => h ((digOf_iff Dg i j).mpr h'))]
      ext n
      simp only [bconv, force_eq, fastBConv, fastBConvZ_digit_canonical,
        FHE.RNS.Basis.fastBConvPoly, FHE.RNS.Basis.mapCoeff, FHE.RNS.Basis.fastBConv_eq_intCast]
      rfl
  · intro i
    simp only [modUp, rmk_eq, modUpPCanon]
    ext n
    simp only [bconv, force_eq, fastBConv, fastBConvZ_digit_canonical,
      FHE.RNS.Basis.fastBConvPoly, FHE.RNS.Basis.mapCoeff, FHE.RNS.Basis.fastBConv_eq_intCast]
    rfl

theorem modUp_centred_eq (Dg : Digits k) (C : FHE.RNS.Basis k) (Bp : FHE.RNS.Basis l)
    (a : FHE.RNS.RNSPoly C N) (j : Fin Dg.dnum) :
    (∀ i, (modUp .centred C.q Bp.q (digOf Dg) j (toB C a)).1.limb i = modUpQ Dg C a j i) ∧
    (∀ i, (modUp .centred C.q Bp.q (digOf Dg) j (toB C a)).2.limb i = modUpP Dg C Bp a j i) := by
  constructor
  · intro i
    simp only [modUp, rmk_eq, modUpQ]
    by_cases h : digOf Dg i = j
    · rw [if_pos h, if_pos ((digOf_iff Dg i j).mp h)]; rfl
    · rw [if_neg h, if_neg (fun h' => h ((digOf_iff Dg i j).mpr h'))]
      ext n
      simp only [bconv, force_eq, fastBConv, fastBConvZ_digit_centred,
        FHE.RNS.Basis.fastBConvCPoly, FHE.RNS.Basis.mapCoeff, FHE.RNS.Basis.fastBConvC_eq_intCast]
      rfl
  · intro i
    simp only [modUp, rmk_eq, modUpP]
    ext n
    simp only [bconv, force_eq, fastBConv, fastBConvZ_digit_centred,
      FHE.RNS.Basis.fastBConvCPoly, FHE.RNS.Basis.mapCoeff, FHE.RNS.Basis.fastBConvC_eq_intCast]
    rfl

/-! ### The whole key switch -/

/-- **Canonical (default OpenFHE) hybrid key switching: B's = A's `keySwitchBGVOpenFHE`.** -/
theorem keySwitch_openfhe_eq [NeZero N] (Dg : Digits k) (C : FHE.RNS.Basis k)
    (Bp : FHE.RNS.Basis l) (t : ℕ) (a : FHE.RNS.RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (∀ i, (hybridKeySwitch .canonical (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
        (toB C a)).1.limb i = (keySwitchBGVOpenFHE Dg C Bp t a kb ka).1 i) ∧
    (∀ i, (hybridKeySwitch .canonical (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
        (toB C a)).2.limb i = (keySwitchBGVOpenFHE Dg C Bp t a kb ka).2 i) := by
  have hQ := fun j => (modUp_canonical_eq Dg C Bp a j).1
  have hP := fun j => (modUp_canonical_eq Dg C Bp a j).2
  constructor <;> intro i <;> ext n <;>
  · simp only [hybridKeySwitch, hybridInner, hybridInnerCore, modDownOpt, modDownBGV,
      modDownBGVCore, rscaleTInv, rdot, rmk_eq, rtableGet_rtable, psmul_eq, psub_eq, coeff_smul',
      coeff_sub', keySwitchBGVOpenFHE, bgvModDownPoly, FHE.RNS.Basis.bgvModDown,
      FHE.RNS.Basis.modDownWith, FHE.RNS.Basis.coeffVec, keyOfA, innerQCanon, innerPCanon]
    simp only [bconv, force_eq, fastBConv, fastBConvZ_all_canonical,
      FHE.RNS.Basis.fastBConv_eq_intCast, psum_finRange, pmul_eq, hQ, hP]
    have e : ∀ (S : (j : Fin l) → Poly (Bp.q j) N),
        (({ limb := fun j => ((t : ℕ) : ZMod (Bp.q j))⁻¹ • S j } : RnsPoly Bp.q N).res n) =
          fun j => (S j).coeff n * ((t : ℕ) : ZMod (Bp.q j))⁻¹ := by
      intro S; funext j; simp only [RnsPoly.res, coeff_smul', mul_comm]
    rw [e]
    show (((Bp.prod : ℕ) : ZMod (C.q i)))⁻¹ * _ = _
    ring

/-- For odd moduli the centred fast base conversion is odd: `FBC_C(−y) = −FBC_C(y)`. -/
theorem fbcIntC_neg (Bp : FHE.RNS.Basis l) (hodd : ∀ j, Bp.q j % 2 = 1)
    (y : (j : Fin l) → ZMod (Bp.q j)) :
    Bp.fbcIntC (fun j => -y j) = -Bp.fbcIntC y := by
  unfold FHE.RNS.Basis.fbcIntC
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_mul, ZMod.valMinAbs_neg_of_ne_half, neg_mul]
  have := hodd j
  omega

/-- **Centred (OpenFHE `WITH_REDUCED_NOISE`) hybrid key switching: B's = A's `keySwitchBGV`,
for odd special primes.** -/
theorem keySwitch_centred_eq [NeZero N] (Dg : Digits k) (C : FHE.RNS.Basis k)
    (Bp : FHE.RNS.Basis l) (hodd : ∀ j, Bp.q j % 2 = 1) (t : ℕ) (a : FHE.RNS.RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (∀ i, (hybridKeySwitch .centred (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
        (toB C a)).1.limb i = (keySwitchBGV Dg C Bp t a kb ka).1 i) ∧
    (∀ i, (hybridKeySwitch .centred (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
        (toB C a)).2.limb i = (keySwitchBGV Dg C Bp t a kb ka).2 i) := by
  have hQ := fun j => (modUp_centred_eq Dg C Bp a j).1
  have hP := fun j => (modUp_centred_eq Dg C Bp a j).2
  constructor <;> intro i <;> ext n <;>
  · simp only [hybridKeySwitch, hybridInner, hybridInnerCore, modDownOpt, modDownBGV,
      modDownBGVCore, rscaleTInv, rdot, rmk_eq, rtableGet_rtable, psmul_eq, psub_eq, coeff_smul',
      coeff_sub', keySwitchBGV, FHE.RNS.Basis.bgvModDownCPoly, FHE.RNS.Basis.bgvModDownC,
      FHE.RNS.Basis.modDownWith, FHE.RNS.Basis.coeffVec, keyOfA, innerQ, innerP]
    simp only [bconv, force_eq, fastBConv, fastBConvZ_all_centred,
      FHE.RNS.Basis.fastBConvC_eq_intCast, psum_finRange, pmul_eq, hQ, hP]
    have e : ∀ (S : (j : Fin l) → Poly (Bp.q j) N),
        (({ limb := fun j => ((t : ℕ) : ZMod (Bp.q j))⁻¹ • S j } : RnsPoly Bp.q N).res n) =
          fun j => (S j).coeff n * ((t : ℕ) : ZMod (Bp.q j))⁻¹ := by
      intro S; funext j; simp only [RnsPoly.res, coeff_smul', mul_comm]
    rw [e]
    have e2 : ∀ (S : (j : Fin l) → Poly (Bp.q j) N),
        Bp.fbcIntC (fun j => -(S j).coeff n * ((t : ℕ) : ZMod (Bp.q j))⁻¹) =
          -Bp.fbcIntC (fun j => (S j).coeff n * ((t : ℕ) : ZMod (Bp.q j))⁻¹) := by
      intro S
      rw [← fbcIntC_neg Bp hodd]
      congr 1; funext j; ring
    rw [e2]
    show (((Bp.prod : ℕ) : ZMod (C.q i)))⁻¹ * _ = _
    push_cast
    ring

/-- Every limb of the special basis of a `SpecialOK` parameter set is odd. -/
theorem specialBasis_odd (P : FullParams) (hS : Spec.Budget.SpecialOK P)
    (j : Fin (P.store.special.map (·.q)).length) : (schemeSpecialBasis P hS).q j % 2 = 1 :=
  (hS.1 _ (List.getElem_mem j.isLt)).2

/-- **Centred hybrid key switching: B's = A's `keySwitchBGV` on every `SpecialOK` parameter
set** (special basis `schemeSpecialBasis P hS`; any ciphertext basis and digit partition). -/
theorem keySwitch_centred_eq_specialOK [NeZero N] (P : FullParams) (hS : Spec.Budget.SpecialOK P)
    (Dg : Digits k) (C : FHE.RNS.Basis k) (t : ℕ) (a : FHE.RNS.RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * (schemeSpecialBasis P hS).prod) N) :
    (∀ i, (hybridKeySwitch .centred (some t) C.q (schemeSpecialBasis P hS).q (digOf Dg)
        (keyOfA Dg C (schemeSpecialBasis P hS) kb ka) (toB C a)).1.limb i =
          (keySwitchBGV Dg C (schemeSpecialBasis P hS) t a kb ka).1 i) ∧
    (∀ i, (hybridKeySwitch .centred (some t) C.q (schemeSpecialBasis P hS).q (digOf Dg)
        (keyOfA Dg C (schemeSpecialBasis P hS) kb ka) (toB C a)).2.limb i =
          (keySwitchBGV Dg C (schemeSpecialBasis P hS) t a kb ka).2 i) :=
  keySwitch_centred_eq Dg C (schemeSpecialBasis P hS) (specialBasis_odd P hS) t a kb ka

/-- **At an even special modulus the two centred ModDowns differ.** One ciphertext limb `q = 3`,
special modulus `P = 2`, `t = 1`, input `X ≡ 1 (mod 2)`, `X ≡ 0 (mod 3)` (i.e. `X = 3`): A adds
`t·[−X·t⁻¹]_2 = valMinAbs 1 = 1` and gets `(3 + 1)/2 = 2`; B subtracts `t·[X·t⁻¹]_2 = 1` and gets
`(3 − 1)/2 = 1`. Both are exact divisions with `t ∣` the correction; they are different integers. -/
theorem centredModDown_differs :
    let xq : ZMod 3 := 0
    let xp : ZMod 2 := 1
    ((xq + (1 : ZMod 3) * ((((-xp * (1 : ZMod 2)⁻¹).valMinAbs * 1 : ℤ)) : ZMod 3)) * (2 : ZMod 3)⁻¹)
      ≠ (2 : ZMod 3)⁻¹ * (xq - (1 : ZMod 3) * ((((xp * (1 : ZMod 2)⁻¹).valMinAbs * 1 : ℤ)) : ZMod 3)) := by
  decide +kernel

/-- The same witness through the actual definitions: A's `bgvModDownC` (bases `[3]`, `[2]`) and
B's `modDownBGVZ .centred` on the integer `X = 3`. -/
theorem centredModDown_differs' :
    (FHE.RNS.Basis.ofList [3] (by decide) (by decide)).bgvModDownC
        (FHE.RNS.Basis.ofList [2] (by decide) (by decide)) 1 (fun _ => 0) (fun _ => 1) ⟨0, by decide⟩
      ≠ ((modDownBGVZ .centred 1 (![2] : Respec.Basis 1) 3 : ℤ) : ZMod 3) := by
  intro h
  have h' := congrArg (fun z : ZMod 3 => z.val) h
  revert h'
  decide +kernel

end Respec.Equiv
