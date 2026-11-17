import FHE.Pin.Force
import FHE.KeySwitch.Canonical

/-!
# FHE.Pin.AlgoStage — staged (memoised) execution of the proved RNS algorithms, with equality proofs
(UNTRUSTED glue; the theorems are kernel-checked)

The proved algorithms of `FHE/RNS` and `FHE/KeySwitch` are written over functions
(`RNSPoly C N = (i : Fin ℓ) → Poly (C.q i) N`), and nothing is memoised: calling
`keySwitchBGVOpenFHE` on real sizes recomputes ModUp inside every coefficient of every product.
This module runs the **same stage functions** on arrays, forcing every intermediate result:

* `forceFam K p a` evaluates every coefficient of every limb of `a` once (canonical residues, as
  integers); `ofFam p arr` wraps such arrays as a family; `ofFam_forceFam : ofFam p (forceFam K p a) = a`.
* `Stages` bundles the three stage functions of a hybrid key switch (ModUp to the ciphertext
  limbs, ModUp to the special limbs, ModDown); `ksPipe S` is their composition, and
  `ksPipe_openfhe`, `ksPipe_centred`, `ksPipe_addDown` say (by `rfl`) that for the stage functions
  of the three proved variants it **is** `keySwitchBGVOpenFHE`, `keySwitchBGV`, `keySwitchBGVAddDown`.
* `ksStaged S K a kb ka` computes `ksPipe S a kb ka` stage by stage, forcing the ModUp of every
  digit, every key limb, the four inner products and the two ModDowns; `ksStaged_eq` proves the
  result equal to `ksPipe S a kb ka`. No stage is re-implemented: `ksStaged` only applies the
  fields of `S`, the trusted `*`/`∑` of `Spec.NPoly` and `keyLimb`.

So `ofFam (ksStaged (openfheStages …) …) = keySwitchBGVOpenFHE …` is a theorem
(`ksStaged_openfhe`), not a test.
-/

namespace FHE.Pin.Algo
open Spec Spec.NPoly FHE.RNS FHE.RNS.Basis FHE.KeySwitch FHE.Pin Validation.Ring Validation.Scheme

variable {N : ℕ}

/-! ## Arrays ↔ families of limbs -/

theorem getElem!_ofFn {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Array.ofFn f)[i.val]! = f i := by
  rw [getElem!_pos _ _ (by simp)]; simp

/-- Wrap arrays of integers (one per limb) as a family of polynomials, limb `i` modulo `p i`. -/
def ofFam {m : ℕ} (p : Fin m → ℕ) (arr : Array (Array ℤ)) : (i : Fin m) → Poly (p i) N :=
  fun i => ofInt (p i) (ofArr arr[i.val]!)

/-- Evaluate every coefficient of every limb once (`K` tasks per limb); the result holds the
representatives `ZMod.cast` (canonical residues in `[0, p i)` when `p i > 0`). -/
def forceFam {m : ℕ} (K : ℕ) (p : Fin m → ℕ) (a : (i : Fin m) → Poly (p i) N) : Array (Array ℤ) :=
  Array.ofFn fun i : Fin m => toArr K (NPoly.map (ZMod.cast : ZMod (p i) → ℤ) (a i))

@[simp] theorem ofFam_forceFam {m : ℕ} (K : ℕ) (p : Fin m → ℕ) (a : (i : Fin m) → Poly (p i) N) :
    ofFam p (forceFam K p a) = a := by
  funext i
  ext c
  simp only [ofFam, forceFam, getElem!_ofFn, ofArr_toArr]
  show ((ZMod.cast ((a i).coeff c) : ℤ) : ZMod (p i)) = (a i).coeff c
  exact ZMod.intCast_zmod_cast _

/-- One limb of the automorphism `X ↦ X^g`, by the linear-time scatter `Kron.autoArr`, as the
canonical residues (an array: see `FHE.Pin.mulArr`). -/
def autoLimb {q : ℕ} (g : ℕ) (x : Poly q N) : Array ℤ :=
  (Kron.autoArr g x).map fun z : ZMod q => (ZMod.cast z : ℤ)

/-- `forceFam` of the family `i ↦ automorph g (a i)`, limb by limb with `autoLimb`. -/
def autoFam {m : ℕ} (p : Fin m → ℕ) (g : ℕ) (a : (i : Fin m) → Poly (p i) N) : Array (Array ℤ) :=
  Array.ofFn fun i : Fin m => autoLimb g (a i)

theorem ofInt_ofArr_autoLimb {q : ℕ} (g : ℕ) (x : Poly q N) :
    ofInt q (ofArr (N := N) (autoLimb g x)) = automorph g x := by
  rw [← Kron.autoL_eq]
  ext k
  have hs := (Kron.autoArr_prefix g x N).1
  simp only [ofInt, ofArr, autoLimb, Kron.autoL, Kron.ofArrD, Kron.autoArr] at hs ⊢
  rw [getElem!_pos _ _ (by simp [hs]), Array.getElem_map, Array.getD, dif_pos (by simp [hs])]
  exact ZMod.intCast_zmod_cast _

@[simp] theorem ofFam_autoFam {m : ℕ} (p : Fin m → ℕ) (g : ℕ) (a : (i : Fin m) → Poly (p i) N) :
    ofFam p (autoFam p g a) = fun i => automorph g (a i) := by
  funext i
  simp only [ofFam, autoFam, getElem!_ofFn, ofInt_ofArr_autoLimb]

/-! ## The stages of a hybrid key switch -/

/-- The stage functions of one hybrid key switch. -/
structure Stages {ℓ k : ℕ} (Dg : Digits ℓ) (C : Basis ℓ) (Bp : Basis k) (N : ℕ) where
  /-- ModUp of digit `j`, ciphertext limbs. -/
  upQ : RNSPoly C N → Fin Dg.dnum → RNSPoly C N
  /-- ModUp of digit `j`, special limbs. -/
  upP : RNSPoly C N → Fin Dg.dnum → RNSPoly Bp N
  /-- ModDown by `P`. -/
  down : RNSPoly C N → RNSPoly Bp N → RNSPoly C N

variable {ℓ k : ℕ} (Dg : Digits ℓ) (C : Basis ℓ) (Bp : Basis k)

/-- The stages of `keySwitchBGVOpenFHE`: canonical ModUp, OpenFHE's BGV ModDown. -/
def openfheStages (t : ℕ) : Stages Dg C Bp N :=
  ⟨modUpQCanon Dg C, modUpPCanon Dg C Bp, bgvModDownPoly C Bp t⟩

/-- The stages of `keySwitchBGV`: centred ModUp, centred BGV ModDown. -/
def centredStages (t : ℕ) : Stages Dg C Bp N :=
  ⟨modUpQ Dg C, modUpP Dg C Bp, C.bgvModDownCPoly Bp t⟩

/-- The stages of `keySwitchBGVAddDown`: canonical ModUp, the adding-sign BGV ModDown. -/
def addDownStages (t : ℕ) : Stages Dg C Bp N :=
  ⟨modUpQCanon Dg C, modUpPCanon Dg C Bp, bgvModDownKPoly C Bp t⟩

variable {Dg C Bp} [NeZero N]

/-- ModUp per digit, inner product with the key over `C ∪ Bp`, ModDown: the shape shared by
every variant in `FHE/KeySwitch`. -/
def ksPipe (S : Stages Dg C Bp N) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (S.down (fun i => ∑ j, S.upQ a j i * keyLimb (C.q i) (kb j))
          (fun i => ∑ j, S.upP a j i * keyLimb (Bp.q i) (kb j)),
   S.down (fun i => ∑ j, S.upQ a j i * keyLimb (C.q i) (ka j))
          (fun i => ∑ j, S.upP a j i * keyLimb (Bp.q i) (ka j)))

theorem ksPipe_openfhe (t : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    ksPipe (openfheStages Dg C Bp t) a kb ka = keySwitchBGVOpenFHE Dg C Bp t a kb ka := rfl

theorem ksPipe_centred (t : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    ksPipe (centredStages Dg C Bp t) a kb ka = keySwitchBGV Dg C Bp t a kb ka := rfl

theorem ksPipe_addDown (t : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    ksPipe (addDownStages Dg C Bp t) a kb ka = keySwitchBGVAddDown Dg C Bp t a kb ka := rfl

/-- One limb of `innerZ`: `Σ_j U[j][i]·Kk[j][i]` over the integer representatives, every product
an array (`Kron.mulNeg`, Kronecker substitution) and the sum accumulated as arrays, then the
canonical residues modulo `q`. (Computed as arrays: an `NPoly`-valued family would be re-evaluated
by the compiled code for every coefficient; see `FHE.Pin.mulArr`.) -/
def innerLimb (N K q dn i : ℕ) (U Kk : Array (Array (Array ℤ))) : Array ℤ :=
  let acc : Array ℤ := (List.range dn).foldl
    (fun acc j => addArr N acc (Kron.mulNeg N (U[j]!)[i]! (Kk[j]!)[i]!)) (Array.replicate N 0)
  toArr K (NPoly.map (ZMod.cast : ZMod q → ℤ) (ofInt q (ofArr (N := N) acc)))

/-- Inner product of forced ModUp digits `U[j][i]` with forced key limbs `Kk[j][i]`: for every
limb `i`, the trusted negacyclic products and sum are taken on the integer representatives (the
arrays) and then reduced modulo `p i`, which is the sum of products in `Poly (p i) N`
(`ofFam_innerZ`, by `Kron.mulNeg_eq`, `ofInt_sum`, `ofInt_mul`). -/
def innerZ {m : ℕ} (K : ℕ) (p : Fin m → ℕ) (dn : ℕ) (U Kk : Array (Array (Array ℤ))) :
    Array (Array ℤ) :=
  Array.ofFn fun i : Fin m => innerLimb N K (p i) dn i.val U Kk

theorem ofFam_innerZ {m : ℕ} (K : ℕ) (p : Fin m → ℕ) (dn : ℕ) (U Kk : Array (Array (Array ℤ))) :
    ofFam (N := N) p (innerZ (N := N) K p dn U Kk) =
      fun i => ∑ j : Fin dn, ofFam (N := N) p U[j.val]! i * ofFam (N := N) p Kk[j.val]! i := by
  funext i
  simp only [ofFam, innerZ, getElem!_ofFn, innerLimb, ofArr_toArr, Kron.ofInt_map_cast]
  rw [ofArr_foldl_addArr, ← Fin.sum_univ_eq_sum_range (fun j => ofArr (N := N)
    (Kron.mulNeg N (U[j]!)[i.val]! (Kk[j]!)[i.val]!)) dn, ofInt_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ofInt_mul]
  congr 1
  exact Kron.mulNeg_eq N _ _

/-- **Staged key switch.** Every intermediate result is forced into arrays:
ModUp of each digit (`UQ`, `UP`), the key limbs (`KbQ`, `KbP`, `KaQ`, `KaP`), the four inner
products, and the two ModDowns. Returns the canonical residues of `(c₀', c₁')`, limb by limb. -/
def ksStaged (S : Stages Dg C Bp N) (K : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : Array (Array ℤ) × Array (Array ℤ) :=
  let UQ : Array (Array (Array ℤ)) := Array.ofFn fun j : Fin Dg.dnum => forceFam K C.q (S.upQ a j)
  let UP : Array (Array (Array ℤ)) := Array.ofFn fun j : Fin Dg.dnum => forceFam K Bp.q (S.upP a j)
  let KbQ : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K C.q (fun i => keyLimb (C.q i) (kb j))
  let KbP : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K Bp.q (fun i => keyLimb (Bp.q i) (kb j))
  let KaQ : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K C.q (fun i => keyLimb (C.q i) (ka j))
  let KaP : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K Bp.q (fun i => keyLimb (Bp.q i) (ka j))
  let IbQ := innerZ (N := N) K C.q Dg.dnum UQ KbQ
  let IbP := innerZ (N := N) K Bp.q Dg.dnum UP KbP
  let IaQ := innerZ (N := N) K C.q Dg.dnum UQ KaQ
  let IaP := innerZ (N := N) K Bp.q Dg.dnum UP KaP
  (forceFam K C.q (S.down (ofFam C.q IbQ) (ofFam Bp.q IbP)),
   forceFam K C.q (S.down (ofFam C.q IaQ) (ofFam Bp.q IaP)))

/-- **The staged key switch is the pipeline.** -/
theorem ksStaged_eq (S : Stages Dg C Bp N) (K : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (ksStaged S K a kb ka).1, ofFam C.q (ksStaged S K a kb ka).2) = ksPipe S a kb ka := by
  simp only [ksStaged, ksPipe, ofFam_innerZ, getElem!_ofFn, ofFam_forceFam]

/-- **The staged key switch with the OpenFHE-convention stages is `keySwitchBGVOpenFHE`.** -/
theorem ksStaged_openfhe (t K : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (ksStaged (openfheStages Dg C Bp t) K a kb ka).1,
     ofFam C.q (ksStaged (openfheStages Dg C Bp t) K a kb ka).2) =
      keySwitchBGVOpenFHE Dg C Bp t a kb ka := by
  rw [ksStaged_eq, ksPipe_openfhe]

/-- **The staged key switch with the centred stages is `keySwitchBGV`.** -/
theorem ksStaged_centred (t K : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (ksStaged (centredStages Dg C Bp t) K a kb ka).1,
     ofFam C.q (ksStaged (centredStages Dg C Bp t) K a kb ka).2) =
      keySwitchBGV Dg C Bp t a kb ka := by
  rw [ksStaged_eq, ksPipe_centred]

/-- **The staged key switch with the adding-sign stages is `keySwitchBGVAddDown`.** -/
theorem ksStaged_addDown (t K : ℕ) (a : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (ksStaged (addDownStages Dg C Bp t) K a kb ka).1,
     ofFam C.q (ksStaged (addDownStages Dg C Bp t) K a kb ka).2) =
      keySwitchBGVAddDown Dg C Bp t a kb ka := by
  rw [ksStaged_eq, ksPipe_addDown]

omit [NeZero N] in
/-- The literal (unstaged) pipeline, forced only at the end: for cross-checks at tiny `N`. -/
theorem forceFam_literal (K : ℕ) (a : RNSPoly C N) : ofFam C.q (forceFam K C.q a) = a :=
  ofFam_forceFam K C.q a

end FHE.Pin.Algo
