import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# FHE.RNS.Basis — RNS bases and the Chinese remainder theorem

An RNS basis is a finite family `q₀, …, q_{ℓ-1}` of positive, pairwise coprime moduli with
product `Q`. We use the notation of Bajard–Eynard–Hasan–Zucca (BEHZ 2016) and
Halevi–Polyakov–Shoup (HPS 2018):

* `B.prod = Q = ∏ qᵢ`;
* `B.hat i = q̂ᵢ = Q / qᵢ = ∏_{j ≠ i} qⱼ` (defined as the product, so no division is involved);
* `B.hatInv i = q̃ᵢ = q̂ᵢ⁻¹ mod qᵢ`.

Main results:

* `Basis.crt` — the CRT ring isomorphism `ZMod Q ≃+* Π i, ZMod qᵢ` (Mathlib's
  `ZMod.prodEquivPi`), with `crt_apply` saying the `i`-th component is reduction mod `qᵢ`;
* `Basis.crt_symm_eq_reconstruct` — the explicit inverse
  `x = Σᵢ [xᵢ · q̃ᵢ]_{qᵢ} · q̂ᵢ  (mod Q)`;
* `Basis.prod_dvd_sum_sub` — the integer core of every RNS algorithm: for *any* integers
  `tᵢ ≡ xᵢ · q̃ᵢ (mod qᵢ)` (canonical, centred or otherwise) and any integer `X` with residues
  `xᵢ`, `Q ∣ Σᵢ tᵢ · q̂ᵢ − X`.

Residue vectors are functions `x : (i : Fin ℓ) → ZMod (B.q i)`; an integer `X` *has residues* `x`
when `∀ i, (X : ZMod (B.q i)) = x i`.
-/

namespace FHE.RNS

open Finset
open scoped Function

/-- An RNS basis: `ℓ` positive, pairwise coprime moduli. -/
structure Basis (ℓ : ℕ) where
  /-- The moduli `q₀, …, q_{ℓ-1}`. -/
  q : Fin ℓ → ℕ
  pos : ∀ i, 0 < q i
  coprime : Pairwise (Nat.Coprime on q)

namespace Basis

variable {ℓ : ℕ} (B : Basis ℓ)

instance (i : Fin ℓ) : NeZero (B.q i) := ⟨(B.pos i).ne'⟩

/-- `Q = ∏ qᵢ`. -/
abbrev prod : ℕ := ∏ i, B.q i

/-- `q̂ᵢ = ∏_{j ≠ i} qⱼ = Q / qᵢ`. -/
def hat (i : Fin ℓ) : ℕ := ∏ j ∈ univ.erase i, B.q j

/-- `q̃ᵢ = q̂ᵢ⁻¹ mod qᵢ`. -/
def hatInv (i : Fin ℓ) : ZMod (B.q i) := (B.hat i : ZMod (B.q i))⁻¹

theorem prod_pos : 0 < B.prod := Finset.prod_pos fun i _ => B.pos i

instance : NeZero B.prod := ⟨B.prod_pos.ne'⟩

theorem hat_pos (i : Fin ℓ) : 0 < B.hat i := Finset.prod_pos fun j _ => B.pos j

theorem q_mul_hat (i : Fin ℓ) : B.q i * B.hat i = B.prod :=
  Finset.mul_prod_erase _ _ (mem_univ i)

theorem hat_eq_div (i : Fin ℓ) : B.hat i = B.prod / B.q i := by
  rw [← B.q_mul_hat i, Nat.mul_div_cancel_left _ (B.pos i)]

theorem q_dvd_prod (i : Fin ℓ) : B.q i ∣ B.prod := ⟨_, (B.q_mul_hat i).symm⟩

/-- `qⱼ ∣ q̂ᵢ` for `j ≠ i`. -/
theorem q_dvd_hat {i j : Fin ℓ} (h : j ≠ i) : B.q j ∣ B.hat i :=
  Finset.dvd_prod_of_mem _ (mem_erase.mpr ⟨h, mem_univ j⟩)

theorem hat_coprime (i : Fin ℓ) : Nat.Coprime (B.hat i) (B.q i) :=
  Nat.Coprime.symm <| Nat.coprime_prod_right_iff.mpr fun _ hj =>
    B.coprime (mem_erase.mp hj).1.symm

theorem hat_mul_hatInv (i : Fin ℓ) : (B.hat i : ZMod (B.q i)) * B.hatInv i = 1 :=
  ZMod.coe_mul_inv_eq_one _ (B.hat_coprime i)

/-! ### The CRT isomorphism -/

/-- The Chinese remainder theorem `ZMod Q ≃+* Π i, ZMod qᵢ`. -/
noncomputable def crt : ZMod B.prod ≃+* ((i : Fin ℓ) → ZMod (B.q i)) :=
  ZMod.prodEquivPi B.q B.coprime

/-- The `i`-th component of `crt` is reduction modulo `qᵢ`. -/
theorem crt_apply (y : ZMod B.prod) (i : Fin ℓ) : B.crt y i = (y.val : ZMod (B.q i)) := by
  rw [crt, ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem crt_apply_intCast (X : ℤ) (i : Fin ℓ) : B.crt (X : ZMod B.prod) i = (X : ZMod (B.q i)) := by
  rw [map_intCast]; rfl

/-- The CRT reconstruction `Σᵢ [xᵢ · q̃ᵢ]_{qᵢ} · q̂ᵢ mod Q`, with `[·]_{qᵢ}` the canonical
representative in `[0, qᵢ)`. Computable. -/
def reconstruct (x : (i : Fin ℓ) → ZMod (B.q i)) : ZMod B.prod :=
  ∑ i, (((x i * B.hatInv i).val : ℕ) : ZMod B.prod) * (B.hat i : ZMod B.prod)

/-- The representative of `x` in `[0, Q)`. -/
def lift (x : (i : Fin ℓ) → ZMod (B.q i)) : ℕ := (B.reconstruct x).val

/-- The representative of `x` in `(-Q/2, Q/2]` (`ZMod.valMinAbs` convention). -/
def liftC (x : (i : Fin ℓ) → ZMod (B.q i)) : ℤ := (B.reconstruct x).valMinAbs

/-! ### The integer core -/

/-- Integers congruent modulo every `qᵢ` are congruent modulo `Q`. -/
theorem prod_dvd_of_forall {z : ℤ} (h : ∀ i, (z : ZMod (B.q i)) = 0) : (B.prod : ℤ) ∣ z := by
  have hco : Pairwise (IsCoprime on fun i => (B.q i : ℤ)) := fun i j hij =>
    Nat.isCoprime_iff_coprime.mpr (B.coprime hij)
  have := Fintype.prod_dvd_of_coprime hco fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp (h i)
  simpa using this

/-- **CRT core.** For any integers `tᵢ ≡ xᵢ·q̃ᵢ (mod qᵢ)` and any integer `X` with residues `x`,
`Σᵢ tᵢ·q̂ᵢ ≡ X (mod Q)`. -/
theorem prod_dvd_sum_sub (x : (i : Fin ℓ) → ZMod (B.q i)) (X : ℤ)
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) (t : Fin ℓ → ℤ)
    (ht : ∀ i, (t i : ZMod (B.q i)) = x i * B.hatInv i) :
    (B.prod : ℤ) ∣ (∑ i, t i * B.hat i) - X := by
  apply B.prod_dvd_of_forall
  intro j
  push_cast
  rw [Finset.sum_eq_single j]
  · rw [ht j, hX j, mul_assoc, mul_comm (B.hatInv j), B.hat_mul_hatInv, mul_one, sub_self]
  · intro i _ hij
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr (B.q_dvd_hat hij.symm), mul_zero]
  · intro h; exact absurd (mem_univ j) h

theorem reconstruct_eq_intCast (x : (i : Fin ℓ) → ZMod (B.q i)) :
    B.reconstruct x = ((∑ i, ((x i * B.hatInv i).val : ℤ) * B.hat i : ℤ) : ZMod B.prod) := by
  simp [reconstruct]

/-- The residues of `reconstruct x` are `x`. -/
theorem crt_reconstruct (x : (i : Fin ℓ) → ZMod (B.q i)) : B.crt (B.reconstruct x) = x := by
  funext j
  rw [reconstruct_eq_intCast, crt_apply_intCast]
  push_cast
  rw [Finset.sum_eq_single j]
  · rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm (B.hatInv j), B.hat_mul_hatInv, mul_one]
  · intro i _ hij
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr (B.q_dvd_hat hij.symm), mul_zero]
  · intro h; exact absurd (mem_univ j) h

/-- **Explicit CRT inverse**: `crt⁻¹ x = Σᵢ [xᵢ · q̃ᵢ]_{qᵢ} · q̂ᵢ mod Q`. -/
theorem crt_symm_eq_reconstruct (x : (i : Fin ℓ) → ZMod (B.q i)) :
    B.crt.symm x = B.reconstruct x := by
  rw [RingEquiv.symm_apply_eq, crt_reconstruct]

/-- An integer with residues `x` is congruent to `reconstruct x` modulo `Q`. -/
theorem intCast_eq_reconstruct {x : (i : Fin ℓ) → ZMod (B.q i)} {X : ℤ}
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) : (X : ZMod B.prod) = B.reconstruct x := by
  apply B.crt.injective
  funext i
  rw [crt_apply_intCast, crt_reconstruct, hX]

/-- Residues of `X` determine `X` modulo `Q`. -/
theorem prod_dvd_sub_of_residues {X Y : ℤ} (h : ∀ i, (X : ZMod (B.q i)) = (Y : ZMod (B.q i))) :
    (B.prod : ℤ) ∣ X - Y := by
  apply B.prod_dvd_of_forall
  intro i; push_cast; rw [h i, sub_self]

theorem lift_lt (x : (i : Fin ℓ) → ZMod (B.q i)) : B.lift x < B.prod := ZMod.val_lt _

theorem lift_residue (x : (i : Fin ℓ) → ZMod (B.q i)) (i : Fin ℓ) :
    (((B.lift x : ℕ) : ℤ) : ZMod (B.q i)) = x i := by
  have h := congrFun (B.crt_reconstruct x) i
  rw [crt_apply] at h
  simpa [lift] using h

theorem liftC_residue (x : (i : Fin ℓ) → ZMod (B.q i)) (i : Fin ℓ) :
    ((B.liftC x : ℤ) : ZMod (B.q i)) = x i := by
  have h := congrFun (B.crt_reconstruct x) i
  rw [← ZMod.coe_valMinAbs (B.reconstruct x), crt_apply_intCast] at h
  exact h

/-- `-Q < 2·liftC x ≤ Q`. -/
theorem liftC_bounds (x : (i : Fin ℓ) → ZMod (B.q i)) :
    -(B.prod : ℤ) < 2 * B.liftC x ∧ 2 * B.liftC x ≤ B.prod := by
  have := ZMod.valMinAbs_mem_Ioc (B.reconstruct x)
  simp only [Set.mem_Ioc] at this
  unfold liftC; constructor <;> linarith [this.1, this.2]

/-! ### Bases from lists and sub-bases -/

/-- A basis from a list of positive, pairwise coprime moduli (the form `Spec` uses). -/
def ofList (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime) :
    Basis qs.length where
  q i := qs[i]
  pos i := hpos _ (List.getElem_mem _)
  coprime i j hij := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact List.pairwise_iff_getElem.mp hcop _ _ _ _ h
    · exact (List.pairwise_iff_getElem.mp hcop _ _ _ _ h).symm

theorem ofList_prod (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime) :
    (ofList qs hpos hcop).prod = qs.prod := by
  exact Fin.prod_univ_getElem qs

/-- Distinct primes are pairwise coprime (the form `Spec.ParamsOK` provides). -/
theorem pairwise_coprime_of_prime_nodup {qs : List ℕ} (hp : ∀ q ∈ qs, q.Prime) (hd : qs.Nodup) :
    qs.Pairwise Nat.Coprime :=
  (List.Nodup.pairwise_of_forall_ne hd fun a ha b hb hab =>
    (Nat.coprime_primes (hp a ha) (hp b hb)).mpr hab)

/-- The basis of the first `ℓ` moduli of a list (a ciphertext at level `ℓ`). -/
def take (qs : List ℕ) (ℓ : ℕ) (h : ℓ ≤ qs.length) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) : Basis ℓ where
  q i := qs[(i : ℕ)]'(by omega)
  pos i := hpos _ (List.getElem_mem _)
  coprime i j hij := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h' | h'
    · exact List.pairwise_iff_getElem.mp hcop _ _ _ _ h'
    · exact (List.pairwise_iff_getElem.mp hcop _ _ _ _ h').symm

theorem take_prod (qs : List ℕ) (ℓ : ℕ) (h : ℓ ≤ qs.length) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) : (take qs ℓ h hpos hcop).prod = (qs.take ℓ).prod := by
  rw [← Fin.prod_univ_getElem (qs.take ℓ)]
  have hl : (qs.take ℓ).length = ℓ := by simp [h]
  refine Fintype.prod_equiv (finCongr hl.symm) _ _ fun i => ?_
  simp [take]

/-- Restriction to a sub-family of moduli (e.g. one digit of hybrid key switching). -/
def restrict {m : ℕ} (f : Fin m → Fin ℓ) (hf : Function.Injective f) : Basis m where
  q i := B.q (f i)
  pos _ := B.pos _
  coprime _ _ hij := B.coprime (hf.ne hij)

/-- Drop the last modulus. -/
def dropLast (B : Basis (ℓ + 1)) : Basis ℓ where
  q i := B.q i.castSucc
  pos _ := B.pos _
  coprime _ _ hij := B.coprime (Fin.castSucc_injective _ |>.ne hij)

/-- The last modulus `q_ℓ`. -/
abbrev last (B : Basis (ℓ + 1)) : ℕ := B.q (Fin.last ℓ)

theorem prod_eq_dropLast_mul (B : Basis (ℓ + 1)) : B.prod = B.dropLast.prod * B.last := by
  simp [prod, Fin.prod_univ_castSucc, dropLast]

theorem last_coprime (B : Basis (ℓ + 1)) (i : Fin ℓ) : Nat.Coprime B.last (B.dropLast.q i) :=
  B.coprime (Fin.castSucc_lt_last i).ne'

theorem take_dropLast (qs : List ℕ) (ℓ : ℕ) (h : ℓ + 1 ≤ qs.length) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) :
    (take qs (ℓ + 1) h hpos hcop).dropLast = take qs ℓ (by omega) hpos hcop := rfl

theorem take_last (qs : List ℕ) (ℓ : ℕ) (h : ℓ + 1 ≤ qs.length) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) : (take qs (ℓ + 1) h hpos hcop).last = qs[ℓ] := rfl

end Basis
end FHE.RNS
