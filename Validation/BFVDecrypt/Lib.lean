import Validation.BFVDecrypt.Correct
import Validation.Scheme.Basic

/-!
# Validation.BFVDecrypt.Lib — the whole polynomial
-/

namespace Validation.BFVDecrypt
open Spec Spec.Float Spec.DecryptBFV Spec.Scheme NPoly FHE.Float Challenge.BFVDecrypt

/-- `Challenge.BFVDecrypt.bfvDecryptLib_correct`. -/
theorem bfvDecryptLib_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ)
    (hp : decParamsOK? t qs = true) {N : ℕ} (s : IntPoly N) (ct : List (Poly qs.prod N))
    (m : Poly t N) (B : ℕ)
    (hnoise : normInf (centered (phase (ofInt qs.prod s) ct -
      ofInt qs.prod ⟨fun i => ((qs.prod / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decLibOK? t qs B = true) (i : Fin N) :
    (((bfvDecryptLib A t qs s ct).coeff i : ℕ) : ZMod t) = m.coeff i ∧
      (bfvDecryptLib A t qs s ct).coeff i ≤ t := by
  obtain ⟨ht2, _, _, _, hq, _⟩ := params hp
  have hQ : 0 < qs.prod := List.prod_pos fun q h => by have := (hq q h).1; omega
  haveI : NeZero qs.prod := ⟨hQ.ne'⟩
  haveI : NeZero t := ⟨by omega⟩
  set x := ((phase (ofInt qs.prod s) ct).coeff i).val with hxd
  have hx : x < qs.prod := ZMod.val_lt _
  have hm : (m.coeff i).val < t := ZMod.val_lt _
  set D : Poly qs.prod N := phase (ofInt qs.prod s) ct -
      ofInt qs.prod ⟨fun i => ((qs.prod / t * (m.coeff i).val : ℕ) : ℤ)⟩ with hD
  have hco := Validation.Scheme.abs_coeff_le_normInf (centered D) i
  have hn : (((x : ℤ) - (qs.prod / t * (m.coeff i).val : ℕ) : ℤ) : ZMod qs.prod).valMinAbs.natAbs
      ≤ B := by
    have e : (((x : ℤ) - (qs.prod / t * (m.coeff i).val : ℕ) : ℤ) : ZMod qs.prod) = D.coeff i := by
      show _ = (phase (ofInt qs.prod s) ct).coeff i - (((qs.prod / t * (m.coeff i).val : ℕ) : ℤ) :
        ZMod qs.prod)
      rw [Int.cast_sub, Int.cast_natCast, hxd, ZMod.natCast_zmod_val]
    rw [e]
    have h3 : |(D.coeff i).valMinAbs| ≤ (B : ℤ) := hco.trans (by exact_mod_cast hnoise)
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3
  obtain ⟨h1, h2, _, _⟩ := decrypt1_correct A hA t qs hp B hB x (m.coeff i).val hm hx hn
  refine ⟨?_, h2⟩
  have e : (bfvDecryptLib A t qs s ct).coeff i =
      decrypt1 A t qs (tables A.base t qs) (residues qs x) := rfl
  rw [e, h1, ZMod.natCast_zmod_val]

/-- `Challenge.BFVDecrypt.bfvDecryptLib_eq`. -/
theorem bfvDecryptLib_eq (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ)
    (hp : decParamsOK? t qs = true) {N : ℕ} (s : IntPoly N) (ct : List (Poly qs.prod N))
    (m : Poly t N) (B : ℕ) (he : BFVEncrypts t B s ct m) (hB : decLibOK? t qs B = true)
    (i : Fin N) :
    (((bfvDecryptLib A t qs s ct).coeff i : ℕ) : ZMod t) = (bfvDecrypt t s ct).coeff i ∧
      (bfvDecryptLib A t qs s ct).coeff i ≤ t := by
  rw [he.1]
  exact bfvDecryptLib_correct A hA t qs hp s ct m B he.2 hB i

end Validation.BFVDecrypt
