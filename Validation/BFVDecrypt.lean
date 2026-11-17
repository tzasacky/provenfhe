import Validation.BFVDecrypt.Certify
import Validation.BFVMul.FloatSums

/-!
# Validation.BFVDecrypt — proofs of the statements of `Challenge.BFVDecrypt`

* `Validation/BFVDecrypt/Sum.lean`: the rounding error of the decryption sum (`fold_err'`).
* `Words.lean`: the words of a coefficient as data; caps; the word split.
* `Float.lean`: the power-of-two sum error (`floatSum_err_pow2`).
* `CRT.lean`: what the tables encode (`crt`, `crt_value`, `limb_value`).
* `Int.lean`: `intSum` never wraps (`intSum_no_wrap`).
* `Odd.lean`: the non-power-of-two reduction (`reduced_err_odd`).
* `Main.lean`: exactness (`decrypt1_exact`).
* `Correct.lean`: one coefficient under the margin (`decrypt1_correct`).
* `Lib.lean`: the whole polynomial (`bfvDecryptLib_correct`, `bfvDecryptLib_eq`).
* `Certify.lean`: the certificate (`output_decryptLib`, `certifyBFV?_decryptsLib`).
-/

namespace Validation.BFVDecrypt
open Spec Spec.Float Spec.DecryptBFV Spec.Scheme NPoly Challenge.BFVDecrypt

theorem exactD_conforms : ConformsD exactD :=
  { base := Validation.BFVMul.exact_conforms
    sub := fun a b _ => ⟨0, by simp [u], by simp [exactD]⟩
    fnma := fun a b c _ => ⟨0, by simp [u], by simp [exactD]⟩
    subSmall := fun a b h => by simpa [exactD] using h.le
    fnmaSmall := fun a b c h => by simpa [exactD] using h.le
    mulSub := fun s a b => Or.inl rfl
    ofNatExact := fun n _ => rfl
    mulExact := fun a b _ => by simp [exactD, Spec.Float.exact] }

theorem advD_conforms : ConformsD advD :=
  { base :=
      { ofNat := fun n _ => ⟨0, by simp [u], by show (n : ℚ) = n * (1 + 0); ring⟩
        mul := fun a b _ => ⟨0, by simp [u], by show a * b = a * b * (1 + 0); ring⟩
        div := fun a b _ _ => ⟨0, by simp [u], by show a / b = a / b * (1 + 0); ring⟩
        add := fun a b _ => ⟨0, by simp [u], by show a + b = (a + b) * (1 + 0); ring⟩
        fma := fun a b c _ => ⟨u, by rw [abs_of_pos FHE.Float.u_pos],
          by show (a * b + c) * (1 + u) = (a * b + c) * (1 + u); rfl⟩
        mulAdd := fun s a b => Or.inr (by
          show (s + a * b) * (1 + u) = (a * b + s) * (1 + u); ring) }
    sub := fun a b _ => ⟨0, by simp [u], by show a - b = (a - b) * (1 + 0); ring⟩
    fnma := fun a b c _ => ⟨0, by simp [u], by show c - a * b = (c - a * b) * (1 + 0); ring⟩
    subSmall := fun a b h => by show |a - b| ≤ _; exact h.le
    fnmaSmall := fun a b c h => by show |c - a * b| ≤ _; exact h.le
    mulSub := fun s a b => Or.inl rfl
    ofNatExact := fun n _ => rfl
    mulExact := fun a b _ => rfl }

theorem words_split (qs : List ℕ) (hq : qMSBHf qs ≤ 60) (x : ℕ) (hx : x < 2 ^ 60) :
    rshift x (qMSBHf qs) * 2 ^ qMSBHf qs < 2 ^ 64 ∧
    lshift (rshift x (qMSBHf qs)) (qMSBHf qs) = rshift x (qMSBHf qs) * 2 ^ qMSBHf qs ∧
    subFast x (lshift (rshift x (qMSBHf qs)) (qMSBHf qs)) + rshift x (qMSBHf qs) * 2 ^ qMSBHf qs
      = x := by
  have hx64 : x < 2 ^ 64 := lt_trans hx (by norm_num)
  obtain ⟨h1, h2, _⟩ := split_exact (qMSBHf qs) x hq hx64
  exact ⟨h1, h2, rshift_mul_add (qMSBHf qs) x hq hx64⟩

theorem allWords_fst (A : Arith) (t : ℕ) (qs xs : List ℕ) :
    (allWords qs (tables A t qs) xs).map (fun w => (w.1, w.2.1)) =
      (allWords qs (tables Spec.Float.exact t qs) xs).map (fun w => (w.1, w.2.1)) := by
  rw [allWords_eq, allWords_eq, List.map_map, List.map_map]
  rfl

theorem margin_needed :
    decParamsOK? 2 [q0] = true ∧ Challenge.BFV.decOK 2 q0 ((q0 - 3) / 4) = true ∧
      roundDiv (2 * ((q0 - 3) / 4 : ℕ)) q0 = 0 ∧
      decrypt1 exactD 2 [q0] (tables Spec.Float.exact 2 [q0]) (residues [q0] ((q0 - 3) / 4)) = 0 ∧
      decrypt1 advD 2 [q0] (tables advD.base 2 [q0]) (residues [q0] ((q0 - 3) / 4)) = 1 ∧
      decLibOK? 2 [q0] ((q0 - 3) / 4) = false := by
  decide +kernel

example := (@exactD_conforms : type_of% @Challenge.BFVDecrypt.exactD_conforms)
example := (@decrypt1_exact : type_of% @Challenge.BFVDecrypt.decrypt1_exact)
example := (@words_split : type_of% @Challenge.BFVDecrypt.words_split)
example := (@intSum_no_wrap : type_of% @Challenge.BFVDecrypt.intSum_no_wrap)
example := (@allWords_fst : type_of% @Challenge.BFVDecrypt.allWords_fst)
example := (@floatSum_err_pow2 : type_of% @Challenge.BFVDecrypt.floatSum_err_pow2)
example := (@reduced_err_odd : type_of% @Challenge.BFVDecrypt.reduced_err_odd)
example := (@decrypt1_correct : type_of% @Challenge.BFVDecrypt.decrypt1_correct)
example := (@bfvDecryptLib_correct : type_of% @Challenge.BFVDecrypt.bfvDecryptLib_correct)
example := (@bfvDecryptLib_eq : type_of% @Challenge.BFVDecrypt.bfvDecryptLib_eq)
example := (@output_decryptLib : type_of% @Challenge.BFVDecrypt.output_decryptLib)
example := (@certifyBFV?_decryptsLib : type_of% @Challenge.BFVDecrypt.certifyBFV?_decryptsLib)
example := (@advD_conforms : type_of% @Challenge.BFVDecrypt.advD_conforms)
example := (@margin_needed : type_of% @Challenge.BFVDecrypt.margin_needed)

end Validation.BFVDecrypt
