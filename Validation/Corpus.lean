import Challenge.Corpus
import Validation.Params

/-!
# Validation.Corpus — proofs of the parameter pins of `Challenge.Corpus`

* `tinyBGV_ok`: `norm_num` primality, kernel arithmetic for roots of unity.
* `paramsOK?_tinyBGV`: by kernel evaluation.
-/
namespace Validation.Corpus
open Spec

theorem tinyBGV_ok : ParamsOK Spec.FullParams.tinyBGV := by
  have hL : Spec.FullParams.tinyBGV.allLimbs = [⟨65537, 16⟩, ⟨786433, 241748⟩] := rfl
  have hN : Spec.FullParams.tinyBGV.src.N = 4 := rfl
  have ht : Spec.FullParams.tinyBGV.src.t = 17 := rfl
  have hsch : SchemeParamsOK Spec.FullParams.tinyBGV :=
    { N_pow2 := ⟨2, rfl⟩
      qs_nonempty := List.cons_ne_nil _ _
      prime := by
        have hqs : Spec.FullParams.tinyBGV.src.qs = [65537, 786433] := rfl
        simp only [hqs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num⟩
      distinct := by decide
      plaintext := by
        have hqs : Spec.FullParams.tinyBGV.src.qs = [65537, 786433] := rfl
        simp only [hqs, ht, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq]
        refine ⟨by decide, ?_, ?_⟩ <;> decide +kernel
      msgRange := fun _ => by decide }
  refine
    { scheme := hsch
      W_pos := by decide
      W_dvd := ⟨2, rfl⟩
      limbs_match := rfl
      limbs_nonempty := List.cons_ne_nil _ _
      prime := ?_
      odd := ?_
      fits := ?_
      root := ?_
      distinct := ?_
      plaintext := ?_ }
  all_goals simp only [hL, hN, ht, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.map_cons, List.map_nil]
  · exact ⟨by norm_num, by norm_num⟩
  · decide
  · decide
  · refine ⟨?_, ?_⟩ <;> apply Validation.Params.pow_eq_neg_one_of_mod <;> decide +kernel
  · decide
  · refine ⟨by decide, ?_, ?_⟩ <;> decide +kernel

/-- The decision procedure accepts `tinyBGV`. -/
theorem paramsOK?_tinyBGV : paramsOK? Spec.FullParams.tinyBGV = true := by decide +kernel

end Validation.Corpus
