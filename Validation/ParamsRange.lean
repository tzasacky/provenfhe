import Challenge.Params
import Validation.Ring
import Validation.Scheme.Basic
import Validation.Scheme.Honest

/-!
# Validation.ParamsRange — why `SchemeParamsOK.msgRange` is `t / 2 ≤ inputNoise`

Proofs of `Challenge.Params.bgv_inputs_exist` and `Challenge.Params.bgv_small_noise_excludes`.
-/

namespace Validation.Params
open Spec NPoly Scheme Source Correct Validation.Ring Validation.Scheme

/-- Local unfolding of `Encrypts` for BGV with a known exact message. -/
theorem encrypts_bgv_exact_iff (P : FullParams) (hk : P.src.kind = .bgv) (s : IntPoly P.src.N)
    (B : ℕ) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (ct : List (IntPoly P.src.N)) :
    Encrypts P s B v ct ↔ ct.length = v.parts ∧
      BGVEncrypts P.src.t B (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) m := by
  unfold Encrypts
  simp only [hk, hm]

theorem bgv_inputs_exist (P : FullParams) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (h2 : v.parts = 2) (hQ : P.src.t < P.src.modulus v.level) :
    ∃ ct, Encrypts P s P.inputNoise v ct := by
  have ht : 2 ≤ P.src.t := (hP.plaintext).1
  have : NeZero P.src.t := ⟨by omega⟩
  have hB : P.src.t / 2 ≤ P.inputNoise := hP.msgRange hk
  have hc : ∀ i, (((centered m).coeff i).natAbs) ≤ P.src.t / 2 := fun i =>
    ZMod.natAbs_valMinAbs_le _
  refine ⟨[centered m, 0], ?_⟩
  rw [encrypts_bgv_exact_iff P hk s _ v m hm]
  refine ⟨by simp [h2], ?_⟩
  have hph : phase (ofInt (P.src.modulus v.level) (automorph v.key s))
      ([centered m, 0].map (ofInt (P.src.modulus v.level)))
      = ofInt (P.src.modulus v.level) (centered m) := by
    rw [List.map_cons, List.map_cons, List.map_nil, phase_two', ofInt_zero]
    ext i
    simp [coeff_mul']
  have hcp : centeredPhase (automorph v.key s)
      ([centered m, 0].map (ofInt (P.src.modulus v.level))) = centered m := by
    rw [centeredPhase, hph]
    apply centered_ofInt
    intro i
    have h1 := hc i
    have h3 : |(centered m).coeff i| = (((centered m).coeff i).natAbs : ℤ) :=
      Int.abs_eq_natAbs _
    rw [h3]
    have : 2 * ((centered m).coeff i).natAbs < P.src.modulus v.level := by omega
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · rw [bgvDecrypt, hcp, ofInt_centered]
  · rw [hcp]
    unfold normInf
    exact Finset.sup_le fun i _ => (hc i).trans hB

theorem bgv_small_noise_excludes (P : FullParams) (hk : P.src.kind = .bgv) (hN : 0 < P.src.N)
    (ht : 2 ≤ P.src.t) (s : IntPoly P.src.N) (B : ℕ) (hB : B < P.src.t / 2) (v : Val P.src)
    (hm : v.msg = .exact (NPoly.const ((P.src.t / 2 : ℕ) : ZMod P.src.t)))
    (ct : List (IntPoly P.src.N)) : ¬ Encrypts P s B v ct := by
  intro h
  rw [encrypts_bgv_exact_iff P hk s B v _ hm] at h
  obtain ⟨-, hE⟩ := h
  have hb := BGVEncrypts.bound hE ⟨0, hN⟩
  have hmsg := congrArg (fun p => p.coeff ⟨0, hN⟩) (BGVEncrypts.msg hE)
  simp only [coeff_ofInt, coeff_const'] at hmsg
  have hmsg' : ((((centeredPhase (automorph v.key s)
      (ct.map (ofInt (P.src.modulus v.level)))).coeff ⟨0, hN⟩ : ℤ)) : ZMod P.src.t)
      = (((P.src.t / 2 : ℕ) : ℤ) : ZMod P.src.t) := by
    rw [hmsg, Int.cast_natCast, ite_true]
  obtain ⟨j, hj⟩ := exists_eq_add_mul_of_cast_eq hmsg'
  generalize (centeredPhase (automorph v.key s)
      (ct.map (ofInt (P.src.modulus v.level)))).coeff ⟨0, hN⟩ = x at hb hj
  generalize P.src.t = t at ht hB hj hb
  have hBz : (B : ℤ) < ((t / 2 : ℕ) : ℤ) := by exact_mod_cast hB
  have h2 : 2 * ((t / 2 : ℕ) : ℤ) ≤ (t : ℤ) := by
    have : 2 * (t / 2) ≤ t := by omega
    exact_mod_cast this
  have htz : (2 : ℤ) ≤ t := by exact_mod_cast ht
  rw [abs_le] at hb
  rcases le_or_gt 0 j with hj0 | hj0
  · have : (0 : ℤ) ≤ (t : ℤ) * j := by positivity
    linarith
  · have : (t : ℤ) * j ≤ (t : ℤ) * (-1) := by
      apply mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith

end Validation.Params

