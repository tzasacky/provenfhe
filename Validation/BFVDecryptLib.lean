import Validation.BFVDecrypt
import Validation.BFVDecryptLow
import Validation.BFVDecryptBEHZ
import Challenge.BFVDecryptLib

/-!
# Validation.BFVDecryptLib — proofs of the statements of `Challenge.BFVDecryptLib`
-/

namespace Validation.BFVDecryptLib
open Spec NPoly Scheme Source Correct Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow
  Spec.DecryptBFVBEHZ Spec.DecryptBFVLib Spec.CertifyBFV Challenge.CertifyBFV
  Challenge.BFVDecryptLib

theorem output_decryptLibExt (P : FullParams) (hk : P.src.kind = .bfv) (A : ArithD)
    (hA : ConformsD A) (behz : Bool) (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src)
    (ct : List (IntPoly P.src.N)) (m : Poly P.src.t P.src.N) (hmsg : v.msg = .exact m)
    (hkey : v.key = 1) (he : Encrypts P s B v ct)
    (hok : outputLibOK? behz P.src.t P.src.qs v.level B = true) (i : Fin P.src.N) :
    (((bfvDecryptOpenFHE A behz P.src.t P.src.qs v.level s ct).coeff i : ℕ) : ZMod P.src.t) =
        m.coeff i ∧
      (bfvDecryptOpenFHE A behz P.src.t P.src.qs v.level s ct).coeff i ≤ P.src.t := by
  unfold Encrypts at he
  rw [hk, hmsg] at he
  obtain ⟨_, he⟩ := he
  simp only at he
  rw [hkey, FHE.KeySwitch.automorph_one] at he
  unfold outputLibOK? at hok
  unfold bfvDecryptOpenFHE
  by_cases hL : v.level = P.src.qs.length
  · have hQ : P.src.modulus v.level = P.src.qs.prod := by
      rw [hL]; unfold Params.modulus; rw [List.take_length]
    rw [hQ] at he
    rw [if_pos hL] at hok ⊢
    cases behz
    · simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at hok ⊢
      exact Validation.BFVDecrypt.bfvDecryptLib_correct A hA _ _ hok.1 s _ m B he.2 hok.2 i
    · simp only [ite_true, Bool.and_eq_true] at hok ⊢
      exact Validation.BFVDecryptBEHZ.bfvDecryptBEHZ_correct _ _ hok.1 s _ m B he.2 hok.2 i
  · rw [if_neg hL] at hok ⊢
    simp only [Bool.and_eq_true] at hok
    have h := Validation.BFVDecryptLow.bfvDecryptLow_correct A hA _ _ v.level hok.1.1 s _ m B
      he.2 hok.1.2 i
    exact ⟨h.1, h.2.le⟩

theorem certifyBFV?_decryptsLibExt (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hd : decryptLibExtOK? x c = true) (behz : Bool) (hb : techLib? x.mul = some behz) (A : ArithD)
    (hA : ConformsD A) (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ ρ, Source.eval x.P.src x.prog msgs = some ρ ∧
      ∀ σ, TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
          (Trace.initCt x.P x.prog cts) σ →
        ∀ o ∈ x.prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
          ∀ i, (((bfvDecryptOpenFHE A behz x.P.src.t x.P.src.qs v.level s ct).coeff i : ℕ) :
                  ZMod x.P.src.t) = m.coeff i ∧
            (bfvDecryptOpenFHE A behz x.P.src.t x.P.src.qs v.level s ct).coeff i ≤ x.P.src.t := by
  obtain ⟨_, hk, -, -, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK x c h
  unfold decryptLibExtOK? at hd
  rw [hb] at hd
  have hd' : (x.prog.outputs.all fun o =>
      match Decrypt.outputLevel? x.P.src x.prog o, c.outputs.lookup o with
      | some ℓ, some B => outputLibOK? behz x.P.src.t x.P.src.qs ℓ B
      | _, _ => false) = true := hd
  obtain ⟨ρ, hev, hrun⟩ := Validation.CertifyBFV.certifyBFV?_sound x c h s msgs cts hin
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, m, B, hv, hct, hlk, henc, hm, hkey, _⟩ := hrun σ hσ o ho
  have hl := Validation.BFVDecrypt.outputLevel?_eq_bfv x.P.src hk x.prog msgs ρ hev o v hv
  have hok := List.all_eq_true.mp hd' o ho
  rw [hl, hlk] at hok
  have hok' : outputLibOK? behz x.P.src.t x.P.src.qs v.level B = true := hok
  refine ⟨v, ct, m, hv, hct, hm, fun i => ?_⟩
  exact output_decryptLibExt x.P hk A hA behz s B v ct m hm hkey henc hok' i

theorem decryptLibOK?_ext (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hd : Challenge.BFVDecrypt.decryptLibOK? x c = true) : decryptLibExtOK? x c = true := by
  obtain ⟨hd1, hd2⟩ := Bool.and_eq_true_iff.mp hd
  obtain ⟨hd3, hd4⟩ := Bool.and_eq_true_iff.mp hd1
  obtain ⟨ht, hp⟩ := Bool.and_eq_true_iff.mp hd3
  have hspec := Validation.CertifyBFV.certifyBFV?_spec x c h
  have hlk := hspec.2.2.2.2.2.2.2.2
  have hb : techLib? x.mul = some false := by
    revert ht
    rcases hm : x.mul with _ | (_ | _ | _ | _ | _) <;> intro ht <;>
      first | rfl | exact absurd ht Bool.false_ne_true
  unfold decryptLibExtOK?
  rw [hb]
  show (x.prog.outputs.all fun o =>
      match Decrypt.outputLevel? x.P.src x.prog o, c.outputs.lookup o with
      | some ℓ, some B => outputLibOK? false x.P.src.t x.P.src.qs ℓ B
      | _, _ => false) = true
  rw [List.all_eq_true]
  intro o ho
  obtain ⟨B, hB, _⟩ := hlk o ho
  have hl : Decrypt.outputLevel? x.P.src x.prog o = some x.P.src.qs.length := by
    simpa using List.all_eq_true.mp hd4 o ho
  rw [hl, hB]
  have hlib : Spec.DecryptBFV.decLibOK? x.P.src.t x.P.src.qs B = true :=
    List.all_eq_true.mp hd2 (o, B) (Validation.BFVDecrypt.lookup_mem hB)
  show outputLibOK? false x.P.src.t x.P.src.qs x.P.src.qs.length B = true
  unfold outputLibOK?
  rw [if_pos rfl]
  simp [hp, hlib]

example := (@decryptLibOK?_ext : type_of% @Challenge.BFVDecryptLib.decryptLibOK?_ext)
example := (@output_decryptLibExt : type_of% @Challenge.BFVDecryptLib.output_decryptLibExt)
example := (@certifyBFV?_decryptsLibExt : type_of% @Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt)

end Validation.BFVDecryptLib
