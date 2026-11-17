import Challenge.MSBScale
import Validation.MSB
import Validation.Scaling

/-!
# Validation.MSBScale — proof of `Challenge.MSBScale.certifyProfile?_user_msb`

`Validation.MSB.certifyProfile?_sound_msb` gives the MSB decryption of every output;
`Validation.Scaling.eval_scaled` gives that message as `phi •` the plain result; dividing by the
unit `phi` leaves the plain result.
-/

namespace Validation.MSBScale
open Spec NPoly Scheme Source Correct Spec.Scaling Spec.MSB Challenge.Profile

theorem certifyProfile?_user_msb (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (sd : ScaleData) (hsc : Spec.MSBScale.scaleOK? P.src prog sd = true)
    (Bin : ℕ) (hBin : Bin ≤ P.inputNoise) (hbnd : ∀ x b, prog.boundOf x = some b → Bin ≤ b)
    (hwrap : ∀ d ∈ prog.inputs, 2 * Bin < P.src.modulus d.level)
    (s : IntPoly P.src.N) (u : Var → Poly P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N))
    (hin : MSB.InputsOK P s Bin prog (scaledMsgs P.src sd u) cts) :
    ∀ σ, MSB.Run P E s prog.body (initEnv P.src prog (scaledMsgs P.src sd u))
        (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ ct lam ℓ, σ o = some ct ∧
        Spec.MSBScale.decodeAt? P.src prog sd o = some (lam, ℓ) ∧
        Spec.MSBScale.userDecrypt P.src lam ℓ s ct = plainEval prog sd.marks u o := by
  intro σ hrun o ho
  -- the scale check
  cases hF : factors? P.src prog sd with
  | none => simp [Spec.MSBScale.scaleOK?, hF] at hsc
  | some F =>
    have hunit : ∀ x, F o = some x → x.phi * x.phi⁻¹ = 1 := by
      intro x hx
      simp only [Spec.MSBScale.scaleOK?, hF, List.all_eq_true] at hsc
      have := hsc o ho
      rw [hx] at this
      simpa using this
    obtain ⟨ρ, hρ, hall⟩ := Validation.MSB.certifyProfile?_sound_msb P E prog sw B outs h Bin
      hBin hbnd hwrap s _ cts hin
    obtain ⟨v, ct, m, b, hv, hσ, -, hm, -, hdec, -⟩ := hall σ hrun o ho
    obtain ⟨x, hFx, hmsg, hlvl⟩ :=
      Validation.Scaling.eval_scaled P.src prog sd F hF u ρ hρ o v hv
    refine ⟨ct, x.phi, x.level, hσ, by simp [Spec.MSBScale.decodeAt?, hF, hFx], ?_⟩
    rw [hm] at hmsg
    cases hmsg
    show x.phi⁻¹ • msbDecrypt P.src.t s (ct.map (ofInt (P.src.modulus x.level))) = _
    rw [← hlvl, hdec]
    have hu := hunit x hFx
    ext i
    show x.phi⁻¹ * (x.phi * _) = _
    rw [← mul_assoc, mul_comm x.phi⁻¹, hu, one_mul]

example := (@certifyProfile?_user_msb : type_of% @Challenge.MSBScale.certifyProfile?_user_msb)

end Validation.MSBScale
