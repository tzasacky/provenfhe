import Challenge.BFVMul
import Validation.BFV.Sound
import FHE.KeySwitch.Step

/-!
# Validation.BFVMul.Cert — the BFV certificate: decryption with the secret key itself

Proofs of the pins `certified_decrypts` and `certifiedApprox_sound` of `Challenge.BFVMul`.

* `outputKey?_eq_bfv`: the key an output is recorded under does not depend on the messages
  (`Spec.Encrypt.outputKey?` computes it on all-zero messages), by the zeroing argument of
  `Validation.BFV.SoundAux.step_zenv`. This is the BFV counterpart of
  `Validation.FreshNoise.outputKey?_eq` (which is stated for BGV).
* `certified_decrypts`: the headline `Validation.BFV.refAnalyzeBFV_sound` gives `Encrypts` under
  the recorded key; `outputsUnderS?` makes that key `1`, `σ₁(s) = s`, and for BFV `Encrypts`
  contains exact decryption (`Validation.BFV.encrypts_bfv_decrypts`).
* `certifiedApprox_sound`: the headline at the budget `Spec.BudgetBFV.certifiedApprox`.

The helper lemmas are in the namespace `Validation.BFVMul.Cert`; the pins in `Validation.BFVMul`.
-/

namespace Validation.BFVMul.Cert
open Spec NPoly Scheme Source Correct Spec.Encrypt Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.BFV.SoundAux

/-- Running a body on zeroed messages is zeroing the result of the run (BFV). -/
theorem foldlM_zenv {Pr : Params} (hk : Pr.kind = .bfv) : ∀ (body : List Instr) (ρ : Env Pr),
    AllExact ρ → body.foldlM (step Pr) (zenv ρ) = (body.foldlM (step Pr) ρ).map zenv
  | [], _, _ => rfl
  | i :: is, ρ, hρ => by
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    simp only [List.foldlM_cons, Option.bind_eq_bind, hz]
    rcases hs : step Pr ρ i with _ | ρ'
    · rfl
    · simp only [Option.map_some, Option.bind_some]
      exact foldlM_zenv hk is ρ' (hex ρ' hs)

/-- The key of an output of a BFV program is the same for all messages. -/
theorem outputKey?_eq_bfv (P : Params) (hk : P.kind = .bfv) (prog : Program)
    (msgs : Var → Msg P.t P.N) (ρ : Env P) (h : eval P prog msgs = some ρ) (o : Var) (v : Val P)
    (ho : ρ o = some v) : outputKey? P prog o = some v.key := by
  simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, guard, Option.pure_def] at h
  obtain ⟨_, h1, _, h2, ρ', h3, _, h4, h5⟩ := h
  have hd : (prog.inputs.all fun dcl => dcl.ok P) = true := by by_contra hc; simp [hc] at h1
  have hf : (prog.inputs.all fun dcl => (msgs dcl.name).fits P.kind) = true := by
    by_contra hc; simp [hc] at h2
  have hout : (prog.outputs.all fun o => (ρ' o).isSome) = true := by by_contra hc; simp [hc] at h4
  cases h5
  have hρ0 : AllExact (initEnv P prog msgs) := by
    intro x w hw
    simp only [initEnv, Option.map_eq_some_iff] at hw
    obtain ⟨d, hd', rfl⟩ := hw
    have hn : d.name = x := by simpa using List.find?_some hd'
    have := List.all_eq_true.mp hf d (List.mem_of_find?_eq_some hd')
    rw [hn, hk] at this
    dsimp only
    cases hmx : msgs x with
    | exact m => exact ⟨m, rfl⟩
  have hz0 : zenv (initEnv P prog msgs) = initEnv P prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  have hfold := foldlM_zenv hk prog.body _ hρ0
  rw [hz0, h3, Option.map_some] at hfold
  have hev : eval P prog (fun _ => .exact 0) = some (zenv ρ) := by
    have hfz : (prog.inputs.all fun dcl =>
        ((fun _ => .exact 0 : Var → Msg P.t P.N) dcl.name).fits P.kind) = true := by
      rw [List.all_eq_true]; intro dcl _; rw [hk]; rfl
    have hoz : (prog.outputs.all fun o => (zenv ρ o).isSome) = true := by
      simpa [zenv] using hout
    simp only [eval, hd, hfz, hfold, hoz, guard, Option.bind_eq_bind, ite_true,
      Option.pure_def, Option.bind_some]
  simp only [outputKey?, hev, Option.bind_eq_bind, Option.bind_some, zenv, ho, Option.map_some,
    Option.pure_def, zv]

/-- From the BFV noise headline's conclusion and `outputsUnderS?` to decryption with `s`. -/
theorem outputsDecrypt_of_encrypts (P : FullParams) (E : TraceBFV.Budget) (prog : Program)
    (B : ℕ) (hk : P.src.kind = .bfv) (hc : outputsUnderS? P.src prog = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N))
    (h : ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, TraceBFV.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct) :
    OutputsDecrypt P E prog s msgs cts := by
  obtain ⟨ρ, hev, hrun⟩ := h
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, hv, hct, henc⟩ := hrun σ hσ o ho
  have hkey : v.key = 1 := by
    have h1 := List.all_eq_true.mp hc o ho
    rw [outputKey?_eq_bfv P.src hk prog msgs ρ hev o v hv] at h1
    simpa using h1
  obtain ⟨m, hm, hdm⟩ := Validation.BFV.encrypts_bfv_decrypts P hk s B v ct henc
  rw [hkey, FHE.KeySwitch.automorph_one] at hdm
  exact ⟨v, ct, m, hv, hct, hm, hkey, hdm⟩

end Validation.BFVMul.Cert

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul

variable (P : FullParams)

/-- **The worst-case BFV certificate.** If the reference analysis accepts and every output is
under the secret key itself, every output of every run within the budget decrypts with `s` to
the message the program computes. -/
theorem certified_decrypts (E : TraceBFV.Budget) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bfv)
    (h : refAnalyzeBFV P E prog = some B)
    (hc : Encrypt.outputsUnderS? P.src prog = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    OutputsDecrypt P E prog s msgs cts :=
  Cert.outputsDecrypt_of_encrypts P E prog B hk hc s msgs cts
    (Validation.BFV.refAnalyzeBFV_sound P E prog B hP hk h s msgs cts hin)

/-- **The BFV headline at the budget of an approximate multiplication.** -/
theorem certifiedApprox_sound (lay : Budget.KSLayout) (U r pa : ℕ) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bfv)
    (h : refAnalyzeBFV P (BudgetBFV.certifiedApprox P lay U r pa) prog = some B)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, TraceBFV.Run P (BudgetBFV.certifiedApprox P lay U r pa) s prog.body
          (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct :=
  Validation.BFV.refAnalyzeBFV_sound P _ prog B hP hk h s msgs cts hin

end Validation.BFVMul
