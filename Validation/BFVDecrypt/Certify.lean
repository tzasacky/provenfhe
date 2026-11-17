import Validation.BFVDecrypt.Lib
import Validation.BFV.Sound
import Validation.CertifyBFV
import Validation.Budget.KeySwitch

/-!
# Validation.BFVDecrypt.Certify — the certificate with the library's decryption
-/

namespace Validation.BFVDecrypt
open Spec NPoly Scheme Source Correct Spec.Float Spec.DecryptBFV Spec.CertifyBFV
  Challenge.CertifyBFV Challenge.BFVDecrypt
open Validation.BFV.SoundAux

/-! ### Levels do not depend on the messages (BFV) -/

theorem foldlM_zenv_bfv {Pr : Params} (hk : Pr.kind = .bfv) : ∀ (body : List Instr) (ρ : Env Pr),
    AllExact ρ → body.foldlM (step Pr) (zenv ρ) = (body.foldlM (step Pr) ρ).map zenv
  | [], _, _ => rfl
  | i :: is, ρ, hρ => by
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    simp only [List.foldlM_cons, Option.bind_eq_bind, hz]
    rcases hs : step Pr ρ i with _ | ρ'
    · rfl
    · simp only [Option.map_some, Option.bind_some]
      exact foldlM_zenv_bfv hk is ρ' (hex ρ' hs)

/-- The level of an output is the same for all messages (BFV). -/
theorem outputLevel?_eq_bfv (P : Params) (hk : P.kind = .bfv) (prog : Program)
    (msgs : Var → Msg P.t P.N) (ρ : Env P) (h : eval P prog msgs = some ρ) (o : Var) (v : Val P)
    (ho : ρ o = some v) : Decrypt.outputLevel? P prog o = some v.level := by
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
  have hfold := foldlM_zenv_bfv hk prog.body _ hρ0
  rw [hz0, h3, Option.map_some] at hfold
  have hev : eval P prog (fun _ => .exact 0) = some (zenv ρ) := by
    have hfz : (prog.inputs.all fun dcl =>
        ((fun _ => .exact 0 : Var → Msg P.t P.N) dcl.name).fits P.kind) = true := by
      rw [List.all_eq_true]; intro dcl _; rw [hk]; rfl
    have hoz : (prog.outputs.all fun o => (zenv ρ o).isSome) = true := by
      simpa [zenv] using hout
    simp only [eval, hd, hfz, hfold, hoz, guard, Option.bind_eq_bind, ite_true,
      Option.pure_def, Option.bind_some]
  simp only [Decrypt.outputLevel?, hev, Option.bind_eq_bind, Option.bind_some, zenv, ho,
    Option.map_some, Option.pure_def, zv]

/-- `Challenge.BFVDecrypt.output_decryptLib`. -/
theorem output_decryptLib (P : FullParams) (hk : P.src.kind = .bfv) (A : ArithD)
    (hA : ConformsD A) (hp : decParamsOK? P.src.t P.src.qs = true)
    (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N))
    (m : Poly P.src.t P.src.N) (hmsg : v.msg = .exact m) (hkey : v.key = 1)
    (hlev : v.level = P.src.qs.length) (he : Encrypts P s B v ct)
    (hB : decLibOK? P.src.t P.src.qs B = true) (i : Fin P.src.N) :
    (((bfvDecryptLib A P.src.t P.src.qs s (ct.map (ofInt P.src.qs.prod))).coeff i : ℕ) :
        ZMod P.src.t) = m.coeff i ∧
      (bfvDecryptLib A P.src.t P.src.qs s (ct.map (ofInt P.src.qs.prod))).coeff i ≤ P.src.t := by
  have hQ : P.src.modulus v.level = P.src.qs.prod := by
    rw [hlev]; unfold Params.modulus; rw [List.take_length]
  unfold Encrypts at he
  rw [hk, hmsg] at he
  obtain ⟨_, he⟩ := he
  simp only at he
  rw [hkey, FHE.KeySwitch.automorph_one, hQ] at he
  exact bfvDecryptLib_correct A hA P.src.t P.src.qs hp s _ m B he.2 hB i

theorem lookup_mem {o : Var} {B : ℕ} : ∀ {l : List (Var × ℕ)}, l.lookup o = some B → (o, B) ∈ l
  | [], h => by simp at h
  | (a, b) :: l, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hab
      cases h
      have : o = a := by simpa using hab
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- `Challenge.BFVDecrypt.certifyBFV?_decryptsLib`. -/
theorem certifyBFV?_decryptsLib (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hd : decryptLibOK? x c = true) (A : ArithD) (hA : ConformsD A)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ ρ, Source.eval x.P.src x.prog msgs = some ρ ∧
      ∀ σ, TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
          (Trace.initCt x.P x.prog cts) σ →
        ∀ o ∈ x.prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
          ∀ i, (((bfvDecryptLib A x.P.src.t x.P.src.qs s
                  (ct.map (ofInt x.P.src.qs.prod))).coeff i : ℕ) : ZMod x.P.src.t) = m.coeff i ∧
            (bfvDecryptLib A x.P.src.t x.P.src.qs s (ct.map (ofInt x.P.src.qs.prod))).coeff i
              ≤ x.P.src.t := by
  obtain ⟨_, hk, -, -, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK x c h
  obtain ⟨hd1, hd2⟩ := Bool.and_eq_true_iff.mp hd
  obtain ⟨hd3, hd4⟩ := Bool.and_eq_true_iff.mp hd1
  obtain ⟨_, hp⟩ := Bool.and_eq_true_iff.mp hd3
  have hlev : ∀ o ∈ x.prog.outputs, Decrypt.outputLevel? x.P.src x.prog o = some x.P.src.qs.length :=
    fun o ho => by simpa using List.all_eq_true.mp hd4 o ho
  have hlib : ∀ ob ∈ c.outputs, decLibOK? x.P.src.t x.P.src.qs ob.2 = true :=
    fun ob h => List.all_eq_true.mp hd2 ob h
  obtain ⟨ρ, hev, hrun⟩ := Validation.CertifyBFV.certifyBFV?_sound x c h s msgs cts hin
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, m, B, hv, hct, hlk, henc, hm, hkey, _⟩ := hrun σ hσ o ho
  have hl : v.level = x.P.src.qs.length := by
    have h1 := outputLevel?_eq_bfv x.P.src hk x.prog msgs ρ hev o v hv
    rw [hlev o ho] at h1
    exact (Option.some.inj h1).symm
  refine ⟨v, ct, m, hv, hct, hm, fun i => ?_⟩
  exact output_decryptLib x.P hk A hA hp s B v ct m hm hkey hl henc
    (hlib (o, B) (lookup_mem hlk)) i

end Validation.BFVDecrypt
