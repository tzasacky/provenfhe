import Challenge.Profile.Inputs
import Validation.Profile.Tool

/-!
# Validation.Profile.Inputs — proofs of the pins of `Challenge.Profile.Inputs`

The witness is `centered m :: [0, …, 0]` with the declared number of components: its phase is
the centred message whatever the secret and the Galois key, so it encrypts within every bound of
at least `⌊t/2⌋` at every modulus above `t` (as `Validation.Params.bgv_inputs_exist` for two
components). The number of components is at least one by `Decl.ok`, which the reference analysis
checks. Necessity at a small modulus: the centred phase is within `⌊Q/2⌋`, so an encryption within
any bound is one within `⌊Q/2⌋`, excluded by `bgv_small_noise_excludes`.
-/

namespace Validation.ProfileInputs
open Spec NPoly Scheme Source Correct Challenge.Profile Validation.Ring Validation.Scheme
  Challenge.ProfileInputs

theorem phase_replicate_zero {q N : ℕ} (s : Poly q N) (n : ℕ) :
    phase s (List.replicate n (0 : Poly q N)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, phase, ih]
    ext i
    simp [coeff_mul']

/-- The witness, scheme-independent: `centered m :: [0, …, 0]` has centred phase `centered m`
under every secret, at every modulus above `t`. -/
theorem bgvEncrypts_witness {N t Q : ℕ} [NeZero t] (s : IntPoly N) (m : Poly t N) (k : ℕ)
    (hQ : t < Q) (b : ℕ) (hb : t / 2 ≤ b) :
    BGVEncrypts t b s ((centered m :: List.replicate k 0).map (ofInt Q)) m := by
  have hc : ∀ i, (((centered m).coeff i).natAbs) ≤ t / 2 := fun i =>
    ZMod.natAbs_valMinAbs_le _
  have hph : phase (ofInt Q s) ((centered m :: List.replicate k 0).map (ofInt Q))
      = ofInt Q (centered m) := by
    rw [List.map_cons, List.map_replicate, ofInt_zero, phase, phase_replicate_zero]
    ext i
    simp [coeff_mul']
  have hcp : centeredPhase s ((centered m :: List.replicate k 0).map (ofInt Q)) = centered m := by
    rw [centeredPhase, hph]
    apply centered_ofInt
    intro i
    have h1 := hc i
    have h3 : |(centered m).coeff i| = (((centered m).coeff i).natAbs : ℤ) :=
      Int.abs_eq_natAbs _
    rw [h3]
    have : 2 * ((centered m).coeff i).natAbs < Q := by omega
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · rw [bgvDecrypt, hcp, ofInt_centered]
  · rw [hcp]
    unfold normInf
    exact Finset.sup_le fun i _ => (hc i).trans hb

/-- The witness encrypts within every bound of at least `⌊t/2⌋`. -/
theorem encrypts_witness (P : FullParams) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (hp : 1 ≤ v.parts) (hQ : P.src.t < P.src.modulus v.level) (b : ℕ) (hb : P.src.t / 2 ≤ b) :
    Encrypts P s b v (centered m :: List.replicate (v.parts - 1) 0) := by
  have ht : 2 ≤ P.src.t := (hP.plaintext).1
  have : NeZero P.src.t := ⟨by omega⟩
  rw [Validation.Params.encrypts_bgv_exact_iff P hk s _ v m hm]
  exact ⟨by simp; omega, bgvEncrypts_witness _ m _ hQ b hb⟩

/-! ## What acceptance checks -/

theorem certifyProfile?_inputs_checked (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (d : Decl) (hd : d ∈ prog.inputs) :
    P.src.t < P.src.modulus d.level ∧ ∀ b, prog.boundOf d.name = some b → P.src.t / 2 ≤ b := by
  have hI := Validation.Profile.certifyProfile?_inputsMsgOK h
  have e : Challenge.Certify.inputsMsgOK? P prog = (prog.inputs.all fun d =>
      decide (P.src.t < P.src.modulus d.level) &&
        (prog.boundOf d.name).all fun b => decide (P.src.t / 2 ≤ b)) := rfl
  rw [e] at hI
  have hd' := List.all_eq_true.mp hI d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd'
  refine ⟨hd'.1, fun b hb => ?_⟩
  have h2 := hd'.2
  rw [hb] at h2
  simpa using h2

theorem certifyBFVProfile?_plain_checked (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Program) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs)) (d : Decl) (hd : d ∈ prog.inputs)
    (hp : d.parts = 1) : P.src.t / 2 ≤ TraceBFV.inputBound P prog d := by
  have hI := Validation.Profile.certifyBFVProfile?_plain h
  have e : Challenge.CertifyBFV.plainBoundsOK P prog = (prog.inputs.all fun d =>
      decide (d.parts ≠ 1) || decide (P.src.t / 2 ≤ TraceBFV.inputBound P prog d)) := rfl
  rw [e] at hI
  have hd' := List.all_eq_true.mp hI d hd
  simpa [hp] using hd'

/-! ## The inputs exist -/

theorem certifyProfile?_inputs_exist_all (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts := by
  classical
  have hname : ∀ {x : Var} {d : Decl}, prog.inputs.find? (·.name = x) = some d → d.name = x :=
    fun hd => by simpa using List.find?_some hd
  have hQ : ∀ x d, prog.inputs.find? (·.name = x) = some d → P.src.t < P.src.modulus d.level :=
    fun x d hd => (certifyProfile?_inputs_checked P E prog sw B outs h d
      (List.mem_of_find?_eq_some hd)).1
  have hbd : ∀ x d b, prog.inputs.find? (·.name = x) = some d → prog.boundOf x = some b →
      P.src.t / 2 ≤ b := fun x d b hd hb =>
    (certifyProfile?_inputs_checked P E prog sw B outs h d (List.mem_of_find?_eq_some hd)).2 b
      (by rw [hname hd]; exact hb)
  obtain ⟨hP, hk, hB, -⟩ := Validation.Profile.certifyProfile?_some h
  obtain ⟨-, hdecl, -⟩ := Validation.Headline.NoiseAux.refAnalyze_some hB
  have hex : ∀ x, ∃ ct, ∀ d, prog.inputs.find? (·.name = x) = some d →
      ∀ b, P.src.t / 2 ≤ b → Encrypts P s b (inputVal P (fun x => .exact (m x)) d) ct := by
    intro x
    rcases hf : prog.inputs.find? (·.name = x) with _ | d
    · exact ⟨[], fun d h => by rw [hf] at h; cases h⟩
    have hmem := List.mem_of_find?_eq_some hf
    have hok := List.all_eq_true.mp hdecl d hmem
    simp only [Decl.ok, decide_eq_true_eq] at hok
    refine ⟨centered (m d.name) :: List.replicate (d.parts - 1) 0, fun d' hd' b hb => ?_⟩
    cases hd'.symm.trans hf
    exact encrypts_witness P hP hk s (inputVal P (fun x => .exact (m x)) d) (m d.name) rfl
      hok.1 (hQ x d hf) b hb
  choose cts hcts using hex
  exact ⟨cts, fun x d hd => hcts x d hd _ (hP.msgRange hk),
    fun x d b hd hb => hcts x d hd b (hbd x d b hd hb)⟩

theorem certify?_inputs_exist (x : Certify.Input) (c : Certify.Certificate)
    (h : Challenge.Certify.certify? x = some c) (s : IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) :
    ∃ cts, InputsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.BoundsOK c.params s x.prog (fun y => .exact (m y)) cts :=
  certifyProfile?_inputs_exist_all _ _ _ _ _ _ (Validation.Profile.certify?_profile x c h) s m

/-- Under the BFV profile decision every level's modulus exceeds `t`. -/
theorem bfv_t_lt_modulus {P : FullParams} (hP : SchemeParamsOK P)
    (henc : P.src.t - 1 ≤ P.src.qs.headD 0 / 2) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    P.src.t < P.src.modulus ℓ := by
  have ht : 2 ≤ P.src.t := hP.plaintext.1
  have hle := Validation.IndCpaD.headD_le_modulus P.src ℓ hℓ (fun q hq => (hP.prime q hq).pos)
  have hmem : P.src.qs.headD 0 ∈ P.src.qs := by
    cases hq : P.src.qs with
    | nil => exact absurd hq hP.qs_nonempty
    | cons q qs => simp
  have hne : P.src.qs.headD 0 ≠ P.src.t := fun e => by
    have hc := hP.plaintext.2 _ hmem
    rw [e, Nat.coprime_self] at hc
    omega
  omega

theorem certifyBFVProfile?_inputs_exist_all (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Program) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs))
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, TraceBFV.InputsOK P s prog (fun x => .exact (m x)) cts := by
  classical
  obtain ⟨hP, hk, hdec, henc, hB, -⟩ := Validation.Profile.certifyBFVProfile?_some h
  obtain ⟨-, hdecl, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hB
  have ht : 0 < P.src.t := by have := hP.plaintext.1; omega
  have : NeZero P.src.t := ⟨by omega⟩
  have hex : ∀ x, ∃ ct, ∀ d, prog.inputs.find? (·.name = x) = some d →
      if d.parts = 1 then
        TraceBFV.PlainOK P s (TraceBFV.inputBound P prog d)
          (inputVal P (fun x => .exact (m x)) d) ct
      else Encrypts P s (TraceBFV.inputBound P prog d) (inputVal P (fun x => .exact (m x)) d)
        ct := by
    intro x
    rcases hf : prog.inputs.find? (·.name = x) with _ | d
    · exact ⟨[], fun d h => by rw [hf] at h; cases h⟩
    have hmem := List.mem_of_find?_eq_some hf
    have hok := List.all_eq_true.mp hdecl d hmem
    have hok' := hok
    simp only [Decl.ok, decide_eq_true_eq] at hok'
    have hmsg : (inputVal P (fun x => .exact (m x)) d).msg = .exact (m d.name) := rfl
    by_cases hp : d.parts = 1
    · refine ⟨[centered (m d.name)], fun d' hd' => ?_⟩
      cases hd'.symm.trans hf
      simp only [hp, ↓reduceIte]
      refine ⟨by simp [inputVal, hp], m d.name, hmsg, ?_⟩
      exact bgvEncrypts_witness _ (m d.name) 0 (bfv_t_lt_modulus hP henc d.level hok'.2.1) _
        (certifyBFVProfile?_plain_checked P E prog B outs h d hmem hp)
    · have hdo := Validation.Profile.inputsDecOK_at hdec d hmem hp hok
      obtain ⟨ct, hct⟩ := Validation.BFV.bfv_inputs_exist P hk ht s
        (inputVal P (fun x => .exact (m x)) d) (m d.name) hmsg hok'.1
        (Validation.Profile.decOK_zero hdo)
      refine ⟨ct, fun d' hd' => ?_⟩
      cases hd'.symm.trans hf
      simp only [hp, ↓reduceIte]
      exact Validation.Profile.encrypts_mono_bfv hk hmsg hct (Nat.zero_le _)
  choose cts hcts using hex
  exact ⟨cts, fun x d hd => hcts x d hd⟩

theorem certifyBFV?_inputs_exist (x : CertifyBFV.InputBFV) (c : CertifyBFV.CertificateBFV)
    (h : Challenge.CertifyBFV.certifyBFV? x = some c) (s : IntPoly x.P.src.N)
    (m : Var → Poly x.P.src.t x.P.src.N) :
    ∃ cts, TraceBFV.InputsOK x.P s x.prog (fun y => .exact (m y)) cts :=
  certifyBFVProfile?_inputs_exist_all _ _ _ _ _ (Validation.Profile.certifyBFV?_profile x c h) s m

theorem bgv_low_level_excludes (P : FullParams) (hk : P.src.kind = .bgv) (hN : 0 < P.src.N)
    (ht : 2 ≤ P.src.t) (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src)
    (hQ0 : 0 < P.src.modulus v.level) (hQ : P.src.modulus v.level / 2 < P.src.t / 2)
    (hm : v.msg = .exact (NPoly.const ((P.src.t / 2 : ℕ) : ZMod P.src.t)))
    (ct : List (IntPoly P.src.N)) : ¬ Encrypts P s B v ct := by
  intro h
  have : NeZero (P.src.modulus v.level) := ⟨by omega⟩
  rw [Validation.Params.encrypts_bgv_exact_iff P hk s B v _ hm] at h
  obtain ⟨hl, hd, -⟩ := h
  apply Validation.Params.bgv_small_noise_excludes P hk hN ht s (P.src.modulus v.level / 2) hQ v
    hm ct
  rw [Validation.Params.encrypts_bgv_exact_iff P hk s _ v _ hm]
  refine ⟨hl, hd, ?_⟩
  unfold normInf centeredPhase
  exact Finset.sup_le fun i _ => ZMod.natAbs_valMinAbs_le _

example := (@certifyProfile?_inputs_exist_all :
  type_of% @Challenge.ProfileInputs.certifyProfile?_inputs_exist_all)
example := (@certifyProfile?_inputs_checked :
  type_of% @Challenge.ProfileInputs.certifyProfile?_inputs_checked)
example := (@certifyBFVProfile?_plain_checked :
  type_of% @Challenge.ProfileInputs.certifyBFVProfile?_plain_checked)
example := (@certify?_inputs_exist : type_of% @Challenge.ProfileInputs.certify?_inputs_exist)
example := (@certifyBFVProfile?_inputs_exist_all :
  type_of% @Challenge.ProfileInputs.certifyBFVProfile?_inputs_exist_all)
example := (@certifyBFV?_inputs_exist : type_of% @Challenge.ProfileInputs.certifyBFV?_inputs_exist)
example := (@bgv_low_level_excludes : type_of% @Challenge.ProfileInputs.bgv_low_level_excludes)

end Validation.ProfileInputs
