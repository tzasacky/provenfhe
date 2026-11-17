import Validation.MSB.KeySwitch
import Validation.Profile

/-!
# Validation.MSB — proofs of the pins of `Challenge.MSB`

Items 1–4 are in `Validation.MSB.Basic`, `Validation.MSB.Steps` and `Validation.MSB.KeySwitch`;
this module restates them under the locked names, adds the t-readings of the algorithms
(`stepOK_toLSB` after the MSB contract) and proves the certificate statement: the MSB inputs are
LSB inputs after the t-reading (`msbEncrypts_toLSB`), an MSB run is an LSB run
(`run_toLSB`), and `Validation.Profile.certifyProfile?_sound` applies. No locked definition is
unfolded by name: `OutputsCertified` is read by `obtain`.
-/

namespace Validation.MSB
open Spec NPoly Scheme Source Correct Spec.Budget Spec.MSB Challenge.Profile Challenge.Certify
open Validation.Ring Validation.Scheme

variable (P : FullParams)

theorem keySwitch_toLSB (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ (.galois x.key) B s keys) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.keySwitch P lay ℓ ca keys))) (.keySwitch d a) :=
  stepOK_toLSB P E s ρ ρ' σ _ _ hstep
    (keySwitch_stepOK P lay hP hS ℓ hℓ hlay E hE B hB s hs ρ ρ' σ d a x ca hstep hx hca hl hlen
      keys hkeys)

theorem relin_toLSB (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ .square B s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.relin P lay ℓ ca keys))) (.relin d a) :=
  stepOK_toLSB P E s ρ ρ' σ _ _ hstep
    (relin_stepOK P lay hP hS ℓ hℓ hlay E hE B hB s hs keys hkeys ρ ρ' σ d a x ca hstep hx hca hl
      hlen)

theorem rescale_toLSB (hP : SchemeParamsOK P) (E : Trace.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hE : msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (hca : σ a = some ca) (hlen : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca))) (.modSwitch d a) :=
  stepOK_toLSB P E s ρ ρ' σ _ _ hstep
    (rescale_stepOK P hP E s hs ρ ρ' σ d a x ca hE hstep hx hca hlen)

theorem mulTensor_stepOK (E : Trace.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src)
    (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.mulTensor P.src.t ca cb)) (.mul d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  obtain ⟨c0, c1, rfl⟩ := List.length_eq_two.mp hla
  obtain ⟨d0, d1, rfl⟩ := List.length_eq_two.mp hlb
  refine ⟨_, _, Validation.Source.set_self _ _ _, ?_, rfl, ?_⟩
  · simp [MSB.mulTensor, h2x, h2y]
  · refine ⟨x, y, _, _, hx, hy, ha, hb, ?_⟩
    try dsimp only
    rw [← hkey]
    unfold Trace.phaseAt
    simp only [MSB.mulTensor, List.map_cons, List.map_nil, ofInt_mul, ofInt_add, ofInt_smul,
      phase_three', phase_two']
    apply eq_of_neZero; intro
    simp only [smul_eq_const_mul]; ring

/-! ## Certificates -/

/-- `t` is coprime to the modulus of every level. -/
theorem coprime_modulus (hP : SchemeParamsOK P) (ℓ : ℕ) :
    Nat.Coprime P.src.t (P.src.modulus ℓ) := by
  show Nat.Coprime P.src.t (P.src.qs.take ℓ).prod
  exact Nat.coprime_list_prod_right_iff.mpr fun q hq => hP.plaintext.2 q (List.mem_of_mem_take hq)

theorem toLSBEnv_initCt (prog : Program) (cts : Var → List (IntPoly P.src.N)) :
    toLSBEnv P (Trace.initCt P prog cts) =
      Trace.initCt P prog (fun x => toLSB P.src.t (cts x)) := by
  funext x
  unfold toLSBEnv Trace.initCt
  cases prog.inputs.find? (·.name = x) <;> rfl

/-- An MSB input with stored-representative bound `Bin` is, read through `t`, an LSB input
within any `b ≥ Bin`. -/
theorem encrypts_toLSB (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (s : IntPoly P.src.N)
    (Bin b : ℕ) (hb : Bin ≤ b) (v : Val P.src) (hwrap : 2 * Bin < P.src.modulus v.level)
    (ct : List (IntPoly P.src.N)) (h : MSB.Encrypts P s Bin v ct) :
    Correct.Encrypts P s b v (toLSB P.src.t ct) := by
  obtain ⟨hlen, hm⟩ := h
  rw [Validation.Source.encrypts_bgv_iff P hk]
  refine ⟨by rw [length_toLSB, hlen], ?_⟩
  cases hv : v.msg with
  | exact m =>
    rw [hv] at hm
    have h := msbEncryptsRep_toLSB P.src.t _ Bin (coprime_modulus P hP v.level) hwrap _ ct m hm
    exact ⟨m, rfl, h.1, h.2.trans hb⟩

theorem certifyProfile?_sound_msb (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (Bin : ℕ) (hBin : Bin ≤ P.inputNoise) (hbnd : ∀ x b, prog.boundOf x = some b → Bin ≤ b)
    (hwrap : ∀ d ∈ prog.inputs, 2 * Bin < P.src.modulus d.level)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : MSB.InputsOK P s Bin prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, MSB.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct m b, ρ o = some v ∧ σ o = some ct ∧
          outs.lookup o = some b ∧ v.msg = .exact m ∧ v.key = 1 ∧
          msbDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m ∧
          BGVEncrypts P.src.t b s ((toLSB P.src.t ct).map (ofInt (P.src.modulus v.level))) m := by
  obtain ⟨hP, hk, -, -⟩ := Validation.Profile.certifyProfile?_some h
  set ctsL : Var → List (IntPoly P.src.N) := fun x => toLSB P.src.t (cts x)
  have hinL : Correct.InputsOK P s prog msgs ctsL := by
    intro x d hd
    exact encrypts_toLSB P hP hk s Bin _ hBin _ (hwrap d (List.mem_of_find?_eq_some hd)) _
      (hin x d hd)
  have hbL : Trace.BoundsOK P s prog msgs ctsL := by
    intro x d b hd hb
    exact encrypts_toLSB P hP hk s Bin b (hbnd x b hb) _
      (hwrap d (List.mem_of_find?_eq_some hd)) _ (hin x d hd)
  obtain ⟨ρ, hρ, hall⟩ :=
    Validation.Profile.certifyProfile?_sound P E prog sw B outs h s msgs ctsL hinL hbL
  refine ⟨ρ, hρ, fun σ hrun o ho => ?_⟩
  have hrunL := run_toLSB P E s prog.body _ _ σ hrun
  rw [toLSBEnv_initCt] at hrunL
  obtain ⟨v, ctL, m, b, hv, hσ, hb, henc, hm, hkey, hdec, -⟩ := hall _ hrunL o ho
  have hσ' : (σ o).map (toLSB P.src.t) = some ctL := hσ
  cases hσo : σ o with
  | none => rw [hσo] at hσ'; simp at hσ'
  | some ct =>
    rw [hσo] at hσ'
    simp only [Option.map_some, Option.some.injEq] at hσ'
    subst hσ'
    refine ⟨v, ct, m, b, hv, rfl, hb, hm, hkey, by rw [msbDecrypt_toLSB]; exact hdec, ?_⟩
    obtain ⟨-, m', hm', hbgv⟩ := (Validation.Source.encrypts_bgv_iff P hk s b v _).mp henc
    rw [hm] at hm'
    cases hm'
    rw [hkey, FHE.KeySwitch.automorph_one] at hbgv
    exact hbgv

/-! ## Twins -/

example := (@msbDecrypt_toLSB : type_of% @Challenge.MSB.msbDecrypt_toLSB)
example := (@msbDecrypt_iff : type_of% @Challenge.MSB.msbDecrypt_iff)
example := (@msbEncrypts_toLSB : type_of% @Challenge.MSB.msbEncrypts_toLSB)
example := (@toLSB_msbEncrypts : type_of% @Challenge.MSB.toLSB_msbEncrypts)
example := (@toLSB_encrypts_of_rep : type_of% @Challenge.MSB.toLSB_encrypts_of_rep)
example := (@msbEncryptsRep_toLSB : type_of% @Challenge.MSB.msbEncryptsRep_toLSB)
example := (@keyValidMSB_iff : type_of% @Challenge.MSB.keyValidMSB_iff)
example := (@gadgetKeysOK_iff : type_of% @Challenge.MSB.gadgetKeysOK_iff)
example := (@keyValidMSB_toLSB : type_of% @Challenge.MSB.keyValidMSB_toLSB)
example := (@gadgetKeys_restrict : type_of% @Challenge.MSB.gadgetKeys_restrict)
example := (@stepOK_toLSB : type_of% @Challenge.MSB.stepOK_toLSB)
example := (@run_toLSB : type_of% @Challenge.MSB.run_toLSB)
example := (@keySwitch_stepOK : type_of% @Challenge.MSB.keySwitch_stepOK)
example := (@relin_stepOK : type_of% @Challenge.MSB.relin_stepOK)
example := (@rescale_stepOK : type_of% @Challenge.MSB.rescale_stepOK)
example := (@mulTensor_stepOK : type_of% @Challenge.MSB.mulTensor_stepOK)
example := (@keySwitch_toLSB : type_of% @Challenge.MSB.keySwitch_toLSB)
example := (@relin_toLSB : type_of% @Challenge.MSB.relin_toLSB)
example := (@rescale_toLSB : type_of% @Challenge.MSB.rescale_toLSB)
example := (@certifyProfile?_sound_msb : type_of% @Challenge.MSB.certifyProfile?_sound_msb)

end Validation.MSB
