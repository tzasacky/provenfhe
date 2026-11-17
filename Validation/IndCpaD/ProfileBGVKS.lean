import Challenge.IndCpaD.ProfileBGVKS
import Validation.IndCpaD.ProfileBGVInstances
import Validation.Realize
import Validation.Budget.Restrict
import Validation.Budget.Basic

/-!
# Validation.IndCpaD.ProfileBGVKS — proofs of the pins of `Challenge.IndCpaD.ProfileBGVKS`

The evaluator's run: induction over the body with three invariants, the shapes and the levels of
`Validation.Budget.RunAux` and "the evaluator's environment is the zero-message replay"
(`zenv ρ`, by `step_zenv_bgv`), so the level and Galois element the evaluator reads are those of
the true values. Each exact step is `exact_step`; relinearization and key switching are
`Validation.Realize.relinOpenFHE_stepOK`, `keySwitchOpenFHE_stepOK` with the top-level keys cut
to the operand's level (`Validation.Budget.gadgetKeys_restrict`, the evaluator reads only the
first digits: `relinOpenFHE_take`, `keySwitchOpenFHE_take`); the modulus switch is
`Validation.Trace.stepOK_modSwitch_textbook_parts`. Key generation: the key relation holds by
ring arithmetic, and the error `t·eⱼ` is its own centred representative below half the modulus.
The locked definitions are read through `show`/`change` with their bodies.
-/

namespace Validation.IndCpaDProfile
open Spec NPoly Scheme Source Spec.Encrypt Spec.IndCpaDProfile Spec.Budget
  Challenge.IndCpaDProfile Challenge.Source Challenge.Realize
open Challenge.Profile (certifyProfile?)
open Validation.Budget.RunAux (Shape shape_step Levels levels_step)
open Validation.BFV.SoundAux (zenv zv)
open Validation.Ring Validation.Scheme

section KS
variable (P : FullParams) (lay : KSLayout) (rots : List ℕ) (E : Trace.Budget)
  (s : IntPoly P.src.N) (rk : List (IntPoly P.src.N × IntPoly P.src.N))
  (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))

theorem ksStep_exact (ρ : Env P.src) (σ : Trace.CtEnv P) (i : Instr)
    (hi : exactInstr i = true) : ksStep P lay rk gk ρ σ i = exactStep P σ i := by
  cases i <;> first | rfl | exact absurd hi Bool.false_ne_true

/-- The side conditions, read. -/
theorem ksSide_facts (h : ksSide P lay = true) :
    SpecialOK P ∧ Spec.Certify.layoutOK? P lay = true ∧ Spec.Certify.keysRestrict? P = true ∧
      lay.canonical = true := by
  change (specialOK? P && Spec.Certify.layoutOK? P lay && Spec.Certify.keysRestrict? P &&
    lay.canonical) = true at h
  simp only [Bool.and_eq_true] at h
  exact ⟨Validation.Budget.specialOK?_sound P h.1.1.1, h.1.1.2, h.1.2, h.2⟩

variable {P lay rots E s rk gk}
variable (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (hside : ksSide P lay = true)
  (hs : SecretOK P.secretBound s)
  (hrk : GadgetKeysOK P lay P.src.qs.length .square s rk)
  (hgk : ∀ g ∈ rots, GadgetKeysOK P lay P.src.qs.length (.galois g) s (gk g))
include hk hP hside hs hrk hgk

/-- One step of the evaluator meets its contract. -/
theorem ks_step {ρ ρ' : Env P.src} {σ : Trace.CtEnv P} (i : Instr) (hsh : Shape P ρ σ)
    (hlv : Levels P ρ) (hneed : ksNeedAt P lay rots E (zenv ρ) i = true)
    (hstep : step P.src ρ i = some ρ') :
    ∃ σ', ksStep P lay rk gk (zenv ρ) σ i = some σ' ∧ Trace.StepOK P E s ρ ρ' σ σ' i := by
  obtain ⟨hS, hlay, hkr, hc⟩ := ksSide_facts P lay hside
  have restrict : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → ∀ tgt keys,
      GadgetKeysOK P lay P.src.qs.length tgt s keys →
      GadgetKeysOK P lay ℓ tgt s (keys.take (lay.sizes ℓ).length) := fun ℓ h1 hℓ tgt keys h =>
    Validation.Budget.gadgetKeys_restrict P lay tgt hP ℓ hℓ
      (Validation.Budget.layoutOK?_restricts P lay hlay ℓ h1 hℓ)
      (fun _ => Validation.Budget.keysRestrict?_level P hkr hP ℓ h1 hℓ) s keys h
  have okAt : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := fun ℓ h1 hℓ =>
    Validation.Budget.restrictsTo_okAt lay _ ℓ hℓ
      (Validation.Budget.layoutOK?_restricts P lay hlay ℓ h1 hℓ)
  by_cases hi : exactInstr i = true
  · rw [ksStep_exact P lay rk gk _ σ i hi]
    exact exact_step P E s i hsh hstep hi
  cases i
  case relin d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    have hz : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hn : ((zenv ρ a).elim true fun x =>
        decide (ksBoundAt P lay x.level ≤ E.keySwitch)) = true := hneed
    rw [hz] at hn
    have hn' : decide (ksBoundAt P lay x.level ≤ E.keySwitch) = true := hn
    have hok := Validation.Realize.relinOpenFHE_stepOK P lay hk hP hS hc x.level hL
      (okAt _ h1 hL) E (of_decide_eq_true hn') s hs _ (restrict _ h1 hL .square rk hrk)
      ρ ρ' σ d a x ca hstep hx ha rfl hla
    rw [Validation.Realize.relinOpenFHE_take] at hok
    refine ⟨_, ?_, hok⟩
    show (zenv ρ a).bind (fun x => (σ a).map fun ca =>
      σ.set d (relinOpenFHE P lay x.level ca rk)) = _
    rw [hz, ha]; rfl
  case keySwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    have hz : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hn : ((zenv ρ a).elim true fun x =>
        decide (ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)) = true := hneed
    rw [hz] at hn
    have hn' : (decide (ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)) =
      true := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn'
    have hok := Validation.Realize.keySwitchOpenFHE_stepOK P lay hk hP hS hc x.level hL
      (okAt _ h1 hL) E hn'.1 s hs ρ ρ' σ d a x ca hstep hx ha rfl hla _
      (restrict _ h1 hL (.galois x.key) (gk x.key) (hgk x.key hn'.2))
    rw [Validation.Realize.keySwitchOpenFHE_take] at hok
    refine ⟨_, ?_, hok⟩
    show (zenv ρ a).bind (fun x => (σ a).map fun ca =>
      σ.set d (keySwitchOpenFHE P lay x.level ca (gk x.key))) = _
    rw [hz, ha]; rfl
  case modSwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    have hz : zenv ρ a = some (zv x) := by simp [zenv, hx]
    have hn : ((zenv ρ a).elim true fun x =>
        decide (msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)) = true := hneed
    rw [hz] at hn
    have hn' : decide (msBudgetAt P x.parts ≤ E.modSwitchAt x.parts) = true := hn
    have hok := Validation.Trace.stepOK_modSwitch_textbook_parts P hk hP E s hs ρ ρ' σ d a x ca
      (of_decide_eq_true hn') hstep hx ha hla
    refine ⟨_, ?_, hok⟩
    show (zenv ρ a).bind (fun x => (σ a).map fun ca =>
      σ.set d (ca.map (bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!))) = _
    rw [hz, ha]; rfl
  all_goals exact absurd rfl hi

/-- **The evaluator's run** is a run within `E`. -/
theorem ks_run : ∀ (body : List Instr) (ρ ρf : Env P.src) (σ : Trace.CtEnv P),
    Shape P ρ σ → Levels P ρ → ksNeed P lay rots E body (zenv ρ) = true →
    body.foldlM (step P.src) ρ = some ρf →
    ∃ σf, ksRun P lay rk gk body (zenv ρ) σ = some σf ∧ Trace.Run P E s body ρ σ σf
  | [], _, _, σ, _, _, _, _ => ⟨σ, rfl, rfl⟩
  | i :: is, ρ, ρf, σ, hsh, hlv, hneed, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', hstep, hrest⟩ := h
    have hz := (step_zenv_bgv hk (Validation.IndCpaD.allExact_all ρ) i).1
    rw [hstep, Option.map_some] at hz
    have hn : (ksNeedAt P lay rots E (zenv ρ) i &&
        (step P.src (zenv ρ) i).elim true (ksNeed P lay rots E is)) = true := hneed
    rw [hz, Bool.and_eq_true] at hn
    obtain ⟨σ', he, hok⟩ := ks_step hk hP hside hs hrk hgk i hsh hlv hn.1 hstep
    obtain ⟨σf, hf, hrun⟩ := ks_run is ρ' ρf σ' (shape_step hsh hstep hok)
      (levels_step hlv hstep) hn.2 hrest
    refine ⟨σf, ?_, ρ', σ', hstep, hok, hrun⟩
    show (step P.src (zenv ρ) i).bind (fun ρ0' => (ksStep P lay rk gk (zenv ρ) σ i).bind
      fun σ' => ksRun P lay rk gk is ρ0' σ') = _
    rw [hz, Option.bind_some, he, Option.bind_some]
    exact hf

end KS

/-! ## The locked statements -/

theorem ksEval_meets (D : AbsScheme) (henc : D.EncOKBGV) (lay : KSLayout) (rots : List ℕ)
    (prof : D.Circ → Trace.Budget)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      GadgetKeysOK D.P lay D.P.src.qs.length .square (D.sec sk) (rk pk) ∧
      ∀ g ∈ rots, GadgetKeysOK D.P lay D.P.src.qs.length (.galois g) (D.sec sk) (gk pk g)) :
    EvalMeetsBGV D prof (ksClass D lay rots prof)
      (fun pk C cs => ksEval D lay (rk pk) (gk pk) C cs) := by
  intro pk sk hk C hC ins hins hlen
  change (admBGV D prof C && ksSide D.Pe lay && ksNeed D.Pe lay rots (prof C) (D.prog C).body
    (initEnv D.P.src (D.prog C) fun _ => .exact 0)) = true at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hadm, hside⟩, hneed⟩ := hC
  obtain ⟨B, outs, hcert, hfit, hpe⟩ := admBGV_some hadm
  obtain ⟨hP, hkind, -⟩ := Validation.Profile.certifyProfile?_some hcert
  have ht : 0 < D.P.src.t := by have := hP.plaintext.1; exact lt_of_lt_of_le (by norm_num) this
  obtain ⟨hin, hbd⟩ := inputsOK_bgv hkind henc C ht hfit hpe pk sk hk ins hins hlen
  obtain ⟨ρ, hρ, -⟩ := Validation.Profile.certifyProfile?_sound D.Pe (prof C) (D.prog C)
    false B outs hcert (D.sec sk) _ _ hin hbd
  have hρ' := hρ
  simp only [Source.eval, Option.bind_eq_bind, Option.pure_def] at hρ'
  obtain ⟨hdecl, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨-, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨ρf, hbody, -⟩ := Option.bind_eq_some_iff.mp hρ'
  obtain ⟨hs, hrk, hgk⟩ := hkeys pk sk hk
  have hsh : Shape D.Pe (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x))
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2))) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact ⟨_, by simp [Trace.initCt, hd], (hin x d hd).1⟩
  have hlv : Levels D.Pe (initEnv D.P.src (D.prog C)
      fun x => .exact (D.msg C (ins.map Prod.fst) x)) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩
  have hz0 : zenv (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x)) =
      initEnv D.P.src (D.prog C) fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hneed
  obtain ⟨σf, hf, hrun⟩ := ks_run (P := D.Pe) (lay := lay) (rots := rots) (E := prof C)
    (s := D.sec sk) (rk := rk pk) (gk := gk pk) hkind hP hside hs hrk hgk (D.prog C).body _ ρf _
    hsh hlv hneed hbody
  refine ⟨σf, hrun, ?_⟩
  show ((ksRun D.Pe lay (rk pk) (gk pk) (D.prog C).body
      (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2)))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] = _
  rw [← hz0, hf]; rfl

theorem correct_ksEval (D : AbsScheme) (henc : D.EncOKBGV) (lay : KSLayout) (rots : List ℕ)
    (prof : D.Circ → Trace.Budget)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      GadgetKeysOK D.P lay D.P.src.qs.length .square (D.sec sk) (rk pk) ∧
      ∀ g ∈ rots, GadgetKeysOK D.P lay D.P.src.qs.length (.galois g) (D.sec sk) (gk pk g)) :
    Spec.IndCpaD.Correct (schemeBGV D (fun pk C cs => ksEval D lay (rk pk) (gk pk) C cs)
      (ksClass D lay rots prof)) :=
  correct_bgv D henc prof (ksClass D lay rots prof)
    (fun C h => by
      change (admBGV D prof C && ksSide D.Pe lay && ksNeed D.Pe lay rots (prof C) (D.prog C).body
        (initEnv D.P.src (D.prog C) fun _ => .exact 0)) = true at h
      simp only [Bool.and_eq_true] at h
      exact h.1.1)
    _ (ksEval_meets D henc lay rots prof rk gk hkeys)

/-! ## Key generation -/

theorem keyValid_gen (P : FullParams) (req : KeyReq P.src.N) (f : ℕ)
    (hf : req.factor = const (f : ZMod req.modulus)) (s e a : IntPoly P.src.N)
    (he1 : P.src.t * normInf e ≤ P.keyNoise) (he2 : 2 * (P.src.t * normInf e) < req.modulus) :
    KeyValid P.src.kind P.src.t P.keyNoise s req
      (ofInt _ ((P.src.t : ℤ) • e - a * s + ((f : ℤ)) • req.target.eval s)) (ofInt _ a) := by
  have hbnd : ∀ i, |((P.src.t : ℤ) • e).coeff i| ≤ (P.src.t * normInf e : ℕ) := by
    intro i
    rw [coeff_smul', abs_mul, Nat.cast_mul]
    have := (normInf_le_iff e (normInf e)).mp le_rfl i
    have h0 : |(P.src.t : ℤ)| = P.src.t := abs_of_nonneg (by positivity)
    rw [h0]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have heq : ofInt req.modulus ((P.src.t : ℤ) • e - a * s + ((f : ℤ)) • req.target.eval s) +
      ofInt req.modulus a * ofInt req.modulus s - req.factor * ofInt req.modulus (req.target.eval s)
      = ofInt req.modulus ((P.src.t : ℤ) • e) := by
    apply eq_of_neZero; intro
    simp only [hf, ofInt_add, ofInt_sub, ofInt_mul, smul_eq_const_mul, ofInt_const]
    simp only [Int.cast_natCast]
    ring
  have hc : centered (ofInt req.modulus ((P.src.t : ℤ) • e)) = (P.src.t : ℤ) • e :=
    centered_ofInt _ fun i => by
      have := hbnd i
      have h2 : ((2 * (P.src.t * normInf e) : ℕ) : ℤ) < req.modulus := by exact_mod_cast he2
      push_cast at h2 this
      linarith
  refine ⟨?_, fun _ i => ?_⟩
  · show normInf (centered _) ≤ _
    rw [heq, hc, normInf_le_iff]
    intro i
    exact (hbnd i).trans (by exact_mod_cast he1)
  · show (P.src.t : ℤ) ∣ (centered _).coeff i
    rw [heq, hc, coeff_smul']
    exact dvd_mul_right _ _

theorem gadgetGen_ok (P : FullParams) (lay : KSLayout) (tgt : KeyTarget)
    (s : IntPoly P.src.N) (as es : List (IntPoly P.src.N))
    (hes : ∀ j, P.src.t * normInf (es.getD j 0) ≤ P.keyNoise ∧
      2 * (P.src.t * normInf (es.getD j 0)) < P.src.modulus P.src.qs.length * specialProd P) :
    GadgetKeysOK P lay P.src.qs.length tgt s (gadgetGen P lay tgt s as es) := by
  have hlen : (gadgetGen P lay tgt s as es).length = (lay.sizes P.src.qs.length).length := by
    show (List.map _ (List.range _)).length = _
    simp
  refine ⟨hlen, fun j hj => ?_⟩
  have e1 : (gadgetGen P lay tgt s as es)[j] =
      ((P.src.t : ℤ) • es.getD j 0 - as.getD j 0 * s +
        ((gadgetFactor (specialProd P) (digitModuli P lay P.src.qs.length) j : ℕ) : ℤ) •
          tgt.eval s, as.getD j 0) := by
    show (List.map _ (List.range _))[j] = _
    simp
  rw [e1]
  exact keyValid_gen P (gadgetReq P lay P.src.qs.length tgt j)
    (gadgetFactor (specialProd P) (digitModuli P lay P.src.qs.length) j) rfl s
    (es.getD j 0) (as.getD j 0) (hes j).1 (hes j).2

theorem keyGen_keysOK (P : FullParams) (lay : KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ)
    (s e a : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (he : normInf e ≤ Bk) (ra re : List (IntPoly P.src.N)) (ga ge : ℕ → List (IntPoly P.src.N))
    (hre : ∀ j, P.src.t * normInf (re.getD j 0) ≤ P.keyNoise ∧
      2 * (P.src.t * normInf (re.getD j 0)) < P.src.modulus P.src.qs.length * specialProd P)
    (hge : ∀ g ∈ rots, ∀ j, P.src.t * normInf ((ge g).getD j 0) ≤ P.keyNoise ∧
      2 * (P.src.t * normInf ((ge g).getD j 0)) < P.src.modulus P.src.qs.length * specialProd P) :
    (bgvKSData P lay rots Bk Bu B1 B2).KeysOK (keyGen P lay s e a ra re ga ge) (s, e) := by
  refine ⟨hs, he, ?_, gadgetGen_ok P lay .square s ra re hre,
    fun g hg => gadgetGen_ok P lay (.galois g) s (ga g) (ge g) (hge g hg)⟩
  show ofInt _ ((P.src.t : ℤ) • e - a * s + a * s) = ofInt _ ((P.src.t : ℤ) • e)
  congr 1
  apply eq_of_neZero; intro; ring

theorem encOK_bgvKSData (P : FullParams) (lay : KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ)
    (ht : 2 ≤ P.src.t)
    (hQ : 2 * (bgvKSData P lay rots Bk Bu B1 B2).eps < P.src.modulus P.src.qs.length) :
    (bgvKSData P lay rots Bk Bu B1 B2).EncOKBGV := by
  intro pk sk hk m r hr
  change Poly P.src.t P.src.N at m
  change KSPK P.src.N at pk
  change IntPoly P.src.N × IntPoly P.src.N at sk
  obtain ⟨hs, he, hpk, -⟩ := hk
  obtain ⟨hu, h1, h2⟩ := hr
  have hε := Validation.FreshNoise.freshError_worst sk.1 sk.2 r.1 r.2.1 r.2.2
    P.secretBound Bk Bu B1 B2 hs he hu h1 h2
  obtain ⟨hst1, hst2⟩ := Validation.FreshNoise.liftMsg_stored P.src.t (by omega) m
  have := Validation.FreshNoise.encrypt_encrypts P.src.t (P.src.modulus P.src.qs.length)
    (P.src.t - 1) _ ht sk.1 sk.2 pk.1 pk.2.1 (liftMsg m) r.1 r.2.1 r.2.2 hpk hst2 hε hQ
  rw [hst1] at this
  exact ⟨rfl, rfl, this⟩

theorem correct_ksEval_bgvKSSeal :
    Spec.IndCpaD.Correct (schemeBGV bgvKSSealData
      (fun pk C cs => ksEval bgvKSSealData bgvKSLayout pk.2.2.1 pk.2.2.2 C cs)
      (ksClass bgvKSSealData bgvKSLayout [5] bgvKSSealProfile)) :=
  correct_ksEval bgvKSSealData
    (encOK_bgvKSData bgvKSSeal bgvKSLayout [5] 21 1 21 21 (by decide) (by decide))
    bgvKSLayout [5] bgvKSSealProfile (fun pk => pk.2.2.1) (fun pk => pk.2.2.2)
    (fun _ _ hk => ⟨hk.1, hk.2.2.2.1, hk.2.2.2.2⟩)

theorem keyGen_noisy_bgvKSSeal (s e a : IntPoly bgvKSSeal.src.N)
    (hs : SecretOK bgvKSSeal.secretBound s) (he : normInf e ≤ 21)
    (ra : List (IntPoly bgvKSSeal.src.N)) (ga : ℕ → List (IntPoly bgvKSSeal.src.N)) :
    bgvKSSealData.KeysOK
      (keyGen bgvKSSeal bgvKSLayout s e a ra (List.replicate 4 (onesPoly _))
        ga (fun _ => List.replicate 4 (onesPoly _))) (s, e) := by
  have h1 : ∀ j, normInf ((List.replicate 4 (onesPoly bgvKSSeal.src.N)).getD j 0) ≤ 1 := by
    intro j
    have e : (List.replicate 4 (onesPoly bgvKSSeal.src.N)).getD j 0 =
        if j < 4 then onesPoly _ else 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
    rw [e]
    split_ifs
    · rw [normInf_le_iff]; intro i
      show |(1 : ℤ)| ≤ ((1 : ℕ) : ℤ)
      simp
    · rw [normInf_zero]; omega
  have hb : ∀ j, bgvKSSeal.src.t * normInf ((List.replicate 4 (onesPoly bgvKSSeal.src.N)).getD j 0)
      ≤ bgvKSSeal.keyNoise ∧
      2 * (bgvKSSeal.src.t * normInf ((List.replicate 4 (onesPoly bgvKSSeal.src.N)).getD j 0)) <
        bgvKSSeal.src.modulus bgvKSSeal.src.qs.length * specialProd bgvKSSeal := by
    intro j
    have hm := Nat.mul_le_mul_left bgvKSSeal.src.t (h1 j)
    have c1 : bgvKSSeal.src.t * 1 ≤ bgvKSSeal.keyNoise := by decide
    have c2 : 2 * (bgvKSSeal.src.t * 1) <
        bgvKSSeal.src.modulus bgvKSSeal.src.qs.length * specialProd bgvKSSeal := by decide
    exact ⟨hm.trans c1, lt_of_le_of_lt (Nat.mul_le_mul_left 2 hm) c2⟩
  exact keyGen_keysOK bgvKSSeal bgvKSLayout [5] 21 1 21 21 s e a hs he ra _ ga _ hb
    (fun _ _ => hb)

theorem ksClass_bgvKSSeal :
    ksClass bgvKSSealData bgvKSLayout [5] bgvKSSealProfile bgvKSSealCirc = true ∧
      exactClass bgvSealData bgvSealProfile bgvSealCirc = true := by
  decide +kernel

example := (@ksEval_meets : type_of% @Challenge.IndCpaDProfile.ksEval_meets)
example := (@correct_ksEval : type_of% @Challenge.IndCpaDProfile.correct_ksEval)
example := (@keyGen_keysOK : type_of% @Challenge.IndCpaDProfile.keyGen_keysOK)
example := (@encOK_bgvKSData : type_of% @Challenge.IndCpaDProfile.encOK_bgvKSData)
example := (@correct_ksEval_bgvKSSeal :
  type_of% @Challenge.IndCpaDProfile.correct_ksEval_bgvKSSeal)
example := (@keyGen_noisy_bgvKSSeal : type_of% @Challenge.IndCpaDProfile.keyGen_noisy_bgvKSSeal)
example := (@ksClass_bgvKSSeal : type_of% @Challenge.IndCpaDProfile.ksClass_bgvKSSeal)

end Validation.IndCpaDProfile
