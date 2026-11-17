import Challenge.IndCpaD.ProfileBGVInstances
import Validation.IndCpaD.ProfileBGV
import Validation.Budget.RunExists
import Validation.FreshNoise.Basic

/-!
# Validation.IndCpaD.ProfileBGVInstances — proofs of the pins of `Challenge.IndCpaD.ProfileBGVInstances`

The exact evaluator: induction over the body with the shape invariant of
`Validation.Budget.RunAux` (every defined variable holds a ciphertext with the recorded number of
components); each step is the exact operation of `Validation.Trace` (`stepOK_add_padded`,
`stepOK_mul_tensor`, …), which meets its contract at every budget. The run starts from the inputs
because `Spec.Correct.InputsOK` gives the numbers of components, and the body is accepted by
`Source.step` because the profile certificate's `Source.eval` succeeds. The encryption:
`Validation.FreshNoise.encrypt_encrypts` with the stored representative `liftMsg m` of norm at
most `t − 1`. `exactStep` and `exactEval` are read through `show` with their bodies.
-/

namespace Validation.IndCpaDProfile
open Spec NPoly Scheme Source Spec.Encrypt Spec.IndCpaDProfile Challenge.IndCpaDProfile
  Challenge.Source
open Challenge.Profile (certifyProfile?)
open Validation.Budget.RunAux (Shape shape_step)

section Exact
variable (P : FullParams) (E : Trace.Budget) (s : IntPoly P.src.N)

/-- One exact step meets its contract. -/
theorem exact_step {ρ ρ' : Env P.src} {σ : Trace.CtEnv P} (i : Instr) (hsh : Shape P ρ σ)
    (hstep : step P.src ρ i = some ρ') (hi : exactInstr i = true) :
    ∃ σ', exactStep P σ i = some σ' ∧ Trace.StepOK P E s ρ ρ' σ σ' i := by
  cases i with
  | add d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    refine ⟨_, ?_, Validation.Trace.stepOK_add_padded P E s ρ ρ' σ d a b x y ca cb hstep hx hy
      ha hb hla hlb⟩
    show (σ a).bind (fun ca => (σ b).map fun cb => σ.set d (padZip (· + ·) ca cb)) = _
    rw [ha, hb]; rfl
  | sub d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    refine ⟨_, ?_, Validation.Trace.stepOK_sub_padded P E s ρ ρ' σ d a b x y ca cb hstep hx hy
      ha hb hla hlb⟩
    show (σ a).bind (fun ca => (σ b).map fun cb => σ.set d (padZip (· - ·) ca cb)) = _
    rw [ha, hb]; rfl
  | mul d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    refine ⟨_, ?_, Validation.Trace.stepOK_mul_tensor P E s ρ ρ' σ d a b x y ca cb hstep hx hy
      ha hb hla hlb⟩
    show (σ a).bind (fun ca => (σ b).map fun cb => σ.set d (tensorParts ca cb)) = _
    rw [ha, hb]; rfl
  | square d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.Trace.stepOK_square_textbook P E s ρ ρ' σ d a x ca hstep hx ha hla⟩
    show (σ a).map (fun ca => σ.set d (tensorParts ca ca)) = _
    rw [ha]; rfl
  | mulConst d a c =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.Trace.stepOK_mulConst_textbook P E s ρ ρ' σ d a c x ca hstep hx ha
      hla⟩
    show (σ a).map (fun ca => σ.set d (ca.map (c • ·))) = _
    rw [ha]; rfl
  | copy d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.Trace.stepOK_copy_textbook P E s ρ ρ' σ d a _ (Or.inl rfl) x ca
      hstep hx ha hla⟩
    show (σ a).map (fun ca => σ.set d ca) = _
    rw [ha]; rfl
  | toEval d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.Trace.stepOK_copy_textbook P E s ρ ρ' σ d a _ (Or.inr (Or.inl rfl))
      x ca hstep hx ha hla⟩
    show (σ a).map (fun ca => σ.set d ca) = _
    rw [ha]; rfl
  | toCoeff d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.Trace.stepOK_copy_textbook P E s ρ ρ' σ d a _ (Or.inr (Or.inr rfl))
      x ca hstep hx ha hla⟩
    show (σ a).map (fun ca => σ.set d ca) = _
    rw [ha]; rfl
  | dropLimbs d a k =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.Trace.stepOK_dropLimbs_textbook P E s ρ ρ' σ d a k x ca hstep hx ha
      hla⟩
    show (σ a).map (fun ca => σ.set d ca) = _
    rw [ha]; rfl
  | automorph d a g =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    refine ⟨_, ?_, Validation.Trace.stepOK_automorph_textbook P E s ρ ρ' σ d a g x ca hstep hx ha
      hla⟩
    show (σ a).map (fun ca => σ.set d (ca.map (automorph g))) = _
    rw [ha]; rfl
  | addPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    refine ⟨_, ?_, Validation.Trace.stepOK_addPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx
      hy ha hb hla⟩
    show (σ a).bind (fun ca => (σ p).map fun cp => σ.set d (padZip (· + ·) ca cp)) = _
    rw [ha, hb]; rfl
  | subPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    refine ⟨_, ?_, Validation.Trace.stepOK_subPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx
      hy ha hb hla⟩
    show (σ a).bind (fun ca => (σ p).map fun cp => σ.set d (padZip (· - ·) ca cp)) = _
    rw [ha, hb]; rfl
  | mulPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    refine ⟨_, ?_, Validation.Trace.stepOK_mulPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx
      hy ha hb hla⟩
    show (σ a).bind (fun ca => (σ p).map fun cp => σ.set d (ca.map (cp.headD 0 * ·))) = _
    rw [ha, hb]; rfl
  | relin d a => exact absurd hi Bool.false_ne_true
  | keySwitch d a => exact absurd hi Bool.false_ne_true
  | modSwitch d a => exact absurd hi Bool.false_ne_true

/-- **The exact run**: from the shapes, every body without key or modulus switching that
`Source.step` accepts is executed by `exactStep`, and the execution is a run at every budget. -/
theorem exact_run : ∀ (body : List Instr) (ρ ρf : Env P.src) (σ : Trace.CtEnv P),
    Shape P ρ σ → body.all exactInstr = true → body.foldlM (step P.src) ρ = some ρf →
    ∃ σf, body.foldlM (exactStep P) σ = some σf ∧ Trace.Run P E s body ρ σ σf
  | [], _, _, σ, _, _, _ => ⟨σ, rfl, rfl⟩
  | i :: is, ρ, ρf, σ, hsh, hall, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', hstep, hrest⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨σ', he, hok⟩ := exact_step P E s i hsh hstep hall.1
    obtain ⟨σf, hf, hrun⟩ := exact_run is ρ' ρf σ' (shape_step hsh hstep hok) hall.2 hrest
    refine ⟨σf, ?_, ρ', σ', hstep, hok, hrun⟩
    simp only [List.foldlM_cons, he, Option.bind_eq_bind, Option.bind_some]
    exact hf

end Exact

/-! ## The locked statements -/

theorem exactEval_meets (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget) :
    EvalMeetsBGV D prof (exactClass D prof) (fun _ C cs => exactEval D C cs) := by
  intro pk sk hk C hC ins hins hlen
  change (admBGV D prof C && exactOnly (D.prog C).body) = true at hC
  rw [Bool.and_eq_true] at hC
  obtain ⟨hadm, hex⟩ := hC
  change (D.prog C).body.all exactInstr = true at hex
  obtain ⟨B, outs, hcert, hfit, hpe⟩ := admBGV_some hadm
  obtain ⟨hP, hkind, -⟩ := Validation.Profile.certifyProfile?_some hcert
  have ht : 0 < D.P.src.t := by have := hP.plaintext.1; exact lt_of_lt_of_le (by norm_num) this
  obtain ⟨hin, hbd⟩ := inputsOK_bgv hkind henc C ht hfit hpe pk sk hk ins hins hlen
  obtain ⟨ρ, hρ, -⟩ := Validation.Profile.certifyProfile?_sound D.Pe (prof C) (D.prog C)
    false B outs hcert (D.sec sk) _ _ hin hbd
  have hρ' := hρ
  simp only [Source.eval, Option.bind_eq_bind, Option.pure_def] at hρ'
  obtain ⟨-, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨-, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨ρf, hbody, -⟩ := Option.bind_eq_some_iff.mp hρ'
  have hsh : Shape D.Pe (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x))
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2))) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact ⟨_, by simp [Trace.initCt, hd], (hin x d hd).1⟩
  obtain ⟨σf, hf, hrun⟩ := exact_run D.Pe (prof C) (D.sec sk) (D.prog C).body _ ρf _ hsh hex hbody
  refine ⟨σf, hrun, ?_⟩
  show (((D.prog C).body.foldlM (exactStep D.Pe)
      (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2)))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] = _
  rw [hf]; rfl

theorem correct_exactEval (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget) :
    Spec.IndCpaD.Correct (schemeBGV D (fun _ C cs => exactEval D C cs) (exactClass D prof)) :=
  correct_bgv D henc prof (exactClass D prof)
    (fun C h => by
      change (admBGV D prof C && exactOnly (D.prog C).body) = true at h
      exact ((Bool.and_eq_true _ _).mp h).1)
    _ (exactEval_meets D henc prof)

theorem encOK_bgvData (P : FullParams) (Bk Bu B1 B2 : ℕ) (ht : 2 ≤ P.src.t)
    (hQ : 2 * (bgvData P Bk Bu B1 B2).eps < P.src.modulus P.src.qs.length) :
    (bgvData P Bk Bu B1 B2).EncOKBGV := by
  intro pk sk hk m r hr
  change Poly P.src.t P.src.N at m
  change IntPoly P.src.N × IntPoly P.src.N at pk sk
  obtain ⟨hs, he, hpk⟩ := hk
  obtain ⟨hu, h1, h2⟩ := hr
  have hε := Validation.FreshNoise.freshError_worst sk.1 sk.2 r.1 r.2.1 r.2.2
    P.secretBound Bk Bu B1 B2 hs he hu h1 h2
  obtain ⟨hst1, hst2⟩ := Validation.FreshNoise.liftMsg_stored P.src.t (by omega) m
  have := Validation.FreshNoise.encrypt_encrypts P.src.t (P.src.modulus P.src.qs.length)
    (P.src.t - 1) _ ht sk.1 sk.2 pk.1 pk.2 (liftMsg m) r.1 r.2.1 r.2.2 hpk hst2 hε hQ
  rw [hst1] at this
  exact ⟨rfl, rfl, this⟩

theorem correct_exactEval_bgvSeal :
    Spec.IndCpaD.Correct (schemeBGV bgvSealData (fun _ C cs => exactEval bgvSealData C cs)
      (exactClass bgvSealData bgvSealProfile)) :=
  correct_exactEval bgvSealData
    (encOK_bgvData bgvSeal 41 1 41 41 (by decide) (by decide)) bgvSealProfile

example := (@exactEval_meets : type_of% @Challenge.IndCpaDProfile.exactEval_meets)
example := (@correct_exactEval : type_of% @Challenge.IndCpaDProfile.correct_exactEval)
example := (@encOK_bgvData : type_of% @Challenge.IndCpaDProfile.encOK_bgvData)
example := (@correct_exactEval_bgvSeal :
  type_of% @Challenge.IndCpaDProfile.correct_exactEval_bgvSeal)

end Validation.IndCpaDProfile
