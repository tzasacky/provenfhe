import Challenge.IndCpaD.Textbook
import Validation.IndCpaD.Generic

/-!
# Validation.IndCpaD.Textbook — proofs of the pins of `Challenge.IndCpaD.Textbook`

The textbook-multiplication evaluator is the transcription's execution of the input `tb x`
(`x` with the technique `textbook`). At every instruction other than a product it computes what
the transcription of `x` computes (`libStep_tb`, when `x` is not `HPSPOVERQLEVELED`), so the step
lemma of the library (`Validation.CertifyBFV.lib_stepOK`, at the exact arithmetic, which conforms)
applies; at a product it is `bfvMul`, which meets the contract within the budget of every
instruction (`certifyBFV?_textbook_mul`, `_square`). The induction along the body (`tb_run`) and
its start (`tb_run_aux`) are those of `lib_run` and `library_run_aux`.
-/

namespace Validation.IndCpaD
open Spec NPoly Scheme Source Correct Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
  Spec.BudgetBFV Challenge.BFV Challenge.BFVMul Challenge.CertifyBFV Challenge.BFVEncrypt
  Challenge.IndCpaD Spec.IndCpaDBFV Challenge.RealizeBFV

/-- `x` with the technique `textbook`. -/
abbrev tb (x : InputBFV) : InputBFV := { x with mul := some .textbook }

set_option maxHeartbeats 1000000 in
/-- **Away from a product, the textbook-multiplication execution computes what the
transcription computes**, when the technique is not `HPSPOVERQLEVELED`. -/
theorem libStep_tb (x : InputBFV) (hnl : ∀ Ps, x.mul ≠ some (.leveled Ps)) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (n : ℕ) (ρ : Env x.P.src)
    (σ : Trace.CtEnv x.P) (i : Instr) (hi : ∀ d a b, i ≠ .mul d a b) (hi' : ∀ d a, i ≠ .square d a) :
    libStep (tb x) A rk gk n ρ σ i = libStep x A rk gk n ρ σ i := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  have hks : ∀ (ℓ : ℕ) (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
      libKS (tb ⟨P, lay, prog, mul, ft, pa, ms, drops⟩) A n ℓ ca keys =
        libKS ⟨P, lay, prog, mul, ft, pa, ms, drops⟩ A n ℓ ca keys := by
    intro ℓ ca keys
    rw [Validation.CertifyBFV.libKS_plain (x := tb ⟨P, lay, prog, mul, ft, pa, ms, drops⟩) A n ℓ
        (by rintro ⟨⟨Ps, h⟩, -⟩; cases h) ca keys,
      Validation.CertifyBFV.libKS_plain (x := ⟨P, lay, prog, mul, ft, pa, ms, drops⟩) A n ℓ
        (by rintro ⟨⟨Ps, h⟩, -⟩; exact hnl Ps h) ca keys]
  cases i with
  | mul d a b => exact absurd rfl (hi d a b)
  | square d a => exact absurd rfl (hi' d a)
  | relin d a => exact hks (levelOf ρ a) ((σ a).getD []) rk
  | keySwitch d a =>
    exact congrArg (List.map (automorph (((ρ a).map (·.key)).getD 1)))
      (hks (levelOf ρ a) (((σ a).getD []).map (automorph (rotInv P.src.N (((ρ a).map (·.key)).getD 1))))
        (gk (((ρ a).map (·.key)).getD 1)))
  | _ => rfl

section TB
open Validation.CertifyBFV
open Validation.BFV Validation.BFV.SoundAux Validation.BFV.PerInstrAux
open Validation.Budget.RunAux (Shape Levels levels_step)

variable {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
  (hks : ksDeclOK? x.P x.lay = true)
  (hft : x.floatTol = false →
    (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
    ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
  (hnl : ∀ Ps, x.mul ≠ some (.leveled Ps))
  {s : IntPoly x.P.src.N} (hs : SecretOK x.P.secretBound s)
  {rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N)}
  (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
  {gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)}
  (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
    Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
  {msgs : Var → Msg x.P.src.t x.P.src.N} {cts : Var → List (IntPoly x.P.src.N)}
  (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)

include h hks hft hnl hs hrk hgk hin in
/-- **One instruction of the textbook-multiplication execution** meets its contract within its
budget. -/
theorem tb_stepOK (n : ℕ) (i : Instr) (ρ ρ' : Env x.P.src) (σ : Trace.CtEnv x.P)
    (β : Var → Option TraceBFV.Bnd) (v : Val x.P.src) (b : TraceBFV.Bnd)
    (hat : AtInstr x msgs n i ρ) (hstep : step x.P.src ρ i = some ρ')
    (hv : ρ' (Trace.dst i) = some v) (hb : refBoundBFV x.P (c.budget n) v.level β i = some b)
    (hdom : domainOK ρ i = true) (hsh : Shape x.P ρ σ) (hlv : Levels x.P ρ)
    (hpp : PartsPos ρ) (hinv : Validation.BFV.SoundAux.Inv x.P s ρ β σ) (hpt : PtB x β)
    (hodd : FHE.BFV.KSLeveled.KeyOdd ρ) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set (Trace.dst i) (libStep (tb x) Spec.Float.exact rk gk n (zenv ρ) σ i)) i := by
  have hlvl : ∀ a xa, ρ a = some xa → levelOf (zenv ρ) a = xa.level := fun a xa hx => by
    rw [levelOf_zenv, levelOf_some hx]
  by_cases hm : (∃ d a b, i = .mul d a b) ∨ ∃ d a, i = .square d a
  · rcases hm with ⟨d, a, b', rfl⟩ | ⟨d, a, rfl⟩
    · rcases hx : ρ a with _ | xa
      · simp [step, hx] at hstep
      rcases hy : ρ b' with _ | xb
      · simp [step, hx, hy] at hstep
      rw [dom_mul, hx, hy] at hdom
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hdom
      obtain ⟨ca, ha, hla⟩ := hsh a xa hx
      obtain ⟨cb, hcb, hlb⟩ := hsh b' xb hy
      show TraceBFV.StepOK _ _ _ _ _ _
        (σ.set d (bfvMul x.P.src.t (x.P.src.modulus (levelOf (zenv ρ) a)) ((σ a).getD [])
          ((σ b').getD []))) _
      rw [getD_of ha, getD_of hcb, hlvl a xa hx]
      exact Validation.CertifyBFV.certifyBFV?_textbook_mul x c h s hs msgs cts hin n d a b' ρ ρ' hat σ xa xb ca cb
        hstep hx hy ha hcb (hla.trans hdom.1) (hlb.trans hdom.2) hdom.1 hdom.2
    · rcases hx : ρ a with _ | xa
      · simp [step, hx] at hstep
      rw [dom_sq, hx] at hdom
      simp only [Option.any_some, beq_iff_eq] at hdom
      obtain ⟨ca, ha, hla⟩ := hsh a xa hx
      show TraceBFV.StepOK _ _ _ _ _ _
        (σ.set d (bfvMul x.P.src.t (x.P.src.modulus (levelOf (zenv ρ) a)) ((σ a).getD [])
          ((σ a).getD []))) _
      rw [getD_of ha, hlvl a xa hx]
      exact Validation.CertifyBFV.certifyBFV?_textbook_square x c h s hs msgs cts hin n d a ρ ρ' hat σ xa ca hstep hx
        ha (hla.trans hdom) hdom
  · have hi : ∀ d a b, i ≠ .mul d a b := fun d a b e => hm (Or.inl ⟨d, a, b, e⟩)
    have hi' : ∀ d a, i ≠ .square d a := fun d a e => hm (Or.inr ⟨d, a, e⟩)
    rw [libStep_tb x hnl Spec.Float.exact rk gk n (zenv ρ) σ i hi hi']
    exact lib_stepOK h hks hft (A := Spec.Float.exact)
      (fun _ => Validation.BFVMul.exact_conforms) hs hrk hgk hin n i ρ ρ' σ β v b hat hstep hv hb
      hdom hsh hlv hpp hinv hpt hodd

include h hks hft hnl hs hrk hgk hin in
/-- **The induction along the body** (as `lib_run`). -/
theorem tb_run : ∀ (body pre : List Instr) (ρ : Env x.P.src) (σ : Trace.CtEnv x.P)
    (β : Var → Option TraceBFV.Bnd) (r : Env x.P.src × (Var → Option TraceBFV.Bnd)),
    x.prog.body = pre ++ body →
    pre.foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ →
    AllExact ρ → Shape x.P ρ σ → Levels x.P ρ → PartsPos ρ → Validation.BFV.SoundAux.Inv x.P s ρ β σ → PtB x β →
    FHE.BFV.KSLeveled.KeyOdd ρ →
    refRunBFVAt x.P c.budget pre.length body (zenv ρ) β = some r →
    TraceBFV.RunAt x.P c.budget s pre.length body ρ σ
      (runLibraryAux (tb x) Spec.Float.exact rk gk pre.length body (zenv ρ) σ)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | i :: is, pre, ρ, σ, β, r, hbody, hρf, hρ, hsh, hlv, hpp, hinv, hpt, hodd, hr => by
    obtain ⟨hP, hk, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK x c h
    obtain ⟨ρz', vz, b, h1, h2, h3, h4, h5, hdom⟩ := refRunAt_cons_some x.P hr
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    rw [hz] at h1
    obtain ⟨ρ', hstep, rfl⟩ := Option.map_eq_some_iff.mp h1
    simp only [zenv] at h2
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h2
    have h3' : refBoundBFV x.P (c.budget pre.length) v.level β i = some b := h3
    have h4' : bndOK x.P v.level b = true := h4
    rw [domainOK_zenv] at hdom
    have hat : AtInstr x msgs pre.length i ρ := ⟨pre, is, hbody, rfl, hρf⟩
    have hok := tb_stepOK h hks hft hnl hs hrk hgk hin pre.length i ρ ρ' σ β v b hat hstep hv h3'
      hdom hsh hlv hpp hinv hpt hodd
    set σ' := σ.set (Trace.dst i) (libStep (tb x) Spec.Float.exact rk gk pre.length (zenv ρ) σ i)
      with hσ'
    obtain ⟨ct, hσct, hct⟩ := dst_ok hk hP (c.budget pre.length) s hinv h3' hstep hv h4' hok
    obtain ⟨w, hw⟩ := step_set hstep
    have hinv' : Validation.BFV.SoundAux.Inv x.P s ρ' (fun y => if y = Trace.dst i then some b else β y) σ' := by
      intro y by' hy
      by_cases hyd : y = Trace.dst i
      · subst hyd
        simp only [ite_true, Option.some.injEq] at hy
        subst hy
        refine ⟨v, ct, hv, ?_, hct⟩
        rw [hσct]; simp [Trace.CtEnv.set]
      · simp only [hyd, ite_false] at hy
        obtain ⟨v', ct', h1', h2', h3''⟩ := hinv y by' hy
        refine ⟨v', ct', ?_, ?_, h3''⟩
        · rw [hw]; simp [Env.set, hyd, h1']
        · rw [hσct]; simp [Trace.CtEnv.set, hyd, h2']
    have hpt' : PtB x (fun y => if y = Trace.dst i then some b else β y) := by
      intro y b' hb'
      by_cases hyd : y = Trace.dst i
      · simp only [hyd, ite_true, Option.some.injEq] at hb'
        subst hb'
        obtain ⟨y', hy'⟩ := refBound_pt h3'
        exact hpt y' b' hy'
      · simp only [hyd, ite_false] at hb'
        exact hpt y b' hb'
    have hρf' : (pre ++ [i]).foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ' := by
      rw [List.foldlM_append, hρf]
      simp [hstep]
    have hlen : (pre ++ [i]).length = pre.length + 1 := by simp
    have ih := tb_run is (pre ++ [i]) ρ' σ' _ r (by rw [hbody]; simp) hρf' (hex ρ' hstep)
      (shape_step hsh hstep hok) (levels_step hlv hstep) (partsPos_step hpp hstep) hinv' hpt'
      (FHE.BFV.KSLeveled.step_keyOdd i hstep hodd) (by rw [hlen]; exact h5)
    rw [hlen] at ih
    rw [Validation.CertifyBFV.runLibraryAux_cons (tb x) Spec.Float.exact rk gk pre.length i is
      (zenv ρ) (zenv ρ') σ (by rw [hz, hstep]; rfl)]
    exact ⟨ρ', σ', hstep, hok, ih⟩

end TB

open Validation.CertifyBFV Validation.BFV Validation.BFV.SoundAux Validation.BFV.PerInstrAux in
/-- **The textbook-multiplication execution is a run within the certificate's budget** (as
`library_run_aux`). -/
theorem tb_run_aux (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hks : ksDeclOK? x.P x.lay = true)
    (hft : x.floatTol = false →
      (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
      ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
    (hnl : ∀ Ps, x.mul ≠ some (.leveled Ps))
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
      Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
      (Trace.initCt x.P x.prog cts) (runLibrary (tb x) Spec.Float.exact rk gk cts) := by
  obtain ⟨hP, -, -, -, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK x c h
  obtain ⟨-, -, -, -, hB, -⟩ := Validation.CertifyBFV.certifyBFV?_spec x c h
  obtain ⟨hk, hdecl, ρz, βf, hrun, -⟩ := refAnalyzeAt_some hB
  have hfind : ∀ y d, x.prog.inputs.find? (·.name = y) = some d →
      d.name = y ∧ (cts y).length = d.parts := by
    intro y d hd
    have hn : d.name = y := by simpa using List.find?_some hd
    refine ⟨hn, ?_⟩
    have he := hin y d hd
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte] at he
      exact he.1
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, hl, -⟩ := enc_elim hk he
      exact hl
  have hz0 : zenv (initEnv x.P.src x.prog msgs) = initEnv x.P.src x.prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  have hdok : ∀ y v, initEnv x.P.src x.prog msgs y = some v →
      1 ≤ v.parts ∧ 1 ≤ v.level ∧ v.level ≤ x.P.src.qs.length := by
    intro y v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.1, hok.2.1, hok.2.2.1⟩
  have hinv0 : Validation.BFV.SoundAux.Inv x.P s (initEnv x.P.src x.prog msgs)
      (fun y => (x.prog.inputs.find? (·.name = y)).map fun d =>
        if d.parts = 1 then .pt (TraceBFV.inputBound x.P x.prog d)
        else .ct (TraceBFV.inputBound x.P x.prog d))
      (Trace.initCt x.P x.prog cts) := by
    intro y b hb
    obtain ⟨d, hd, hbe⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨hn, -⟩ := hfind y d hd
    have he := hin y d hd
    have he' : Sem x.P s b (inputVal x.P msgs d) (cts y) := by
      by_cases hp : d.parts = 1
      · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
      · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
    unfold inputVal at he'; rw [hn] at he'
    exact ⟨_, cts y, by simp [initEnv, hd], by simp [Trace.initCt, hd], he'⟩
  have hpt0 : PtB x (fun y => (x.prog.inputs.find? (·.name = y)).map fun d =>
        if d.parts = 1 then .pt (TraceBFV.inputBound x.P x.prog d)
        else .ct (TraceBFV.inputBound x.P x.prog d)) := by
    intro y b hb
    obtain ⟨d, hd, hbe⟩ := Option.map_eq_some_iff.mp hb
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte, TraceBFV.Bnd.pt.injEq] at hbe
      subst hbe
      refine le_foldl_max 0 (List.mem_map.mpr ⟨d, List.mem_filter.mpr
        ⟨List.mem_of_find?_eq_some hd, by simp [hp]⟩, rfl⟩)
    · simp only [hp, ↓reduceIte] at hbe; cases hbe
  have hrunL := tb_run h hks hft hnl hs hrk hgk hin x.prog.body [] _ _ _ _ rfl rfl
    (Validation.CertifyBFV.allExact_init hk hin)
    (fun y v hv => by
      simp only [initEnv, Option.map_eq_some_iff] at hv
      obtain ⟨d, hd, rfl⟩ := hv
      exact ⟨cts y, by simp [Trace.initCt, hd], (hfind y d hd).2⟩)
    (fun y v hv => (hdok y v hv).2) (fun y v hv => (hdok y v hv).1) hinv0 hpt0
    (FHE.BFV.KSLeveled.initEnv_keyOdd _ _ _ hdecl) hrun
  change TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
    (Trace.initCt x.P x.prog cts)
    (runLibraryAux (tb x) Spec.Float.exact rk gk 0 x.prog.body
      (initEnv x.P.src x.prog fun _ => .exact 0) (Trace.initCt x.P x.prog cts))
  rw [← hz0]
  exact hrunL

/-- `textEval`, unfolded (a local `rfl` equation). -/
theorem textEval_eq (St : Setting) (pk : PK (St := St)) (C : Circ St)
    (cs : List (CT (St := St))) :
    textEval St pk C cs = C.prog.outputs.map fun o =>
      (C.outLevel o, (runLibrary (tb C.input) Spec.Float.exact pk.rk pk.gk (C.cts cs) o).getD []) :=
  rfl

theorem textEval_meets (St : Setting) (hnl : ∀ Ps, St.base.mul ≠ some (.leveled Ps)) :
    EvalMeets St (textEval St) := by
  intro pk sk hk C hadm fc hfc hx ins hins hlen
  have hadm' := admissible_some C fc hfc hadm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hadm'
  have hid' : AssumptionBFV.idealised ∉ fc.cert.assumed := by
    intro hm
    have : fc.cert.assumed.contains AssumptionBFV.idealised = true := List.elem_eq_true_of_mem hm
    rw [this] at hadm'; exact absurd hadm'.1 (by simp)
  have hcert := analysed_cert C fc hfc
  obtain ⟨hP, -, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK _ fc.cert hcert
  have hks : ksKeysIn St.base.P.src St.rots C.prog.body
      (initEnv St.base.P.src C.prog fun _ => .exact 0) = true := by
    unfold Circ.extraOK at hx
    simp only [Bool.and_eq_true] at hx
    exact hx.2
  have hin := inputsOK_fresh C fc hfc hx pk sk hk ins hins hlen
  obtain ⟨gk', hagree, hgk'⟩ := gk_extend hP.N_pow2 pk sk hk
  obtain ⟨hs, -, -, hrk, -⟩ := hk
  have hrun := tb_run_aux (analysed C fc.params.inputNoise) fc.cert hcert
    (Validation.CertifyBFV.ksDecl_of _ fc.cert hcert)
    (Validation.CertifyBFV.hft_of _ fc.cert hcert hid') hnl sk.s hs pk.rk hrk gk' hgk' _ _ hin
  refine ⟨runLibrary (tb C.input) Spec.Float.exact pk.rk pk.gk
    (C.cts (ins.map fun p => enc pk p.1 p.2)), ?_, ?_⟩
  swap
  · exact (textEval_eq St pk C _).symm ▸ rfl
  have e1 := runLibrary_gk_congr (tb C.input) St.rots Spec.Float.exact pk.rk pk.gk gk'
    (C.cts (ins.map fun p => enc pk p.1 p.2)) hks hagree
  have e2 := runLibrary_inputNoise (tb C.input) fc.params.inputNoise Spec.Float.exact pk.rk gk'
    (C.cts (ins.map fun p => enc pk p.1 p.2))
  have e3 : runLibrary (tb C.input) Spec.Float.exact pk.rk pk.gk
      (C.cts (ins.map fun p => enc pk p.1 p.2)) =
      runLibrary (tb (analysed C fc.params.inputNoise)) Spec.Float.exact pk.rk gk'
        (C.cts (ins.map fun p => enc pk p.1 p.2)) := e1.trans e2.symm
  rw [e3]
  exact hrun

theorem correct_textEval (St : Setting) (hSt : freshDecOK St = true)
    (hnl : ∀ Ps, St.base.mul ≠ some (.leveled Ps)) :
    Spec.IndCpaD.Correct (schemeWith St (textEval St)) :=
  correct_of_meets St hSt _ (textEval_meets St hnl)

theorem correct_textEval_tiny :
    Spec.IndCpaD.Correct (schemeWith tinySetting (textEval tinySetting)) :=
  correct_textEval tinySetting Validation.IndCpaD.admissible_tiny.1 (fun Ps h => by cases h)

theorem correct_textEval_seal :
    Spec.IndCpaD.Correct (schemeWith sealSetting (textEval sealSetting)) :=
  correct_textEval sealSetting (by decide +kernel) (fun Ps h => by cases h)

example := (@textEval_meets : type_of% @Challenge.IndCpaD.textEval_meets)
example := (@correct_textEval : type_of% @Challenge.IndCpaD.correct_textEval)
example := (@correct_textEval_tiny : type_of% @Challenge.IndCpaD.correct_textEval_tiny)
example := (@correct_textEval_seal : type_of% @Challenge.IndCpaD.correct_textEval_seal)

end Validation.IndCpaD
