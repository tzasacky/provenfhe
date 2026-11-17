import Challenge.BFVMul.KSLeveled
import FHE.BFV.KSLeveled
import FHE.BFV.KeySwitch
import Validation.Budget.Restrict

/-!
# Validation.BFVMul.KSLeveled — OpenFHE's key switching with an internal drop

Proofs of `Challenge.BFVMul.ksCore_realizable`, `stepOK_relin_leveled_tol`,
`stepOK_keySwitch_leveled_tol` and `run_key_odd`. The arithmetic is in `FHE/BFV/KSLeveled.lean`
(`leveledKS_phase`: the phase moves by `(D·X − c)·tgt + D·e`); the key switch at the reduced level
is `FHE.BFV.layoutKSPlain` on the top-level keys cut down
(`Validation.Budget.gadgetKeys_restrict`).
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFVMul
open FHE.BFV.KSLeveled FHE.BFV.FloatPOverQ

variable (P : FullParams)

/-- The basis facts both step statements use: with `qs = P.src.qs.take x.level` and
`l = qs.length - drop`, the first `l` limbs of `qs` are those of level `x.level - drop`, and
`Q/Q_l` is the product of the dropped limbs. -/
theorem leveled_basis (level drop : ℕ) (hℓL : level ≤ P.src.qs.length)
    (hpos : ∀ q ∈ P.src.qs.take level, 0 < q) :
    ((P.src.qs.take level).take ((P.src.qs.take level).length - drop)).prod =
        P.src.modulus (level - drop) ∧
      (P.src.qs.take level).drop ((P.src.qs.take level).length - drop) =
        (P.src.qs.take level).drop (level - drop) ∧
      P.src.modulus level / P.src.modulus (level - drop) =
        ((P.src.qs.take level).drop (level - drop)).prod := by
  have hlen : (P.src.qs.take level).length = level := by
    rw [List.length_take, min_eq_left hℓL]
  have htake : (P.src.qs.take level).take (level - drop) = P.src.qs.take (level - drop) := by
    rw [List.take_take, min_eq_left (Nat.sub_le _ _)]
  have hQl : 0 < P.src.modulus (level - drop) := by
    show 0 < (P.src.qs.take (level - drop)).prod
    rw [← htake]
    exact List.prod_pos fun q hq => hpos q (List.mem_of_mem_take hq)
  refine ⟨by rw [hlen, htake]; rfl, by rw [hlen], ?_⟩
  have h := FHE.BFV.MulPOverQ.prod_take_mul_drop (P.src.qs.take level) (level - drop)
  rw [htake] at h
  show (P.src.qs.take level).prod / P.src.modulus (level - drop) = _
  rw [← h]
  exact Nat.mul_div_cancel_left _ hQl

theorem ksCore_realizable (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hk : P.src.kind = .bfv) (hS : Budget.SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : Budget.restrictsTo lay P.src.qs.length ℓ = true) :
    ∃ core : IntPoly P.src.N → List (IntPoly P.src.N × IntPoly P.src.N) →
        IntPoly P.src.N × IntPoly P.src.N,
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (tgt : KeyTarget) (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay P.src.qs.length tgt s keys →
        KSCoreOK (P.src.modulus ℓ) (BudgetBFV.ksBoundAt P lay ℓ) s (tgt.eval s)
          (fun c => core c (keys.take (lay.sizes ℓ).length)) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  have hlay' : lay.okAt ℓ = true :=
    Validation.Budget.restrictsTo_okAt lay _ ℓ hℓ hlay
  refine ⟨fun c keys => FHE.BFV.layoutKSPlain P hP hS lay ℓ hℓ hlay' c keys, ?_⟩
  intro s hs tgt keys hkeys
  have hkeys' := Validation.Budget.gadgetKeys_restrict P lay tgt hP ℓ hℓ hlay
    (fun h => by rw [hk] at h; cases h) s keys hkeys
  refine (KSCoreOK_def _ _ _ _ _).mpr fun d => ?_
  obtain ⟨e, he, hb⟩ := FHE.BFV.layoutKSPlain_spec P hP hS lay ℓ hℓ hlay' s hs tgt _ hkeys' d
  exact ⟨e, hb, he⟩

theorem stepOK_relin_leveled_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (drop ksl : ℕ) (core : IntPoly P.src.N → IntPoly P.src.N × IntPoly P.src.N)
    (hcore : KSCoreOK (P.src.modulus (x.level - drop)) ksl s (s * s) core)
    (hE : (if drop = 0 then ksl else
            BudgetBFV.ksLeveled P.src.N (P.src.modulus x.level / P.src.modulus (x.level - drop))
              ksl (P.src.N * P.secretBound * P.secretBound)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))) ≤
          E.keySwitch)
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (ha : σ a = some ca)
    (hla : ca.length = 3) (hℓL : x.level ≤ P.src.qs.length) (hdrop : drop < x.level)
    (haux : floatAuxOK? (P.src.qs.take x.level) [] = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.leveledKS S (P.src.qs.take x.level) drop core ca)) (.relin d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  -- `hdrop` (at least one limb is kept) is not used: the bound holds for every `drop`
  have _ := hdrop
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 3 ∧ x.key = 1
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  obtain ⟨c0, c1, c2, rfl⟩ : ∃ c0 c1 c2, ca = [c0, c1, c2] := by
    match ca, hla with
    | [c0, c1, c2], _ => exact ⟨_, _, _, rfl⟩
  obtain ⟨hfq, -, hpos, hcop⟩ := floatAuxOK_imp haux
  rw [List.append_nil] at hpos hcop
  obtain ⟨hb1, hb2, hb3⟩ := leveled_basis P x.level drop hℓL hpos
  have hcore' : KSCoreOK ((P.src.qs.take x.level).take
      ((P.src.qs.take x.level).length - drop)).prod ksl s (s * s) core := by
    rw [hb1]; exact hcore
  obtain ⟨err, he, hn1, hn2⟩ := leveledKS_phase S hS (P.src.qs.take x.level)
    ((P.src.qs.take x.level).length - drop) hpos hcop hfq s (s * s) ksl
    (P.src.N * P.secretBound * P.secretBound) (normInf_sq_le s _ hs) core hcore' c2
  have he' : ofInt (P.src.modulus x.level) _ + ofInt (P.src.modulus x.level) _ *
      ofInt (P.src.modulus x.level) s = ofInt (P.src.modulus x.level) c2 *
      ofInt (P.src.modulus x.level) (s * s) + ofInt (P.src.modulus x.level) err := he
  refine ⟨{ x with parts := 2 }, _, ?_, rfl, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg.2]
  refine ⟨x, [c0, c1, c2], err, hx, ha, ?_, ?_⟩
  · by_cases hd : drop = 0
    · rw [ite_eq_left hd] at hE
      exact (hn2 (by omega)).trans hE
    · rw [ite_eq_right hd, hb3] at hE
      rw [hb2] at hn1
      exact hn1.trans hE
  rw [leveledKS_three]
  simp only [Trace.phaseAt, hg.2, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add] at he' ⊢
  rw [Validation.Scheme.ofInt_mul] at he'
  linear_combination he'

theorem stepOK_keySwitch_leveled_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (drop ksl : ℕ) (core : IntPoly P.src.N → IntPoly P.src.N × IntPoly P.src.N)
    (hcore : KSCoreOK (P.src.modulus (x.level - drop)) ksl s (automorph x.key s) core)
    (hE : (if drop = 0 then ksl else
            BudgetBFV.ksLeveled P.src.N (P.src.modulus x.level / P.src.modulus (x.level - drop))
              ksl P.secretBound
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))) ≤
          E.keySwitch)
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (ha : σ a = some ca)
    (hla : ca.length = 2) (hodd : x.key % 2 = 1)
    (hℓL : x.level ≤ P.src.qs.length) (hdrop : drop < x.level)
    (haux : floatAuxOK? (P.src.qs.take x.level) [] = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.leveledKS S (P.src.qs.take x.level) drop core ca)) (.keySwitch d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  -- `hdrop` (at least one limb is kept) is not used: the bound holds for every `drop`
  have _ := hdrop
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 2
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, ca = [c0, c1] := by
    match ca, hla with
    | [c0, c1], _ => exact ⟨_, _, rfl⟩
  obtain ⟨hfq, -, hpos, hcop⟩ := floatAuxOK_imp haux
  rw [List.append_nil] at hpos hcop
  obtain ⟨hb1, hb2, hb3⟩ := leveled_basis P x.level drop hℓL hpos
  have hcore' : KSCoreOK ((P.src.qs.take x.level).take
      ((P.src.qs.take x.level).length - drop)).prod ksl s (automorph x.key s) core := by
    rw [hb1]; exact hcore
  obtain ⟨err, he, hn1, hn2⟩ := leveledKS_phase S hS (P.src.qs.take x.level)
    ((P.src.qs.take x.level).length - drop) hpos hcop hfq s (automorph x.key s) ksl
    P.secretBound ((FHE.KeySwitch.normInf_automorph_le hP.N_pow2 hodd s).trans hs) core hcore' c1
  have he' : ofInt (P.src.modulus x.level) _ + ofInt (P.src.modulus x.level) _ *
      ofInt (P.src.modulus x.level) s = ofInt (P.src.modulus x.level) c1 *
      ofInt (P.src.modulus x.level) (automorph x.key s) + ofInt (P.src.modulus x.level) err := he
  refine ⟨{ x with key := 1 }, _, ?_, ?_, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg]
  · simp [hg, leveledKS_two]
  refine ⟨x, [c0, c1], err, hx, ha, ?_, ?_⟩
  · by_cases hd : drop = 0
    · rw [ite_eq_left hd] at hE
      exact (hn2 (by omega)).trans hE
    · rw [ite_eq_right hd, hb3] at hE
      rw [hb2] at hn1
      exact hn1.trans hE
  rw [leveledKS_two]
  simp only [Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add] at he' ⊢
  linear_combination he'

theorem run_key_odd (Pr : Params) (prog : Program) (msgs : Var → Msg Pr.t Pr.N)
    (hin : (prog.inputs.all fun d => d.ok Pr) = true) (pre : List Instr) (ρ : Env Pr)
    (hρ : pre.foldlM (step Pr) (initEnv Pr prog msgs) = some ρ)
    (a : Var) (xa : Val Pr) (hx : ρ a = some xa) : xa.key % 2 = 1 :=
  foldlM_keyOdd pre hρ (initEnv_keyOdd Pr prog msgs hin) a xa hx

/-! ### With no internal drop the arithmetic does not matter -/

/-- `Fl.leveledKS` reads the sums only through the scaling down of the switched component. -/
def ksWith {N : ℕ} (qs : List ℕ) (drop : ℕ) (sd : IntPoly N → IntPoly N)
    (core : IntPoly N → IntPoly N × IntPoly N) (ct : List (IntPoly N)) : List (IntPoly N) :=
  let l := qs.length - drop
  match ct with
  | [c0, c1, c2] =>
    let ab := core (sd c2)
    [c0 + Fl.scaleUp qs l ab.1, c1 + Fl.scaleUp qs l ab.2]
  | [c0, c1] =>
    let ab := core (sd c1)
    [c0 + Fl.scaleUp qs l ab.1, Fl.scaleUp qs l ab.2]
  | _ => []

theorem leveledKS_eq_ksWith {N : ℕ} (S : Fl.Sums) (qs : List ℕ) (drop : ℕ)
    (core : IntPoly N → IntPoly N × IntPoly N) (ct : List (IntPoly N)) :
    Fl.leveledKS S qs drop core ct =
      ksWith qs drop (Fl.scaleDown S qs (qs.length - drop)) core ct := by
  match ct with
  | [_, _, _] => rfl
  | [_, _] => rfl
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ :: _ :: _ => rfl

/-- A scaling from no input limb: its truncated sum is `⌊1/2⌋` in every arithmetic. -/
theorem scaleRoundOut_nil {N : ℕ} (A B : Spec.Float.Arith) (t : ℕ) (outs : List ℕ)
    (xin xout : List (IntPoly N)) :
    Fl.scaleRoundOut (Fl.floatSums A) t [] outs xin xout =
      Fl.scaleRoundOut (Fl.floatSums B) t [] outs xin xout := rfl

theorem scaleDown_full {N : ℕ} (A B : Spec.Float.Arith) (qs : List ℕ) (c : IntPoly N) :
    Fl.scaleDown (Fl.floatSums A) qs qs.length c = Fl.scaleDown (Fl.floatSums B) qs qs.length c := by
  rw [scaleDown_def, scaleDown_def, List.drop_length, scaleRoundOut_nil A B]

theorem leveledKS_drop_zero {N : ℕ} (A B : Spec.Float.Arith) (qs : List ℕ)
    (core : IntPoly N → IntPoly N × IntPoly N) (ct : List (IntPoly N)) :
    Fl.leveledKS (Fl.floatSums A) qs 0 core ct = Fl.leveledKS (Fl.floatSums B) qs 0 core ct := by
  rw [leveledKS_eq_ksWith, leveledKS_eq_ksWith, Nat.sub_zero]
  have h : Fl.scaleDown (Fl.floatSums A) qs qs.length =
      (Fl.scaleDown (Fl.floatSums B) qs qs.length : IntPoly N → IntPoly N) :=
    funext (scaleDown_full A B qs)
  rw [h]

example := (@leveledKS_drop_zero : type_of% @Challenge.BFVMul.leveledKS_drop_zero)
example := (@ksCore_realizable : type_of% @Challenge.BFVMul.ksCore_realizable)
example := (@stepOK_relin_leveled_tol : type_of% @Challenge.BFVMul.stepOK_relin_leveled_tol)
example := (@stepOK_keySwitch_leveled_tol : type_of% @Challenge.BFVMul.stepOK_keySwitch_leveled_tol)
example := (@run_key_odd : type_of% @Challenge.BFVMul.run_key_odd)

end Validation.BFVMul
