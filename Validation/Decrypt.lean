import Challenge.Decrypt
import Validation.Headline.Noise
import Validation.Switch

/-!
# Validation.Decrypt — proofs of the pins of `Challenge.Decrypt`

The switched decryption is followed on the un-wrapped integers. One round with last limb `q`
and remaining product `Q'` maps the centred representative `c` of `X` modulo `q·Q'` to the
centred representative modulo `Q'` of `switchPhase t q c`, which is congruent modulo `Q'` to
`switchPhase t q X` (`Validation.Switch.sw_congr`). So after all rounds the library holds the
centred residue modulo `q₀` of the un-wrapped switched value, which `decBoundRev` bounds below
`q₀/2`: the residue is the value, and each round multiplied it by `q⁻¹` modulo `t`.
-/

namespace Validation.Decrypt
open Spec NPoly Scheme Source Correct Spec.Decrypt Challenge.Headline Challenge.Corpus
open Validation.Ring Validation.Scheme Validation.Source Validation.Switch
open Validation.Headline.NoiseAux

section Core
variable {N : ℕ}

theorem zmod_inv_mul {t a b : ℕ} (ha : Nat.Coprime a t) (hb : Nat.Coprime b t) :
    (((a * b : ℕ)) : ZMod t)⁻¹ = (a : ZMod t)⁻¹ * (b : ZMod t)⁻¹ := by
  have h1 := ZMod.coe_mul_inv_eq_one (a * b) (Nat.Coprime.mul_left ha hb)
  have h2 := ZMod.coe_mul_inv_eq_one a ha
  have h3 := ZMod.coe_mul_inv_eq_one b hb
  push_cast at h1 ⊢
  linear_combination (a : ZMod t)⁻¹ * (b : ZMod t)⁻¹ * h1 - ((a : ZMod t) * b)⁻¹ * h2 -
    ((a : ZMod t) * b)⁻¹ * a * (a : ZMod t)⁻¹ * h3

theorem coprime_prod_of_forall {t : ℕ} : ∀ (l : List ℕ), (∀ q ∈ l, Nat.Coprime t q) →
    Nat.Coprime l.prod t
  | [], _ => by simp
  | q :: l, h => by
    rw [List.prod_cons]
    exact Nat.Coprime.mul_left (h q (by simp)).symm
      (coprime_prod_of_forall l fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- The switch-down of the centred representative of `X`, when the bound on the switched value
is below half the last remaining limb. The list is last limb first. -/
theorem switchDown_main (t : ℕ) : ∀ (l : List ℕ), l ≠ [] → (∀ q ∈ l, 0 < q ∧ Nat.Coprime t q) →
    ∀ (X : IntPoly N) (B q0 : ℕ), (∀ i, |X.coeff i| ≤ B) → l.getLast? = some q0 →
      2 * decBoundRev t l B < q0 →
      ofInt t (switchDownRev t l (centered (ofInt l.prod X))) =
        ((l.dropLast.prod : ℕ) : ZMod t)⁻¹ • ofInt t X
  | [], h, _ => absurd rfl h
  | [q], _, _ => by
    intro X B q0 hX hl hb
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    have e1 : decBoundRev t [q] B = B := rfl
    have e2 : switchDownRev t [q] (centered (ofInt [q].prod X)) = centered (ofInt [q].prod X) :=
      rfl
    rw [e1] at hb
    have e3 : centered (ofInt [q].prod X) = X := by
      apply centered_ofInt
      intro i
      have := hX i
      simp only [List.prod_singleton]
      have hb' : (2 * (B : ℤ)) < q := by exact_mod_cast hb
      linarith
    rw [e2, e3]
    ext i
    simp
  | q :: r :: rest, _, hpos => by
    intro X B q0 hX hl hb
    have e1 : decBoundRev t (q :: r :: rest) B =
      decBoundRev t (r :: rest) ((B + t * (q / 2)) / q) := rfl
    have e2 : ∀ c : IntPoly N, switchDownRev t (q :: r :: rest) c =
      switchDownRev t (r :: rest) (centered (ofInt (r :: rest).prod (switchPhase t q c))) :=
      fun _ => rfl
    obtain ⟨hq, hcop⟩ := hpos q (by simp)
    have hcong : ofInt (r :: rest).prod
        (switchPhase t q (centered (ofInt (q :: r :: rest).prod X))) =
        ofInt (r :: rest).prod (switchPhase t q X) := by
      ext i
      show ((sw t q _ : ℤ) : ZMod _) = ((sw t q _ : ℤ) : ZMod _)
      apply sw_congr hq hcop
      have := congrArg (fun p => p.coeff i) (ofInt_centered (ofInt (q :: r :: rest).prod X))
      rw [← List.prod_cons]
      exact this
    rw [e2, hcong]
    rw [e1] at hb
    have ih := switchDown_main t (r :: rest) (by simp)
      (fun p hp => hpos p (List.mem_cons_of_mem _ hp)) (switchPhase t q X)
      ((B + t * (q / 2)) / q) q0 (fun i => natAbs_sw_le hq hcop (hX i)) (by simpa using hl) hb
    rw [ih]
    have e3 : (q :: r :: rest).dropLast = q :: (r :: rest).dropLast := rfl
    have hc2 : Nat.Coprime (r :: rest).dropLast.prod t :=
      coprime_prod_of_forall _ fun p hp =>
        (hpos p (List.mem_cons_of_mem _ (List.dropLast_subset _ hp))).2
    ext i
    simp only [coeff_smul', coeff_ofInt]
    rw [show (switchPhase t q X).coeff i = sw t q (X.coeff i) from rfl, sw_cast_t hcop, e3,
      List.prod_cons, zmod_inv_mul hcop.symm hc2]
    ring

/-- The switched decryption of any ciphertext whose centred phase is within `B`, for a chain of
positive limbs coprime to `t`. -/
theorem decrypt_core (t : ℕ) (L : List ℕ) (hL : ∀ q ∈ L, 0 < q ∧ Nat.Coprime t q)
    (s : IntPoly N) (ct : List (Poly L.prod N)) (B : ℕ)
    (hbound : ∀ i, |(centeredPhase s ct).coeff i| ≤ B)
    (h0 : L ≠ [] → 2 * decBoundRev t L.reverse B < L.headD 0) :
    bgvDecryptSwitched t L s ct =
      (((L.drop 1).prod : ℕ) : ZMod t)⁻¹ • ofInt t (centeredPhase s ct) := by
  show ofInt t (switchDownRev t L.reverse (centeredPhase s ct)) = _
  by_cases hne : L = []
  · subst hne
    have e : switchDownRev t ([] : List ℕ).reverse (centeredPhase s ct) = centeredPhase s ct := rfl
    rw [e]
    ext i
    simp
  · have hΦ : centered (ofInt L.reverse.prod (centeredPhase s ct)) = centeredPhase s ct := by
      rw [List.prod_reverse]
      unfold centeredPhase
      rw [ofInt_centered]
    have hlast : L.reverse.getLast? = some (L.headD 0) := by
      cases L with
      | nil => exact absurd rfl hne
      | cons a L => simp
    have key := switchDown_main t L.reverse (by simpa using hne)
      (fun q hq => hL q (List.mem_reverse.mp hq)) (centeredPhase s ct) B (L.headD 0) hbound hlast
      (h0 hne)
    rw [hΦ] at key
    rw [key]
    have : L.reverse.dropLast.prod = (L.drop 1).prod := by
      cases L with
      | nil => rfl
      | cons a L => simp [List.prod_reverse]
    rw [this]

end Core

/-- **Switched decryption is exact under `decryptOK?`.** -/
theorem decrypt_switched (P : FullParams) (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N))
    (h : Encrypts P s B v ct) (hok : decryptOK? P.src v.level B = true) :
    ∃ m, v.msg = .exact m ∧
      bgvDecryptSwitched P.src.t (P.src.qs.take v.level) (automorph v.key s)
          (ct.map (ofInt (P.src.qs.take v.level).prod)) =
        decScale P.src v.level • m := by
  rw [encrypts_bgv_iff P hk] at h
  obtain ⟨-, m, hm, hb⟩ := h
  refine ⟨m, hm, ?_⟩
  have hb' : BGVEncrypts P.src.t B (automorph v.key s)
      (ct.map (ofInt (P.src.qs.take v.level).prod)) m := hb
  have hok' : 2 * decBoundRev P.src.t (P.src.qs.take v.level).reverse B < P.src.qs.headD 0 := by
    simpa [decryptOK?, decBound] using hok
  have hcore := decrypt_core P.src.t (P.src.qs.take v.level)
    (fun q hq => by
      have hmem := List.mem_of_mem_take hq
      exact ⟨(hP.prime q hmem).pos, (hP.plaintext).2 q hmem⟩)
    (automorph v.key s) (ct.map (ofInt (P.src.qs.take v.level).prod)) B (BGVEncrypts.bound hb')
    (fun hne => by
      have : (P.src.qs.take v.level).headD 0 = P.src.qs.headD 0 := by
        have h0 : v.level ≠ 0 := by rintro h0; rw [h0] at hne; exact hne rfl
        simp [List.headD_eq_head?_getD, List.head?_take, h0]
      rw [this]; exact hok')
  rw [hcore, BGVEncrypts.msg hb']
  rfl

/-- With one limb the switched decryption is the textbook one. -/
theorem bgvDecryptSwitched_one (t q : ℕ) {N : ℕ} (s : IntPoly N) (ct : List (Poly [q].prod N)) :
    bgvDecryptSwitched t [q] s ct = ofInt t (centeredPhase s ct) := rfl

/-- Each round of `decBoundRev` is at most `⌊B/q⌋ + ⌈t/2⌉`. -/
theorem decBoundRev_step_le (t q B : ℕ) (hq : 0 < q) :
    (B + t * (q / 2)) / q ≤ B / q + (t + 1) / 2 := by
  have h2 : t ≤ 2 * ((t + 1) / 2) := by omega
  have h3 : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
  have hb : t * (q / 2) ≤ q * ((t + 1) / 2) :=
    calc t * (q / 2) ≤ (2 * ((t + 1) / 2)) * (q / 2) := Nat.mul_le_mul_right _ h2
      _ = (2 * (q / 2)) * ((t + 1) / 2) := by ring
      _ ≤ q * ((t + 1) / 2) := Nat.mul_le_mul_right _ h3
  calc (B + t * (q / 2)) / q ≤ (B + q * ((t + 1) / 2)) / q :=
        Nat.div_le_div_right (Nat.add_le_add_left hb _)
    _ = B / q + (t + 1) / 2 := Nat.add_mul_div_left _ _ hq

/-! ### Levels do not depend on the messages -/

theorem foldlM_zenv {Pr : Params} (hk : Pr.kind = .bgv) : ∀ (body : List Instr) (ρ : Env Pr),
    AllExact ρ → body.foldlM (step Pr) (zenv ρ) = (body.foldlM (step Pr) ρ).map zenv
  | [], _, _ => rfl
  | i :: is, ρ, hρ => by
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    simp only [List.foldlM_cons, Option.bind_eq_bind, hz]
    rcases hs : step Pr ρ i with _ | ρ'
    · rfl
    · simp only [Option.map_some, Option.bind_some]
      exact foldlM_zenv hk is ρ' (hex ρ' hs)

/-- The level of an output is the same for all messages. -/
theorem outputLevel?_eq (P : Params) (hk : P.kind = .bgv) (prog : Program)
    (msgs : Var → Msg P.t P.N) (ρ : Env P) (h : eval P prog msgs = some ρ) (o : Var) (v : Val P)
    (ho : ρ o = some v) : outputLevel? P prog o = some v.level := by
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
  simp only [outputLevel?, hev, Option.bind_eq_bind, Option.bind_some, zenv, ho, Option.map_some,
    Option.pure_def, zv]

/-- **The noise headline with the library's decryption.** -/
theorem analyze_decrypt_switched (P : FullParams) (E : Trace.Budget) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (h : refAnalyze P E prog = some B)
    (hd : decryptAllOK? P.src prog B = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
          bgvDecryptSwitched P.src.t (P.src.qs.take v.level) (automorph v.key s)
              (ct.map (ofInt (P.src.qs.take v.level).prod)) =
            decScale P.src v.level • m := by
  obtain ⟨ρ, hev, hrun⟩ := refAnalyze_sound P E prog B hP hk h s msgs cts hin hb
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, hv, hct, henc⟩ := hrun σ hσ o ho
  have hlev := outputLevel?_eq P.src hk prog msgs ρ hev o v hv
  have hdo : decryptOK? P.src v.level B = true := by
    have := List.all_eq_true.mp hd o ho
    rw [hlev] at this
    exact this
  obtain ⟨m, hm, hdec⟩ := decrypt_switched P hk hP s B v ct henc hdo
  exact ⟨v, ct, m, hv, hct, hm, hdec⟩

end Validation.Decrypt
