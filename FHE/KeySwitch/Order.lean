import FHE.KeySwitch.Step
import Validation.Source

/-!
# FHE.KeySwitch.Order — key-switch-then-automorphism meets the `automorph; keySwitch` contracts

`Spec.Source` models a rotation as `automorph d a g` (result under `σ_g` of the operand's key,
phase `σ_g(φ_a)`) followed by `keySwitch d d` (back to `s`, phase error `e` with
`‖e‖∞ ≤ E.keySwitch`, `t ∣ e`). OpenFHE does the two in the other order: key-switch first
(phase `φ_a + e`), then apply `σ_g` to every component, giving phase
`σ_g(φ_a + e) = σ_g(φ_a) + σ_g(e)` under `s`.

Since `σ_g` (odd `g`, `N` a power of two) permutes coefficients up to sign, `σ_g(e)` meets the
same budget as `e`, so the existing contracts admit OpenFHE's order:

* `normInf_automorph_le`, `dvd_coeff_automorph`: `σ_g` does not increase `‖·‖∞` and preserves
  coefficientwise divisibility.
* `keySwitch_stepOK_of_automorph_error`: a `keySwitch` step whose phase error is `σ_g(e)`.
* `openfhe_rotation_run`: the composite is a `Spec.Trace.Run` of
  `[.automorph d a g, .keySwitch d d]`.
-/

namespace FHE.KeySwitch

open Finset Spec Spec.NPoly Spec.Scheme Spec.Source Spec.Trace
  Validation.Ring Validation.Scheme Validation.Source

/-! ### `σ_g` on integer polynomials -/

/-- For odd `g` and `N` a power of two, `σ_g` does not increase the infinity norm. -/
theorem normInf_automorph_le {N : ℕ} (hN : ∃ k, N = 2 ^ k) {g : ℕ} (hg : g % 2 = 1)
    (e : IntPoly N) : normInf (automorph g e) ≤ normInf e := by
  rw [normInf_le_iff]
  exact fun j => abs_coeff_automorph_le hN hg e _ (abs_coeff_le_normInf e) j

/-- `σ_g` preserves coefficientwise divisibility (any `g`, any `N`). -/
theorem dvd_coeff_automorph {N : ℕ} (g : ℕ) (t : ℤ) (e : IntPoly N)
    (h : ∀ j, t ∣ e.coeff j) : ∀ j, t ∣ (automorph g e).coeff j := by
  intro j
  rw [coeff_automorph']
  refine Finset.dvd_sum fun i _ => ?_
  split_ifs
  · exact h i
  · exact (dvd_neg).mpr (h i)
  · exact dvd_zero _

/-! ### The `keySwitch` step with error `σ_g(e)` -/

/-- **A `keySwitch` step whose phase error is `σ_g(e)`.** If the output `ct` (two components) has
phase under `s` equal to the operand's phase plus `σ_g(e mod Q)`, with `e` within the key-switching
budget and divisible by `t`, then the step meets `StepOK` (witness error: `σ_g(e)`). -/
theorem keySwitch_stepOK_of_automorph_error (P : FullParams) (hP : SchemeParamsOK P) (E : Budget)
    (s : IntPoly P.src.N) {ρ ρ' : Env P.src} {σ : CtEnv P} {d a : Var} {x : Val P.src}
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x)
    {ca : List (IntPoly P.src.N)} (hca : σ a = some ca)
    {g : ℕ} (hg : g % 2 = 1) (e : IntPoly P.src.N)
    (he : normInf e ≤ E.keySwitch) (hdvd : ∀ j, (P.src.t : ℤ) ∣ e.coeff j)
    {ct : List (IntPoly P.src.N)} (hlen : ct.length = 2)
    (hphase : phaseAt P (P.src.modulus x.level) 1 s ct =
      phaseAt P (P.src.modulus x.level) x.key s ca +
        automorph g (ofInt (P.src.modulus x.level) e)) :
    StepOK P E s ρ ρ' σ (σ.set d ct) (.keySwitch d a) := by
  simp only [step, hx, guard] at hstep
  by_cases h2 : x.parts = 2
  swap
  · simp [h2] at hstep
  simp [h2] at hstep
  subst hstep
  refine ⟨{ x with key := 1 }, ct, ?_, ?_, rfl, ?_⟩
  · simp [Env.set, dst, h2]
  · exact hlen.trans h2.symm
  refine ⟨x, ca, automorph g e, hx, hca, (normInf_automorph_le hP.N_pow2 hg e).trans he,
    dvd_coeff_automorph g _ e hdvd, ?_⟩
  rw [ofInt_automorph]
  exact hphase

/-! ### The two-step run -/

/-- The phase of the componentwise image `ca.map σ_g`, read under the key `(key·g) mod 2N`, is
`σ_g` of the phase of `ca` under `key`. -/
theorem phaseAt_map_automorph (P : FullParams) (Q key : ℕ) (s : IntPoly P.src.N)
    {g : ℕ} (hg : g % 2 = 1) (ca : List (IntPoly P.src.N)) :
    phaseAt P Q ((key * g) % (2 * P.src.N)) s (ca.map (automorph g)) =
      automorph g (phaseAt P Q key s ca) := by
  unfold phaseAt
  have hmap : (ca.map (automorph g)).map (ofInt Q) = (ca.map (ofInt Q)).map (automorph g) := by
    simp only [List.map_map]
    congr 1; funext c; exact ofInt_automorph Q g c
  rw [hmap, automorph_mod, ← automorph_automorph hg, ofInt_automorph, phase_automorph hg]

/-- **OpenFHE's rotation order is a valid run of `[automorph, keySwitch]`.** OpenFHE key-switches
first and applies `σ_g` afterwards; read under `s`, its output `ct` has phase `σ_g(φ_a + e)` with
`e` the key-switching error. Taking the intermediate ciphertext to be `ca.map σ_g`, this is a
`Run` of `automorph d a g` followed by `keySwitch d d`, ending in
`(σ.set d (ca.map σ_g)).set d ct`, where `d` holds `ct`. -/
theorem openfhe_rotation_run (P : FullParams) (hP : SchemeParamsOK P) (E : Budget)
    (s : IntPoly P.src.N) {ρ : Env P.src} {σ : CtEnv P} (d a : Var) {x : Val P.src}
    (hx : ρ a = some x) (hparts : x.parts = 2)
    {ca : List (IntPoly P.src.N)} (hca : σ a = some ca) (hcalen : ca.length = 2)
    {g : ℕ} (hg : g % 2 = 1) (e : IntPoly P.src.N)
    (he : normInf e ≤ E.keySwitch) (hdvd : ∀ j, (P.src.t : ℤ) ∣ e.coeff j)
    {ct : List (IntPoly P.src.N)} (hlen : ct.length = 2)
    (hphase : phaseAt P (P.src.modulus x.level) 1 s ct =
      automorph g (phaseAt P (P.src.modulus x.level) x.key s ca +
        ofInt (P.src.modulus x.level) e)) :
    Run P E s [.automorph d a g, .keySwitch d d] ρ σ
        ((σ.set d (ca.map (automorph g))).set d ct) ∧
      ((σ.set d (ca.map (automorph g))).set d ct) d = some ct := by
  refine ⟨?_, by simp [CtEnv.set]⟩
  set v1 : Val P.src := { x with msg := x.msg.lift₁ (automorph g),
                                 key := (x.key * g) % (2 * P.src.N) } with hv1
  have hstep1 : step P.src ρ (.automorph d a g) = some (ρ.set d v1) := by
    simp [step, hx, hg, hv1]
  have hρ1 : (ρ.set d v1) d = some v1 := by simp [Env.set]
  have hstep2 : step P.src (ρ.set d v1) (.keySwitch d d) =
      some ((ρ.set d v1).set d { v1 with key := 1 }) := by
    have hp : v1.parts = 2 := hparts
    simp only [step, hρ1, guard, Option.bind_eq_bind, Option.bind_some, hp, ite_true]
    rfl
  have hσ1 : (σ.set d (ca.map (automorph g))) d = some (ca.map (automorph g)) := by
    simp [CtEnv.set]
  refine ⟨ρ.set d v1, σ.set d (ca.map (automorph g)), hstep1, ?_, ?_⟩
  · refine ⟨v1, ca.map (automorph g), hρ1, ?_, rfl, ?_⟩
    · simp [hv1, hcalen, hparts]
    · exact ⟨x, ca, hx, hca, phaseAt_map_automorph P _ x.key s hg ca⟩
  · refine ⟨_, _, hstep2, ?_, rfl⟩
    refine keySwitch_stepOK_of_automorph_error P hP E s hstep2 hρ1 hσ1 hg e he hdvd hlen ?_
    have h1 : phaseAt P (P.src.modulus v1.level) v1.key s (ca.map (automorph g)) =
        automorph g (phaseAt P (P.src.modulus x.level) x.key s ca) :=
      phaseAt_map_automorph P _ x.key s hg ca
    rw [h1]
    change phaseAt P (P.src.modulus x.level) 1 s ct = _
    rw [hphase, automorph_add]

end FHE.KeySwitch
