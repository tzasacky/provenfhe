import FHE.KeySwitch.Hybrid
import FHE.RNS.Params
import Spec.Trace

/-!
# FHE.KeySwitch.Step — hybrid key switching discharges the `relin` / `keySwitch` contracts

`Spec.Trace.StepOK` asks of a `relin` or `keySwitch` step only that the result's phase be the
operand's phase plus an error `e` with `‖e‖∞ ≤ E.keySwitch` and `t ∣ e`. Here the real RNS
algorithm (`keySwitchBGV`, with keys meeting `Spec.Scheme.KeyValid` for the gadget requests
`gadgetReq`) is shown to meet that contract whenever

  `E.keySwitch ≥ ksBound N B_k B_s t (k·P) P (digitWeight Dg C)`
  `= ⌊(N·B_k·Σⱼ ℓⱼ·Qⱼ + t·k·P·(1 + N·B_s)) / (2P)⌋`

at the operand's level (`B_k = P.keyNoise`, `B_s = P.secretBound`, `k` = number of special
primes, `P` = their product, `Qⱼ`/`ℓⱼ` = product/size of digit `j` at that level).

* `relin_stepOK`: input `[c₀, c₁, c₂]` under `(1, s, s²)`, key target `s²`, output
  `[c₀ + KS(c₂)₀, c₁ + KS(c₂)₁]`.
* `keySwitch_stepOK`: input `[c₀, c₁]` under `σ_g(s)` (`g` = the operand's `key`), key target
  `σ_g(s)`, output `[c₀ + KS(c₁)₀, KS(c₁)₁]`.

The `Budget` is one number for all levels; a backend takes the maximum of the bound over the
levels (and digit layouts) it uses.
-/

namespace FHE.KeySwitch

open Finset Spec Spec.NPoly Spec.Scheme Spec.Source Spec.Trace FHE.RNS FHE.RNS.Basis
  Validation.Ring Validation.Scheme

/-- `X ↦ X¹` is the identity. -/
theorem automorph_one {R : Type} [CommRing R] {N : ℕ} (a : NPoly R N) : automorph 1 a = a := by
  ext k
  rw [coeff_automorph', Finset.sum_eq_single k]
  · simp [Nat.mod_eq_of_lt (show k.val < 2 * N by omega)]
  · intro i _ hik
    have hi : (i.val * 1) % (2 * N) = i.val := by rw [mul_one, Nat.mod_eq_of_lt (by omega)]
    have h1 : ¬ (i.val * 1) % (2 * N) = k.val := by rw [hi]; exact fun h => hik (Fin.ext h)
    have h2 : ¬ (i.val * 1) % (2 * N) = k.val + N := by rw [hi]; omega
    simp only [h1, h2, ite_false]
  · intro h; exact absurd (Finset.mem_univ k) h

variable (P : FullParams) (hP : ParamsOK P)

/-- The ciphertext basis at level `ℓ` and the special basis, from `ParamsOK`. -/
abbrev Cℓ (ℓ : ℕ) (h : ℓ ≤ P.src.qs.length) : Basis ℓ := levelBasis P hP ℓ h
abbrev Bsp : Basis (P.store.special.map (·.q)).length := specialBasis P hP

variable [NeZero P.src.N]

/-- The relinearized ciphertext: `[c₀ + KS(c₂)₀, c₁ + KS(c₂)₁]` (integer representatives). -/
def relinCt {ℓ : ℕ} (h : ℓ ≤ P.src.qs.length) (Dg : Digits ℓ)
    (kb ka : Fin Dg.dnum → Poly ((Cℓ P hP ℓ h).prod * (Bsp P hP).prod) P.src.N)
    (c0 c1 c2 : IntPoly P.src.N) : List (IntPoly P.src.N) :=
  let out := keySwitchBGV Dg (Cℓ P hP ℓ h) (Bsp P hP) P.src.t ((Cℓ P hP ℓ h).toRNS c2) kb ka
  [c0 + centered ((Cℓ P hP ℓ h).combine out.1), c1 + centered ((Cℓ P hP ℓ h).combine out.2)]

/-- The key-switched ciphertext: `[c₀ + KS(c₁)₀, KS(c₁)₁]`. -/
def keySwitchCt {ℓ : ℕ} (h : ℓ ≤ P.src.qs.length) (Dg : Digits ℓ)
    (kb ka : Fin Dg.dnum → Poly ((Cℓ P hP ℓ h).prod * (Bsp P hP).prod) P.src.N)
    (c0 c1 : IntPoly P.src.N) : List (IntPoly P.src.N) :=
  let out := keySwitchBGV Dg (Cℓ P hP ℓ h) (Bsp P hP) P.src.t ((Cℓ P hP ℓ h).toRNS c1) kb ka
  [c0 + centered ((Cℓ P hP ℓ h).combine out.1), centered ((Cℓ P hP ℓ h).combine out.2)]

/-- The integer form of the BGV theorem at a `ParamsOK` level, transported to the `Spec`
modulus `P.src.modulus ℓ`: output lifts `Y₀, Y₁` with
`Y₀ + Y₁·s ≡ d·tgt(s) + e (mod Q_ℓ)`. -/
theorem keySwitchBGV_level (hk : P.src.kind = .bgv) {ℓ : ℕ} (h : ℓ ≤ P.src.qs.length)
    (Dg : Digits ℓ) (s : IntPoly P.src.N) (hs : normInf s ≤ P.secretBound) (tgt : KeyTarget)
    (kb ka : Fin Dg.dnum → Poly ((Cℓ P hP ℓ h).prod * (Bsp P hP).prod) P.src.N)
    (hkey : ∀ j, KeyValid .bgv P.src.t P.keyNoise s
      (gadgetReq Dg (Cℓ P hP ℓ h) (Bsp P hP) tgt j) (kb j) (ka j))
    (d : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (centered ((Cℓ P hP ℓ h).combine
          (keySwitchBGV Dg (Cℓ P hP ℓ h) (Bsp P hP) P.src.t ((Cℓ P hP ℓ h).toRNS d) kb ka).1)) +
        ofInt (P.src.modulus ℓ) (centered ((Cℓ P hP ℓ h).combine
          (keySwitchBGV Dg (Cℓ P hP ℓ h) (Bsp P hP) P.src.t ((Cℓ P hP ℓ h).toRNS d) kb ka).2)) *
          ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) d * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      (∀ c, (P.src.t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound P.src.N P.keyNoise P.secretBound P.src.t
        ((P.store.special.map (·.q)).length * (Bsp P hP).prod) (Bsp P hP).prod
        (digitWeight Dg (Cℓ P hP ℓ h)) := by
  have ht : ∀ j, Nat.Coprime P.src.t ((Bsp P hP).q j) := fun j =>
    t_coprime_special P hP (List.getElem_mem _)
  have hcop : ∀ i, Nat.Coprime (Bsp P hP).prod ((Cℓ P hP ℓ h).q i) := fun i =>
    specialProd_coprime P hP (List.getElem_mem _)
  obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
    keySwitchBGV_spec Dg (Cℓ P hP ℓ h) (Bsp P hP) ht hcop s hs tgt kb ka hkey
      ((Cℓ P hP ℓ h).toRNS d)
  refine ⟨e, ?_, hdvd, hb⟩
  rw [hout, combine_toRNS, combine_toRNS]
  rw [combine_toRNS] at heq
  have hQ : (Cℓ P hP ℓ h).prod = P.src.modulus ℓ := levelBasis_prod P hP ℓ h
  revert heq
  generalize (Cℓ P hP ℓ h).prod = Q' at hQ ⊢
  subst hQ
  intro heq
  rw [ofInt_centered, ofInt_centered, ← ofInt_mul, ← ofInt_add, heq, ofInt_add, ofInt_mul,
    ofInt_centered]

/-- **`relin` meets its `StepOK` contract.** -/
theorem relin_stepOK (hk : P.src.kind = .bgv) (E : Budget) (s : IntPoly P.src.N)
    (hs : normInf s ≤ P.secretBound) {ρ ρ' : Env P.src} {σ : CtEnv P} {d a : Var}
    {x : Val P.src} (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x)
    {c0 c1 c2 : IntPoly P.src.N} (hca : σ a = some [c0, c1, c2])
    (hlev : x.level ≤ P.src.qs.length) (Dg : Digits x.level)
    (kb ka : Fin Dg.dnum → Poly ((Cℓ P hP x.level hlev).prod * (Bsp P hP).prod) P.src.N)
    (hkey : ∀ j, KeyValid .bgv P.src.t P.keyNoise s
      (gadgetReq Dg (Cℓ P hP x.level hlev) (Bsp P hP) .square j) (kb j) (ka j))
    (hE : ksBound P.src.N P.keyNoise P.secretBound P.src.t
        ((P.store.special.map (·.q)).length * (Bsp P hP).prod) (Bsp P hP).prod
        (digitWeight Dg (Cℓ P hP x.level hlev)) ≤ E.keySwitch) :
    StepOK P E s ρ ρ' σ (σ.set d (relinCt P hP hlev Dg kb ka c0 c1 c2)) (.relin d a) := by
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 3 ∧ x.key = 1
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  obtain ⟨e, he, hdvd, hb⟩ := keySwitchBGV_level P hP hk hlev Dg s hs .square kb ka hkey c2
  refine ⟨{ x with parts := 2 }, relinCt P hP hlev Dg kb ka c0 c1 c2, ?_, rfl, rfl, ?_⟩
  · simp [Env.set, dst, hg.2]
  refine ⟨x, [c0, c1, c2], e, hx, hca, hb.trans hE, hdvd, ?_⟩
  simp only [phaseAt, relinCt, hg.2, automorph_one, List.map, phase, ofInt_add,
    KeyTarget.eval] at he ⊢
  rw [ofInt_mul] at he
  linear_combination he

/-- **`keySwitch` meets its `StepOK` contract** (key target `σ_g(s)` for the operand's key
`g`). -/
theorem keySwitch_stepOK (hk : P.src.kind = .bgv) (E : Budget) (s : IntPoly P.src.N)
    (hs : normInf s ≤ P.secretBound) {ρ ρ' : Env P.src} {σ : CtEnv P} {d a : Var}
    {x : Val P.src} (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x)
    {c0 c1 : IntPoly P.src.N} (hca : σ a = some [c0, c1])
    (hlev : x.level ≤ P.src.qs.length) (Dg : Digits x.level)
    (kb ka : Fin Dg.dnum → Poly ((Cℓ P hP x.level hlev).prod * (Bsp P hP).prod) P.src.N)
    (hkey : ∀ j, KeyValid .bgv P.src.t P.keyNoise s
      (gadgetReq Dg (Cℓ P hP x.level hlev) (Bsp P hP) (.galois x.key) j) (kb j) (ka j))
    (hE : ksBound P.src.N P.keyNoise P.secretBound P.src.t
        ((P.store.special.map (·.q)).length * (Bsp P hP).prod) (Bsp P hP).prod
        (digitWeight Dg (Cℓ P hP x.level hlev)) ≤ E.keySwitch) :
    StepOK P E s ρ ρ' σ (σ.set d (keySwitchCt P hP hlev Dg kb ka c0 c1)) (.keySwitch d a) := by
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 2
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  obtain ⟨e, he, hdvd, hb⟩ := keySwitchBGV_level P hP hk hlev Dg s hs (.galois x.key) kb ka hkey c1
  refine ⟨{ x with key := 1 }, keySwitchCt P hP hlev Dg kb ka c0 c1, ?_, ?_, rfl, ?_⟩
  · simp [Env.set, dst, hg]
  · simp [keySwitchCt, hg]
  refine ⟨x, [c0, c1], e, hx, hca, hb.trans hE, hdvd, ?_⟩
  simp only [phaseAt, keySwitchCt, automorph_one, List.map, phase, ofInt_add,
    KeyTarget.eval] at he ⊢
  linear_combination he

end FHE.KeySwitch
