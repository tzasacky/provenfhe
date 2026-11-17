import FHE.KeySwitch.Core

/-!
# FHE.KeySwitch.Hybrid — RNS hybrid key switching: algorithm and correctness

Ciphertext basis `C = (q₀, …, q_{ℓ-1})` (product `Q`), special basis `Bp = (p₀, …, p_{k-1})`
(product `P`), digits `Dg` (product of digit `j` is `Qⱼ`, `size j` limbs). The input is one
ciphertext component `d` in RNS form over `C` (the `c₂` of relinearization, or the `c₁` of a
rotated ciphertext); the keys are pairs `(bⱼ, aⱼ)` modulo `Q·P`.

**Algorithm** (Han–Ki 2019, §3; OpenFHE `KeySwitchHYBRID`):
1. *ModUp* (`modUpQ`, `modUpP`): for each digit `j`, keep the limbs of digit `j` and fill every
   other limb of `C` and every limb of `Bp` by centred fast base conversion from digit `j`.
2. *Inner product* (`innerQ`, `innerP`): limbwise `Σⱼ ModUpⱼ(d) · bⱼ` and `Σⱼ ModUpⱼ(d) · aⱼ`
   over `C ∪ Bp`.
3. *ModDown* by `P`: the BGV `t`-preserving centred ModDown (`keySwitchBGV`) or the plain centred
   ModDown (`keySwitchPlain`, BFV).

**Correctness** (`keySwitchBGV_spec`, `keySwitchPlain_spec`): the output `(y₀, y₁)` satisfies
`y₀ + y₁·s ≡ d·T + e (mod Q)` for the key target `T` (`s²` or `σ_g(s)`), with
`t ∣ e` (BGV) and `‖e‖∞ ≤ ksBound N B_k B_s t (k·P) P (Qⱼ·(size j + 1))`, i.e.

  `‖e‖∞ ≤ ⌊(N·B_k·Σⱼ ℓⱼ·Qⱼ + t·k·P·(1 + N·B_s)) / (2P)⌋`.

The first summand (divided by `2P`) is the key-noise term, the second the ModDown rounding term
`(k/2)·t·(1 + N·B_s)`. For the plain variant `t = 1` in the rounding term.
-/

namespace FHE.KeySwitch

open Finset Spec Spec.NPoly Spec.Scheme FHE.RNS FHE.RNS.Basis Validation.Ring Validation.Scheme

variable {N ℓ k : ℕ} (Dg : Digits ℓ) (C : Basis ℓ) (Bp : Basis k)

/-! ### The algorithm -/

/-- The limbs of digit `j`, as an RNS polynomial over the digit basis. -/
def digitLimbs (a : RNSPoly C N) (j : Fin Dg.dnum) : RNSPoly (Dg.sub C j) N :=
  fun r => a (Dg.emb j r)

/-- ModUp of digit `j`, ciphertext limbs: copy the limbs of digit `j`, centred fast base
conversion from digit `j` for the others. -/
def modUpQ (a : RNSPoly C N) (j : Fin Dg.dnum) : RNSPoly C N := fun i =>
  if ∃ r, Dg.emb j r = i then a i
  else (Dg.sub C j).fastBConvCPoly C.q (digitLimbs Dg C a j) i

/-- ModUp of digit `j`, special limbs: centred fast base conversion from digit `j`. -/
def modUpP (a : RNSPoly C N) (j : Fin Dg.dnum) : RNSPoly Bp N :=
  (Dg.sub C j).fastBConvCPoly Bp.q (digitLimbs Dg C a j)

/-- A key polynomial modulo `M`, reduced to one limb `q ∣ M`. -/
def keyLimb {M : ℕ} (q : ℕ) (b : Poly M N) : Poly q N := ofInt q (centered b)

variable [NeZero N]

/-- Inner product with the key over the ciphertext limbs. -/
def innerQ (a : RNSPoly C N) (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N :=
  fun i => ∑ j, modUpQ Dg C a j i * keyLimb (C.q i) (kb j)

/-- Inner product with the key over the special limbs. -/
def innerP (a : RNSPoly C N) (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly Bp N :=
  fun i => ∑ j, modUpP Dg C Bp a j i * keyLimb (Bp.q i) (kb j)

/-- **Hybrid key switching, BGV** (`t`-preserving centred ModDown). Returns `(c₀', c₁')`. -/
def keySwitchBGV (t : ℕ) (a : RNSPoly C N) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    RNSPoly C N × RNSPoly C N :=
  (C.bgvModDownCPoly Bp t (innerQ Dg C Bp a kb) (innerP Dg C Bp a kb),
   C.bgvModDownCPoly Bp t (innerQ Dg C Bp a ka) (innerP Dg C Bp a ka))

/-- **Hybrid key switching, BFV** (plain centred ModDown). Returns `(c₀', c₁')`. -/
def keySwitchPlain (a : RNSPoly C N) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    RNSPoly C N × RNSPoly C N :=
  (C.modDownCPoly Bp (innerQ Dg C Bp a kb) (innerP Dg C Bp a kb),
   C.modDownCPoly Bp (innerQ Dg C Bp a ka) (innerP Dg C Bp a ka))

/-- The key a hybrid key switch needs for digit `j`: modulus `Q·P`, factor the gadget entry
`gⱼ`, target `tgt`. -/
def gadgetReq (tgt : KeyTarget) (j : Fin Dg.dnum) : KeyReq N where
  modulus := C.prod * Bp.prod
  factor := const ((gadget Dg C Bp.prod j : ℤ) : ZMod (C.prod * Bp.prod))
  target := tgt

/-! ### ModUp -/

omit [NeZero N] in
/-- **ModUp, exact.** ModUp of digit `j` is the RNS form, over `C ∪ Bp`, of one integer
polynomial `Dⱼ ≡ d̄ (mod Qⱼ)` (`d̄` the centred lift of the input) with
`2‖Dⱼ‖∞ ≤ ℓⱼ·Qⱼ`: `Dⱼ = Σᵣ [xᵣ·q̃ᵣ]_{qᵣ}·q̂ᵣ` with centred terms, i.e. `[d]_{Qⱼ} + Qⱼ·u`
with the fast-base-conversion overflow `u`, `|u| ≤ ⌊ℓⱼ/2⌋`. -/
theorem modUp_spec (a : RNSPoly C N) (j : Fin Dg.dnum) :
    ∃ D : IntPoly N, (∀ i, modUpQ Dg C a j i = ofInt (C.q i) D) ∧
      (∀ i, modUpP Dg C Bp a j i = ofInt (Bp.q i) D) ∧
      (∀ c, ((Dg.basis C).q j : ℤ) ∣ D.coeff c - (centered (C.combine a)).coeff c) ∧
      2 * normInf D ≤ Dg.size j * (Dg.basis C).q j := by
  set S := Dg.sub C j
  set x := digitLimbs Dg C a j
  -- `Dⱼ = Σᵣ [xᵣ·q̃ᵣ]·q̂ᵣ` (centred terms) `= [d]_{Qⱼ} + Qⱼ·u`, `fbcIntC_eq`
  let D : IntPoly N := ⟨fun c => S.fbcIntC (S.coeffVec x c)⟩
  have hfbc : ∀ {m : ℕ} (p : Fin m → ℕ) (i : Fin m), S.fastBConvCPoly p x i = ofInt (p i) D := by
    intro m p i; ext c; exact S.fastBConvC_eq_intCast p _ i
  -- the digit's own limbs are the RNS form of `D` too
  have hown : ∀ r, a (Dg.emb j r) = ofInt (C.q (Dg.emb j r)) D := by
    intro r; ext c; exact (S.fbcIntC_residue (S.coeffVec x c) r).symm
  refine ⟨D, fun i => ?_, fun i => hfbc Bp.q i, fun c => ?_, ?_⟩
  · unfold modUpQ
    split_ifs with h
    · obtain ⟨r, rfl⟩ := h; exact hown r
    · exact hfbc C.q i
  · show (S.prod : ℤ) ∣ _
    refine S.prod_dvd_sub_of_residues fun r => ?_
    have h1 := congrArg (fun p => p.coeff c) (hown r)
    have h2 := congrArg (fun p => (p (Dg.emb j r)).coeff c) (C.toRNS_centered_combine a)
    simp only [coeff_ofInt, toRNS] at h1 h2
    exact h1.symm.trans h2.symm
  · refine two_mul_normInf_le fun c => ?_
    show 2 * |S.fbcIntC (S.coeffVec x c)| ≤ ((Dg.size j * S.prod : ℕ) : ℤ)
    rw [Nat.cast_mul]
    exact S.two_mul_abs_fbcIntC_le _

/-! ### Inner product -/

/-- The inner product over `C` is the RNS form of `Σⱼ Dⱼ · b̄ⱼ`. -/
theorem innerQ_eq (a : RNSPoly C N) (D : Fin Dg.dnum → IntPoly N)
    (hD : ∀ j i, modUpQ Dg C a j i = ofInt (C.q i) (D j))
    (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    innerQ Dg C Bp a kb = C.toRNS (∑ j, D j * centered (kb j)) := by
  funext i
  simp only [innerQ, toRNS, keyLimb, hD, ofInt_sum, ofInt_mul]

/-- The inner product over `Bp` is the RNS form of `Σⱼ Dⱼ · b̄ⱼ`. -/
theorem innerP_eq (a : RNSPoly C N) (D : Fin Dg.dnum → IntPoly N)
    (hD : ∀ j i, modUpP Dg C Bp a j i = ofInt (Bp.q i) (D j))
    (kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    innerP Dg C Bp a kb = Bp.toRNS (∑ j, D j * centered (kb j)) := by
  funext i
  simp only [innerP, toRNS, keyLimb, hD, ofInt_sum, ofInt_mul]

/-! ### Keys -/

/-- A valid key, read as an integer congruence modulo `Q·P` with explicit error `eⱼ`. -/
theorem key_congr (s : IntPoly N) (tgt : KeyTarget) (j : Fin Dg.dnum)
    (b a : Poly (C.prod * Bp.prod) N) :
    let e := centered (b + a * ofInt (C.prod * Bp.prod) s -
      const ((gadget Dg C Bp.prod j : ℤ) : ZMod (C.prod * Bp.prod)) *
        ofInt (C.prod * Bp.prod) (tgt.eval s))
    ofInt (C.prod * Bp.prod) (centered b + centered a * s -
      (gadget Dg C Bp.prod j : IntPoly N) * tgt.eval s - e) = 0 := by
  intro e
  simp only [e, ofInt_sub, ofInt_add, ofInt_mul, ofInt_centered, ofInt_intCast]
  rw [intCast_def]
  ring

/-! ### Main theorems -/

/-- The term `Mⱼ = ℓⱼ·Qⱼ` bounding `2‖ModUpⱼ(d)‖∞` (centred ModUp; `Qⱼ` for single-limb
digits, where ModUp is exact). -/
def digitWeight (j : Fin Dg.dnum) : ℕ := Dg.size j * (Dg.basis C).q j

/-- **Hybrid key switching, BGV: correctness and worst-case noise.**

Hypotheses: `P = ∏ pⱼ` coprime to every `qᵢ`; `t` coprime to every `pⱼ`; `‖s‖∞ ≤ B_s`; for every
digit `j`, `(bⱼ, aⱼ)` is a valid BGV key (noise `≤ B_k`, divisible by `t`) modulo `Q·P` for
`gⱼ · tgt(s)`. Then for every input `d` (RNS over `C`) the output is the RNS form of integer
polynomials `y₀, y₁` with

  `y₀ + y₁·s ≡ d·tgt(s) + e (mod Q)`,  `t ∣ e`,
  `‖e‖∞ ≤ ⌊(N·B_k·Σⱼ ℓⱼ·Qⱼ + t·k·P·(1 + N·B_s)) / (2P)⌋`.

Here `d` is read through its centred lift; any integer lift gives the same congruence. -/
theorem keySwitchBGV_spec {t Bk Bs : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (a : RNSPoly C N) :
    ∃ y0 y1 e : IntPoly N,
      keySwitchBGV Dg C Bp t a kb ka = (C.toRNS y0, C.toRNS y1) ∧
      ofInt C.prod (y0 + y1 * s) = ofInt C.prod (centered (C.combine a) * tgt.eval s + e) ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (k * Bp.prod) Bp.prod (digitWeight Dg C) := by
  choose D hDQ hDP hDc hDb using modUp_spec Dg C Bp a
  have hP := Bp.prod_pos
  obtain ⟨y0, f0, hy0, h0, hf0, -⟩ := bgvModDownCPoly_spec ht hcop (∑ j, D j * centered (kb j))
  obtain ⟨y1, f1, hy1, h1, hf1, -⟩ := bgvModDownCPoly_spec ht hcop (∑ j, D j * centered (ka j))
  set E : Fin Dg.dnum → IntPoly N := fun j => centered (kb j + ka j * ofInt _ s -
    const ((gadget Dg C Bp.prod j : ℤ) : ZMod (C.prod * Bp.prod)) * ofInt _ (tgt.eval s))
  obtain ⟨err, herr, herrc⟩ := ks_core (Q := C.prod) hP (gadget Dg C Bp.prod) D
    (fun j => centered (kb j)) (fun j => centered (ka j)) E (centered (C.combine a)) (tgt.eval s)
    s y0 y1 f0 f1 (gadget_poly Dg C Bp.prod _ D hDc)
    (fun j => key_congr Dg C Bp s tgt j (kb j) (ka j))
    h0 h1
  refine ⟨y0, y1, err, ?_, herr, ?_, ?_⟩
  · simp only [keySwitchBGV, innerQ_eq Dg C Bp a D hDQ, innerP_eq Dg C Bp a D hDP, hy0, hy1]
  · exact ks_core_dvd (Nat.coprime_prod_right_iff.mpr fun j _ => ht j) D E s f0 f1 err
      (fun j => (hkey j).2 rfl) herrc
  · exact ks_core_bound hP D E (digitWeight Dg C) s f0 f1 err hDb (fun j => (hkey j).1) hs
      hf0 hf1 herrc

/-- **Hybrid key switching, BFV (plain ModDown): correctness and worst-case noise.**
As `keySwitchBGV_spec` without `t`:
`‖e‖∞ ≤ ⌊(N·B_k·Σⱼ ℓⱼ·Qⱼ + k·P·(1 + N·B_s)) / (2P)⌋`.
Keys of any scheme kind are accepted (only their noise bound is used). -/
theorem keySwitchPlain_spec {kind : Kind} {t' Bk Bs : ℕ}
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid kind t' Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (a : RNSPoly C N) :
    ∃ y0 y1 e : IntPoly N,
      keySwitchPlain Dg C Bp a kb ka = (C.toRNS y0, C.toRNS y1) ∧
      ofInt C.prod (y0 + y1 * s) = ofInt C.prod (centered (C.combine a) * tgt.eval s + e) ∧
      normInf e ≤ ksBound N Bk Bs 1 (k * Bp.prod) Bp.prod (digitWeight Dg C) := by
  choose D hDQ hDP hDc hDb using modUp_spec Dg C Bp a
  have hP := Bp.prod_pos
  obtain ⟨y0, f0, hy0, h0, hf0⟩ := modDownCPoly_spec hcop (∑ j, D j * centered (kb j))
  obtain ⟨y1, f1, hy1, h1, hf1⟩ := modDownCPoly_spec hcop (∑ j, D j * centered (ka j))
  set E : Fin Dg.dnum → IntPoly N := fun j => centered (kb j + ka j * ofInt _ s -
    const ((gadget Dg C Bp.prod j : ℤ) : ZMod (C.prod * Bp.prod)) * ofInt _ (tgt.eval s))
  obtain ⟨err, herr, herrc⟩ := ks_core (Q := C.prod) (t := 1) hP (gadget Dg C Bp.prod) D
    (fun j => centered (kb j)) (fun j => centered (ka j)) E (centered (C.combine a)) (tgt.eval s)
    s y0 y1 f0 f1 (gadget_poly Dg C Bp.prod _ D hDc)
    (fun j => key_congr Dg C Bp s tgt j (kb j) (ka j))
    (fun c => by rw [h0 c]; push_cast; ring) (fun c => by rw [h1 c]; push_cast; ring)
  refine ⟨y0, y1, err, ?_, herr, ?_⟩
  · simp only [keySwitchPlain, innerQ_eq Dg C Bp a D hDQ, innerP_eq Dg C Bp a D hDP, hy0, hy1]
  · exact ks_core_bound hP D E (digitWeight Dg C) s f0 f1 err hDb (fun j => (hkey j).1) hs
      hf0 hf1 herrc

end FHE.KeySwitch
