import FHE.Pin.AlgoStage
import FHE.KeySwitch.Order

/-!
# FHE.Pin.AlgoOpenFHE — OpenFHE's ciphertext-level key-switching operations, in RNS form

`FHE.KeySwitch.keySwitchBGVOpenFHE` is the key-switching core `(c₂ or c₁) ↦ (KS₀, KS₁)`.
OpenFHE's ciphertext-level operations use it as follows (source references: v1.6.1,
`src/pke/lib/schemebase/base-leveledshe.cpp`):

* `relinOpenFHE` — one round of `LeveledSHEBase::RelinearizeInPlace` (`:362-380`) /
  `LeveledSHEBase::EvalMult(ct, ct, key)` (`:232-247`): `(c₀ + KS(d)₀, c₁ + KS(d)₁)`, limb by
  limb. The same in v1.3.1.
* `rotateOpenFHE161` — `EvalAutomorphism` and `EvalFastRotation` of **v1.6.1**
  (`EvalAutomorphismCore`, `:455-506`): the inner products of the ModUp digits of `c₁` with the
  key stored for `g`, over `Q_ℓ·P`; `P·c₀` added; `σ_g` over `Q_ℓ·P`; then ModDown. This is not
  the core followed by `σ_g`: see "OpenFHE v1.6.1's rotation" below.
* `rotateOpenFHE` — the rotation of **v1.3.1**: key switch `c₁` under the key stored for `g`
  first, add to `c₀`, then apply `σ_g` to both components: `(σ_g(c₀ + KS(c₁)₀), σ_g(KS(c₁)₁))`.
  Kept as a recorded variant; it does not reproduce v1.6.1's output.

These differ from `FHE.KeySwitch.relinCt` / `keySwitchCt` (`FHE/KeySwitch/Step.lean`) in three
ways: they use the canonical-representative core `keySwitchBGVOpenFHE` instead of the centred
`keySwitchBGV`; they stay in RNS form (no `centered (combine ·)`); and the rotation applies the
automorphism *after* the key switch (the order `FHE/KeySwitch/Order.lean` shows admissible).

Proved here (kernel-checked):
* `addKS_eq`, `rotStaged161_eq`, `rotStaged_eq`: the staged (memoised) executions used by the
  differential harness equal the pipelines; with the OpenFHE stages they are `relinOpenFHE`,
  `rotateOpenFHE161`, `rotateOpenFHE` (`addKS_openfhe`, `rotStaged161_openfhe`,
  `rotStaged_openfhe`).
* `relinOpenFHE_spec`: for valid BGV keys, `relinOpenFHE` returns the RNS form of
  `(c₀ + y₀, c₁ + y₁)` with `y₀ + y₁·s ≡ d·tgt(s) + e (mod Q)`, `t ∣ e`, and the noise bound of
  `keySwitchBGVOpenFHE_spec`.
* `rotateOpenFHE_spec`: the same for the v1.3.1 rotation, the output being the RNS form of
  `(σ_g(c₀ + y₀), σ_g(y₁))`.
* `rotateOpenFHE161_spec`: the same for the v1.6.1 rotation (odd `g`, `N` a power of two): the
  output is the RNS form of `(σ_g(c₀) + y₀, y₁)` with
  `y₀ + y₁·σ_g(s) ≡ σ_g(c₁)·σ_g(tgt(s)) + e (mod Q)`, `t ∣ e`, and the same noise bound.

NOT proved here: the statement of these two operations as `Spec.Trace` steps (that is
`FHE/KeySwitch/Order.lean` + `Step.lean` for the centred variant).
-/

namespace FHE.Pin.Algo
open Finset Spec Spec.NPoly Spec.Scheme FHE.RNS FHE.RNS.Basis FHE.KeySwitch FHE.Pin
  Validation.Ring Validation.Scheme Validation.Source

variable {N ℓ k : ℕ} {Dg : Digits ℓ} {C : Basis ℓ} {Bp : Basis k} [NeZero N]

/-! ## The operations -/

/-- `(c₀ + KS(d)₀, c₁ + KS(d)₁)` for a key-switching pipeline `S`. -/
def addPipe (S : Stages Dg C Bp N) (c0 c1 d : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (fun i => c0 i + (ksPipe S d kb ka).1 i, fun i => c1 i + (ksPipe S d kb ka).2 i)

/-- `(σ_g(c₀ + KS(c₁)₀), σ_g(KS(c₁)₁))` for a key-switching pipeline `S`. -/
def rotPipe (S : Stages Dg C Bp N) (g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (fun i => automorph g (c0 i + (ksPipe S c1 kb ka).1 i),
   fun i => automorph g ((ksPipe S c1 kb ka).2 i))

variable (Dg C Bp)

/-- **OpenFHE's relinearization step** (`KeySwitchInPlace` on three parts, one round of
`RelinearizeInPlace`, `EvalMult` with a key): `(c₀ + KS(d)₀, c₁ + KS(d)₁)` with
`KS = keySwitchBGVOpenFHE`. -/
def relinOpenFHE (t : ℕ) (c0 c1 d : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (fun i => c0 i + (keySwitchBGVOpenFHE Dg C Bp t d kb ka).1 i,
   fun i => c1 i + (keySwitchBGVOpenFHE Dg C Bp t d kb ka).2 i)

/-- **OpenFHE's rotation** (`EvalAutomorphism`, `EvalFastRotation`): key switch `c₁` under the key
stored for `g`, add to `c₀`, then `σ_g` on both components. -/
def rotateOpenFHE (t g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (fun i => automorph g (c0 i + (keySwitchBGVOpenFHE Dg C Bp t c1 kb ka).1 i),
   fun i => automorph g ((keySwitchBGVOpenFHE Dg C Bp t c1 kb ka).2 i))

variable {Dg C Bp}

theorem addPipe_openfhe (t : ℕ) (c0 c1 d : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    addPipe (openfheStages Dg C Bp t) c0 c1 d kb ka = relinOpenFHE Dg C Bp t c0 c1 d kb ka := rfl

theorem rotPipe_openfhe (t g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    rotPipe (openfheStages Dg C Bp t) g c0 c1 kb ka = rotateOpenFHE Dg C Bp t g c0 c1 kb ka := rfl

/-! ## Staged execution -/

/-- Staged `addPipe`: the staged key switch, then the two limbwise sums, forced. -/
def addKS (S : Stages Dg C Bp N) (K : ℕ) (c0 c1 d : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : Array (Array ℤ) × Array (Array ℤ) :=
  let o := ksStaged S K d kb ka
  (forceFam K C.q (fun i => c0 i + ofFam (N := N) C.q o.1 i),
   forceFam K C.q (fun i => c1 i + ofFam (N := N) C.q o.2 i))

theorem addKS_eq (S : Stages Dg C Bp N) (K : ℕ) (c0 c1 d : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (addKS S K c0 c1 d kb ka).1, ofFam C.q (addKS S K c0 c1 d kb ka).2) =
      addPipe S c0 c1 d kb ka := by
  have h := ksStaged_eq S K d kb ka
  simp only [addKS, addPipe, ofFam_forceFam, ← h]

/-- **The staged relinearization step is `relinOpenFHE`.** -/
theorem addKS_openfhe (t K : ℕ) (c0 c1 d : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (addKS (openfheStages Dg C Bp t) K c0 c1 d kb ka).1,
     ofFam C.q (addKS (openfheStages Dg C Bp t) K c0 c1 d kb ka).2) =
      relinOpenFHE Dg C Bp t c0 c1 d kb ka := by
  rw [addKS_eq, addPipe_openfhe]

/-- Staged `rotPipe`: the staged key switch, the sum with `c₀`, the two automorphisms, each
forced. -/
def rotStaged (S : Stages Dg C Bp N) (K g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : Array (Array ℤ) × Array (Array ℤ) :=
  let o := ksStaged S K c1 kb ka
  let r0 := forceFam K C.q (fun i => c0 i + ofFam (N := N) C.q o.1 i)
  (autoFam C.q g (fun i => ofFam (N := N) C.q r0 i),
   autoFam C.q g (fun i => ofFam (N := N) C.q o.2 i))

theorem rotStaged_eq (S : Stages Dg C Bp N) (K g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (rotStaged S K g c0 c1 kb ka).1, ofFam C.q (rotStaged S K g c0 c1 kb ka).2) =
      rotPipe S g c0 c1 kb ka := by
  have h := ksStaged_eq S K c1 kb ka
  simp only [rotStaged, rotPipe, ofFam_forceFam, ofFam_autoFam, ← h]

/-- **The staged rotation is `rotateOpenFHE`.** -/
theorem rotStaged_openfhe (t K g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (rotStaged (openfheStages Dg C Bp t) K g c0 c1 kb ka).1,
     ofFam C.q (rotStaged (openfheStages Dg C Bp t) K g c0 c1 kb ka).2) =
      rotateOpenFHE Dg C Bp t g c0 c1 kb ka := by
  rw [rotStaged_eq, rotPipe_openfhe]

/-! ## OpenFHE v1.6.1's rotation

From v1.6.1 on, `LeveledSHEBase::EvalAutomorphism` and `EvalFastRotation` share
`EvalAutomorphismCore` (`base-leveledshe.cpp:455-495`, HYBRID branch): the inner products of the
ModUp digits of `c₁` with the key are formed over `Q_ℓ·P` (`EvalFastKeySwitchCoreExt`), `P·c₀` is
added to the first one on the ciphertext limbs, **the automorphism is applied over `Q_ℓ·P`**, and
only then ModDown. With canonical representatives ModDown does not commute with `σ_g` (a
coefficient `x` becomes `−x`, whose representative in `[0, p)` is `p − x`), so the result differs
from `rotateOpenFHE` (the v1.3.1 order: ModDown, add `c₀`, then `σ_g`) by multiples of `t`. -/

/-- `(ModDown(σ_g(P·c₀ + ⟨ModUp c₁, kb⟩)), ModDown(σ_g(⟨ModUp c₁, ka⟩)))` for the stages `S`. -/
def rotPipe161 (S : Stages Dg C Bp N) (g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (S.down (fun i => automorph g (((Bp.prod : ℕ) : ZMod (C.q i)) • c0 i +
              ∑ j, S.upQ c1 j i * keyLimb (C.q i) (kb j)))
          (fun i => automorph g (∑ j, S.upP c1 j i * keyLimb (Bp.q i) (kb j))),
   S.down (fun i => automorph g (∑ j, S.upQ c1 j i * keyLimb (C.q i) (ka j)))
          (fun i => automorph g (∑ j, S.upP c1 j i * keyLimb (Bp.q i) (ka j))))

variable (Dg C Bp) in
/-- **OpenFHE v1.6.1's rotation** (`EvalAutomorphismCore`, HYBRID): canonical ModUp of `c₁`, inner
products with the key stored for `g` over `Q_ℓ·P`, `P·c₀` added, `σ_g` over `Q_ℓ·P`, then
OpenFHE's BGV ModDown of both components. -/
def rotateOpenFHE161 (t g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : RNSPoly C N × RNSPoly C N :=
  (bgvModDownPoly C Bp t
      (fun i => automorph g (((Bp.prod : ℕ) : ZMod (C.q i)) • c0 i + innerQCanon Dg C Bp c1 kb i))
      (fun i => automorph g (innerPCanon Dg C Bp c1 kb i)),
   bgvModDownPoly C Bp t
      (fun i => automorph g (innerQCanon Dg C Bp c1 ka i))
      (fun i => automorph g (innerPCanon Dg C Bp c1 ka i)))

theorem rotPipe161_openfhe (t g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    rotPipe161 (openfheStages Dg C Bp t) g c0 c1 kb ka = rotateOpenFHE161 Dg C Bp t g c0 c1 kb ka := rfl

/-- Staged `rotPipe161`: ModUp of every digit, the key limbs, the four inner products, the four
automorphisms over `Q_ℓ·P` and the two ModDowns, each forced. -/
def rotStaged161 (S : Stages Dg C Bp N) (K g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) : Array (Array ℤ) × Array (Array ℤ) :=
  let UQ : Array (Array (Array ℤ)) := Array.ofFn fun j : Fin Dg.dnum => forceFam K C.q (S.upQ c1 j)
  let UP : Array (Array (Array ℤ)) := Array.ofFn fun j : Fin Dg.dnum => forceFam K Bp.q (S.upP c1 j)
  let KbQ : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K C.q (fun i => keyLimb (C.q i) (kb j))
  let KbP : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K Bp.q (fun i => keyLimb (Bp.q i) (kb j))
  let KaQ : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K C.q (fun i => keyLimb (C.q i) (ka j))
  let KaP : Array (Array (Array ℤ)) :=
    Array.ofFn fun j : Fin Dg.dnum => forceFam K Bp.q (fun i => keyLimb (Bp.q i) (ka j))
  let IbQ := innerZ (N := N) K C.q Dg.dnum UQ KbQ
  let IbP := innerZ (N := N) K Bp.q Dg.dnum UP KbP
  let IaQ := innerZ (N := N) K C.q Dg.dnum UQ KaQ
  let IaP := innerZ (N := N) K Bp.q Dg.dnum UP KaP
  let AbQ := autoFam C.q g (fun i => ((Bp.prod : ℕ) : ZMod (C.q i)) • c0 i + ofFam (N := N) C.q IbQ i)
  let AbP := autoFam Bp.q g (fun i => ofFam (N := N) Bp.q IbP i)
  let AaQ := autoFam C.q g (fun i => ofFam (N := N) C.q IaQ i)
  let AaP := autoFam Bp.q g (fun i => ofFam (N := N) Bp.q IaP i)
  (forceFam K C.q (S.down (ofFam C.q AbQ) (ofFam Bp.q AbP)),
   forceFam K C.q (S.down (ofFam C.q AaQ) (ofFam Bp.q AaP)))

theorem rotStaged161_eq (S : Stages Dg C Bp N) (K g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (rotStaged161 S K g c0 c1 kb ka).1, ofFam C.q (rotStaged161 S K g c0 c1 kb ka).2) =
      rotPipe161 S g c0 c1 kb ka := by
  simp only [rotStaged161, rotPipe161, ofFam_innerZ, getElem!_ofFn, ofFam_forceFam, ofFam_autoFam]

/-- **The staged v1.6.1 rotation is `rotateOpenFHE161`.** -/
theorem rotStaged161_openfhe (t K g : ℕ) (c0 c1 : RNSPoly C N)
    (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N) :
    (ofFam C.q (rotStaged161 (openfheStages Dg C Bp t) K g c0 c1 kb ka).1,
     ofFam C.q (rotStaged161 (openfheStages Dg C Bp t) K g c0 c1 kb ka).2) =
      rotateOpenFHE161 Dg C Bp t g c0 c1 kb ka := by
  rw [rotStaged161_eq, rotPipe161_openfhe]

/-! ## What the two operations compute -/

/-- **`relinOpenFHE`: correctness and worst-case noise.** For valid BGV keys for `tgt`, the
output is the RNS form of `(c₀ + y₀, c₁ + y₁)` with `y₀ + y₁·s ≡ d·tgt(s) + e (mod Q)`, `t ∣ e`
and `‖e‖∞` within the bound of `keySwitchBGVOpenFHE_spec`. -/
theorem relinOpenFHE_spec {t Bk Bs : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (c0 c1 : IntPoly N) (d : RNSPoly C N) :
    ∃ y0 y1 e : IntPoly N,
      relinOpenFHE Dg C Bp t (C.toRNS c0) (C.toRNS c1) d kb ka =
        (C.toRNS (c0 + y0), C.toRNS (c1 + y1)) ∧
      ofInt C.prod (y0 + y1 * s) = ofInt C.prod (centered (C.combine d) * tgt.eval s + e) ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (2 * (k * (Bp.prod - 1))) Bp.prod (canonWeight Dg C) := by
  obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
    keySwitchBGVOpenFHE_spec Dg C Bp ht hcop s hs tgt kb ka hkey d
  refine ⟨y0, y1, e, ?_, heq, hdvd, hb⟩
  simp only [relinOpenFHE, hout]
  refine Prod.ext ?_ ?_ <;> funext i <;> simp only [toRNS, ofInt_add]

/-- **`rotateOpenFHE`: correctness and worst-case noise.** For valid BGV keys for `tgt`, the
output is the RNS form of `(σ_g(c₀ + y₀), σ_g(y₁))` with `y₀ + y₁·s ≡ c₁·tgt(s) + e (mod Q)`,
`t ∣ e` and `‖e‖∞` within the bound of `keySwitchBGVOpenFHE_spec`. (With `tgt = σ_{g⁻¹}(s)`-type
keys this is OpenFHE's rotation; the phase statement is `FHE/KeySwitch/Order.lean`.) -/
theorem rotateOpenFHE_spec {t Bk Bs : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (g : ℕ) (c0 : IntPoly N) (c1 : RNSPoly C N) :
    ∃ y0 y1 e : IntPoly N,
      rotateOpenFHE Dg C Bp t g (C.toRNS c0) c1 kb ka =
        (C.toRNS (automorph g (c0 + y0)), C.toRNS (automorph g y1)) ∧
      ofInt C.prod (y0 + y1 * s) = ofInt C.prod (centered (C.combine c1) * tgt.eval s + e) ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (2 * (k * (Bp.prod - 1))) Bp.prod (canonWeight Dg C) := by
  obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
    keySwitchBGVOpenFHE_spec Dg C Bp ht hcop s hs tgt kb ka hkey c1
  refine ⟨y0, y1, e, ?_, heq, hdvd, hb⟩
  simp only [rotateOpenFHE, hout]
  refine Prod.ext ?_ ?_ <;> funext i <;> simp only [toRNS, ofInt_add, ofInt_automorph]

/-! ## What the v1.6.1 rotation computes -/

/-- `σ_g` commutes with multiplication by an integer constant. -/
theorem automorph_intCast_mul (g : ℕ) (z : ℤ) (a : IntPoly N) :
    automorph g ((z : IntPoly N) * a) = (z : IntPoly N) * automorph g a := by
  ext k
  rw [coeff_intCast_mul', coeff_automorph', coeff_automorph', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_intCast_mul']
  split_ifs <;> ring

/-- `σ_g` commutes with multiplication by a natural constant. -/
theorem automorph_natCast_mul (g n : ℕ) (a : IntPoly N) :
    automorph g ((n : IntPoly N) * a) = (n : IntPoly N) * automorph g a := by
  ext k
  rw [coeff_natCast_mul', coeff_automorph', coeff_automorph', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_natCast_mul']
  split_ifs <;> ring

theorem automorph_sub' (g : ℕ) (a b : IntPoly N) :
    automorph g (a - b) = automorph g a - automorph g b := by
  have h : automorph g a = automorph g (a - b) + automorph g b := by
    rw [← automorph_add]; congr 1; ext i; simp
  rw [h]; ext i; simp

theorem automorph_sum' (g : ℕ) {ι : Type} (S : Finset ι) (f : ι → IntPoly N) :
    automorph g (∑ j ∈ S, f j) = ∑ j ∈ S, automorph g (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [automorph_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, automorph_add, ih]

/-- **`rotateOpenFHE161` (OpenFHE v1.6.1's rotation): correctness and worst-case noise.** For odd
`g`, `N` a power of two and valid BGV keys for `tgt`, the output is the RNS form of
`(σ_g(c₀) + y₀, y₁)` with `y₀ + y₁·σ_g(s) ≡ σ_g(c₁)·σ_g(tgt(s)) + e (mod Q)`, `t ∣ e`, and `‖e‖∞`
within the same bound as `keySwitchBGVOpenFHE_spec`. (OpenFHE's stored rotation key for `g` is
valid for the secret `s = σ_{g⁻¹}(s₀)` and the target `galois g`, where `s₀` is the user's secret
— the reading `secret=sigma_{i^-1}(s) target=galois(i) key=as-stored` of the harness's
`d.reading` lines. Then `σ_g(s) = s₀` and `σ_g(tgt(s)) = σ_g(s₀)`, so the output has phase
`σ_g(c₀) + y₀ + y₁·s₀ ≡ σ_g(c₀ + c₁·s₀) + e` under `s₀`: the rotated phase plus the error.) The
automorphism is applied over `Q·P` before ModDown; the proof applies `σ_g` to the ModUp digits,
the keys and the key errors, which keeps every norm (`normInf_automorph_le`). -/
theorem rotateOpenFHE161_spec {t Bk Bs : ℕ} (hN : ∃ m, N = 2 ^ m) {g : ℕ} (hg : g % 2 = 1)
    (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (c0 : IntPoly N) (c1 : RNSPoly C N) :
    ∃ y0 y1 e : IntPoly N,
      rotateOpenFHE161 Dg C Bp t g (C.toRNS c0) c1 kb ka =
        (C.toRNS (automorph g c0 + y0), C.toRNS y1) ∧
      ofInt C.prod (y0 + y1 * automorph g s) =
        ofInt C.prod (automorph g (centered (C.combine c1)) * automorph g (tgt.eval s) + e) ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (2 * (k * (Bp.prod - 1))) Bp.prod (canonWeight Dg C) := by
  choose D hDQ hDP hDc hDb using modUpCanon_spec Dg C Bp c1
  have hP := Bp.prod_pos
  set X0 : IntPoly N := ∑ j, D j * centered (kb j) with hX0
  set X1 : IntPoly N := ∑ j, D j * centered (ka j) with hX1
  obtain ⟨z0, f0, hz0, h0, hf0⟩ :=
    bgvModDownPoly_spec ht hcop (automorph g ((Bp.prod : IntPoly N) * c0 + X0))
  obtain ⟨y1, f1, hy1, h1, hf1⟩ := bgvModDownPoly_spec ht hcop (automorph g X1)
  set E : Fin Dg.dnum → IntPoly N := fun j => centered (kb j + ka j * ofInt _ s -
    const ((gadget Dg C Bp.prod j : ℤ) : ZMod (C.prod * Bp.prod)) * ofInt _ (tgt.eval s))
  -- the σ_g-images of the digits, the keys and the key errors
  have hgad := gadget_poly Dg C Bp.prod (automorph g (centered (C.combine c1)))
    (fun j => automorph g (D j)) (fun j c => by
      have := dvd_coeff_automorph g _ (D j - centered (C.combine c1))
        (fun c => by simpa using hDc j c) c
      rw [automorph_sub'] at this
      simpa using this)
  have hkc : ∀ j, ofInt (C.prod * Bp.prod)
      (automorph g (centered (kb j)) + automorph g (centered (ka j)) * automorph g s -
        (gadget Dg C Bp.prod j : IntPoly N) * automorph g (tgt.eval s) - automorph g (E j)) = 0 := by
    intro j
    have h := key_congr Dg C Bp s tgt j (kb j) (ka j)
    have h' := congrArg (automorph g) h
    rw [← ofInt_automorph, automorph_zero, automorph_sub', automorph_sub', automorph_add,
      automorph_mul hg, automorph_intCast_mul] at h'
    exact h'
  have hsum : ∀ K' : Fin Dg.dnum → IntPoly N,
      automorph g (∑ j, D j * K' j) = ∑ j, automorph g (D j) * automorph g (K' j) := by
    intro K'
    rw [automorph_sum']
    exact Finset.sum_congr rfl fun j _ => automorph_mul hg _ _
  have h0' : ∀ c, (Bp.prod : ℤ) * (z0 - automorph g c0).coeff c =
      (∑ j, automorph g (D j) * automorph g (centered (kb j))).coeff c + t * f0.coeff c := by
    intro c
    have := h0 c
    rw [automorph_add, automorph_natCast_mul, hsum, coeff_add', coeff_natCast_mul'] at this
    rw [coeff_sub']
    linarith
  have h1' : ∀ c, (Bp.prod : ℤ) * y1.coeff c =
      (∑ j, automorph g (D j) * automorph g (centered (ka j))).coeff c + t * f1.coeff c := by
    intro c
    have := h1 c
    rw [hsum] at this
    exact this
  obtain ⟨err, herr, herrc⟩ := ks_core (Q := C.prod) hP (gadget Dg C Bp.prod)
    (fun j => automorph g (D j)) (fun j => automorph g (centered (kb j)))
    (fun j => automorph g (centered (ka j))) (fun j => automorph g (E j))
    (automorph g (centered (C.combine c1))) (automorph g (tgt.eval s)) (automorph g s)
    (z0 - automorph g c0) y1 f0 f1 hgad hkc h0' h1'
  refine ⟨z0 - automorph g c0, y1, err, ?_, herr, ?_, ?_⟩
  · have e0 : automorph g c0 + (z0 - automorph g c0) = z0 := by ext i; simp
    rw [e0, ← hz0, ← hy1]
    simp only [rotateOpenFHE161, innerQCanon_eq Dg C Bp c1 D hDQ, innerPCanon_eq Dg C Bp c1 D hDP]
    refine Prod.ext ?_ ?_
    · show bgvModDownPoly C Bp t _ _ = bgvModDownPoly C Bp t _ _
      congr 1
      · funext i
        show automorph g (_ • ofInt (C.q i) c0 + ofInt (C.q i) X0) = ofInt (C.q i) _
        rw [ofInt_automorph, ofInt_add, ofInt_mul, ofInt_natCast]
        congr 2
        ext c; rw [natCast_def, coeff_const_mul]; rfl
      · funext i
        show automorph g (ofInt (Bp.q i) X0) = ofInt (Bp.q i) _
        rw [ofInt_automorph, ofInt_add, ofInt_mul, ofInt_natCast]
        have hz : ((Bp.prod : ℕ) : Poly (Bp.q i) N) = 0 := by
          have h2 : ((Bp.prod : ℕ) : Poly (Bp.q i) N) = ((0 : ℕ) : Poly (Bp.q i) N) := by
            rw [natCast_def, natCast_def, (ZMod.natCast_eq_zero_iff _ _).mpr (Bp.q_dvd_prod i),
              Nat.cast_zero]
          rw [h2, Nat.cast_zero]
        rw [hz, zero_mul, zero_add]
    · show bgvModDownPoly C Bp t _ _ = bgvModDownPoly C Bp t _ _
      congr 1
      · funext i
        show automorph g (ofInt (C.q i) X1) = ofInt (C.q i) _
        rw [ofInt_automorph]
      · funext i
        show automorph g (ofInt (Bp.q i) X1) = ofInt (Bp.q i) _
        rw [ofInt_automorph]
  · exact ks_core_dvd (Nat.coprime_prod_right_iff.mpr fun j _ => ht j) _ _ _ f0 f1 err
      (fun j => dvd_coeff_automorph g _ (E j) ((hkey j).2 rfl)) herrc
  · exact ks_core_bound hP _ _ (canonWeight Dg C) _ f0 f1 err
      (fun j => (Nat.mul_le_mul_left 2 (normInf_automorph_le hN hg (D j))).trans (hDb j))
      (fun j => (normInf_automorph_le hN hg (E j)).trans (hkey j).1)
      ((normInf_automorph_le hN hg s).trans hs) hf0 hf1 herrc

end FHE.Pin.Algo
