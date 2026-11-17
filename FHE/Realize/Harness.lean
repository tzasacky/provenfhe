import FHE.Realize.KeySwitch
import FHE.Pin.AlgoOpenFHE

/-!
# FHE.Realize.Harness — the locked transcriptions are the functions the harness runs

`Challenge.Realize.relinOpenFHE` and `Challenge.Realize.rotateOpenFHE161` (locked transcriptions,
integer representatives) are proved equal, limb for limb, to `FHE.Pin.Algo.relinOpenFHE` and
`FHE.Pin.Algo.rotateOpenFHE161` (the RNS functions the conformance harness compares with OpenFHE
v1.6.1's relinearization and `EvalAutomorphism`, checks `algo.relin` and `algo.rotate`), on the
bases built from `SchemeParamsOK`, `SpecialOK` and the layout, with the keys read modulo `Q_ℓ·P`
(`relinOpenFHE_toRNS`, `rotateOpenFHE161_toRNS`). (The harness runs the staged forms
`addKS`/`rotStaged161`, proved equal to these in `FHE/Pin/AlgoOpenFHE.lean`: `addKS_openfhe`,
`rotStaged161_openfhe`; and the unstaged ones literally at small `N`.) Its correctness and worst-case noise at the `Spec` modulus of the
level, within the canonical `ksBoundAt`, then follow from `FHE.Pin.Algo.rotateOpenFHE161_spec`
(`rotateOpenFHE161_spec`). This file imports `FHE.Pin.AlgoOpenFHE` and changes nothing there.
-/

namespace FHE.Realize

open Finset Spec Spec.NPoly Spec.Scheme FHE.RNS FHE.RNS.Basis FHE.KeySwitch
  Validation.Ring Validation.Scheme

section Level

variable (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P) [NeZero P.src.N]
  (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)

/-- The two components of the transcription on a two-component operand. -/
def rot0 (g : ℕ) (c0 c1 : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    IntPoly P.src.N :=
  automorph g (((Spec.Budget.specialProd P : ℕ) : ℤ) • c0 +
    Challenge.Realize.innerKey P lay ℓ c1 fun j => (keys.getD j (0, 0)).1)

/-- The argument of the second ModDown. -/
def rot1 (g : ℕ) (c1 : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    IntPoly P.src.N :=
  automorph g (Challenge.Realize.innerKey P lay ℓ c1 fun j => (keys.getD j (0, 0)).2)

theorem rotateOpenFHE161_pair (g : ℕ) (c0 c1 : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    Challenge.Realize.rotateOpenFHE161 P lay ℓ g [c0, c1] keys =
      [Challenge.Realize.modDownBGV P (rot0 P lay ℓ g c0 c1 keys),
       Challenge.Realize.modDownBGV P (rot1 P lay ℓ g c1 keys)] := rfl

/-- **The transcribed relinearization is `FHE.Pin.Algo.relinOpenFHE`**, limb for limb. -/
theorem relinOpenFHE_toRNS (c0 c1 c2 : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    FHE.Pin.Algo.relinOpenFHE (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS) P.src.t ((schemeLevelBasis P hP ℓ hℓ).toRNS c0)
        ((schemeLevelBasis P hP ℓ hℓ).toRNS c1) ((schemeLevelBasis P hP ℓ hℓ).toRNS c2)
        (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2) =
      ((schemeLevelBasis P hP ℓ hℓ).toRNS (c0 + (Challenge.Realize.ksOpenFHE P lay ℓ c2 keys).1),
       (schemeLevelBasis P hP ℓ hℓ).toRNS (c1 + (Challenge.Realize.ksOpenFHE P lay ℓ c2 keys).2)) := by
  have h := ksOpenFHE_toRNS P hP hS lay ℓ hℓ hlay c2 keys
  unfold FHE.Pin.Algo.relinOpenFHE
  rw [h, toRNS_add, toRNS_add]
  rfl

theorem relinOpenFHE_triple (c0 c1 c2 : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    Challenge.Realize.relinOpenFHE P lay ℓ [c0, c1, c2] keys =
      [c0 + (Challenge.Realize.ksOpenFHE P lay ℓ c2 keys).1,
       c1 + (Challenge.Realize.ksOpenFHE P lay ℓ c2 keys).2] := rfl

theorem ofInt_zsmul {N : ℕ} (q : ℕ) (z : ℤ) (c : IntPoly N) :
    ofInt q (z • c) = (z : ZMod q) • ofInt q c := by
  ext k
  show ((z * c.coeff k : ℤ) : ZMod q) = (z : ZMod q) * (c.coeff k : ZMod q)
  push_cast; rfl

/-- **The transcription is `FHE.Pin.Algo.rotateOpenFHE161`**, limb for limb: on the RNS forms of
`c₀`, `c₁`, with the keys read modulo `Q_ℓ·P`, the harness's function returns the RNS form of
the two components of `Challenge.Realize.rotateOpenFHE161 P lay ℓ g [c₀, c₁] keys`. -/
theorem rotateOpenFHE161_toRNS (g : ℕ) (c0 c1 : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    FHE.Pin.Algo.rotateOpenFHE161 (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
        (schemeSpecialBasis P hS) P.src.t g ((schemeLevelBasis P hP ℓ hℓ).toRNS c0)
        ((schemeLevelBasis P hP ℓ hℓ).toRNS c1)
        (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2) =
      ((schemeLevelBasis P hP ℓ hℓ).toRNS
          (Challenge.Realize.modDownBGV P (rot0 P lay ℓ g c0 c1 keys)),
       (schemeLevelBasis P hP ℓ hℓ).toRNS
          (Challenge.Realize.modDownBGV P (rot1 P lay ℓ g c1 keys))) := by
  rw [← modDownBGV_eq P hP hS ℓ hℓ, ← modDownBGV_eq P hP hS ℓ hℓ]
  unfold FHE.Pin.Algo.rotateOpenFHE161
  rw [innerQ_eq P hP hS lay ℓ hℓ hlay c1 (fun j => (keys.getD j (0, 0)).1),
    innerP_eq P hP hS lay ℓ hℓ hlay c1 (fun j => (keys.getD j (0, 0)).1),
    innerQ_eq P hP hS lay ℓ hℓ hlay c1 (fun j => (keys.getD j (0, 0)).2),
    innerP_eq P hP hS lay ℓ hℓ hlay c1 (fun j => (keys.getD j (0, 0)).2)]
  refine Prod.ext ?_ ?_
  · show bgvModDownPoly _ _ _ _ _ = bgvModDownPoly _ _ _ _ _
    congr 1
    · funext i
      show automorph g (_ • ofInt _ c0 + ofInt _ _) = ofInt _ (automorph g _)
      rw [ofInt_automorph, ofInt_add, ofInt_zsmul]
      congr 3
      rw [schemeSpecialBasis_prod P hS, Int.cast_natCast]
    · funext i
      show automorph g (ofInt _ _) = ofInt _ (automorph g _)
      rw [ofInt_automorph, ofInt_add, ofInt_zsmul]
      have hz : (((Spec.Budget.specialProd P : ℕ) : ℤ) : ZMod ((schemeSpecialBasis P hS).q i)) = 0 := by
        rw [Int.cast_natCast, ← schemeSpecialBasis_prod P hS,
          (ZMod.natCast_eq_zero_iff _ _).mpr ((schemeSpecialBasis P hS).q_dvd_prod i)]
      rw [hz, zero_smul, zero_add]
  · show bgvModDownPoly _ _ _ _ _ = bgvModDownPoly _ _ _ _ _
    congr 1
    · funext i; exact (ofInt_automorph _ _ _).symm
    · funext i; exact (ofInt_automorph _ _ _).symm

end Level

/-- **The transcribed v1.6.1 rotation: correctness and worst-case noise** at the `Spec` modulus of
the level `ℓ`, within the canonical `ksBoundAt`. For odd `g`, keys valid for the secret `s'` and
the target `tgt`: the output's phase under `σ_g(s')` is `σ_g(c₀) + σ_g(c₁)·σ_g(tgt(s')) + e`,
`t ∣ e`, `‖e‖∞ ≤ ksBoundAt P lay ℓ`. -/
theorem rotateOpenFHE161_spec (P : FullParams) (hP : SchemeParamsOK P)
    (hS : Spec.Budget.SpecialOK P) [NeZero P.src.N] (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) (hk : P.src.kind = .bgv)
    (hc : lay.canonical = true) (s' : IntPoly P.src.N) (hs' : normInf s' ≤ P.secretBound)
    (tgt : KeyTarget) (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Spec.Budget.GadgetKeysOK P lay ℓ tgt s' keys) (g : ℕ) (hg : g % 2 = 1)
    (c0 c1 : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (Challenge.Realize.modDownBGV P (rot0 P lay ℓ g c0 c1 keys)) +
        ofInt (P.src.modulus ℓ) (Challenge.Realize.modDownBGV P (rot1 P lay ℓ g c1 keys)) *
          ofInt (P.src.modulus ℓ) (automorph g s') =
        ofInt (P.src.modulus ℓ) (automorph g c0) +
          ofInt (P.src.modulus ℓ) (automorph g c1) *
            ofInt (P.src.modulus ℓ) (automorph g (tgt.eval s')) +
          ofInt (P.src.modulus ℓ) e ∧
      (∀ c, (P.src.t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ Spec.Budget.ksBoundAt P lay ℓ := by
  have hQ := schemeLevelBasis_prod P hP ℓ hℓ
  have hPm := schemeSpecialBasis_prod P hS
  have hkey : ∀ j : Fin (layoutDigits lay ℓ hlay).dnum,
      KeyValid .bgv P.src.t P.keyNoise s'
        (gadgetReq (layoutDigits lay ℓ hlay) (schemeLevelBasis P hP ℓ hℓ)
          (schemeSpecialBasis P hS) tgt j)
        (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
          (keys.getD j (0, 0)).1)
        (ofInt ((schemeLevelBasis P hP ℓ hℓ).prod * (schemeSpecialBasis P hS).prod)
          (keys.getD j (0, 0)).2) := by
    intro j
    obtain ⟨hlen, hv⟩ := hkeys
    have hj : (j : ℕ) < keys.length := by rw [hlen]; exact j.isLt
    have h := hv j hj
    rw [hk] at h
    have hg1 : keys.getD j (0, 0) = keys[(j : ℕ)] := by simp [hj]
    rw [hg1]
    exact keyValid_congr (by rw [hQ, hPm])
      (gadget_eq_gadgetFactor P hP hS lay ℓ hℓ hlay j) tgt _ _ h
  obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
    FHE.Pin.Algo.rotateOpenFHE161_spec (Dg := layoutDigits lay ℓ hlay)
      (C := schemeLevelBasis P hP ℓ hℓ) (Bp := schemeSpecialBasis P hS) hP.N_pow2 hg
      (special_ht P hS) (special_hcop P hP hS ℓ hℓ) s' hs' tgt _ _ hkey c0
      ((schemeLevelBasis P hP ℓ hℓ).toRNS c1)
  rw [rotateOpenFHE161_toRNS P hP hS lay ℓ hℓ hlay g c0 c1 keys] at hout
  have h0 := congrArg (fun p => (schemeLevelBasis P hP ℓ hℓ).combine p.1) hout
  have h1 := congrArg (fun p => (schemeLevelBasis P hP ℓ hℓ).combine p.2) hout
  simp only [combine_toRNS] at h0 h1
  rw [combine_toRNS, ofInt_add, ofInt_add, ofInt_mul, ofInt_mul, ofInt_automorph _ g (centered _),
    ofInt_centered, ← ofInt_automorph] at heq
  refine ⟨e, ?_, hdvd, ?_⟩
  · rw [← hQ, h0, h1, ofInt_add]
    linear_combination heq
  · rw [ksBoundAt_eq P hP hS lay ℓ hℓ hlay, hc]
    simpa using hb

end FHE.Realize
