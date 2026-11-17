import Challenge.Instances.Lattigo.MSB
import Validation.Instances.Lattigo
import Validation.MSB

/-!
# Validation.Instances.Lattigo.MSB — proofs of the pins of `Challenge.Instances.Lattigo.MSB`

`instanceOK?` is read through `Validation.Instances.Lattigo.instanceOK?_facts` and
`Validation.Profile.coversBGV?_facts`; the top-level MSB keys are cut to each level by
`Validation.MSB.gadgetKeys_restrict` (the size condition `2·19 < Q_ℓ·P` follows from the
key-size check `keysRestrict?` and `t·19 ≤ keyNoise`); then `Validation.MSB.relin_stepOK`,
`keySwitch_stepOK`, `rescale_stepOK` at the profile, and `stepOK_toLSB` for the t-readings.
-/

namespace Validation.Instances.Lattigo
open Spec NPoly Scheme Source Correct Spec.MSB Challenge.Profile Challenge.Instances.Lattigo

theorem params_keyNoise (N : ℕ) (qs ps : List ℕ) (t : ℕ) :
    (params N qs ps t).src.t * errBound ≤ (params N qs ps t).keyNoise := le_refl _

/-- The size condition for one top-level MSB key set. -/
theorem keySize (P : FullParams) (h : instanceOK? P = true)
    (hkn : P.src.t * errBound ≤ P.keyNoise) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    2 * errBound < P.src.modulus ℓ * Budget.specialProd P := by
  obtain ⟨hc, hr⟩ := Validation.Instances.Lattigo.instanceOK?_facts h
  obtain ⟨hP, -, -, -, -⟩ := Validation.Profile.coversBGV?_facts hc
  have hlt := Validation.Budget.keysRestrict?_level P hr hP ℓ h1 hℓ
  have ht : 1 ≤ P.src.t := by have := hP.plaintext.1; omega
  have h19 : errBound ≤ P.keyNoise / P.src.t :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hkn)
  have h2 : errBound ≤ P.keyNoise / P.src.t * P.src.t :=
    h19.trans (Nat.le_mul_of_pos_right _ (by omega))
  omega

theorem relin_meets_msb (P : FullParams) (h : instanceOK? P = true)
    (hkn : P.src.t * errBound ≤ P.keyNoise) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P (layout P) P.src.qs.length .square errBound s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    MSB.StepOK P (profile P) s ρ ρ' σ
      (σ.set d (MSB.relin P (layout P) ℓ ca (keys.take ((layout P).sizes ℓ).length)))
      (.relin d a) := by
  obtain ⟨hc, -⟩ := Validation.Instances.Lattigo.instanceOK?_facts h
  obtain ⟨hP, -, hS, hlv, -⟩ := Validation.Profile.coversBGV?_facts hc
  obtain ⟨hok, hb⟩ := hlv ℓ h1 hℓ
  have hk := Validation.MSB.gadgetKeys_restrict P (layout P) .square hP ℓ hℓ
    (Validation.Instances.Lattigo.layout_restricts P ℓ h1 hℓ) errBound
    (Validation.Instances.Lattigo.keySize P h hkn ℓ h1 hℓ) s keys hkeys
  exact Validation.MSB.relin_stepOK P (layout P) hP hS ℓ hℓ hok (profile P) hb errBound hkn s hs
    _ hk ρ ρ' σ d a x ca hstep hx hca hl hlen

theorem keySwitch_meets_msb (P : FullParams) (h : instanceOK? P = true)
    (hkn : P.src.t * errBound ≤ P.keyNoise) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P (layout P) P.src.qs.length (.galois x.key) errBound s keys) :
    MSB.StepOK P (profile P) s ρ ρ' σ
      (σ.set d (MSB.keySwitch P (layout P) ℓ ca (keys.take ((layout P).sizes ℓ).length)))
      (.keySwitch d a) := by
  obtain ⟨hc, -⟩ := Validation.Instances.Lattigo.instanceOK?_facts h
  obtain ⟨hP, -, hS, hlv, -⟩ := Validation.Profile.coversBGV?_facts hc
  obtain ⟨hok, hb⟩ := hlv ℓ h1 hℓ
  have hk := Validation.MSB.gadgetKeys_restrict P (layout P) (.galois x.key) hP ℓ hℓ
    (Validation.Instances.Lattigo.layout_restricts P ℓ h1 hℓ) errBound
    (Validation.Instances.Lattigo.keySize P h hkn ℓ h1 hℓ) s keys hkeys
  exact Validation.MSB.keySwitch_stepOK P (layout P) hP hS ℓ hℓ hok (profile P) hb errBound hkn s
    hs ρ ρ' σ d a x ca hstep hx hca hl hlen _ hk

theorem rescale_meets_msb (P : FullParams) (h : instanceOK? P = true) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ maxParts) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hparts : x.parts = k) (hlen : ca.length = k) :
    MSB.StepOK P (profile P) s ρ ρ' σ (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca))
      (.modSwitch d a) := by
  obtain ⟨hc, -⟩ := Validation.Instances.Lattigo.instanceOK?_facts h
  obtain ⟨hP, -, -, -, hms⟩ := Validation.Profile.coversBGV?_facts hc
  subst hparts
  exact Validation.MSB.rescale_stepOK P hP (profile P) s hs ρ ρ' σ d a x ca (hms _ hk1 hk) hstep
    hx hca hlen

theorem relin_meets_lsb (P : FullParams) (h : instanceOK? P = true)
    (hkn : P.src.t * errBound ≤ P.keyNoise) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P (layout P) P.src.qs.length .square errBound s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    Trace.StepOK P (profile P) s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.relin P (layout P) ℓ ca (keys.take ((layout P).sizes ℓ).length))))
      (.relin d a) :=
  Validation.MSB.stepOK_toLSB P _ s ρ ρ' σ _ _ hstep
    (Validation.Instances.Lattigo.relin_meets_msb P h hkn ℓ h1 hℓ s hs keys hkeys ρ ρ' σ d a x ca hstep hx hca hl hlen)

theorem keySwitch_meets_lsb (P : FullParams) (h : instanceOK? P = true)
    (hkn : P.src.t * errBound ≤ P.keyNoise) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P (layout P) P.src.qs.length (.galois x.key) errBound s keys) :
    Trace.StepOK P (profile P) s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P
        (σ.set d (MSB.keySwitch P (layout P) ℓ ca (keys.take ((layout P).sizes ℓ).length))))
      (.keySwitch d a) :=
  Validation.MSB.stepOK_toLSB P _ s ρ ρ' σ _ _ hstep
    (Validation.Instances.Lattigo.keySwitch_meets_msb P h hkn ℓ h1 hℓ s hs ρ ρ' σ d a x ca hstep hx hca hl hlen keys hkeys)

theorem rescale_meets_lsb (P : FullParams) (h : instanceOK? P = true) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ maxParts) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hparts : x.parts = k) (hlen : ca.length = k) :
    Trace.StepOK P (profile P) s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca))) (.modSwitch d a) :=
  Validation.MSB.stepOK_toLSB P _ s ρ ρ' σ _ _ hstep
    (Validation.Instances.Lattigo.rescale_meets_msb P h k hk1 hk s hs ρ ρ' σ d a x ca hstep hx hca hparts hlen)

example := (@params_keyNoise : type_of% @Challenge.Instances.Lattigo.params_keyNoise)
example := (@relin_meets_msb : type_of% @Challenge.Instances.Lattigo.relin_meets_msb)
example := (@keySwitch_meets_msb : type_of% @Challenge.Instances.Lattigo.keySwitch_meets_msb)
example := (@rescale_meets_msb : type_of% @Challenge.Instances.Lattigo.rescale_meets_msb)
example := (@relin_meets_lsb : type_of% @Challenge.Instances.Lattigo.relin_meets_lsb)
example := (@keySwitch_meets_lsb : type_of% @Challenge.Instances.Lattigo.keySwitch_meets_lsb)
example := (@rescale_meets_lsb : type_of% @Challenge.Instances.Lattigo.rescale_meets_lsb)

end Validation.Instances.Lattigo
