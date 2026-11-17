import Challenge.Instances.Lattigo
import Challenge.MSB

/-!
# Challenge.Instances.Lattigo.MSB — Lattigo's own MSB algorithms meet its profile   (LOCKED statements; proofs in `Validation/Instances/Lattigo/MSB.lean`)

`Challenge.Instances.Lattigo` proves that the profile `profile P` covers the LSB centred hybrid
family and the LSB centred t-corrected modulus switch, and argues that Lattigo's MSB algorithms
are within it under the t-reading. The statements here replace that argument by theorems about
the MSB algorithms of `Spec.MSB` (transcriptions of Lattigo's `GadgetProduct`/`ModDown`,
`Relinearize`, `ApplyEvaluationKey` and `Rescale`; `Spec.MSB` cites the source lines), on
Lattigo's digit layout `layout P`, with MSB keys of error at most `errBound = 19` generated once
at the top level (Lattigo generates one key set and reads its first digits at every level):

* `relin_meets_msb`, `keySwitch_meets_msb`: MSB relinearization and MSB key switching meet the
  MSB contracts (`Spec.MSB.StepOK`) within `profile P` at every level, wherever `instanceOK?`
  holds and the key noise is at least `t·19` (as `params` sets it: `params_keyNoise`);
* `rescale_meets_msb`: MSB rescaling of `1, …, maxParts` components meets the MSB contract within
  `profile P`;
* `relin_meets_lsb`, `keySwitch_meets_lsb`, `rescale_meets_lsb`: their t-readings meet the LSB
  contracts (`Spec.Trace.StepOK`) within `profile P` (`Challenge.MSB.stepOK_toLSB`).

With `Challenge.MSB.certifyProfile?_sound_msb` and the acceptance facts of
`Challenge.Instances.Lattigo` (`small_accepts`, `exampleLogN14_accepts`), every MSB run within the
profile on an accepted program ends in outputs that MSB-decrypt to what the program computes,
from inputs with stored-representative bound `Bin = inputNoise` (`Spec.MSB.MSBEncryptsRep`) below
half the modulus of their level. A fresh Lattigo encryption stores `p ∈ [0, t)` and has an MSB
error within `19` (secret key) or `pkErrMSB` (public key), so it has that bound
(`skFresh`, `pkFresh`, `Defs` docstring); those error bounds of the encryption routines are
still the argument of the `Defs` docstring, not a theorem.

**What remains executed-only** (`harness/lattigo-pin`): that Lattigo's Go code computes these
functions (the transcription, including the exactness of its floating-point basis extension
`ModUpExact`), and the fused rotation (`core/rlwe/evaluator_automorphism.go:13-60`), which is
not the `automorph; keySwitch` decomposition stated here.
-/

namespace Challenge.Instances.Lattigo
open Spec NPoly Scheme Source Correct Spec.MSB

/-- `params` sets the key noise to `t·19`. -/
theorem params_keyNoise (N : ℕ) (qs ps : List ℕ) (t : ℕ) :
    (params N qs ps t).src.t * errBound ≤ (params N qs ps t).keyNoise := sorry

/-- **Lattigo's MSB relinearization meets the MSB `relin` contract within its profile**, at every
level, with one top-level MSB key set (error at most `19`), wherever `instanceOK?` holds. -/
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
      (.relin d a) := sorry

/-- **Lattigo's MSB key switching meets the MSB `keySwitch` contract within its profile**, at
every level, with one top-level MSB key set for the target `σ_g(s)`, wherever `instanceOK?`
holds. -/
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
      (.keySwitch d a) := sorry

/-- **Lattigo's MSB `Rescale` of `k ≤ maxParts` components meets the MSB `modSwitch` contract
within its profile**, wherever `instanceOK?` holds. -/
theorem rescale_meets_msb (P : FullParams) (h : instanceOK? P = true) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ maxParts) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hparts : x.parts = k) (hlen : ca.length = k) :
    MSB.StepOK P (profile P) s ρ ρ' σ (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca))
      (.modSwitch d a) := sorry

/-- The t-reading of `relin_meets_msb`: the LSB `relin` contract within the profile. -/
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
      (.relin d a) := sorry

/-- The t-reading of `keySwitch_meets_msb`: the LSB `keySwitch` contract within the profile. -/
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
      (.keySwitch d a) := sorry

/-- The t-reading of `rescale_meets_msb`: **Lattigo's `Rescale`, read through `t`, meets the LSB
`modSwitch` contract within the profile** (the claim the instance's docstring argued). -/
theorem rescale_meets_lsb (P : FullParams) (h : instanceOK? P = true) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ maxParts) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hparts : x.parts = k) (hlen : ca.length = k) :
    Trace.StepOK P (profile P) s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca))) (.modSwitch d a) := sorry

end Challenge.Instances.Lattigo
