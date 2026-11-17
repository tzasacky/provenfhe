import FHE.Realize.Harness

/-!
# FHE.Pin.AlgoLocked — the staged key switches the harness runs are the LOCKED transcriptions
(UNTRUSTED glue; the theorems are kernel-checked)

`algo.relin` / `algo.rotate` compare OpenFHE v1.6.1's relinearization and `EvalAutomorphism` with
the staged executions `addKS` / `rotStaged161` (`FHE/Pin/AlgoOpenFHE.lean`). The two theorems here
say that, on the bases the run-time code builds from the scheme parameters (`Basis.take` of the
chain, `Basis.ofList` of the special primes, `digitsOfSizes` of the layout's digit sizes, with
**any** proofs of their side conditions), the staged executions return, limb for limb, the RNS form
of the **locked** definitions `Challenge.Realize.relinOpenFHE` and
`Challenge.Realize.rotateOpenFHE161` (`Challenge/Realize/OpenFHE.lean`) applied to the integer
operands and the keys (read modulo `Q_ℓ·P` through `keys.getD j (0, 0)`):

* `addKS_locked`: `addKS (openfheStages …) K (toRNS c₀) (toRNS c₁) (toRNS c₂) kb ka` =
  `toRNS` of the two components of `Challenge.Realize.relinOpenFHE P lay ℓ [c₀, c₁, c₂] keys`;
* `rotStaged161_locked`: the same for `rotStaged161` and `Challenge.Realize.rotateOpenFHE161`.

Proof: `addKS_openfhe` / `rotStaged161_openfhe` (staged = `FHE.Pin.Algo` definition) composed with
`FHE.Realize.relinOpenFHE_toRNS` / `rotateOpenFHE161_toRNS` (`FHE.Pin.Algo` definition = locked
transcription; through `FHE.Realize.ksOpenFHE_toRNS`, whose locked side `Challenge.Realize.ksOpenFHE`
is also the core of `Challenge.Realize.keySwitchOpenFHE`). The bases built at run time are those of
`FHE.Realize` up to proof irrelevance (`schemeLevelBasis` is `Basis.take P.src.qs …`). Hypotheses
`SchemeParamsOK P`, `SpecialOK P` and `lay.okAt ℓ` are decided at run time (`schemeParamsOK?`,
`specialOK?`, `okAt`) before a line claims this theorem. No `Challenge` theorem is used (those are
`sorry` here); axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace FHE.Pin.Algo
open Spec Spec.NPoly FHE.RNS FHE.KeySwitch

section
variable (P : FullParams) (hP : SchemeParamsOK P) (hS : Spec.Budget.SpecialOK P) [NeZero P.src.N]
  (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
include hP hS hlay

/-- **The staged relinearization is the locked `Challenge.Realize.relinOpenFHE`**, limb for limb. -/
theorem addKS_locked (K : ℕ)
    (hpos : ∀ q ∈ P.src.qs, 0 < q) (hcop : P.src.qs.Pairwise Nat.Coprime)
    (hppos : ∀ q ∈ P.store.special.map (·.q), 0 < q)
    (hpcop : (P.store.special.map (·.q)).Pairwise Nat.Coprime)
    (hs : (lay.sizes ℓ).sum = ℓ)
    (c0 c1 c2 : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    let C := Basis.take P.src.qs ℓ hℓ hpos hcop
    let Bp := Basis.ofList (P.store.special.map (·.q)) hppos hpcop
    let Dg := digitsOfSizes (lay.sizes ℓ) ℓ hs
    let r := addKS (openfheStages Dg C Bp P.src.t) K (C.toRNS c0) (C.toRNS c1) (C.toRNS c2)
      (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2)
    let L := Challenge.Realize.relinOpenFHE P lay ℓ [c0, c1, c2] keys
    (ofFam C.q r.1, ofFam C.q r.2) = (C.toRNS (L.getD 0 0), C.toRNS (L.getD 1 0)) := by
  intro C Bp Dg r L
  have h := FHE.Realize.relinOpenFHE_toRNS P hP hS lay ℓ hℓ hlay c0 c1 c2 keys
  have e := addKS_openfhe (Dg := Dg) (C := C) (Bp := Bp) P.src.t K (C.toRNS c0) (C.toRNS c1)
    (C.toRNS c2) (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2)
  rw [e]
  exact h

/-- **The staged v1.6.1 rotation is the locked `Challenge.Realize.rotateOpenFHE161`**, limb for
limb. -/
theorem rotStaged161_locked (K g : ℕ)
    (hpos : ∀ q ∈ P.src.qs, 0 < q) (hcop : P.src.qs.Pairwise Nat.Coprime)
    (hppos : ∀ q ∈ P.store.special.map (·.q), 0 < q)
    (hpcop : (P.store.special.map (·.q)).Pairwise Nat.Coprime)
    (hs : (lay.sizes ℓ).sum = ℓ)
    (c0 c1 : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    let C := Basis.take P.src.qs ℓ hℓ hpos hcop
    let Bp := Basis.ofList (P.store.special.map (·.q)) hppos hpcop
    let Dg := digitsOfSizes (lay.sizes ℓ) ℓ hs
    let r := rotStaged161 (openfheStages Dg C Bp P.src.t) K g (C.toRNS c0) (C.toRNS c1)
      (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2)
    let L := Challenge.Realize.rotateOpenFHE161 P lay ℓ g [c0, c1] keys
    (ofFam C.q r.1, ofFam C.q r.2) = (C.toRNS (L.getD 0 0), C.toRNS (L.getD 1 0)) := by
  intro C Bp Dg r L
  have h := FHE.Realize.rotateOpenFHE161_toRNS P hP hS lay ℓ hℓ hlay g c0 c1 keys
  have e := rotStaged161_openfhe (Dg := Dg) (C := C) (Bp := Bp) P.src.t K g (C.toRNS c0)
    (C.toRNS c1) (fun j => ofInt _ (keys.getD j (0, 0)).1) (fun j => ofInt _ (keys.getD j (0, 0)).2)
  rw [e]
  exact h

end

end FHE.Pin.Algo
