import FHE.Pin.AlgoStage

/-!
# FHE.Pin.AlgoMutants — representative-convention mutants of the algorithm-level comparison
(UNTRUSTED, test-only)

`FHE.Pin.Algo` compares the proved reference algorithms with OpenFHE's outputs, coefficient by
coefficient. To show that the comparison has teeth, each mutant below perturbs **one**
representative convention; the comparison must then fail (`harness/openfhe-pin/algo/mutation.sh`).
Every mutant is itself assembled from proved stage functions of `FHE/RNS` and `FHE/KeySwitch`
(they are legitimate algorithms meeting the same specification — just not the one OpenFHE runs).
Nothing here is used when `AMut.none` is selected: `mutStages_none` is `rfl`.
-/

namespace FHE.Pin.Algo
open Spec Spec.NPoly FHE.RNS FHE.RNS.Basis FHE.KeySwitch FHE.Pin

/-- Which mutant is active. -/
inductive AMut
  | none
  /-- centred instead of canonical fast base conversion in ModUp (ModDown as OpenFHE) -/
  | upCentred
  /-- centred BGV ModDown `X + t·FBC_c([−X·t⁻¹]_P)` (ModUp as OpenFHE) -/
  | downCentred
  /-- The adding sign `X + t·FBC([−X·t⁻¹]_P)` in ModDown (ModUp as OpenFHE): `keySwitchBGVAddDown` -/
  | downAdd
  /-- ModDown without the `t`-correction: `(X − FBC([X]_P))/P` -/
  | downNoT
  /-- the fully centred variant `keySwitchBGV` -/
  | allCentred
  /-- one limb moved across a digit boundary -/
  | digitBoundary
  /-- rotation: automorphism of both components first, then the key switch (same key) -/
  | autoFirst
  /-- rotation in OpenFHE v1.3.1's order: ModDown, add `c₀`, then the automorphism
  (`rotateOpenFHE`); v1.6.1 applies the automorphism before ModDown (`rotateOpenFHE161`) -/
  | autoLast
  /-- `ModReduce` with the canonical `δ = t·[−c·t⁻¹]_q ∈ [0, t·q)` (`bgvModSwitchCanon`) -/
  | modReduceCanon
  deriving DecidableEq, Repr, Inhabited

def AMut.all : List (String × AMut) :=
  [("modup-centred", .upCentred), ("moddown-centred", .downCentred),
   ("moddown-add", .downAdd), ("moddown-no-t", .downNoT), ("ks-all-centred", .allCentred),
   ("digit-boundary", .digitBoundary), ("automorph-first", .autoFirst), ("automorph-last", .autoLast),
   ("modreduce-canonical", .modReduceCanon)]

def AMut.ofString? (s : String) : Option AMut :=
  if s == "none" then some .none else (AMut.all.find? (·.1 == s)).map (·.2)

variable {N ℓ k : ℕ} (Dg : Digits ℓ) (C : Basis ℓ) (Bp : Basis k)

/-- The key-switching stages selected by a mutant. -/
def mutStages (m : AMut) (t : ℕ) : Stages Dg C Bp N :=
  match m with
  | .upCentred => ⟨modUpQ Dg C, modUpP Dg C Bp, bgvModDownPoly C Bp t⟩
  | .downCentred => ⟨modUpQCanon Dg C, modUpPCanon Dg C Bp, C.bgvModDownCPoly Bp t⟩
  | .downAdd => addDownStages Dg C Bp t
  | .downNoT => ⟨modUpQCanon Dg C, modUpPCanon Dg C Bp, C.modDownPoly Bp⟩
  | .allCentred => centredStages Dg C Bp t
  | _ => openfheStages Dg C Bp t

theorem mutStages_none (t : ℕ) :
    (mutStages Dg C Bp .none t : Stages Dg C Bp N) = openfheStages Dg C Bp t := rfl

/-- The digit sizes with one limb moved across the first boundary (`none`: no other partition
with at most `maxDigits` digits exists). -/
def moveBoundary (maxDigits : ℕ) : List ℕ → Option (List ℕ)
  | a :: b :: rest => if a ≥ 2 then some ((a - 1) :: (b + 1) :: rest) else some ((a + b) :: rest)
  | [a] => if a ≥ 2 ∧ maxDigits ≥ 2 then some [a - 1, 1] else none
  | [] => none

end FHE.Pin.Algo
