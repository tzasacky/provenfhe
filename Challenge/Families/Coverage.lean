import Challenge.Profile
import Challenge.Instances.Lattigo

/-!
# Challenge.Families.Coverage — SEAL's and Lattigo's key-switching layouts and multiplication families as coverage instances   (LOCKED statements; proofs in `Validation/Families/Coverage.lean`)

**Key switching is already general in the layout.** `Challenge.BFV.relin_realizable`,
`keySwitch_realizable` (and the BGV `Challenge.Budget` versions) quantify over every
`Spec.Budget.KSLayout` (any digit sizes at every level, canonical or centred digits) and over any
list of special primes `P.store.special` (any number, any sizes, under `Spec.Budget.SpecialOK`).
They are EXISTENTIAL: some hybrid key switch on that layout (the realizer is the untrusted
library's, `FHE/KeySwitch`) meets the contract within `ksBoundAt`; they do not say that a given
library's key switch does. The statement about a library's own code is
`Challenge.RealizeBFV.relinBFV_stepOK` etc. for OpenFHE's transcription only. So for another
library the layout is a parameter choice, and that its key switch stays within `ksBoundAt` is
ARGUED from its source:

* **SEAL** v4.7.2 (`native/src/seal/evaluator.cpp`): one digit per ciphertext prime, the digit
  being the residue in `[0, qⱼ)` reduced modulo each key prime (`kswitch_prepare_digits`,
  `:2907-2925`), one special prime (the last key modulus, `switch_key`, `:3063`), and a ModDown
  that rounds (`kswitch_mod_down`, "Add (qk - 1) / 2 … to change from flooring to rounding",
  `:2787-2860`, the rounding at `:2857`): the layout `uniformLayout 1` with canonical digits
  (`sealLayout`), with
  `sealBFV.store.special` the special prime of `BFVDefault(8192)`.
* **Lattigo** v6.2.0: digits of `#P` consecutive limbs, centred (`ring/basis_extension.go:381-470`,
  `DecomposeAndSplit`; `core/rlwe/params.go:543-550`): `Challenge.Instances.Lattigo.layout`
  (`uniformLayout #P`, centred). Its base-2 decomposition (`BaseTwoDecomposition ≠ 0`) is not a
  `KSLayout` and is not covered.

**The instances.** `coversBFV? P lay U r body E` (`Challenge.Profile.Defs`) decides that the
per-instruction budget `E` covers the families `(lay, U, r)`; the corollaries
`Challenge.Profile.coversBFV?_mul`, `_square`, `_relin`, `_keySwitch`, `_modSwitch` then give the
contracts for every algorithm of those families. Checked here (kernel):

* `sealBFV_covers`: `sealBFV` with `sealLayout` and the multiplication family `(U, r) = (1, 8)`
  (BEHZ at `k ≤ 4`: rounding slack `2k ≤ 8`; its lifts are within `Q/2 + (k−1)·Q/m̃ < Q`, so
  they are `[c]_Q + Q·u` with `‖u‖∞ ≤ 1`: that step is proved for `sealBFV` on `sealProg` by
  `Challenge.Families.stepOK_mul_behz_sealBFV_covered`; the size form is
  proved, `Challenge.Families.stepOK_mul_behz_sealRule`), on `Challenge.BFVMul.sealProg`;
* `lattigoBFV_covers`: Lattigo's example set as a BFV parameter set (`lattigoBFV`), its layout,
  and the family `(U, r) = (0, t)` of exact rounding before scaling
  (`Challenge.Families.stepOK_mul_quantize`), on seven relinearized squarings.

The guards record the depths the profile decision accepts: SEAL with the BEHZ family three
squarings (as with the textbook budget); Lattigo seven with `(0, t)` (as with the textbook
`(0, 1)`), six with the whole-multiple float form `(1, 3t)`, seven with the float error charged
by size (`e = 1 + ⌈2δQ⌉`, `ρ = 2t`; not a `coversBFV?` family, checked with a direct profile).
`lattigoBFV` keeps the noise fields of the BGV instance (`inputNoise`, `keyNoise`, derived there
for Lattigo's encryption and keys in the t-reading); they are not re-derived for the BFV reading,
so the depths are indicative, not a certificate for Lattigo's BFV mode. The "rounding slack `t`
costs < 1 ppm" statements are measured on `sealProg` and these chains only.
-/

namespace Challenge.Families
open Spec Spec.Source Challenge.BFV Challenge.BFVMul Challenge.Profile

/-- SEAL's key-switching layout: one canonical digit per ciphertext prime (module docstring). -/
def sealLayout : Budget.KSLayout := Budget.uniformLayout 1 true

/-- Lattigo's `ExampleParameters128BitLogN14LogQP438` read as a BFV parameter set (Lattigo's
scale-invariant mode on the same parameters; `schemes/bfv/README.md`). -/
def lattigoBFV : FullParams :=
  let P := Challenge.Instances.Lattigo.exampleLogN14
  { P with src := { P.src with kind := .bfv } }

/-- `n` relinearized squarings of one input at level `L`. -/
def squareChain (L n : ℕ) : Program where
  inputs := [⟨"a", 2, L, 1, 1⟩]
  body := (List.replicate n [Instr.square "a" "a", .relin "a" "a"]).flatten
  outputs := ["a"]

/-- **SEAL's layout and BEHZ family are covered at `sealBFV`** by the certified budget of
`(sealLayout, U = 1, r = 8)`, on `sealProg`. -/
theorem sealBFV_covers :
    coversBFV? sealBFV sealLayout 1 8 sealProg.body
      (fun _ => BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0) = true := sorry

/-- **Lattigo's layout and quantization family are covered at its example set** by the certified
budget of `(layout, U = 0, r = t)`, on seven relinearized squarings at the top level. -/
theorem lattigoBFV_covers :
    coversBFV? lattigoBFV (Challenge.Instances.Lattigo.layout lattigoBFV) 0 65537
      (squareChain 12 7).body
      (fun _ => BudgetBFV.certifiedApprox lattigoBFV
        (Challenge.Instances.Lattigo.layout lattigoBFV) 0 65537 0) = true := sorry

#guard schemeParamsOK? lattigoBFV && Budget.specialOK? lattigoBFV
#guard (Challenge.Instances.Lattigo.layout lattigoBFV).sizes 12 == [2, 2, 2, 2, 2, 2]
-- Accepted depths (bit lengths of the whole-program bound; `none`: rejected).
#guard (List.range 5).map (fun n =>
    (certifyBFVProfile? sealBFV (fun _ => BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0)
      (squareChain 4 n)).map (Nat.log2 ·.1))
  == [some 19, some 62, some 106, some 149, none]
#guard (List.range 9).map (fun n =>
    (certifyBFVProfile? lattigoBFV (fun _ => BudgetBFV.certifiedApprox lattigoBFV
      (Challenge.Instances.Lattigo.layout lattigoBFV) 0 65537 0) (squareChain 12 n)).map
        (Nat.log2 ·.1))
  == [some 29, some 73, some 117, some 161, some 205, some 249, some 293, some 337, none]
#guard (List.range 9).map (fun n =>
    (certifyBFVProfile? lattigoBFV (fun _ => BudgetBFV.certifiedApprox lattigoBFV
      (Challenge.Instances.Lattigo.layout lattigoBFV) 1 (3 * 65537) 0) (squareChain 12 n)).map
        (Nat.log2 ·.1))
  == [some 29, some 74, some 120, some 165, some 211, some 256, some 302, none, none]
#guard (List.range 9).map (fun n =>
    (certifyBFVProfile? lattigoBFV (fun _ => BudgetBFV.certifiedApprox lattigoBFV
      (Challenge.Instances.Lattigo.layout lattigoBFV) 0 1 0) (squareChain 12 n)).map
        (Nat.log2 ·.1))
  == [some 29, some 73, some 117, some 161, some 205, some 249, some 293, some 337, none]

-- The float error by size instead (`Challenge.Families.stepOK_mul_quantize_lifted`): lift excess
-- `e = 1 + ⌈2δQ⌉` with `δ = doubleSw 12 / 2⁵³` (OpenFHE's bound for its own summation order,
-- ASSUMED here as the tolerance of Lattigo's `Σ float64(y)/float64(q)`; not proved for Lattigo's
-- order) and `ρ = 2t`: the lift budget is the textbook one and no level is lost.
#guard
  let e := 1 + BudgetBFV.ceilDiv (2 * lattigoBFV.src.modulus 12 * BudgetBFV.doubleSw 12)
    BudgetBFV.floatDen
  let E := BudgetBFV.budgetOf
    (BudgetBFV.ksBudget lattigoBFV (Challenge.Instances.Lattigo.layout lattigoBFV))
    (BudgetBFV.msBudget lattigoBFV) (BudgetBFV.mulLiftNormAt lattigoBFV 12 e)
    (BudgetBFV.mulRoundApprox lattigoBFV (2 * 65537)) 0
  BudgetBFV.mulLiftNormAt lattigoBFV 12 e == BudgetBFV.mulLiftNormAt lattigoBFV 12 0 &&
  (List.range 9).map (fun n =>
    (certifyBFVProfile? lattigoBFV (fun _ => E) (squareChain 12 n)).map (Nat.log2 ·.1))
    == [some 29, some 73, some 117, some 161, some 205, some 249, some 293, some 337, none]

-- The definitions themselves: SEAL's layout is canonical with one-limb digits, Lattigo's
-- centred with two-limb digits; `lattigoBFV` differs from the BGV instance in the kind only;
-- the chain has `2n` instructions; a budget below the family's is not covered.
#guard sealLayout.canonical && sealLayout.sizes 4 == [1, 1, 1, 1]
#guard !(Challenge.Instances.Lattigo.layout lattigoBFV).canonical
#guard lattigoBFV.src.kind == .bfv &&
  lattigoBFV.src.qs == Challenge.Instances.Lattigo.exampleLogN14.src.qs
#guard (squareChain 12 7).body.length == 14
#guard !coversBFV? lattigoBFV (Challenge.Instances.Lattigo.layout lattigoBFV) 0 65537
  (squareChain 12 7).body
  (fun _ => BudgetBFV.certifiedApprox lattigoBFV
    (Challenge.Instances.Lattigo.layout lattigoBFV) 0 1 0)

end Challenge.Families
