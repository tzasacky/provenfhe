import Challenge.IndCpaD.LMBFV

/-!
# Challenge.IndCpaD.LMBounds — declared input bounds are kept when a query is inlined   (LOCKED statements; proofs in `Validation/IndCpaD/LMBounds.lean`)

The global program of `Spec.IndCpaDLM` keeps the bounds a query declares for its plaintext
constants (`Global.bounds`). Two queries on one fresh entry, with nothing else in the history,
whose answer would differ from the fresh-only game's if those bounds were dropped, get the same
answer in both games, kernel-checked:

* `lm_bounds_kernel` (BGV at `bgvKSSeal`, class `admSeal`): `gapQuery` (three plaintext products
  by a constant declared at `t − 1`) is in the class as a fresh-only circuit and is accepted by
  the oracle;
* `lm_bounds_bfv_kernel` (BFV at `sealBFV`, class `admBFVSeal`): `gapQueryBFV` (two plaintext
  products by a constant declared at `2⁶⁰`) is outside the class and is refused by the oracle.

The general statement is `Challenge.IndCpaD.LMAgree`.
-/

namespace Challenge.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile

/-- A plaintext constant at level 4. -/
def gapPtDecl (x : Var) : Decl := { name := x, parts := 1, level := 4, scale := 0, key := 1 }

/-- Three plaintext products of the fresh entry `a` by the constant `p`, which is declared with
the bound `65536`, at `bgvKSSeal`. -/
def gapQuery : QCirc bgvKSSealData :=
  ({ inputs := [sealDecl "a", gapPtDecl "p"],
     body := [.mulPlain "c1" "a" "p", .mulPlain "c2" "c1" "p", .mulPlain "c3" "c2" "p"],
     outputs := ["c3"], bounds := [("p", 65536)] }, ["a"], fun _ => 0)

/-- Two plaintext products of the fresh entry `a` by the constant `p`, declared with the bound
`2⁶⁰`, at `sealBFV`. -/
def gapQueryBFV : QCirc bfvSealData :=
  ({ inputs := [bfvSealDecl "a", gapPtDecl "p"],
     body := [.mulPlain "c1" "a" "p", .mulPlain "c2" "c1" "p"],
     outputs := ["c2"], bounds := [("p", 2 ^ 60)] }, ["a"], fun _ => 0)

/-- The global program after one encryption named `a`, at `bgvKSSeal`. -/
def gapG : Global bgvKSSealData := (Global.empty bgvKSSealData).link "a"

/-- The global program after one encryption named `a`, at `sealBFV`. -/
def gapGBFV : Global bfvSealData := (Global.empty bfvSealData).link "a"

/-- **BGV: the same answer in both games**, kernel-checked. -/
theorem lm_bounds_kernel :
    admSeal (mkSeal gapQuery.1 gapQuery.2.1 gapQuery.2.2) = true ∧
      admLM mkSeal admSeal gapG gapQuery [("a", true)] = true := sorry

/-- **BFV: the same answer in both games**, kernel-checked. -/
theorem lm_bounds_bfv_kernel :
    admBFVSeal (mkBFVSeal gapQueryBFV.1 gapQueryBFV.2.1 gapQueryBFV.2.2) = false ∧
      admLM mkBFVSeal admBFVSeal gapGBFV gapQueryBFV [("a", true)] = false := sorry

end Challenge.IndCpaDLM
