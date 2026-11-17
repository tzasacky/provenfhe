import Challenge.Profile

/-!
# Challenge.Sanity.Edges — edge cases of the profile decisions   (compiled `#guard`s; no locked statement)

* **Appending dead code can turn acceptance into rejection** (both schemes). The analyses require
  every intermediate bound to stay below `Q/2` at its level, including the bounds of variables no
  output depends on. So acceptance is not stable under appending instructions whose results are
  never used. This is conservative (a rejection is never unsound) and intended; no statement is
  weakened by it.
* Benign (accepted, and the conclusion says what a reader expects): an output that is an input
  with an empty body (its bound is the input bound), a repeated output name (one entry per
  occurrence, equal bounds), `N = 1`, `t = 2`, an instruction that overwrites an input.
-/

namespace Challenge.Sanity
open Spec Spec.Source Challenge.Profile

/-- A one-input program at `tinyBGV`/`tinyBFV`, level 2. -/
def edgeIn : List Decl := [⟨"a", 2, 2, 1, 1⟩]

-- BGV: the copy is accepted; with two overflowing products appended (never read), rejected.
#guard (certifyProfile? FullParams.tinyBGV
  (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [], outputs := ["a"] } false).isSome
#guard (certifyProfile? FullParams.tinyBGV
  (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [.mul "c" "a" "a", .mul "c" "c" "c", .mul "c" "c" "c"],
    outputs := ["a"] } false).isNone
-- BFV: the same.
#guard (certifyBFVProfile? Challenge.BFV.tinyBFV
  (fun _ => BudgetBFV.certified Challenge.BFV.tinyBFV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [], outputs := ["a"] }).isSome
#guard (certifyBFVProfile? Challenge.BFV.tinyBFV
  (fun _ => BudgetBFV.certified Challenge.BFV.tinyBFV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [.mul "c" "a" "a", .mul "c" "c" "c"], outputs := ["a"] }).isNone
-- Benign cases (BGV): repeated output, N = 1, t = 2, an input overwritten.
#guard certifyProfile? FullParams.tinyBGV
  (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [.copy "c" "a"], outputs := ["c", "c"] } false ==
    some (64, [("c", 64), ("c", 64)])
#guard (certifyProfile? { FullParams.tinyBGV with src := { FullParams.tinyBGV.src with N := 1 } }
  (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [.mul "c" "a" "a"], outputs := ["c"] } false).isSome
#guard (certifyProfile? { FullParams.tinyBGV with src := { FullParams.tinyBGV.src with t := 2 } }
  (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [.mul "c" "a" "a"], outputs := ["c"] } false).isSome
#guard (certifyProfile? FullParams.tinyBGV
  (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
  { inputs := edgeIn, body := [.add "a" "a" "a", .add "a" "a" "a"], outputs := ["a"] }
  false) == some (256, [("a", 256)])

end Challenge.Sanity
