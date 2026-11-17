import FHE.Pin.Sound
import Spec.Budget

/-!
# FHE.Pin.BFV.Keys — the deciding mirror of `Spec.Budget.GadgetKeysOK` for BFV, with soundness
(UNTRUSTED glue; the theorem is kernel-checked)

`Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys` is `Spec.Scheme.KeyValid P.src.kind …` of every
digit. For `P.src.kind = .bfv` that is the norm bound alone (the key error need not be a multiple
of `t`), so the BGV decision `FHE.Pin.gadgetKeysCheck` (which also tests divisibility by `t`) is
not the BFV predicate. `gadgetKeysCheck` below tests the norm of the same forced error
(`FHE.Pin.keyErrA`, `keyErrA_spec`); `gadgetKeysCheck_sound`: a `true` verdict is a proof of
`GadgetKeysOK` for the first `(lay.sizes ℓ).length` stored digits.
-/

namespace FHE.Pin.BFV
open Spec Spec.NPoly Spec.Scheme Spec.Source FHE.Pin

/-- The forced error of digit `j` at level `ℓ` (the `e` of `Spec.Scheme.KeyValid` for
`Spec.Budget.gadgetReq P lay ℓ tgt j`), from the forced `b + a·s` and the forced target. -/
def gadgetErrA (P : FullParams) (lay : Budget.KSLayout) (ℓ K j : ℕ) (lhs tg : Array ℤ) : Array ℤ :=
  let M := P.src.modulus ℓ * Budget.specialProd P
  keyErrA P.src.N K M
    ((Budget.gadgetFactor (Budget.specialProd P) (Budget.digitModuli P lay ℓ) j : ℕ) : ZMod M) lhs tg

/-- **The decision of the BFV `d.key`** at level `ℓ`, from the forced `b + a·s` of each stored
digit (`lhs`, `FHE.Pin.keyLhsZ`) and the forced target (`tg`, `FHE.Pin.targetZ`): the key has at
least as many digits as the layout, and the error of each of the first `(lay.sizes ℓ).length` has
norm at most `P.keyNoise`. -/
def gadgetKeysCheck (P : FullParams) (lay : Budget.KSLayout) (ℓ K : ℕ)
    (lhs : Array (Array ℤ)) (tg : Array ℤ) : Bool :=
  decide ((lay.sizes ℓ).length ≤ lhs.size) &&
    (List.range (lay.sizes ℓ).length).all fun j =>
      decide (normA P.src.N (gadgetErrA P lay ℓ K j lhs[j]! tg) ≤ P.keyNoise)

/-- **Soundness of the BFV `d.key` decision**: `Spec.Budget.GadgetKeysOK` of the first
`(lay.sizes ℓ).length` stored digits. -/
theorem gadgetKeysCheck_sound (P : FullParams) (hk : P.src.kind = .bfv) (lay : Budget.KSLayout)
    (ℓ K : ℕ) (tgt : KeyTarget) (s : Array ℤ) (keys : Array (Array ℤ × Array ℤ))
    (h : gadgetKeysCheck P lay ℓ K
      (keys.map fun k => keyLhsZ P.src.N K .none k.1 k.2 s) (targetZ P.src.N K .none s tgt) = true) :
    Budget.GadgetKeysOK P lay ℓ tgt (ofArr s)
      ((keys.toList.take (lay.sizes ℓ).length).map fun k => (ofArr k.1, ofArr k.2)) := by
  simp only [gadgetKeysCheck, Bool.and_eq_true, decide_eq_true_eq, Array.size_map, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  have hl : ((keys.toList.take (lay.sizes ℓ).length).map
      fun k => ((ofArr k.1 : IntPoly P.src.N), (ofArr k.2 : IntPoly P.src.N))).length =
      (lay.sizes ℓ).length := by
    simp only [List.length_map, List.length_take, Array.length_toList]; omega
  refine ⟨hl, fun j hj => ?_⟩
  have hjn : j < (lay.sizes ℓ).length := hl ▸ hj
  have hjk : j < keys.size := lt_of_lt_of_le hjn hlen
  have hv := hall j hjn
  rw [getElem!_pos _ _ (by simpa using hjk), Array.getElem_map] at hv
  have hget : ((keys.toList.take (lay.sizes ℓ).length).map
      fun k => ((ofArr k.1 : IntPoly P.src.N), (ofArr k.2 : IntPoly P.src.N)))[j] =
      (ofArr keys[j].1, ofArr keys[j].2) := by
    simp only [List.getElem_map, List.getElem_take, Array.getElem_toList]
  rw [hget]
  simp only [normA, gadgetErrA, keyErrA_spec] at hv
  exact ⟨hv, fun hb => by rw [hk] at hb; cases hb⟩

end FHE.Pin.BFV
