import Spec.IndCpaD
import Spec.IndCpaDLM

/-!
# Spec.IndCpaDSanity — vocabulary for the sanity statements about the games   (TRUSTED)

Small definitions used by `Challenge.IndCpaD.Sanity`, none of which is read by the games,
the reduction or any earlier statement:

* `CpaBounded A q`: the IND-CPA adversary `A` makes at most `q` left-or-right queries on every
  path (the counterpart of `Spec.IndCpaD.Bounded` for `CpaAdv`);
* `Adv.swap`, `CpaAdv.swap`: the adversary with the two messages of every encryption query
  exchanged (`(m₀, m₁)` becomes `(m₁, m₀)`), everything else unchanged;
* `Entry.swap`: a table entry with its two messages exchanged;
* `LAdv.swap`, `LEntry.swap`: the same for the game with evaluation on earlier results
  (`Spec.IndCpaDLM`).
-/

namespace Spec.IndCpaD

variable {S : HEScheme}

/-- The IND-CPA adversary makes at most `q` left-or-right queries on every path. -/
inductive CpaBounded : CpaAdv S Bool → Nat → Prop
  | ret (a q) : CpaBounded (.ret a) q
  | lr (m0 m1 k q) : (∀ c, CpaBounded (k c) q) → CpaBounded (.lr m0 m1 k) (q + 1)

/-- The IND-CPA-D adversary with the two messages of every encryption query exchanged. -/
def Adv.swap {α : Type} : Adv S α → Adv S α
  | .ret a => .ret a
  | .enc m0 m1 k => .enc m1 m0 fun c => (k c).swap
  | .eval C idx k => .eval C idx fun r => (k r).swap
  | .dec j k => .dec j fun r => (k r).swap

/-- The IND-CPA adversary with the two messages of every query exchanged. -/
def CpaAdv.swap {α : Type} : CpaAdv S α → CpaAdv S α
  | .ret a => .ret a
  | .lr m0 m1 k => .lr m1 m0 fun c => (k c).swap

/-- A table entry with its two messages exchanged. -/
def Entry.swap (e : Entry S) : Entry S := ⟨e.m1, e.m0, e.c, e.fresh⟩

end Spec.IndCpaD

namespace Spec.IndCpaDLM

variable {D : Spec.IndCpaDProfile.AbsScheme}

/-- The adversary with the two messages of every encryption query exchanged (names unchanged). -/
def LAdv.swap {α : Type} : LAdv D α → LAdv D α
  | .ret a => .ret a
  | .enc m0 m1 x k => .enc m1 m0 x fun c => (k c).swap
  | .eval C idx k => .eval C idx fun r => (k r).swap
  | .dec j k => .dec j fun r => (k r).swap

/-- A table entry with its two messages exchanged. -/
def LEntry.swap (e : LEntry D) : LEntry D := ⟨e.m1, e.m0, e.c, e.name, e.linked⟩

end Spec.IndCpaDLM
