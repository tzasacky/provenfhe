import Challenge.Profile
import Challenge.Families.BEHZ
import Challenge.Families.Coverage

/-!
# Challenge.Families.BEHZCover — the BEHZ family inside the profile coverage check   (LOCKED statements; proofs in `Validation/Families/BEHZCover.lean`)

`Challenge.BFVMul.stepOK_mul_behz` states BEHZ in the LIFTED form: the algorithm multiplies
representatives `A` of the operands modulo `Q` of size `2·‖Aᵢ‖∞ ≤ Q + e`, with
`e = ⌈2(k−1)·Q/m̃⌉` (`Spec.BudgetBFV.behzSlack`). The profile coverage check
`Challenge.Profile.coversBFV? P lay U r body E` names multiplication families in the
WHOLE-MULTIPLE form `[c]_Q + Q·u`, `‖u‖∞ ≤ U` (`Challenge.BFVMul.approxLift`). This file joins
the two.

* `approxLift_of_lifted` (the bridge): a representative modulo `Q` with `2·‖A‖∞ ≤ Q + e` and
  `e < 2Q` is `[c]_Q + Q·u` with `‖u‖∞ ≤ 1`. (`|A − [c]_Q| ≤ (Q + e)/2 + Q/2 < 2Q` and
  `Q ∣ A − [c]_Q`.) The bound `e < 2Q` is sharp: at `e = 2Q`, `A = 3Q/2` against `[c]_Q = −Q/2`
  needs `u = 2`. (BEHZ needs only `e ≤ Q`, below; the bridge is stated at the sharp bound.)
* `behzSlack_e_le`: under `behzAuxOK?` (which contains `2(k−1) ≤ m̃`) the lift excess of BEHZ is
  at most `Q`, so the bridge always applies: BEHZ is in the family `U = 1` at EVERY parameter set
  accepted by the side condition, with no further hypothesis.
* `stepOK_mul_behz_covered`, `stepOK_square_behz_covered`: hence every `mul` / `square` of a body
  covered by `coversBFV? P lay 1 r body E`, run by `behzMul` with any auxiliary base accepted by
  `behzAuxOK?`, meets its contract within `E k`, provided `2k ≤ r` (`k` the level of the
  operand: BEHZ's rounding slack).
* `stepOK_mul_behz_sealBFV_covered`: the closed instance. At `Challenge.BFV.sealBFV` with SEAL's
  own bases (`Challenge.Families.sealAuxB`, `sealMsk`, `m̃ = 2³²`), every `mul` of
  `Challenge.BFV.sealProg` computed by BEHZ meets its contract within the profile
  `BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0`, the one `Challenge.Families.sealBFV_covers`
  decides is covered (kernel). The budget coincides with that of `sealBFV_covers`: what is new is
  that the step its docstring marks "argued here, not proved" (BEHZ's lifts are `[c]_Q + Q·u` with
  `‖u‖∞ ≤ 1`) is now proved, so the coverage instance is about SEAL's BEHZ multiplication as read
  from its source (`Challenge.Families.BEHZ`, module docstring), not only about the family.

**The price of the whole-multiple form.** The family `(U, r) = (1, 8)` charges a lift budget of
`mulLiftApprox P 1 = 4097 + 8193` at `sealBFV`, while the size form charges
`mulLiftNormAt P 4 e = 4097` for BEHZ's real `e ≈ Q·2⁻²⁹` (`#guard`s below). The coverage check
is conservative by the `U·(1 + N·B_s)` term (and the rounding slack `r = 8` is charged at every
level): `sealProg` is still accepted at the covered profile, with a whole-program bound of
`2¹³³` against `2¹³⁰` at the size-form budget (`#guard`s below).
-/

namespace Challenge.Families
open Spec NPoly Scheme Source Challenge.BFV Challenge.BFVMul Challenge.Profile

/-- **The bridge: a representative slightly outside the centred range is a whole-multiple lift
with `U = 1`.** If each `Aᵢ` is congruent to `cᵢ` modulo `Q` and `2·‖Aᵢ‖∞ ≤ Q + e` with
`e < 2Q`, then `A = [c]_Q + Q·u` for some `u` with `‖uᵢ‖∞ ≤ 1`, one per component. -/
theorem approxLift_of_lifted {N : ℕ} (Q e : ℕ) (hQ : 0 < Q) (he : e < 2 * Q)
    (c A : List (IntPoly N)) (hA : A.map (ofInt Q) = c.map (ofInt Q))
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ Q + e) :
    ∃ u : List (IntPoly N), u.length = c.length ∧ (∀ v ∈ u, normInf v ≤ 1) ∧
      approxLift Q c u = A := sorry

/-- **BEHZ's lift excess is at most `Q`** at every auxiliary base accepted by `behzAuxOK?`
(which requires `2(k−1) ≤ m̃`, `0 < m̃`). -/
theorem behzSlack_e_le (t N : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true) :
    (BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).e ≤ qs.prod := sorry

/-- **BEHZ multiplication is in the coverage family `U = 1`.** For every body covered by
`coversBFV? P lay 1 r body E`, every `mul` instruction `k` of it computed by `behzMul` with an
auxiliary base accepted by `behzAuxOK?` at the operand's level `ℓ`, with `2ℓ ≤ r`, meets the
`mul` contract within `E k`, under every secret within the bound. -/
theorem stepOK_mul_behz_covered (P : FullParams) (lay : Budget.KSLayout) (r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay 1 r body E = true)
    (k : ℕ) (d a b : Var) (hk : body[k]? = some (.mul d a b))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (hr : 2 * x.level ≤ r)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca cb)) (.mul d a b) := sorry

/-- **BEHZ squaring is in the coverage family `U = 1`**: as `stepOK_mul_behz_covered` for every
`square` instruction (the operand is lifted once, on both sides of the tensor product). -/
theorem stepOK_square_behz_covered (P : FullParams) (lay : Budget.KSLayout) (r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay 1 r body E = true)
    (k : ℕ) (d a : Var) (hk : body[k]? = some (.square d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (hr : 2 * x.level ≤ r)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca ca)) (.square d a) := sorry

/-- **SEAL's BEHZ multiplication at `sealBFV` within the covered profile** (closed instance).
Every `mul` of `sealProg`, computed by `behzMul` with SEAL's bases at the operand's level
(`sealAuxB`, `sealMsk`, `m̃ = 2³²`), meets its contract within
`certifiedApprox sealBFV sealLayout 1 8 0`, under every secret within the bound: the profile
`sealBFV_covers` decides is covered. About the algorithm read from SEAL's source
(`Challenge.Families.BEHZ`), not about SEAL's code. -/
theorem stepOK_mul_behz_sealBFV_covered (k : ℕ) (d a b : Var)
    (hk : sealProg.body[k]? = some (.mul d a b))
    (s : IntPoly sealBFV.src.N) (hs : SecretOK sealBFV.secretBound s) (ρ ρ' : Env sealBFV.src)
    (σ : Trace.CtEnv sealBFV) (x y : Val sealBFV.src) (ca cb : List (IntPoly sealBFV.src.N))
    (hstep : step sealBFV.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ sealBFV.src.qs.length) :
    TraceBFV.StepOK sealBFV (BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0) s ρ ρ' σ
      (σ.set d (behzMul sealBFV.src.t (sealBFV.src.qs.take x.level) (sealAuxB x.level) sealMsk
        (2 ^ 32) ca cb)) (.mul d a b) := sorry

-- `sealBFV` has four data levels, so BEHZ's rounding slack `2k` is at most 8 = `r`.
#guard sealBFV.src.qs.length == 4
-- The lift excess of SEAL's BEHZ at every level is far below `Q` (about `Q·2⁻²⁹` at the top),
-- and the size-form lift budget is the textbook one; the coverage form charges `U = 1`.
#guard [1, 2, 3, 4].all fun ℓ =>
  decide ((BudgetBFV.behzSlack sealBFV.src.t sealBFV.src.N (sealBFV.src.modulus ℓ)
    (sealAuxB ℓ).prod sealMsk ℓ (sealAuxB ℓ).length (2 ^ 32)).e * 2 ^ 29 ≤
      sealBFV.src.modulus ℓ)
#guard BudgetBFV.mulLiftNormAt sealBFV 4
    (BudgetBFV.behzSlack sealBFV.src.t sealBFV.src.N (sealBFV.src.modulus 4)
      (sealAuxB 4).prod sealMsk 4 (sealAuxB 4).length (2 ^ 32)).e == 4097
#guard BudgetBFV.mulLiftApprox sealBFV 1 == 4097 + 8193
-- `sealProg` is accepted at the covered profile, with a whole-program bound of bit length 133,
-- against 130 at the size-form BEHZ budget `sealBudget (behzSlack …)` (`Challenge.Families.BEHZ`,
-- the bound `1487107268619559764005097146872301164369`); decryption needs about `2¹⁵⁶`.
#guard (certifyBFVProfile? sealBFV (fun _ => BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0)
  sealProg).map (Nat.log2 ·.1) == some 133
#guard Nat.log2 1487107268619559764005097146872301164369 == 130
-- The textbook profile does not cover the family `(1, 8)`: the coverage check is not vacuous.
#guard !coversBFV? sealBFV sealLayout 1 8 sealProg.body
  (fun _ => BudgetBFV.certifiedApprox sealBFV sealLayout 0 1 0)

end Challenge.Families
