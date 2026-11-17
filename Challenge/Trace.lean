import Spec.Budget
import Challenge.Source

/-!
# Challenge.Trace — pins for the ciphertext-level run semantics   (LOCKED statements; proofs in `Validation/`)

`Spec.Trace` specifies each BGV operation by a contract on the phase. These pins show that

* the phase used there is the phase `Spec.Correct.Encrypts` decrypts and bounds
  (`encrypts_bgv_iff_phase`), and that `Encrypts` for BGV contains exact decryption
  (`encrypts_bgv_decrypts`), so a noise headline stated with `Encrypts` is a decryption claim;
* the contracts can be met, by the textbook algorithms. Without these a statement about "every
  run meeting the contracts" could be about no runs. One pin per operation, each with the weakest
  hypotheses under which it holds (what `Source.step` checks, plus that the operand ciphertexts
  have the recorded numbers of components):

  | instruction | textbook operation | pin |
  |---|---|---|
  | `add`, `sub` | componentwise, the shorter operand padded with zero components | `stepOK_add_padded`, `stepOK_sub_padded` (`stepOK_add_textbook`: equal numbers of components, `zipWith`) |
  | `addPlain`, `subPlain`, `mulPlain` | on the first component / on every component | `stepOK_addPlain_textbook`, `stepOK_subPlain_textbook`, `stepOK_mulPlain_textbook` |
  | `mul` | tensor product, any numbers of components | `stepOK_mul_tensor` (`stepOK_mul_textbook`: 2 × 2) |
  | `square` | tensor product with itself | `stepOK_square_textbook` |
  | `mulConst c` | every component times `c` | `stepOK_mulConst_textbook` |
  | `copy`, `toEval`, `toCoeff` | the same components | `stepOK_copy_textbook` |
  | `automorph g` | `σ_g` of every component | `stepOK_automorph_textbook` |
  | `dropLimbs k` | the same components | `stepOK_dropLimbs_textbook` |
  | `modSwitch` | t-corrected switch of every component, any number `k` of components, within `Spec.Budget.msBudgetAt P k` | `stepOK_modSwitch_textbook_parts` (`stepOK_modSwitch_textbook`: `k = 2`) |
  | `relin`, `keySwitch` | hybrid key switching within `Spec.Budget.ksBoundAt` | `Challenge.Budget.relin_realizable`, `keySwitch_realizable` (per-level keys); `relin_realizable_top`, `keySwitch_realizable_top` (one top-level key set) |

  `Challenge.Budget.certified_run_exists` puts these together: every program the reference
  analysis accepts at the certified budget has a run.

The textbook operations are the ones in `Challenge.Source`.
-/

namespace Challenge.Trace
open Spec NPoly Scheme Source Correct

variable (P : FullParams)

/-- `Encrypts`, for BGV, in terms of `Trace.phaseAt`. -/
theorem encrypts_bgv_iff_phase (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (ct : List (IntPoly P.src.N)) :
    Encrypts P s B v ct ↔
      ct.length = v.parts ∧
      ofInt P.src.t (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)) = m ∧
      normInf (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)) ≤ B := sorry

/-- For BGV, a ciphertext that `Encrypts` a value decrypts to its message exactly, by the
decryption function pinned in `Challenge.Scheme`, under the key the value is recorded under. -/
theorem encrypts_bgv_decrypts (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (ct : List (IntPoly P.src.N)) (h : Encrypts P s B v ct) :
    ∃ m, v.msg = .exact m ∧
      bgvDecrypt P.src.t (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) = m := sorry

/-- Componentwise addition meets the `add` contract. -/
theorem stepOK_add_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.add d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) (hparts : x.parts = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (List.zipWith (· + ·) ca cb)) (.add d a b) := sorry

/-- The tensor product of two 2-component ciphertexts meets the `mul` contract. (Any numbers of
components: `stepOK_mul_tensor`.) -/
theorem stepOK_mul_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.tensor ca cb)) (.mul d a b) := sorry

/-- Textbook t-corrected modulus switching of a 2-component ciphertext meets the `modSwitch`
contract whenever the budget is at least `⌈t · (1 + N · secretBound) / 2⌉`. The correction of
each component is centered, `|δ_c| ≤ t · ⌊q/2⌋`, so the phase correction `δ₀ + s·δ₁` is at most
`t · ⌊q/2⌋ · (1 + N · secretBound) ≤ q · ⌈t · (1 + N · secretBound) / 2⌉`. This is the least
integer budget this worst-case bound allows uniformly in `q`: the bound is `x·(q-1)/(2q)` with
`x = t · (1 + N · secretBound)`, which exceeds `⌈x/2⌉ - 1` for every odd `q > x`. (That the bound
is attained by some ciphertext is not proved here.) Any number of components:
`stepOK_modSwitch_textbook_parts`. -/
theorem stepOK_modSwitch_textbook (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (E : Trace.Budget)
    (hE : (P.src.t * (1 + P.src.N * P.secretBound) + 1) / 2 ≤ E.modSwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (h2 : x.parts = 2) (hla : ca.length = 2) :
    Trace.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)))
      (.modSwitch d a) := sorry

/-! ## Mixed numbers of components, plaintext operands, dropped limbs -/

/-- Componentwise addition with the shorter ciphertext padded by zero components meets the `add`
contract, whatever the two numbers of components (e.g. a 3-component product plus a fresh
ciphertext, before relinearization). -/
theorem stepOK_add_padded (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.add d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· + ·) ca cb)) (.add d a b) :=
  sorry

/-- The same for subtraction. -/
theorem stepOK_sub_padded (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.sub d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· - ·) ca cb)) (.sub d a b) :=
  sorry

/-- Adding the plaintext polynomial `c` to the first component meets the `addPlain` contract
(under whatever key the ciphertext is). -/
theorem stepOK_addPlain_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· + ·) ca [c]))
      (.addPlain d a p) := sorry

/-- Subtracting the plaintext polynomial from the first component meets the `subPlain`
contract. -/
theorem stepOK_subPlain_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· - ·) ca [c]))
      (.subPlain d a p) := sorry

/-- Multiplying every component by the plaintext polynomial `c` meets the `mulPlain` contract. -/
theorem stepOK_mulPlain_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.mulPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c * ·))) (.mulPlain d a p) := sorry

/-- Keeping the components (in RNS storage: forgetting the last `k` limbs) meets the `dropLimbs`
contract. -/
theorem stepOK_dropLimbs_textbook (E : Trace.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (k : ℕ)
    (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.dropLimbs d a k) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d ca) (.dropLimbs d a k) := sorry

/-! ## Every instruction, every number of components

The pins above cover `mul` and `modSwitch` for 2-component operands only, and say nothing about
`square`, `mulConst`, `copy`/`toEval`/`toCoeff` and `automorph`. `Source.step` and the reference
analysis accept these instructions on operands with any number of components (a 3-component
product times a fresh ciphertext, a modulus switch before relinearization), so the contracts must
be realizable there too. -/

/-- The tensor product of two ciphertexts with any numbers of components
(`Challenge.Source.tensorParts`) meets the `mul` contract. (`step` checks that both operands have
at least one component.) -/
theorem stepOK_mul_tensor (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.tensorParts ca cb)) (.mul d a b) := sorry

/-- The tensor product of a ciphertext with itself meets the `square` contract, whatever its
number of components. -/
theorem stepOK_square_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.tensorParts ca ca)) (.square d a) := sorry

/-- Multiplying every component by the integer `c` meets the `mulConst` contract. -/
theorem stepOK_mulConst_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (c : ℤ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mulConst d a c) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c • ·))) (.mulConst d a c) := sorry

/-- Keeping the components meets the contract of `copy`, `toEval` and `toCoeff` (at this level
the three mean "the same ciphertext"; they differ in storage form only). -/
theorem stepOK_copy_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (i : Instr)
    (hi : i = .copy d a ∨ i = .toEval d a ∨ i = .toCoeff d a) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ i = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d ca) i := sorry

/-- Applying `σ_g` to every component meets the `automorph` contract (`step` checks that `g` is
odd; the result is under `σ_g` of the operand's key). -/
theorem stepOK_automorph_textbook (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (g : ℕ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.automorph d a g) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (ca.map (automorph g))) (.automorph d a g) := sorry

/-- **Textbook modulus switching of a value with any number `k` of components** meets the
`modSwitch` contract whenever the budget for `k` components is at least
`Spec.Budget.msBudgetAt P k = ⌈t · Σ_{i<k} (N · secretBound)ⁱ / 2⌉`: the correction of each
component is centred, `|δ_i| ≤ t · ⌊q/2⌋`, and the phase correction is `Σ_{i<k} σ(s)ⁱ · δ_i`
(`σ(s)` the Galois conjugate of the secret the operand is under), of norm at most
`t · ⌊q/2⌋ · Σ_{i<k} (N · secretBound)ⁱ`. `k = 2` is `stepOK_modSwitch_textbook`; `k = 1` is the
switch of a plaintext operand (`Challenge.Budget.modSwitch_realizable_one` states it without the
bound on the secret); `k = 3` is the switch of a product that has not been relinearized, which
the two-component budget does *not* cover (`Challenge.Budget`, "The many-component budget is
needed": at `tinyBGV` the textbook switch of a 3-component product reaches noise 85, above the
43 the two-component budget would promise). The bound is a worst case over all secrets within
the bound; it is not claimed to be attained. (That the level is inside the chain is part of
`step` succeeding.) -/
theorem stepOK_modSwitch_textbook_parts (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (E : Trace.Budget) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hE : Spec.Budget.msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)))
      (.modSwitch d a) := sorry

end Challenge.Trace
