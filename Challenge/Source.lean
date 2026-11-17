import Spec.Correct

/-!
# Challenge.Source — realizability pins for `Spec.Source.step`   (LOCKED; proofs in `Validation/`)

Each pin says: a textbook operation on ciphertexts maps inputs that encrypt `step`'s operands to
an output that encrypts `step`'s result, with an explicit noise bound. If `step` had the wrong
message, factor, key or scale bookkeeping, the matching pin would be false.

The textbook operations are defined here, not in `Spec/`: they are the yardstick, not the thing
being trusted.
-/

namespace Challenge.Source
open Spec NPoly Scheme Layout Source Correct

variable {N : ℕ}

/-- Tensor product of two 2-component ciphertexts (integer representatives). -/
def tensor (c d : List (IntPoly N)) : List (IntPoly N) :=
  match c, d with
  | [c₀, c₁], [d₀, d₁] => [c₀ * d₀, c₀ * d₁ + c₁ * d₀, c₁ * d₁]
  | _, _ => []

/-- Textbook t-corrected BGV modulus switching of one component by the prime `q`:
`(c + δ) / q` with `δ = t·[−c·t⁻¹]_q`, so that `δ ≡ −c (mod q)` and `δ ≡ 0 (mod t)`. -/
def bgvModSwitchComp (t q : ℕ) (c : IntPoly N) : IntPoly N :=
  ⟨fun i =>
    let r : ZMod q := ((-(c.coeff i) : ℤ) : ZMod q) * (t : ZMod q)⁻¹
    (c.coeff i + (t : ℤ) * r.valMinAbs) / q⟩

/-- Componentwise `f` on two ciphertexts with possibly different numbers of components, the
shorter one padded with zero components (a zero component contributes nothing to the phase). -/
def padZip (f : IntPoly N → IntPoly N → IntPoly N) :
    List (IntPoly N) → List (IntPoly N) → List (IntPoly N)
  | [], bs => bs.map (f 0)
  | as, [] => as.map (fun a => f a 0)
  | a :: as, b :: bs => f a b :: padZip f as bs

/-- Tensor product of two ciphertexts with any numbers of components (integer representatives):
the product of the two polynomials in the key variable, `(Σᵢ cᵢ·Yⁱ)·(Σⱼ dⱼ·Yʲ)`, coefficient by
coefficient. For `p` and `p'` components (both at least one) the result has `p + p' − 1`. On two
2-component ciphertexts it is `tensor` (`tensorParts_two`). -/
def tensorParts : List (IntPoly N) → List (IntPoly N) → List (IntPoly N)
  | [], _ => []
  | c :: cs, ds => padZip (· + ·) (ds.map (c * ·)) (0 :: tensorParts cs ds)

/-- On two 2-component ciphertexts the general tensor product is the textbook one. -/
theorem tensorParts_two (c₀ c₁ d₀ d₁ : IntPoly N) :
    tensorParts [c₀, c₁] [d₀, d₁] = tensor [c₀, c₁] [d₀, d₁] := sorry

variable (P : FullParams)

/-- (BGV only: for BFV the sum's noise also picks up `Q mod t`.) -/
theorem step_add_bgv (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (ρ : Env P.src) (d a b : Var) (x y : Val P.src)
    (hx : ρ a = some x) (hy : ρ b = some y) (hlev : x.level = y.level) (hkey : x.key = y.key)
    (hparts : x.parts = y.parts)
    (ca cb : List (IntPoly P.src.N)) (B B' : ℕ)
    (hca : Encrypts P s B x ca) (hcb : Encrypts P s B' y cb)
    (hQ : 2 * (B + B') < P.src.modulus x.level) :
    ∃ ρ' v, step P.src ρ (.add d a b) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s (B + B') v (List.zipWith (· + ·) ca cb) := sorry

theorem step_mul_bgv (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (ρ : Env P.src) (d a b : Var)
    (x y : Val P.src) (hx : ρ a = some x) (hy : ρ b = some y) (hlev : x.level = y.level)
    (hkey : x.key = y.key) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (ca cb : List (IntPoly P.src.N)) (B B' : ℕ)
    (hca : Encrypts P s B x ca) (hcb : Encrypts P s B' y cb)
    (hQ : 2 * (P.src.N * B * B') < P.src.modulus x.level) :
    ∃ ρ' v, step P.src ρ (.mul d a b) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s (P.src.N * B * B') v (tensor ca cb) := sorry

theorem step_automorph_bgv (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (s : IntPoly P.src.N)
    (ρ : Env P.src) (d a : Var) (g : ℕ) (hg : g % 2 = 1) (x : Val P.src) (hx : ρ a = some x)
    (ca : List (IntPoly P.src.N)) (B : ℕ) (hca : Encrypts P s B x ca)
    (hQ : 2 * B < P.src.modulus x.level) :
    ∃ ρ' v, step P.src ρ (.automorph d a g) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s B v (ca.map (automorph g)) := sorry

/-- t-corrected modulus switching multiplies the message by `q_last⁻¹ mod t`, which is what
`step` records.

**This pin is about the message, and its noise bound is not the one the certificate uses.** It
is one of the realizability pins of `Source.step` (the textbook operation maps a ciphertext
encrypting the operand to one encrypting `step`'s result), with a bound that is easy to state
and deliberately not tight: `⌊B/q⌋ + 1 + t·(1 + N·B_s)`. The
certified bound for the same switch is `⌊B/q⌋ + msBudget`, with
`Spec.Budget.msBudget P = ⌈t·(1 + N·B_s)/2⌉`, about half as large: it is proved for the same
algorithm in `Challenge.Trace.stepOK_modSwitch_textbook` (two components) and
`stepOK_modSwitch_textbook_parts` (any number), and that is the one the analyzer
(`Challenge.Headline.refBound`), the budget (`Spec.Budget.certified`) and every certificate
use. Both statements are true, this one is weaker, and no other statement uses its bound. -/
theorem step_modSwitch_bgv (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (s : IntPoly P.src.N)
    (hs : SecretOK P.secretBound s) (ρ : Env P.src) (d a : Var) (x : Val P.src) (hx : ρ a = some x)
    (hℓ : 2 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (ca : List (IntPoly P.src.N)) (B : ℕ) (hca : Encrypts P s B x ca)
    (hQ : 2 * (B / P.src.qs[x.level - 1]! + 1 + P.src.t * (1 + P.src.N * P.secretBound)) <
      P.src.modulus (x.level - 1)) :
    ∃ ρ' v, step P.src ρ (.modSwitch d a) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s (B / P.src.qs[x.level - 1]! + 1 + P.src.t * (1 + P.src.N * P.secretBound)) v
        (ca.map (bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)) := sorry

/-! ## Plaintexts and dropped limbs -/

/-- **A plaintext operand is any representative of its message, with a declared bound.** For
every integer polynomial `p` with `‖p‖∞ ≤ B` that represents the message `m` (`p mod t = m`), the
one-component "ciphertext" `[p]` encrypts `m` with noise at most `B`, under every secret and
every key index, at every level whose modulus exceeds `2·B`. No convention for the
representative is assumed: the two standard ones are the instances below. -/
theorem encrypts_plain_bgv (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (s : IntPoly P.src.N)
    (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m) (h1 : v.parts = 1)
    (p : IntPoly P.src.N) (B : ℕ) (hp : ofInt P.src.t p = m) (hB : normInf p ≤ B)
    (hQ : 2 * B < P.src.modulus v.level) :
    Encrypts P s B v [p] := sorry

/-- **The canonical convention: bound `t − 1`.** For every message `m` the one-component
"ciphertext" `[p]`, `p` the lift of `m` to `[0, t)` (what OpenFHE's packed encoding stores),
encrypts `m` with noise at most `t − 1`, at every level whose modulus exceeds `2·(t − 1)`. So a
plaintext input (a declaration with `parts = 1`) stored this way with declared bound `t − 1`
restricts nothing. -/
theorem encrypts_plain_canonical (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (h1 : v.parts = 1) (hQ : 2 * (P.src.t - 1) < P.src.modulus v.level) :
    Encrypts P s (P.src.t - 1) v [⟨fun i => ((m.coeff i).val : ℤ)⟩] := sorry

/-- **The centred convention: bound `⌊t/2⌋`.** For every message `m` the one-component
"ciphertext" `[m̃]`, `m̃` the centred lift of `m`, encrypts `m` with noise at most `⌊t/2⌋`, at
every level whose modulus exceeds `2·⌊t/2⌋`. So a plaintext input stored centred with declared
bound `⌊t/2⌋` restricts nothing, and by `SchemeParamsOK.msgRange` it also meets `InputsOK`. -/
theorem encrypts_plain_centred (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (h1 : v.parts = 1) (hQ : 2 * (P.src.t / 2) < P.src.modulus v.level) :
    Encrypts P s (P.src.t / 2) v [centered m] := sorry

/-- **The bound `⌊t/2⌋` is not valid for the canonical convention.** `t = 17`, one prime
`q = 65537`, `N = 1`: the message `16` stored as `16` (its representative in `[0, t)`) is not
within the bound `⌊17/2⌋ = 8` of the centred convention; it is within `t − 1 = 16`. (Stored
centred it is `−1`.) -/
theorem plain_canonical_exceeds_centred :
    ¬ BGVEncrypts 17 (17 / 2) (0 : IntPoly 1) [ofInt 65537 (⟨fun _ => 16⟩ : IntPoly 1)]
        (ofInt 17 (⟨fun _ => 16⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (17 - 1) (0 : IntPoly 1) [ofInt 65537 (⟨fun _ => 16⟩ : IntPoly 1)]
        (ofInt 17 (⟨fun _ => 16⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (17 / 2) (0 : IntPoly 1) [ofInt 65537 (⟨fun _ => -1⟩ : IntPoly 1)]
        (ofInt 17 (⟨fun _ => 16⟩ : IntPoly 1)) := sorry

/-- Dropping limbs without dividing keeps the components: the same integer representatives
encrypt the same message with the same noise bound at the lower level, as long as the bound stays
below half the shorter modulus. -/
theorem step_dropLimbs_bgv (hk : P.src.kind = .bgv) (s : IntPoly P.src.N)
    (ρ : Env P.src) (d a : Var) (k : ℕ) (x : Val P.src) (hx : ρ a = some x) (hkℓ : k < x.level)
    (ca : List (IntPoly P.src.N)) (B : ℕ) (hca : Encrypts P s B x ca)
    (hQ : 2 * B < P.src.modulus (x.level - k)) :
    ∃ ρ' v, step P.src ρ (.dropLimbs d a k) = some ρ' ∧ ρ' d = some v ∧
      v.level = x.level - k ∧ v.msg = x.msg ∧ Encrypts P s B v ca := sorry

/-- `dropLimbs` must leave at least one limb. -/
theorem step_dropLimbs_level (P : Params) (ρ : Env P) (d a : Var) (k : ℕ) (x : Val P)
    (hx : ρ a = some x) (h : x.level ≤ k) : step P ρ (.dropLimbs d a k) = none := sorry

/-- A plaintext operand has exactly one component. -/
theorem step_addPlain_parts (P : Params) (ρ : Env P) (d a p : Var) (y : Val P)
    (hy : ρ p = some y) (h : y.parts ≠ 1) : step P ρ (.addPlain d a p) = none := sorry

/-- A ciphertext–plaintext product has the message `m · p`, and keeps the ciphertext's number of
components, level and key. -/
theorem step_mulPlain_msg (P : Params) (ρ ρ' : Env P) (d a p : Var) (x y : Val P)
    (m mp : Poly P.t P.N) (hx : ρ a = some x) (hy : ρ p = some y) (hm : x.msg = .exact m)
    (hmp : y.msg = .exact mp) (h : step P ρ (.mulPlain d a p) = some ρ') :
    ∃ v, ρ' d = some v ∧ v.msg = .exact (m * mp) ∧ v.parts = x.parts ∧ v.level = x.level ∧
      v.key = x.key := sorry

/-! ## Levels, parts and keys of declared inputs

`step` once read the dropped modulus as `qs.getD (ℓ-1) 0`: beyond the chain it was `0`, and the
BGV message silently became `0`. Nothing checked declarations either. -/

/-- `modSwitch` at a level beyond the modulus chain is ill-formed. -/
theorem step_modSwitch_level (P : Params) (ρ : Env P) (d a : Var) (x : Val P) (hx : ρ a = some x)
    (h : P.qs.length < x.level) : step P ρ (.modSwitch d a) = none := sorry

/-- A program with an ill-formed input declaration (no parts, level `0`, a level above the chain,
or a key that is not an odd number below `2N`) does not evaluate, whatever its body. -/
theorem eval_badDecl (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) (d : Decl)
    (hd : d ∈ prog.inputs)
    (h : d.parts = 0 ∨ d.level = 0 ∨ P.qs.length < d.level ∨ d.key % 2 = 0 ∨ 2 * P.N ≤ d.key) :
    eval P prog msgs = none := sorry

/-- A well-formed input holds exactly what its (first) declaration says, key included. -/
theorem eval_input (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) (ρ : Env P)
    (h : eval P prog msgs = some ρ) (hbody : prog.body = []) (x : Var) (d : Decl)
    (hd : prog.inputs.find? (·.name = x) = some d) :
    ∃ v, ρ x = some v ∧ v.msg = msgs x ∧ v.parts = d.parts ∧ v.level = d.level ∧
      v.key = d.key ∧ v.scale = d.scale ∧
      1 ≤ v.parts ∧ 1 ≤ v.level ∧ v.level ≤ P.qs.length ∧ v.key % 2 = 1 ∧ v.key < 2 * P.N := sorry

/-- A key switch on an already-permuted input: the program whose input `a` is declared
under `σ_g(s)`. -/
def rotatedKeySwitchProg (g : ℕ) : Program :=
  { inputs := [⟨"a", 2, 1, 1, g⟩], body := [.keySwitch "c" "a"], outputs := ["c"] }

/-- The key-switch kernel on a rotated input is expressible: the program is well formed, its
input is under `σ_g(s)`, and its output holds the same message under `s`. -/
theorem eval_rotatedKeySwitch (P : Params) (g : ℕ) (hg : g % 2 = 1) (hg2 : g < 2 * P.N)
    (hL : 1 ≤ P.qs.length) (msgs : Var → Msg P.t P.N) (hfit : (msgs "a").fits P.kind = true) :
    ∃ ρ va vc, eval P (rotatedKeySwitchProg g) msgs = some ρ ∧ ρ "a" = some va ∧
      ρ "c" = some vc ∧ va.key = g ∧ vc.key = 1 ∧ vc.msg = msgs "a" ∧ vc.parts = 2 ∧
      vc.level = 1 := sorry

/-- A declared input under `σ_g(s)` is *not* accepted where a ciphertext under `s` is required:
relinearization-style ops check the key (`add` of operands under different keys is ill-formed). -/
theorem eval_mixedKeys (P : Params) (g : ℕ) (hg : g ≠ 1) (msgs : Var → Msg P.t P.N) :
    eval P { inputs := [⟨"a", 2, 1, 1, 1⟩, ⟨"b", 2, 1, 1, g⟩], body := [.add "c" "a" "b"],
             outputs := ["c"] } msgs = none := sorry

end Challenge.Source
