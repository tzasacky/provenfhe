import Challenge.Budget

/-!
# Challenge.BudgetRestrict — one set of top-level keys serves every level   (LOCKED statements; proofs in `Validation/`)

`Spec.Budget.GadgetKeysOK P lay ℓ tgt s keys` asks for gadget keys made for level `ℓ`: modulo
`Q_ℓ·P`, one per digit of `lay.sizes ℓ`, encrypting the level-`ℓ` gadget factor. The realizability
pins of `Challenge.Budget` (`relin_realizable`, `keySwitch_realizable`) take such keys as a
hypothesis, as if a separate key set existed for every level. Real libraries (OpenFHE among
them) generate one key set at the top level `L = P.src.qs.length` (modulo `Q_L·P`) and at level
`ℓ` use its first digits, reading the same integer representatives modulo `Q_ℓ·P` (the limbs above
`ℓ` dropped). These pins say when that is valid, and that it is not always valid.

* `Spec.Budget.restrictsTo lay L ℓ` (trusted, computable): the top-level layout is usable and the digits at level
  `ℓ` are the top-level digits cut down to the first `ℓ` limbs (`cutSizes`). `restrictsTo_okAt`:
  the layout is then usable at level `ℓ` too. `uniformLayout_restrictsTo`: uniform digits restrict
  this way at every level `ℓ ≤ L`, for every digit size `α` (`α = 0`: a single digit; a partial
  last digit included).
* `gadgetFactor_restrict`: under `restrictsTo`, the top-level gadget factor of digit `j` is
  congruent to the level-`ℓ` one modulo `Q_ℓ·Pm`, for every `Pm`.
* `gadgetKeys_restrict` (and `gadgetKeys_restrict_uniform` for `uniformLayout`): valid top-level
  gadget keys, cut to the first `(lay.sizes ℓ).length` of them, are valid level-`ℓ` gadget keys
  for the same secret, target (`square` or `galois g`) and noise bound `P.keyNoise`, for every
  scheme. For BFV no further hypothesis is needed: the centred representative modulo
  `Q_ℓ·P` of the top-level error `e` is never larger than `e`. For BGV, `KeyValid` also asks
  `t ∣ e`, which survives only if `e` is unchanged by the reduction; the hypothesis
  `2·(⌊B/t⌋·t) < Q_ℓ·P` (`B = P.keyNoise`; `⌊B/t⌋·t` is the largest multiple of `t` within the
  bound, so the largest possible BGV error) guarantees that. It is sufficient, not necessary (at
  `ℓ = L` it is not needed at all), but it cannot simply be dropped:
  `gadgetKeys_restrict_needs_size_bgv`.
* `relin_realizable_top`, `keySwitch_realizable_top`: the realizability pins of `Challenge.Budget`
  with one top-level key set, cut down at the level of the operand.
* `gadgetKeys_restrict_needs_restrictsTo`: a layout usable at every level whose level-2 digits are
  not the cut top-level digits; valid top-level keys (zero error) cut to level 2 are invalid there:
  the restricted top-level gadget factor differs from the level-2 one. So `restrictsTo` is not a
  vacuous hypothesis.

`SpecialOK` is not needed for the restriction itself (only for the realizability pins it is
combined with); `SchemeParamsOK` is used for the ciphertext primes being positive and pairwise
coprime.
-/

namespace Challenge.Budget
open Spec NPoly Scheme Source Correct Spec.Budget Challenge.Headline

/-! ## Restricting a layout -/

/-! `cutSizes` and `restrictsTo` are trusted definitions of `Spec.Budget` (they were defined
here until `Challenge.Certify.certify?` came to check them). -/

#guard cutSizes [2, 2, 1] 3 == [2, 1]
#guard cutSizes [3] 2 == [2]
#guard cutSizes [1, 1, 1] 0 == []
#guard (List.range 6).all fun ℓ => restrictsTo (uniformLayout 2) 5 ℓ
#guard (List.range 8).all fun α => (List.range 8).all fun ℓ => restrictsTo (uniformLayout α) 7 ℓ
-- At level 5 with `α = 3` the top level has digits `[3, 3, 1]`; the cut keeps `[3, 2]`.
#guard (uniformLayout 3).sizes 7 == [3, 3, 1] && (uniformLayout 3).sizes 5 == [3, 2]

/-- A layout that restricts is usable at the lower level. -/
theorem restrictsTo_okAt (lay : KSLayout) (L ℓ : ℕ) (hℓ : ℓ ≤ L)
    (h : restrictsTo lay L ℓ = true) : lay.okAt ℓ = true := sorry

/-- **Uniform digits restrict.** For every digit size `α` (including `α = 0`, a single digit, and
a partial last digit when `α ∤ ℓ` or `α ∤ L`) the digits of `uniformLayout α` at level `ℓ ≤ L`
are the top-level digits cut down to `ℓ` limbs. -/
theorem uniformLayout_restrictsTo (α : ℕ) (c : Bool) (L ℓ : ℕ) (hℓ : ℓ ≤ L) :
    restrictsTo (uniformLayout α c) L ℓ = true := sorry

/-! ## The gadget factor and the keys restrict -/

/-- **Restricted gadget factor.** If the layout restricts from the top level `L` to level
`ℓ ≤ L`, then for every digit `j` of level `ℓ` the top-level gadget factor `g⁽ᴸ⁾ⱼ` is congruent
to the level-`ℓ` one modulo `Q_ℓ · Pm`, for every special modulus `Pm`. -/
theorem gadgetFactor_restrict (P : FullParams) (lay : KSLayout) (hP : SchemeParamsOK P)
    (Pm ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (j : ℕ) (hj : j < (lay.sizes ℓ).length) :
    ((P.src.modulus ℓ * Pm : ℕ) : ℤ) ∣
      (gadgetFactor Pm (digitModuli P lay P.src.qs.length) j : ℤ) -
        (gadgetFactor Pm (digitModuli P lay ℓ) j : ℤ) := sorry

/-- **Top-level keys serve every level.** If the layout restricts from the top level
`L = P.src.qs.length` to level `ℓ ≤ L`, a list of gadget keys valid at the top level (modulo
`Q_L·P`, for the secret `s`, the target `tgt`, noise at most `P.keyNoise`), cut to its first
`(lay.sizes ℓ).length` entries and read modulo `Q_ℓ·P` (the same integer representatives), is a
list of gadget keys valid at level `ℓ`, with the same noise bound.

`hB` concerns BGV only (the `t ∣ e` clause of `KeyValid`): it makes the top-level error `e`, a
multiple of `t` of size at most `P.keyNoise`, its own centred representative modulo `Q_ℓ·P`. It
is sufficient, not necessary; `gadgetKeys_restrict_needs_size_bgv` shows that it cannot simply be
dropped. For BFV the error modulo `Q_ℓ·P` is the centred representative of `e`, which is
never larger than `e`, and nothing else is asked. -/
theorem gadgetKeys_restrict (P : FullParams) (lay : KSLayout) (tgt : KeyTarget)
    (hP : SchemeParamsOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (hB : P.src.kind = .bgv →
      2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P lay P.src.qs.length tgt s keys) :
    GadgetKeysOK P lay ℓ tgt s (keys.take (lay.sizes ℓ).length) := sorry

/-- `gadgetKeys_restrict` for uniform digits (every `α`, both kinds of representatives). -/
theorem gadgetKeys_restrict_uniform (P : FullParams) (α : ℕ) (c : Bool) (tgt : KeyTarget)
    (hP : SchemeParamsOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hB : P.src.kind = .bgv →
      2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P (uniformLayout α c) P.src.qs.length tgt s keys) :
    GadgetKeysOK P (uniformLayout α c) ℓ tgt s
      (keys.take ((uniformLayout α c).sizes ℓ).length) := sorry

/-! ## Realizability with one top-level key set -/

/-- **Relinearization within `ksBoundAt` from top-level keys.** `relin_realizable`, with the
keys generated once at the top level and cut down to the digits of the operand's level `ℓ`. -/
theorem relin_realizable_top (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (hB : 2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        GadgetKeysOK P lay P.src.qs.length .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca (keys.take (lay.sizes ℓ).length)))
          (.relin d a) := sorry

/-- **Key switching within `ksBoundAt` from top-level keys.** `keySwitch_realizable`, with the
keys for `σ_g(s)` generated once at the top level and cut down to the digits of level `ℓ`. -/
theorem keySwitch_realizable_top (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true)
    (hB : 2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus ℓ * specialProd P) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        GadgetKeysOK P lay P.src.qs.length (.galois x.key) s keys →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca (keys.take (lay.sizes ℓ).length)))
          (.keySwitch d a) := sorry

/-! ## Small numbers

Limbs `5, 7, 11, 13`, special modulus `3`. For uniform digits the top-level gadget factor reduces
to the level-`ℓ` one modulo `Q_ℓ · 3` at every level and for every digit size, also when `α ∤ ℓ`
(the partial last digit at level `ℓ` is the cut of a full top-level digit). -/

/-- Limbs `qs`, special primes `ps`, BGV with `t = 2`, `N = 1`, key noise `B`. -/
def restrictParams (qs ps : List ℕ) (B : ℕ) : FullParams :=
  { src := { kind := .bgv, N := 1, qs := qs, t := 2 },
    store := { W := 1, limbs := [], special := ps.map fun p => ⟨p, 0⟩ },
    secretBound := 1, inputNoise := 1, keyNoise := B, outputNoise := 0 }

/-- Whether the top-level gadget factors of `lay` reduce to the level-`ℓ` ones modulo `Q_ℓ · P`
for every digit of every level `1 ≤ ℓ ≤ L`. -/
def gadgetRestricts (P : FullParams) (lay : KSLayout) : Bool :=
  let L := P.src.qs.length
  (List.range L).all fun i =>
    let ℓ := i + 1
    let M := P.src.modulus ℓ * specialProd P
    (List.range (lay.sizes ℓ).length).all fun j =>
      gadgetFactor (specialProd P) (digitModuli P lay L) j % M ==
        gadgetFactor (specialProd P) (digitModuli P lay ℓ) j % M

#guard (List.range 6).all fun α => gadgetRestricts (restrictParams [5, 7, 11, 13] [3] 0)
  (uniformLayout α)
#guard (List.range 6).all fun α => gadgetRestricts (restrictParams [5, 7, 11, 13, 17] [3, 19] 0)
  (uniformLayout α)
-- One instance spelled out: `α = 2`, top digits `[35, 143]`, level-3 digits `[35, 11]`.
#guard digitModuli (restrictParams [5, 7, 11, 13] [3] 0) (uniformLayout 2) 4 == [35, 143]
#guard digitModuli (restrictParams [5, 7, 11, 13] [3] 0) (uniformLayout 2) 3 == [35, 11]
#guard gadgetFactor 3 [35, 143] 0 % (385 * 3) == gadgetFactor 3 [35, 11] 0 % (385 * 3)
#guard gadgetFactor 3 [35, 143] 1 % (385 * 3) == gadgetFactor 3 [35, 11] 1 % (385 * 3)

/-! ## `restrictsTo` is needed

Limbs `5, 7, 11`, no special prime, BGV with `t = 2`. The layout has digits `[2, 1]` at the top
(level 3) and one limb per digit below (`[1, 1]` at level 2, `[1]` at level 1): usable at every
level, but the level-2 digits are not the cut top-level digits (`cutSizes [2, 1] 2 = [2]`). The
top-level gadget factor of digit 0 is `176` (`≡ 1 mod 35`, `≡ 0 mod 11`), the level-2 one is
`21` (`≡ 1 mod 5`, `≡ 0 mod 7`): they differ modulo `Q₂ = 35`. With the secret `1` the keys
`(gⱼ, 0)` have error `0` at the top level, and at level 2 the first of them has error
`176 − 21 ≡ 15 (mod 35)`. -/

/-- Digits `[2, 1]` at level 3, one limb per digit below. -/
def restrictBadLayout : KSLayout where
  sizes ℓ := if ℓ = 3 then [2, 1] else List.replicate ℓ 1

/-- Limbs `5, 7, 11`, no special prime, `t = 2`, key noise `2`. -/
def restrictBadParams : FullParams := restrictParams [5, 7, 11] [] 2

/-- The secret `1`. -/
def restrictBadSecret : IntPoly 1 := ⟨fun _ => 1⟩

/-- Noiseless top-level relinearization keys for the secret `1`: `(gⱼ, 0)`. -/
def restrictBadKeys : List (IntPoly 1 × IntPoly 1) := [(⟨fun _ => 176⟩, 0), (⟨fun _ => 210⟩, 0)]

#guard schemeParamsOK? restrictBadParams && specialOK? restrictBadParams
#guard [1, 2, 3].all restrictBadLayout.okAt
#guard restrictsTo restrictBadLayout 3 2 == false
#guard restrictsTo restrictBadLayout 3 1
#guard digitModuli restrictBadParams restrictBadLayout 3 == [35, 11]
#guard digitModuli restrictBadParams restrictBadLayout 2 == [5, 7]
#guard [gadgetFactor 1 [35, 11] 0, gadgetFactor 1 [35, 11] 1] == [176, 210]
#guard [gadgetFactor 1 [5, 7] 0, gadgetFactor 1 [5, 7] 1] == [21, 15]
#guard gadgetFactor 1 [35, 11] 0 % 35 != gadgetFactor 1 [5, 7] 0 % 35

/-- **The digits must restrict.** For `restrictBadLayout` (usable at every level, but its level-2
digits are not the cut top-level digits) the conclusion of `gadgetKeys_restrict` fails: the
noiseless top-level keys are valid at the top level, and cut to the two digits of level 2 they are
not valid there (error `15`, above the key noise bound `2`). (Stated as the failure of the
implication, which is equivalent to the conjunction "valid at the top and not valid at level
2".) The parameters satisfy `SchemeParamsOK` and `SpecialOK` (guards above), so the
hypothesis `restrictsTo` of `gadgetKeys_restrict` cannot be dropped. -/
theorem gadgetKeys_restrict_needs_restrictsTo :
    ¬ (GadgetKeysOK restrictBadParams restrictBadLayout 3 .square restrictBadSecret
          restrictBadKeys →
        GadgetKeysOK restrictBadParams restrictBadLayout 2 .square restrictBadSecret
          (restrictBadKeys.take 2)) := sorry

/-! ## The size condition is needed for BGV

Limbs `5, 7`, no special prime, BGV with `t = 2` and key noise `4`, one limb per digit (a layout
that restricts). With the secret `0` a key `(4, 0)` has error `4` at the top level (modulus 35):
within the bound and a multiple of `t`. At level 1 (modulus 5) its error is the centred
representative of `4`, which is `−1`: within the bound, but odd. Here `2·(⌊4/2⌋·2) = 8 ≥ 5`, so
`hB` of `gadgetKeys_restrict` fails. -/

/-- Limbs `5, 7`, no special prime, `t = 2`, key noise `4`. -/
def restrictSizeParams : FullParams := restrictParams [5, 7] [] 4

/-- Top-level keys with error `4` for the secret `0`. -/
def restrictSizeKeys : List (IntPoly 1 × IntPoly 1) := [(⟨fun _ => 4⟩, 0), (⟨fun _ => 4⟩, 0)]

#guard schemeParamsOK? restrictSizeParams && specialOK? restrictSizeParams
#guard restrictsTo (uniformLayout 1) 2 1
#guard !decide (2 * (4 / 2 * 2) < 5)

/-- **BGV needs the size condition.** The conclusion of `gadgetKeys_restrict` fails without `hB`:
valid top-level BGV keys whose restriction to level 1 is not valid there (the error `4` becomes
`−1`, which `t = 2` does not divide), for a layout that restricts and parameters that satisfy
`SchemeParamsOK` and `SpecialOK`. -/
theorem gadgetKeys_restrict_needs_size_bgv :
    ¬ (GadgetKeysOK restrictSizeParams (uniformLayout 1) 2 .square 0 restrictSizeKeys →
        GadgetKeysOK restrictSizeParams (uniformLayout 1) 1 .square 0
          (restrictSizeKeys.take 1)) := sorry

end Challenge.Budget
