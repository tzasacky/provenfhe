import Spec.Trace

/-!
# Spec.Budget — the error budget of key switching and modulus switching, from the parameters   (TRUSTED)

`Spec.Trace.Budget` is what a backend declares: how much phase error one key switch adds, and
how much one modulus switch of a value with `k` components adds (one number for `k = 1`, one for
`k = 2`, a function of `k` for `k ≥ 3`). A noise claim relative to a free budget is only as good
as the numbers put in. This file computes them from what the user already supplies (`FullParams`: ring
dimension, plaintext modulus, key noise bound, secret bound, modulus chain, special primes) and
from the *layout* of hybrid key switching (how the limbs of each level are grouped into digits).

Hybrid key switching (Han–Ki 2019; OpenFHE `KeySwitchHYBRID`). At level `ℓ` the
limbs `q₀, …, q_{ℓ-1}` (product `Q`) are split into consecutive digits with `ℓⱼ` limbs and
product `Qⱼ`; `P` is the product of the `k` special primes. The key for digit `j` encrypts
`gⱼ · target(s)` modulo `Q·P`, where `gⱼ = P · Q̂ⱼ · [Q̂ⱼ⁻¹]_{Qⱼ}` and `Q̂ⱼ = Q / Qⱼ`
(`gadgetFactor`, `gadgetReq`). With keys of noise at most `B_k`, a secret of norm at most `B_s`:

* centred representatives in ModUp and ModDown:
  `‖e‖∞ ≤ ⌊(N·B_k·Σⱼ ℓⱼ·Qⱼ + t·k·P·(1 + N·B_s)) / (2P)⌋`;
* canonical representatives (`[·] ∈ [0, q)`, what libraries compute):
  `‖e‖∞ ≤ ⌊(N·B_k·Σⱼ 2ℓⱼ·(Qⱼ − 1) + t·2k·(P − 1)·(1 + N·B_s)) / (2P)⌋`.

`ksBoundAt` is this number at one level, `ksBudget` its maximum over the levels of the chain.

**Which representatives a library uses** (`KSLayout.canonical`). `canonical = true` is OpenFHE's
BGV key switching as built by default: its `ApproxSwitchCRTBasis` takes the representative in
`[0, qᵢ)` of every fast-base-conversion term on both of its code paths
(`src/core/include/lattice/hal/default/dcrtpoly-impl.h`, v1.6.1 l.938-977). The reference
algorithm with canonical representatives (`FHE.KeySwitch.keySwitchBGVOpenFHE`, whose error is
proved within this bound) is proved equal, limb for limb, to the independent re-specification's
(`Respec.Equiv.keySwitch_openfhe_eq`), and the conformance harness finds it bit-exact with the
output of OpenFHE v1.6.1's relinearization on recorded runs. OpenFHE v1.6.1's rotation uses the
same ModUp, inner product and ModDown but applies the automorphism between the inner product
and ModDown, not after the key switch: that variant (`rotateOpenFHE161` in
`FHE/Pin/AlgoOpenFHE.lean`) is bit-exact with the recorded rotations and proved within the same
bound (`rotateOpenFHE161_spec` there; `harness/openfhe-pin/algo/README.md`). Locked statements
name both: `Challenge.Realize.relinOpenFHE_stepOK`, `keySwitchOpenFHE_stepOK` and
`rotateOpenFHE161_run` (and their certificate forms `certify?_relinOpenFHE`, …) say that locked
transcriptions of these functions (`Challenge/Realize/OpenFHE.lean`, proved equal to the `FHE.*`
functions the harness runs in `FHE/Realize/`) meet the step contracts at `ksBoundAt`. `canonical = false` (centred representatives, the smaller
bound) describes OpenFHE built with the CMake option `WITH_REDUCED_NOISE`, which is off by
default (by reading of the same source; the recorded runs are of default builds only). A default
build takes the canonical representatives read above, so a certificate at `canonical = false`
is not about a default OpenFHE build.

Modulus switching. The textbook t-corrected switch replaces every component `c_i` by
`(c_i + δ_i)/q` with `δ_i = t·[−c_i·t⁻¹]_q` centred, `‖δ_i‖∞ ≤ t·⌊q/2⌋`. The phase of a
`k`-component value is `Σ_{i<k} sⁱ·c_i`, so the correction of the phase is `Σ_{i<k} sⁱ·δ_i`, and
with `‖a·b‖∞ ≤ ‖a‖₁·‖b‖∞ ≤ N·‖a‖∞·‖b‖∞` in `Z[X]/(X^N+1)` (and `‖σ_g(s)‖₁ ≤ ‖s‖₁`, so the same
under any Galois conjugate of the secret) its norm is at most `t·⌊q/2⌋·Σ_{i<k} (N·B_s)ⁱ`.
`msBudgetAt P k = ⌈t·Σ_{i<k} (N·B_s)ⁱ/2⌉` is that bound divided by `q` and rounded up: `⌈t/2⌉`
for `k = 1` (`msBudgetOne`: a plaintext operand, no secret-dependent term), `⌈t·(1 + N·B_s)/2⌉`
for `k = 2` (`msBudget`), `⌈t·(1 + N·B_s + (N·B_s)²)/2⌉` for a three-component product that has
not been relinearized, and so on. It is an upper bound for every secret within `B_s`; it is not
claimed to be attained.

**These modulus-switching budgets are for the centred correction only**: `δ_i = t·[−c_i·t⁻¹]_q`
with `[·]_q` the representative of least absolute value (OpenFHE's `DCRTPoly::ModReduce`, whose
`SwitchModulus` lifts centred; confirmed bit-exact on recorded runs, `algo.modReduce` in
`harness/openfhe-pin/algo/README.md`). A switch that takes the correction in `[0, q)` instead
(the canonical-lift switch `FHE.RNS.Basis.bgvModSwitchCanon`) has `‖δ_i‖∞ ≤ t·(q − 1)`, about twice as much, and exceeds
`msBudget` already for two components (`Respec.Equiv.twoPart_nonCentred_exceeds`). No budget for
that convention is defined here: `Challenge.Certify.certify?` takes the declared method
(`Spec.Certify.MSMethod`) and certifies nothing unless it is the centred one.

`Challenge.Budget` pins that these budgets are achievable from the ciphertext and the keys alone
(for every number of components), that the gadget factor satisfies the reconstruction identity,
and that every program the reference analysis accepts at the certified budget has a run.
-/

namespace Spec.Budget
open NPoly Scheme Source

/-- The layout of hybrid key switching: `sizes ℓ` lists the number of limbs of each digit at
level `ℓ`, in order (digit `0` is the first `sizes[0]` limbs, digit `1` the next `sizes[1]`, …).
`canonical` says which representatives ModUp and ModDown use: `false` for centred ones, `true`
for canonical ones (`[0, q)`), which cost about a factor two in the bound.

`sizes` is an arbitrary function of the level: nothing in this structure relates the digits of
one level to those of another. A real implementation generates one set of keys at the top level
`L` (modulo `Q_L·P`) and at level `ℓ` uses its first digits, the same integers read modulo
`Q_ℓ·P`. **When that is valid** (`Challenge.Budget.gadgetKeys_restrict`; the conditions are
sufficient, and neither can be dropped, but they are not necessary): if

1. the layout is usable at the top level and the digits of level `ℓ` are the top-level digits cut
   down to the first `ℓ` limbs (`restrictsTo lay L ℓ` below; `uniformLayout` satisfies it at every
   level `ℓ ≤ L`, `Challenge.Budget.uniformLayout_restrictsTo`), and
2. for BGV, `2·(⌊B/t⌋·t) < Q_ℓ·P` with `B` the key noise (so that a top-level key error, a
   multiple of `t` within `B`, is its own centred representative modulo `Q_ℓ·P` and stays a
   multiple of `t`; BFV needs no such condition),

then valid top-level gadget keys, cut to the first `(sizes ℓ).length` of them, are valid
level-`ℓ` gadget keys for the same secret and target with the same noise bound, and the
realizability pins hold with one top-level key set (`Challenge.Budget.relin_realizable_top`,
`keySwitch_realizable_top`). Neither hypothesis can be dropped
(`Challenge.Budget.gadgetKeys_restrict_needs_restrictsTo`, `gadgetKeys_restrict_needs_size_bgv`).
Without them the per-level pins `relin_realizable`, `keySwitch_realizable` are about keys
generated for each level's own digits, which no library does. So `Challenge.Certify.certify?`
checks both at every level of the chain (`Spec.Certify.layoutOK?`, `keysRestrict?`;
`Challenge.Certify.certify?_keys_restrict`) and certifies nothing for a layout that does not
restrict. -/
structure KSLayout where
  sizes : ℕ → List ℕ
  canonical : Bool := false

/-- The layout is usable at level `ℓ`: the digits are nonempty and cover exactly `ℓ` limbs. -/
def KSLayout.okAt (lay : KSLayout) (ℓ : ℕ) : Bool :=
  (lay.sizes ℓ).sum == ℓ && (lay.sizes ℓ).all (0 < ·)

/-- The digit sizes `S` cut down to the first `n` limbs: the digits that start below `n`, the last
of them shortened to end at `n`. `cutSizes [2, 2, 1] 3 = [2, 1]`, `cutSizes [3] 2 = [2]`. -/
def cutSizes : List ℕ → ℕ → List ℕ
  | [], _ => []
  | s :: ss, n => if n = 0 then [] else if n ≤ s then [n] else s :: cutSizes ss (n - s)

/-- The layout is usable at the top level `L` and its digits at level `ℓ` are the top-level
digits cut down to the first `ℓ` limbs: digit `j` at level `ℓ` consists of the limbs below `ℓ` of
top-level digit `j`, for every `j` that has such limbs. (Hypothesis 1 of key restriction, in the
docstring of `KSLayout`.) -/
def restrictsTo (lay : KSLayout) (L ℓ : ℕ) : Bool :=
  lay.okAt L && lay.sizes ℓ == cutSizes (lay.sizes L) ℓ

/-- Digits of `α` consecutive limbs, the last one shorter if `α ∤ ℓ` (OpenFHE: `α = ⌈L/dnum⌉`). `α = 0` means a single digit. -/
def uniformLayout (α : ℕ) (canonical : Bool := false) : KSLayout where
  sizes ℓ := List.replicate (ℓ / α) α ++ (if ℓ % α = 0 then [] else [ℓ % α])
  canonical := canonical

/-- The product `P` of the special primes. -/
def specialProd (P : FullParams) : ℕ := (P.store.special.map (·.q)).prod

/-- The modulus `Qⱼ` of digit `j` at level `ℓ`: the product of its limbs. -/
def digitModulus (P : FullParams) (lay : KSLayout) (ℓ j : ℕ) : ℕ :=
  (((P.src.qs.take ℓ).drop ((lay.sizes ℓ).take j).sum).take ((lay.sizes ℓ).getD j 0)).prod

/-- The digit moduli `Q₀, Q₁, …` at level `ℓ`. -/
def digitModuli (P : FullParams) (lay : KSLayout) (ℓ : ℕ) : List ℕ :=
  (List.range (lay.sizes ℓ).length).map (digitModulus P lay ℓ)

/-- The gadget entry `gⱼ = P · Q̂ⱼ · [Q̂ⱼ⁻¹]_{Qⱼ}` for digit moduli `Qs` and special modulus
`Pm`, with `Q̂ⱼ` the product of the other digit moduli and the inverse taken in `[0, Qⱼ)`.
(`Challenge.Budget.gadgetFactor_reconstruct`: `Σⱼ Dⱼ·gⱼ ≡ P·X (mod Q·P)` whenever
`Dⱼ ≡ X (mod Qⱼ)`.) -/
def gadgetFactor (Pm : ℕ) (Qs : List ℕ) (j : ℕ) : ℕ :=
  let hat := (Qs.eraseIdx j).prod
  Pm * hat * ((hat : ZMod (Qs.getD j 1))⁻¹).val

/-- The key hybrid key switching needs for digit `j` at level `ℓ`: modulo `Q_ℓ · P`, encrypting
`gⱼ · target(s)`. -/
def gadgetReq (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (tgt : KeyTarget) (j : ℕ) :
    KeyReq P.src.N where
  modulus := P.src.modulus ℓ * specialProd P
  factor := const ((gadgetFactor (specialProd P) (digitModuli P lay ℓ) j : ℕ) :
    ZMod (P.src.modulus ℓ * specialProd P))
  target := tgt

/-- One key pair `(b, a)` per digit (integer representatives), each
valid for `s` with noise at most `P.keyNoise` for its gadget requirement. -/
def GadgetKeysOK (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (tgt : KeyTarget)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : Prop :=
  keys.length = (lay.sizes ℓ).length ∧
    ∀ j (h : j < keys.length),
      KeyValid P.src.kind P.src.t P.keyNoise s (gadgetReq P lay ℓ tgt j)
        (ofInt _ keys[j].1) (ofInt _ keys[j].2)

/-- What key switching needs of the special primes (a scheme-level matter: no bound on their
size, no roots of unity): each is at least `2` and odd (so at least `3`), they are pairwise
coprime, coprime to every ciphertext prime and to the plaintext modulus.

Odd, because at an even special modulus the centred representative has a tie (`y = p/2`,
`−y ≡ y`), and two ways of writing the centred ModDown that agree everywhere else differ there:
adding `t·[−X·t⁻¹]_P` (`FHE.KeySwitch.keySwitchBGV`) and subtracting `t·[X·t⁻¹]_P` (OpenFHE with
`WITH_REDUCED_NOISE`; `Respec.Equiv.centredModDown_differs'` at `P = 2`). For odd special primes
they are equal (`Respec.Equiv.keySwitch_centred_eq`). Every special prime of a real parameter set
is an odd NTT prime, so nothing real is excluded.

**The special moduli are not required to be prime**, although they are called special primes
throughout. The theorems that take `SpecialOK` (`Challenge.Budget.relin_realizable`,
`keySwitch_realizable`, `certified_run_exists`, and through `Challenge.Certify.certify?_paramsOK`
every statement about a certificate) are proved from exactly the four clauses below, and that
suffices because key switching uses the special moduli only through the Chinese remainder
theorem and three inversions: residues modulo the `p_j` and the `q_i` determine a residue modulo
`Q·P` (pairwise coprime moduli, each at least `2`); ModDown divides by `P` modulo every `q_i`
(`P` invertible there: coprime to every `q_i`); and the BGV correction `t·[X·t⁻¹]_P` needs `t`
invertible modulo every `p_j` (coprime to `t`). A composite special modulus meeting the clauses
is covered; one that shares a factor with another modulus or with `t` is not.

**An empty list is accepted**: then `P = 1` (`specialProd`), ModUp and ModDown do nothing, and
`ksBoundAt` is the bound of key switching by digit decomposition without a special modulus,
`⌊N·B_k·Σⱼ ℓⱼ·Qⱼ / 2⌋` for centred representatives: proportional to the largest digit modulus,
so only programs whose remaining noise budget exceeds a whole digit can be certified. This is
not what a library configured for hybrid key switching runs (there the list is nonempty; the
OpenFHE frontend refuses any other key-switching technique); it is the case of every example at
`FullParams.tinyBGV` (`Challenge.Certify.certify?_accepts_runDemo`), and the same examples
with one special prime are in the guards of `Challenge.Certify`. -/
def SpecialOK (P : FullParams) : Prop :=
  (∀ p ∈ P.store.special.map (·.q), 2 ≤ p ∧ p % 2 = 1) ∧
  (P.store.special.map (·.q)).Pairwise Nat.Coprime ∧
  (∀ p ∈ P.store.special.map (·.q), ∀ q ∈ P.src.qs, Nat.Coprime p q) ∧
  (∀ p ∈ P.store.special.map (·.q), Nat.Coprime P.src.t p)

/-- Whether `ps` are pairwise coprime (compiled check). -/
def pairwiseCoprime? : List ℕ → Bool
  | [] => true
  | p :: ps => ps.all (fun q => Nat.gcd p q == 1) && pairwiseCoprime? ps

/-- Decides `SpecialOK` (soundness: `Challenge.Budget.specialOK?_sound`). -/
def specialOK? (P : FullParams) : Bool :=
  let ps := P.store.special.map (·.q)
  ps.all (fun p => decide (2 ≤ p ∧ p % 2 = 1)) && pairwiseCoprime? ps &&
    ps.all (fun p => P.src.qs.all fun q => Nat.gcd p q == 1) &&
    ps.all (fun p => Nat.gcd P.src.t p == 1)

/-- The worst-case phase error of one hybrid key switch at level `ℓ` (module docstring). -/
def ksBoundAt (P : FullParams) (lay : KSLayout) (ℓ : ℕ) : ℕ :=
  let k := P.store.special.length
  let Pm := specialProd P
  let w : ℕ → ℕ → ℕ := fun n Q => if lay.canonical then 2 * (n * (Q - 1)) else n * Q
  let F : ℕ := if lay.canonical then 2 * (k * (Pm - 1)) else k * Pm
  (P.src.N * P.keyNoise * (List.zipWith w (lay.sizes ℓ) (digitModuli P lay ℓ)).sum +
      P.src.t * F * (1 + P.src.N * P.secretBound)) / (2 * Pm)

/-- The key-switching budget: the largest `ksBoundAt` over the levels `1, …, L` of the chain. -/
def ksBudget (P : FullParams) (lay : KSLayout) : ℕ :=
  ((List.range P.src.qs.length).map fun i => ksBoundAt P lay (i + 1)).foldl max 0

/-- The modulus-switching budget of a two-component ciphertext:
`⌈t · (1 + N · secretBound) / 2⌉`. For the centred correction only (module docstring). -/
def msBudget (P : FullParams) : ℕ := (P.src.t * (1 + P.src.N * P.secretBound) + 1) / 2

/-- The modulus-switching budget of a one-component value (a plaintext operand): `⌈t / 2⌉`. The
correction is `t·[−p·t⁻¹]_q`, centred, with no secret-dependent term. For the centred correction
only (module docstring). -/
def msBudgetOne (P : FullParams) : ℕ := (P.src.t + 1) / 2

/-- The modulus-switching budget of a value with `k` components:
`⌈t · Σ_{i<k} (N · secretBound)ⁱ / 2⌉` (module docstring). `msBudgetAt P 1 = msBudgetOne P` and
`msBudgetAt P 2 = msBudget P` (`Challenge.Budget.msBudgetAt_one`, `msBudgetAt_two`). For the
centred correction only (module docstring). -/
def msBudgetAt (P : FullParams) (k : ℕ) : ℕ :=
  (P.src.t * ((List.range k).map fun i => (P.src.N * P.secretBound) ^ i).sum + 1) / 2

/-- The certified budget of a parameter set and a key-switching layout: `ksBudget` for a key
switch, `msBudgetAt P k` for a modulus switch of a value with `k` components (through
`Trace.Budget.modSwitchAt`: `msBudgetOne` at `k = 1`, `msBudget` at `k = 2`, `msBudgetAt P k`
otherwise). -/
def certified (P : FullParams) (lay : KSLayout) : Trace.Budget :=
  ⟨ksBudget P lay, msBudget P, msBudgetOne P, msBudgetAt P⟩

end Spec.Budget
