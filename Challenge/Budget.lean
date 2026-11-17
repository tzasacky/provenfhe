import Spec.Budget
import Challenge.Headline.Defs

/-!
# Challenge.Budget — the certified budget   (LOCKED statements; proofs in `Validation/`)

The noise headline (`Challenge.Headline.NoiseSoundBGV`) is about every run whose key switches and
modulus switches stay within a budget `E`. `Spec.Budget` computes a budget from the parameters
and the key-switching layout. These pins say that budget is the right one:

* `relin_realizable`, `keySwitch_realizable`: at every level there is a function of the operand
  ciphertext and the key-switching keys alone (it is fixed before the secret is) whose output
  meets the `relin` / `keySwitch` contract of `Spec.Trace.StepOK` for every budget of at least
  `ksBoundAt` at that level, for every secret within the bound and every list of gadget keys
  valid for it with noise at most `P.keyNoise`. Only trusted definitions occur in the statements:
  what the function is (RNS hybrid key switching, `FHE/KeySwitch`) is the proof's business. These
  take keys generated for the level's own digits; with one key set generated at the top level, as
  libraries do: `relin_realizable_top`, `keySwitch_realizable_top` (`Challenge/BudgetRestrict.lean`).
* `modSwitch_realizable_parts`: the same for `modSwitch` of a value with any number `k` of
  components and `msBudgetAt P k` (no keys); `modSwitch_realizable` (`k = 2`, `msBudget`) and
  `modSwitch_realizable_one` (`k = 1`, `msBudgetOne`, and no bound on the secret) are the two
  cases with their own fields in `Trace.Budget`. `msBudgetAt_one`, `msBudgetAt_two`,
  `certified_modSwitchAt`: the certified budget charges `msBudgetAt P k` for every `k`.
* `ksBoundAt_le_ksBudget`: `ksBudget` covers every level of the chain, so the statements above
  hold with `E = Spec.Budget.certified P lay`.
* `gadgetFactor_reconstruct`: the gadget factor the keys are required to encrypt satisfies the
  reconstruction identity `Σⱼ Dⱼ·gⱼ ≡ P·X (mod Q·P)`; `specialOK?_sound`, `uniformLayout_ok`: the
  side conditions can be decided by running a program.
* `certified_sound`: the noise headline at the certified budget, for the reference analyzer.
* `wellFormed_run_exists`, `certified_run_exists`: every well-formed BGV program, in particular
  every program the reference analyzer accepts at the certified budget, has a ciphertext-level
  run at the certified budget from every valid input, so `certified_sound` is about at least one
  run for each accepted program.

The realizability pins need `SchemeParamsOK`, and for key switching `SpecialOK` and a layout
usable at the level (`lay.okAt ℓ`); the top-level versions `relin_realizable_top`,
`keySwitch_realizable_top` need instead `restrictsTo lay L ℓ` and the key-size condition
`2·(⌊keyNoise/t⌋·t) < Q_ℓ·P`. No bound on the size of the primes.

**The budget depends on the number of components.** An earlier version charged the
two-component budget `msBudget` for a modulus switch of any ciphertext. That was wrong for a
product that has not been relinearized: the textbook switch of three components corrects three
components, and the correction of the phase has the extra term `s²·δ₂`. The section "The
many-component budget is needed" below reproduces the counterexample.
-/

namespace Challenge.Budget
open Spec NPoly Scheme Source Correct Spec.Budget Challenge.Headline

/-! ## Side conditions -/

theorem specialOK?_sound (P : FullParams) (h : specialOK? P = true) : SpecialOK P := sorry

/-- Uniform digits are a usable layout at every level. -/
theorem uniformLayout_ok (α : ℕ) (c : Bool) (ℓ : ℕ) : (uniformLayout α c).okAt ℓ = true := sorry

/-- A usable layout has as many digit moduli as digits, and their product is the modulus of the
level. -/
theorem digitModuli_prod (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (hlay : lay.okAt ℓ = true) :
    (digitModuli P lay ℓ).length = (lay.sizes ℓ).length ∧
      (digitModuli P lay ℓ).prod = P.src.modulus ℓ := sorry

/-! ## The gadget -/

/-- **Reconstruction identity.** For pairwise coprime positive digit moduli `Qs` (product `Q`)
and any integers `Dⱼ ≡ X (mod Qⱼ)` (the digits of `X`, with whatever overflow their extension to
the other moduli has): `Σⱼ Dⱼ · gⱼ ≡ P · X (mod Q · P)`. -/
theorem gadgetFactor_reconstruct (Pm : ℕ) (Qs : List ℕ) (hpos : ∀ q ∈ Qs, 0 < q)
    (hcop : Qs.Pairwise Nat.Coprime) (X : ℤ) (D : ℕ → ℤ)
    (hD : ∀ j (h : j < Qs.length), (Qs[j] : ℤ) ∣ D j - X) :
    ((Qs.prod * Pm : ℕ) : ℤ) ∣
      (∑ j ∈ Finset.range Qs.length, D j * (gadgetFactor Pm Qs j : ℤ)) - Pm * X := sorry

/-! ## Realizability with the computed budget -/

/-- **Relinearization within `ksBoundAt`.** -/
theorem relin_realizable (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)), GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := sorry

/-- **Key switching within `ksBoundAt`.** The operand is under `σ_g(s)`, `g` its recorded key;
the keys are valid for the target `σ_g(s)`. The function is fixed before `g` is. -/
theorem keySwitch_realizable (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := sorry

/-- The one-component case of `msBudgetAt`. -/
theorem msBudgetAt_one (P : FullParams) : msBudgetAt P 1 = msBudgetOne P := sorry

/-- The two-component case of `msBudgetAt`. -/
theorem msBudgetAt_two (P : FullParams) : msBudgetAt P 2 = msBudget P := sorry

/-- The certified budget charges `msBudgetAt P k` for a modulus switch of `k` components, for
every `k`. -/
theorem certified_modSwitchAt (P : FullParams) (lay : KSLayout) (k : ℕ) :
    (certified P lay).modSwitchAt k = msBudgetAt P k := sorry

/-- **Modulus switching of any number of components within `msBudgetAt`.** For every level `ℓ`
and every number of components `k` there is a function of the operand ciphertext alone (the
textbook switch of every component, `Challenge.Trace.stepOK_modSwitch_textbook_parts`) that meets
the `modSwitch` contract for every budget whose bound for `k` components
(`Trace.Budget.modSwitchAt`) is at least `msBudgetAt P k = ⌈t · Σ_{i<k} (N · secretBound)ⁱ / 2⌉`,
for every secret within the bound and under every Galois conjugate of it. (That the level is
inside the chain is part of `step` succeeding.) -/
theorem modSwitch_realizable_parts (P : FullParams) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (ℓ k : ℕ) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), msBudgetAt P k ≤ E.modSwitchAt k →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = k → ca.length = k →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := sorry

/-- **Modulus switching within `msBudget`** (two-component ciphertexts): the case `k = 2` of
`modSwitch_realizable_parts`. -/
theorem modSwitch_realizable (P : FullParams) (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (ℓ : ℕ) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), msBudget P ≤ E.modSwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = 2 → ca.length = 2 →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := sorry

/-- **Modulus switching of a one-component value within `msBudgetOne`.** A one-component value
`[p]` (a plaintext operand; OpenFHE's automatic scaling modes modulus-switch it before a
plaintext operation) has phase `p` under every key. Its textbook switch is `(p + δ) / q` with
`δ = t·[−p·t⁻¹]_q` centred, so `‖δ‖∞ ≤ t·⌊q/2⌋ ≤ q·⌈t/2⌉`: no secret-dependent term, and the
statement needs no bound on the secret (which is what it adds to the case `k = 1` of
`modSwitch_realizable_parts`). -/
theorem modSwitch_realizable_one (P : FullParams) (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (ℓ : ℕ) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), msBudgetOne P ≤ E.modSwitchOne →
      ∀ (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = 1 → ca.length = 1 →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := sorry

/-- `ksBudget` is at least `ksBoundAt` at every level of the chain. -/
theorem ksBoundAt_le_ksBudget (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) : ksBoundAt P lay ℓ ≤ ksBudget P lay := sorry

/-- The canonical-representative bound is never below the centred one (same digits): a budget
computed for a library that uses canonical representatives also covers the centred algorithm. -/
theorem ksBoundAt_le_canonical (P : FullParams) (hS : SpecialOK P) (hP : SchemeParamsOK P)
    (sizes : ℕ → List ℕ) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : (KSLayout.mk sizes false).okAt ℓ = true) :
    ksBoundAt P ⟨sizes, false⟩ ℓ ≤ ksBoundAt P ⟨sizes, true⟩ ℓ := sorry

/-! ## The budget is not vacuously large

`exampleBGV31`: `N = 2¹⁴`, `t = 65537`, `keyNoise = 2²¹`, two 31-bit ciphertext primes and one 31-bit
special prime (each just above `2³⁰`). With one limb per digit the key-switching budget is about `2³⁵`, far below
`Q/2 ≈ 2⁵⁹`; the modulus-switching budget is about `2²⁹`. With a single two-limb digit and one
special prime the budget is about `2⁶⁵`, above `Q`: that layout cannot work at these parameters
(the special modulus must be about as large as the largest digit), and the number says so. -/

#guard ksBoundAt .exampleBGV31 (uniformLayout 1) 1 == 17659309320
#guard ksBoundAt .exampleBGV31 (uniformLayout 1) 2 == 34787976413
#guard ksBudget .exampleBGV31 (uniformLayout 1) == 34787976413
#guard ksBudget .exampleBGV31 (uniformLayout 1) < 2 ^ 36
#guard ksBudget .exampleBGV31 (uniformLayout 1 true) == 69575952761
#guard msBudget .exampleBGV31 == 536911873
-- The one-component budget has no `N · secretBound` term: `⌈t/2⌉ = 32769`, 14 bits below.
#guard msBudgetOne .exampleBGV31 == 32769
#guard (certified .exampleBGV31 (uniformLayout 1)).modSwitchOne == 32769
-- The budget by number of components: `⌈t·Σ_{i<k} N^i/2⌉` (`secretBound = 1`). For `k = 3` it is
-- about `2⁴³`, 14 bits above the two-component budget: at `exampleBGV31` (`Q ≈ 2⁶⁰`, 31-bit primes)
-- a modulus switch before relinearization cannot be certified, and the analysis says so.
#guard [1, 2, 3, 4].map (msBudgetAt .exampleBGV31) ==
  [32769, 536911873, 8796764151809, 144126183863263233]
#guard [1, 2, 3, 4].map (certified .exampleBGV31 (uniformLayout 1)).modSwitchAt ==
  [32769, 536911873, 8796764151809, 144126183863263233]
#guard [0, 1, 2, 3, 4].map (msBudgetAt Spec.FullParams.tinyBGV) == [0, 9, 43, 179, 723]
#guard refAnalyze .exampleBGV31 (certified .exampleBGV31 (uniformLayout 1))
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .modSwitch "c" "c"], outputs := ["c"] } == none
#guard 2 ^ 64 < ksBudget .exampleBGV31 (uniformLayout 2)
#guard specialOK? .exampleBGV31
#guard (uniformLayout 3).sizes 8 == [3, 3, 2]
#guard (uniformLayout 0).sizes 8 == [8]
#guard digitModuli .exampleBGV31 (uniformLayout 1) 2 == [1073872897, 1074266113]
#guard digitModuli .exampleBGV31 (uniformLayout 2) 2 == [1073872897 * 1074266113]
-- The gadget for two one-limb digits and `P = 1`: `g₀ ≡ 1 (mod 5)`, `g₀ ≡ 0 (mod 7)`, and so on.
#guard [gadgetFactor 1 [5, 7] 0, gadgetFactor 1 [5, 7] 1] == [21, 15]
#guard gadgetFactor 3 [5, 7] 0 == 63
-- Tensor product and relinearization at `exampleBGV31`, at the certified budget:
-- `N · inputNoise² + ksBudget = 2⁵⁶ + 34787976413`. A modulus switch down to the single prime
-- `q₀ ≈ 2³⁰` is rejected: `⌊· / q₁⌋ + msBudget = 67076144 + 536911873` is above `q₀/2` (the
-- rounding term `t·(1 + N)/2 ≈ 2²⁹` alone is nearly `q₀/2`; `q₀` is a 31-bit prime just above
-- `2³⁰`).
#guard refAnalyze .exampleBGV31 (certified .exampleBGV31 (uniformLayout 1))
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c"], outputs := ["c"] } == some (2 ^ 56 + 34787976413)
#guard refAnalyze .exampleBGV31 (certified .exampleBGV31 (uniformLayout 1))
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c", .modSwitch "c" "c"], outputs := ["c"] }
  == none
#guard (2 ^ 56 + 34787976413) / 1074266113 + 536911873 == 603988017
#guard 1073872897 < 2 * 603988017
-- With the single-digit layout the same program is rejected (the budget alone exceeds `Q/2`).
#guard refAnalyze .exampleBGV31 (certified .exampleBGV31 (uniformLayout 2))
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c"], outputs := ["c"] } == none

/-! ## The many-component budget is needed

The counterexample to charging the two-component budget for
every ciphertext. At `tinyBGV` (`N = 4`, `t = 17`, `Q = 65537 · 786433`, secret bound 1), take the
secret `s = 1 + X + X² + X³` and two noiseless encryptions of `0` (components
`[−a·s mod Q, a]`, `a` pseudo-random); their tensor product has three components and phase `0`.
The textbook t-corrected switch of the three components to the modulus `65537` then has noise
`85`: twice what the two-component budget `msBudget FullParams.tinyBGV = 43` allows for (the old analysis
promised `⌊0/q⌋ + 43`), and within the three-component budget `msBudgetAt FullParams.tinyBGV 3 = 179`. (The
guard shows that the two-component budget is exceeded; it does not show that 179 is attained, and
no such claim is made: `msBudgetAt` is an upper bound over all secrets within the bound.) -/

/-- The witness secret `1 + X + X² + X³` (ternary). -/
def ms3Key : IntPoly 4 := ⟨fun _ => 1⟩

/-- The witness modulus `Q = 65537 · 786433` (`tinyBGV` at level 2). -/
def ms3Q : ℕ := 65537 * 786433

/-- A linear congruential generator, for reproducible pseudo-random components. -/
def ms3Lcg (x : ℕ) : ℕ := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A pseudo-random polynomial with coefficients in `[0, Q)`. -/
def ms3Rnd (seed : ℕ) : IntPoly 4 :=
  let a := ms3Lcg seed; let b := ms3Lcg a; let c := ms3Lcg b; let d := ms3Lcg c
  ⟨fun i => (([a, b, c, d].getD i.val 0 % ms3Q : ℕ) : ℤ)⟩

/-- A noiseless encryption of `0` under `ms3Key`: `[−a·s mod Q, a]`, phase exactly `0`. -/
def ms3Enc0 (seed : ℕ) : List (IntPoly 4) :=
  let a := ms3Rnd seed
  [centered (ofInt ms3Q (-(a * ms3Key))), a]

/-- The noise before and after the textbook switch of the three-component tensor product of two
noiseless encryptions of `0`: `(‖phase mod Q‖∞, ‖phase of the switched ciphertext mod 65537‖∞)`. -/
def ms3Noise (seed : ℕ) : ℕ × ℕ :=
  let ca := (Challenge.Source.tensor (ms3Enc0 seed) (ms3Enc0 (seed + 1000))).map
    fun c => centered (ofInt ms3Q c)
  let ct' := ca.map (Challenge.Source.bgvModSwitchComp 17 786433)
  (normInf (centeredPhase ms3Key (ca.map (ofInt ms3Q))),
   normInf (centeredPhase ms3Key (ct'.map (ofInt 65537))))

-- The operand has three components and noise 0; after the switch the noise is 85.
#guard ms3Noise 19 == (0, 85)
#guard (Challenge.Source.tensor (ms3Enc0 19) (ms3Enc0 1019)).length == 3
#guard normInf ms3Key ≤ Spec.FullParams.tinyBGV.secretBound
-- 85 is above what the two-component budget allows, and within the three-component budget.
#guard msBudget Spec.FullParams.tinyBGV == 43
#guard msBudgetAt Spec.FullParams.tinyBGV 3 == 179
#guard 0 / 786433 + msBudget Spec.FullParams.tinyBGV < (ms3Noise 19).2
#guard (ms3Noise 19).2 ≤ 0 / 786433 + msBudgetAt Spec.FullParams.tinyBGV 3

/-! ## The headline at the certified budget -/

/-- A program with a tensor product, a relinearization, a rotation (automorphism and key switch)
and a modulus switch. -/
def runDemoProg : Source.Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c", .automorph "c" "c" 3, .keySwitch "c" "c",
             .modSwitch "c" "c"],
    outputs := ["c"] }

-- The reference analysis accepts `runDemoProg` at the certified budget of `tinyBGV` (one limb per
-- digit; `tinyBGV` has no special prime, so the key-switching budget is large, `≈ 2²⁷`, and still
-- far below `Q/2 ≈ 2³⁵`), and the side conditions of `certified_run_exists` hold there: that
-- theorem is about at least this program. It is also about the three-component modulus switch
-- of the section above (`Challenge.Headline`: bound 179), and about a four-component one.
#guard ksBudget Spec.FullParams.tinyBGV (uniformLayout 1) == 109052160
#guard refAnalyze Spec.FullParams.tinyBGV
  (certified Spec.FullParams.tinyBGV (uniformLayout 1)) runDemoProg == some 320
#guard (16384 + 2 * 109052160) / 786433 + 43 == 320
#guard schemeParamsOK? Spec.FullParams.tinyBGV && specialOK? Spec.FullParams.tinyBGV
#guard refAnalyze Spec.FullParams.tinyBGV
  (certified Spec.FullParams.tinyBGV (uniformLayout 1))
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .mul "c" "c" "a", .modSwitch "c" "c"], outputs := ["c"] }
  == some (4 * 16384 * 64 / 786433 + 723)

/-- **Noise soundness at the certified budget.** If the parameters are valid at the scheme level
and the reference analysis, run with the budget computed from the parameters and the layout,
returns `B`, then for every secret, all messages and all input ciphertexts within their bounds,
every ciphertext-level run in which each key switch adds at most `ksBudget P lay` and each modulus
switch of a value with `k` components at most `msBudgetAt P k` (`msBudgetOne P` for `k = 1`,
`msBudget P` for `k = 2`) ends with every output encrypting what `Source.eval` computes, with
noise at most `B`.

What this theorem does not say is that such a run exists: it would hold just as well for a budget
that no algorithm meets. That the contracts *are* met at this budget is the content of the
realizability pins:

* `relin`, `keySwitch`: `relin_realizable`, `keySwitch_realizable` (hybrid key switching on the
  digits of `lay`, given `SpecialOK P`, a level `1 ≤ ℓ ≤ L` with `lay.okAt ℓ`, and gadget keys
  valid for the secret at that level; with one top-level key set: `relin_realizable_top`,
  `keySwitch_realizable_top`) with `ksBoundAt_le_ksBudget`;
* `modSwitch` of `k` components, any `k`: `modSwitch_realizable_parts` with
  `certified_modSwitchAt` (`k = 2`: `modSwitch_realizable`; `k = 1`: `modSwitch_realizable_one`);
* every other instruction, for all numbers of components `Source.step` accepts: the textbook
  pins of `Challenge.Trace` (table in its module docstring);

and of `certified_run_exists` below, which puts them together: for *every* program the reference
analysis accepts at the certified budget and every valid input there is a run. (`SpecialOK` and
the usability of the layout are hypotheses there; this theorem does not need them, because here a
run whose key switches meet the budget is assumed, not constructed.)

(`FHE.Holes.analyze` is the reference analyzer: `Challenge.Headline.analyze_tight`,
`analyze_sound`.) -/
theorem certified_sound (P : FullParams) (lay : KSLayout) (prog : Source.Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (h : refAnalyze P (certified P lay) prog = some B)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, Trace.Run P (certified P lay) s prog.body (initEnv P.src prog msgs)
          (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct := sorry

/-- **Every well-formed program has a run at the certified budget.** If the parameters are valid
at the scheme level, the special primes are usable (`SpecialOK`), the layout is usable at every
level of the chain, and the BGV program is well formed (`Source.eval` succeeds), then for every
secret within the bound and all input ciphertexts with the declared numbers of components there
is a ciphertext-level run of the whole program in which every step meets its `Spec.Trace`
contract at the certified budget.

The run is the textbook one: padded componentwise sums and differences, tensor products
(`Challenge.Source.tensorParts`), componentwise automorphisms, the t-corrected switch of every
component for `modSwitch` (any number of components, within `msBudgetAt`), and RNS hybrid key
switching on the digits of `lay` for `relin` and `keySwitch`, with gadget keys chosen in the
proof (valid keys exist for every secret: `Challenge.Scheme.keyValid_exists`; the noiseless ones
are used, and any other valid keys would do as well, by `relin_realizable` and
`keySwitch_realizable`).

The contracts of `Spec.Trace` constrain the phase a step adds, not the noise that has
accumulated, so nothing here depends on the noise of the inputs or on whether the analysis
accepts: a run exists even where the noise has outgrown the modulus (and `certified_sound` then
says nothing, because the analysis rejects). Why each hypothesis is there. `hS`, `hlay`: key
switching (not needed for a program without `relin` and `keySwitch`; `Source.eval` and the
analysis do not check the layout or the special primes, so they cannot be dropped in general).
`hs`: the modulus-switching and key-switching budgets are bounds for secrets within
`P.secretBound`. `hlen`: a step's operands must have the recorded numbers of components. -/
theorem wellFormed_run_exists (P : FullParams) (lay : KSLayout) (prog : Source.Program)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (hS : SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (msgs : Var → Msg P.src.t P.src.N) (ρ : Env P.src)
    (h : Source.eval P.src prog msgs = some ρ)
    (cts : Var → List (IntPoly P.src.N))
    (hlen : ∀ x d, prog.inputs.find? (·.name = x) = some d → (cts x).length = d.parts) :
    ∃ σ, Trace.Run P (certified P lay) s prog.body (initEnv P.src prog msgs)
      (Trace.initCt P prog cts) σ := sorry

/-- **Every accepted program has a run.** If the parameters are valid at the scheme level, the
special primes are usable, the layout is usable at every level of the chain, and the reference
analysis accepts `prog` at the certified budget, then for every secret within the bound and all
input ciphertexts encrypting their messages with noise at most `P.inputNoise` there is a
ciphertext-level run of the whole program in which every step meets its `Spec.Trace` contract at
the certified budget. So the "for every run" of `certified_sound` is never about no runs: not
for one accepted program. (An instance of `wellFormed_run_exists`: acceptance and `InputsOK`
give well-formedness and the numbers of components. `Trace.BoundsOK` is not needed, and the
number `B` plays no role: only acceptance does.) -/
theorem certified_run_exists (P : FullParams) (lay : KSLayout) (prog : Source.Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (hS : SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (h : refAnalyze P (certified P lay) prog = some B)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : InputsOK P s prog msgs cts) :
    ∃ σ, Trace.Run P (certified P lay) s prog.body (initEnv P.src prog msgs)
      (Trace.initCt P prog cts) σ := sorry

end Challenge.Budget
