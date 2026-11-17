import Challenge.Profile.Defs

/-!
# Challenge.Instances.Lattigo.Defs — the implementation profile of Lattigo's BGV   (LOCKED definitions)

The second library read through the profile interface of `Challenge.Profile.Defs`: Lattigo
v6.2.0 (`github.com/tuneinsight/lattigo`, tag `v6.2.0`, commit `c1fd095f`), package
`schemes/bgv`, with the default distributions and RNS gadget decomposition only
(`BaseTwoDecomposition = 0`). Source locations below are paths in that tree, `file:line`.

**The reading.** Lattigo's BGV is the MSB form of the scheme (`schemes/bgv/README.md`): a
ciphertext `c` at level `ℓ` (Lattigo's `Level() = ℓ − 1`) has phase `[c₀ + c₁·s]_Q = T⁻¹·p + e`
with `p` the stored plaintext representative and `e` the error, not multiplied by `t`. Multiplying
every component by `t` modulo `Q` (the *t-reading*) gives a textbook (LSB) BGV ciphertext with
phase `p + t·e`, which is what `Spec.Trace` is about. Under the t-reading:

* an error `e` that a Lattigo key switch adds is the LSB error `t·e` (divisible by `t`, as the
  contract asks);
* Lattigo's `Rescale` (`schemes/bgv/evaluator.go:1363-1393`: `DivRoundByLastModulusNTT` on every
  component, the centred rounding `(c − [c]_q)/q`) is exactly the centred t-corrected modulus
  switch: with `c' = t·c` the correction `t·[−c'·t⁻¹]_q = t·[−c]_q` is `t` times Lattigo's;
* the BGV tensor product is exact on phases (no error).

**Key switching** (`core/rlwe/evaluator_gadget_product.go:108-127` dispatch,
`:129-201` several special primes, `:203-…` one special prime). The level-`ℓ` limbs are split into
consecutive digits of `#P` limbs, the last one shorter (`core/rlwe/params.go:543-550`,
`BaseRNSDecompositionVectorSize = ⌈ℓ / #P⌉`; with no special prime one limb per digit), each digit
lifted to `Q·P` with centred representatives (`ring/basis_extension.go:381-470`,
`DecomposeAndSplit`: one-limb digits centred at l.421, several-limb digits by an exact base
conversion offset by `⌊Q_j/2⌋`), multiplied by the key and divided by `P` with rounding. With key
errors `|e| ≤ 19` and a ternary secret the MSB error is at most
`N·19·Σⱼ ℓⱼ·Qⱼ/(2P) + #P·(1 + N)/2`, and `t` times this is `Spec.Budget.ksBoundAt` at the layout
`layout P` (centred representatives) with `keyNoise = 19·t` and `secretBound = 1`. That
derivation is now a theorem about the MSB transcription of `Spec.MSB`
(`Challenge.Instances.Lattigo.relin_meets_msb`, `keySwitch_meets_msb`, and their t-readings
`relin_meets_lsb`, `keySwitch_meets_lsb`, from `Challenge.MSB`). Still argued or executed, not
proved: that Lattigo's Go code computes that transcription (including the binary64 `ModUpExact`
and the fused `Automorphism`), the fresh-encryption error bounds, and `BaseTwoDecomposition ≠ 0`
(`harness/lattigo-pin` records runs at small ring dimension).

**Error distribution** (`core/rlwe/security.go:10,13,17`: `DefaultNoise = 3.2`,
`DefaultNoiseBound = 19.2`, `DefaultXe`; `ring/sampler_gaussian.go:161-164`: a sample is rejected
unless `|v| ≤ 19.2` and then rounded, `uint64(v + 0.5)`, so `|e| ≤ 19`). Secret and encryption
randomness `u` ternary (`core/rlwe/security.go:19`, `DefaultXs`). A parameter literal that
overrides `Xe` or `Xs` is not described by this profile.

**Fresh encryptions** (MSB errors; the t-reading multiplies them by `t` and adds the stored
representative `p`, of norm at most `t − 1`):

* secret key: `c₀ = −a·s + e + T⁻¹·p`, error `|e| ≤ 19`;
* public key with special primes (`core/rlwe/encryptor.go:204-297`): `u·pk + (e₀, e₁)` over
  `Q·p₀` (only the first special prime), then divided by `p₀` with rounding (`ModDownQPtoQ`):
  error at most `(19·(2N + 1) + ⌊p₀/2⌋·(1 + N)) / p₀`;
* public key without special primes (`encryptor.go:180-184`, `encryptZeroPkNoP`): `u·pk + e`,
  error at most `19·(2N + 1)`.
-/

namespace Challenge.Instances.Lattigo
open Spec Spec.Source

/-- The largest absolute value of an error sample: `⌊19.2⌋` (module docstring). -/
def errBound : ℕ := 19

/-- The digits of Lattigo's RNS gadget decomposition: consecutive groups of `#P` limbs from `q₀`,
the last one shorter; one limb per digit when there is no special prime. Centred
representatives. -/
def layout (P : FullParams) : Budget.KSLayout :=
  Budget.uniformLayout (max 1 P.store.special.length)

/-- The MSB error bound of a public-key encryption with special primes `ps` (module docstring). -/
def pkErrMSB (N : ℕ) (ps : List ℕ) : ℕ :=
  match ps with
  | [] => errBound * (2 * N + 1)
  | p₀ :: _ => (errBound * (2 * N + 1) + p₀ / 2 * (1 + N)) / p₀

/-- The LSB (t-read) noise bound of a fresh secret-key encryption: `(t − 1) + t·19`. -/
def skFresh (t : ℕ) : ℕ := (t - 1) + t * errBound

/-- The LSB (t-read) noise bound of a fresh public-key encryption: `(t − 1) + t·pkErrMSB`. -/
def pkFresh (N t : ℕ) (ps : List ℕ) : ℕ := (t - 1) + t * pkErrMSB N ps

/-- Lattigo BGV parameters as `FullParams`: ring degree `N`, ciphertext primes `qs` (Lattigo's
`Q`, in order), special primes `ps` (Lattigo's `P`), plaintext modulus `t`; ternary secret; input
noise the larger of the two fresh-encryption bounds; key noise `19·t` (the t-reading of a key
error within `19`). The storage fields are not read by any certificate (`Spec.FullParams`); the
roots are left `0`. -/
def params (N : ℕ) (qs ps : List ℕ) (t : ℕ) : FullParams where
  src := { kind := .bgv, N := N, qs := qs, t := t }
  store := { W := N, limbs := qs.map fun q => ⟨q, 0⟩, special := ps.map fun p => ⟨p, 0⟩ }
  secretBound := 1
  inputNoise := max (skFresh t) (pkFresh N t ps)
  keyNoise := t * errBound
  outputNoise := 0

/-- **Lattigo's BGV implementation profile**: the hybrid key-switching bound on `layout P` (its
maximum over the levels) and the centred modulus-switching bounds by number of components. -/
def profile (P : FullParams) : Trace.Budget := Budget.certified P (layout P)

/-- The largest number of components Lattigo's `Rescale` is applied to in the recordings: `3`
(a product rescaled before relinearization). -/
def maxParts : ℕ := 3

/-- The instance check: the profile covers centred hybrid key switching on `layout P` and the
centred t-corrected modulus switch of `1, …, maxParts` components (`Challenge.Profile.coversBGV?`),
and one top-level key set restricts to every level (`Spec.Certify.keysRestrict?`; the layout
restricts at every level for every uniform layout). -/
def instanceOK? (P : FullParams) : Bool :=
  Challenge.Profile.coversBGV? P (layout P) maxParts (profile P) && Certify.keysRestrict? P

/-- `ExampleParameters128BitLogN14LogQP438` (`schemes/bgv/examples_parameters.go:6-14`):
`N = 2¹⁴`, twelve ciphertext primes (40 + 11·29 bits), two special primes (40 + 39 bits),
`t = 65537`. Six digits of two limbs at the top level. -/
def exampleLogN14 : FullParams :=
  params 16384
    [0x10000048001, 0x20008001, 0x1ffc8001, 0x20040001, 0x1ffc0001, 0x1ffb0001,
      0x20068001, 0x1ff60001, 0x200b0001, 0x200d0001, 0x1ff18001, 0x200f8001]
    [0x10000140001, 0x7ffffb0001] 65537

/-- A small set for exact conformance runs, with Lattigo's own primes: the literal
`{LogN: 4, LogQ: [30, 25, 25, 25], LogP: [30], PlaintextModulus: 65537}` gives these moduli
(`bgv.NewParametersFromLiteral`, v6.2.0). -/
def small : FullParams :=
  params 16 [1073741857, 33554273, 33554593, 33554849] [1073741953] 65537

/-- Two inputs at level `L`, multiplied, relinearized and switched down, then `d − 1` times
squared, relinearized and switched down: `d` multiplicative levels. -/
def chain (L d : ℕ) : Program where
  inputs := [⟨"a", 2, L, 1, 1⟩, ⟨"b", 2, L, 1, 1⟩]
  body := [.mul "x" "a" "b", .relin "x" "x", .modSwitch "x" "x"] ++
    (List.range (d - 1)).flatMap fun _ => [.square "x" "x", .relin "x" "x", .modSwitch "x" "x"]
  outputs := ["x"]

/-- The operations of one recorded conformance program at `small`: a product switched down
before relinearization (three components), a rotation (`automorph` by `5`, then key switching
back to `s`), an addition, a second product with relinearization and switching. -/
def smallProg : Program where
  inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩]
  body := [.mul "m" "a" "b", .modSwitch "m" "m", .relin "m" "m", .automorph "r" "m" 5,
    .keySwitch "r" "r", .add "y" "m" "r", .square "z" "y", .relin "z" "z", .modSwitch "z" "z"]
  outputs := ["z"]

end Challenge.Instances.Lattigo
