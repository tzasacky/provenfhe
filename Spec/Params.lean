import Spec.Layout

/-!
# Spec.Params — parameters an end-to-end claim is about   (TRUSTED)

`SchemeParamsOK` is a hypothesis of the noise headline and of the certificates, so it constrains
only what the *user* supplies (moduli, plaintext modulus, noise bounds). `ParamsOK` adds
storage-level clauses (32-bit words, a root of unity per limb) that a claim about code computing
on stored 32-bit residues would also need; no certificate assumes them. `schemeParamsOK?` and
`paramsOK?` decide them.
-/

namespace Spec
open Layout

/-- Everything a compiled program's meaning depends on, besides the program itself.

**Which fields the noise certificates read.** `Challenge.Certify.certify?` (BGV) reads `src`,
`secretBound`, `inputNoise`, `keyNoise`, and of `store` only the moduli of the special primes
(`store.special.map (·.q)`: `Spec.Budget.specialProd`, `SpecialOK`). It ignores `store.W`,
`store.limbs`, the root `ψ` of every entry of `store.limbs` and `store.special`, and
`outputNoise`: these are read only by the storage-level clauses of `ParamsOK`, and examples used
only for certificates may fill them with anything
(a `ψ` of `0`, for instance). -/
structure FullParams where
  src : Source.Params
  store : StoreParams
  /-- Bound on the secret key's coefficients (`1` for ternary secrets). -/
  secretBound : ℕ
  /-- Noise bound of input ciphertexts (`BGVEncrypts`/`BFVEncrypts` bound). -/
  inputNoise : ℕ
  /-- Noise bound of key-switching keys (`KeyValid`). -/
  keyNoise : ℕ
  /-- An output error bound. Read by no statement (the exact schemes need only correct
  decryption); kept so that parameter literals keep their shape. -/
  outputNoise : ℕ
  deriving Repr

/-- All moduli that storage uses, ciphertext limbs first. -/
def FullParams.allLimbs (P : FullParams) : List LimbParams := P.store.limbs ++ P.store.special

/-- Scheme-level validity: what the *mathematics* of the scheme needs from the parameters, and
nothing about how ciphertexts are stored. It reads only `P.src` and the noise bounds, never
`P.store`, so it puts no bound on the size of the primes (OpenFHE/HEIR chains of 45- to 60-bit
primes satisfy it), and asks for no roots of unity (a storage matter: `LimbParams.ψ`). The noise
headline (`Challenge.Headline.NoiseSoundBGV`) assumes only this. (The certified key-switching
budget also reads the special primes, which are stored in `P.store.special`; what it needs of
them is `Spec.Budget.SpecialOK`, a separate hypothesis.) -/
structure SchemeParamsOK (P : FullParams) : Prop where
  N_pow2 : ∃ k, P.src.N = 2 ^ k
  qs_nonempty : P.src.qs ≠ []
  prime : ∀ q ∈ P.src.qs, Nat.Prime q
  distinct : P.src.qs.Nodup
  plaintext : 2 ≤ P.src.t ∧ ∀ q ∈ P.src.qs, Nat.Coprime P.src.t q
  /-- BGV: the input noise bound admits every message. `BGVEncrypts` bounds the whole centered
  phase `m + t·e`, message included, and the centered representative of `m ∈ Z_t` ranges over
  `(-t/2, t/2]`, so its largest absolute value is `⌊t/2⌋`. With `inputNoise < ⌊t/2⌋` no ciphertext
  encrypts a message having a coefficient `⌊t/2⌋` within the bound, and a theorem about "all
  inputs with noise at most `inputNoise`" would silently be about small messages only. `⌊t/2⌋` is
  the least bound with this property (it is met by a noiseless encryption, `e = 0`, of the
  centred representative: `Challenge.Params.bgv_inputs_exist`, `bgv_small_noise_excludes`). A
  real encryption has phase `p + t·e` with `p` whatever representative of the message its encoder
  stores, and needs `‖p‖∞ + t·‖e‖∞`: with `‖p‖∞` up to `t − 1` for a representative in `[0, t)`
  (`Spec.Encrypt`). BFV bounds the error alone, so it needs no such clause. -/
  msgRange : P.src.kind = .bgv → P.src.t / 2 ≤ P.inputNoise

/-- Validity of user-supplied parameters for compiled code: the scheme-level core
(`SchemeParamsOK`) and the storage-level clauses, which are about `P.store` (word size, the limb
table and its agreement with the modulus chain, 32-bit words, the roots of unity the NTT
storage form is defined by) and extend primality, distinctness and coprimality to the special
primes used by key switching. -/
structure ParamsOK (P : FullParams) : Prop where
  scheme : SchemeParamsOK P
  W_pos : 0 < P.store.W
  W_dvd : P.store.W ∣ P.src.N
  limbs_match : P.store.limbs.map (·.q) = P.src.qs
  limbs_nonempty : P.store.limbs ≠ []
  prime : ∀ lp ∈ P.allLimbs, Nat.Prime lp.q
  odd : ∀ lp ∈ P.allLimbs, lp.q % 2 = 1
  /-- Stored residues fit 32-bit words. A storage rule: `SchemeParamsOK` does not have it. -/
  fits : ∀ lp ∈ P.allLimbs, lp.q < 2 ^ 32
  /-- `ψ` is a primitive `2N`-th root of unity (for `N` a power of two this is `ψ^N = -1`). -/
  root : ∀ lp ∈ P.allLimbs, (lp.ψ : ZMod lp.q) ^ P.src.N = -1
  distinct : (P.allLimbs.map (·.q)).Nodup
  plaintext : 2 ≤ P.src.t ∧ ∀ lp ∈ P.allLimbs, Nat.Coprime P.src.t lp.q

/-! ### Decision procedures

`schemeParamsOK?` and `paramsOK?` are compiled checks of every clause of `SchemeParamsOK` and
`ParamsOK` (`Challenge.Params.schemeParamsOK?_sound`, `paramsOK?_sound`: `… = true → …OK P`), so
that a user can discharge the parameter hypothesis of a headline theorem on their own parameters
by running a program.

Primality needs no certificate from the user. Both tests rest on one fact: if `x^(2^(e-1)) = -1
(mod q)` with `q` odd, then every prime factor `r` of `q` satisfies `r ≡ 1 (mod 2^e)` (the order
of `x` modulo `r` is exactly `2^e`, and it divides `r - 1`). So `q` is prime as soon as no
`d = 2^e·a + 1` with `a ≥ 1` and `d² ≤ q` divides it: trial division over at most `√q / 2^e`
candidates.

* Scheme level (`primeOK?`, any size): `2^e` is the power of two in `q - 1`, and `x = a^((q-1)/2^e)`
  for a small `a` with `a^((q-1)/2) = -1` (a quadratic non-residue; the test searches `a < 64`).
  For the NTT-friendly primes FHE uses (`2N ∣ q - 1`) the trial division is short: 4096 candidates
  for a 60-bit prime with `2¹⁸ ∣ q - 1`.
* Storage level (`limbOK?`): the limb's own `ψ` with `ψ^N = -1` is the witness, `2^e = 2N` (one
  candidate for the 31-bit primes of `FullParams.exampleBGV31`). -/

/-- `b^e mod m` by square-and-multiply, structurally recursive on `fuel` (exact when
`e < 2^fuel`), so that it also evaluates in the kernel. -/
def powMod : (fuel b e m : ℕ) → ℕ
  | 0, _, _, m => 1 % m
  | f + 1, b, e, m =>
    if e = 0 then 1 % m else
      let r := powMod f (b * b % m) (e / 2) m
      if e % 2 = 0 then r else r * b % m

/-- `true` only if no `d' ∈ {d, d + step, d + 2·step, …}` with `d'² ≤ q` divides `q`. Gives up
(`false`) when `fuel` runs out. -/
def noDivisorFrom (q step : ℕ) : (fuel d : ℕ) → Bool
  | 0, _ => false
  | f + 1, d =>
    if q < d * d then true else if q % d = 0 then false else noDivisorFrom q step f (d + step)

/-- The largest power of two dividing `n` (as the power itself; `1` for `n = 0`), structurally
recursive on `fuel` (exact when `n < 2^fuel`). -/
def twoPart : (fuel n : ℕ) → ℕ
  | 0, _ => 1
  | f + 1, n => if n ≠ 0 ∧ n % 2 = 0 then 2 * twoPart f (n / 2) else 1

/-- A primality test that is sound for every `q` (`primeOK? q = true → q` is prime) and accepts
the odd primes with a quadratic non-residue below 64 (in particular every prime used in practice;
`2` is rejected, and so is not usable as a ciphertext modulus). See the section docstring. -/
def primeOK? (q : ℕ) : Bool :=
  decide (1 < q) && decide (q % 2 = 1) &&
    (List.range 64).any (fun a => powMod q a ((q - 1) / 2) q == q - 1) &&
    noDivisorFrom q (twoPart q (q - 1)) q (twoPart q (q - 1) + 1)

/-- Decides the clauses of `SchemeParamsOK` (soundness: `Challenge.Params.schemeParamsOK?_sound`). -/
def schemeParamsOK? (P : FullParams) : Bool :=
  decide (P.src.N = 2 ^ Nat.log2 P.src.N) &&
  !P.src.qs.isEmpty && P.src.qs.all primeOK? && decide P.src.qs.Nodup &&
  (decide (2 ≤ P.src.t) && P.src.qs.all fun q => Nat.gcd P.src.t q == 1) &&
  (P.src.kind != .bgv || decide (P.src.t / 2 ≤ P.inputNoise))

/-- The per-limb checks: `1 < q < 2³²`, `q` odd, `ψ^N ≡ -1 (mod q)`, and no divisor of `q` among
the `d ≡ 1 (mod 2N)` with `1 < d` and `d² ≤ q`. Together with `N = 2^k` these make `q` prime. -/
def limbOK? (N : ℕ) (lp : LimbParams) : Bool :=
  decide (1 < lp.q) && decide (lp.q < 2 ^ 32) && decide (lp.q % 2 = 1) &&
    decide (powMod (N + 1) (lp.ψ % lp.q) N lp.q = lp.q - 1) &&
    noDivisorFrom lp.q (2 * N) lp.q (2 * N + 1)

/-- Decides the clauses of `ParamsOK` (soundness: `Challenge.Params.paramsOK?_sound`). -/
def paramsOK? (P : FullParams) : Bool :=
  schemeParamsOK? P &&
  decide (0 < P.store.W) && decide (P.src.N % P.store.W = 0) &&
  decide (P.store.limbs.map (·.q) = P.src.qs) && !P.store.limbs.isEmpty &&
  P.allLimbs.all (limbOK? P.src.N) &&
  decide (P.allLimbs.map (·.q)).Nodup &&
  P.allLimbs.all fun lp => Nat.gcd P.src.t lp.q == 1

namespace FullParams

/-- A tiny BGV instance: `N = 4`, words of 2 coefficients (2 words per limb), ciphertext primes
`65537 = 2¹⁶ + 1` and `786433 = 12·2¹⁶ + 1` (both `≡ 1 (mod 2¹⁶)` and below `2³¹`, so the
Montgomery precondition holds), `ψ = 16` and `241748` (`ψ⁴ = −1`), `t = 17`, ternary secret.
`Q = 51540459521`. No special prime. Small enough to evaluate by hand; the examples and
discrimination pins of the certificates are stated at it. -/
def tinyBGV : FullParams where
  src := { kind := .bgv, N := 4, qs := [65537, 786433], t := 17 }
  store := { W := 2, limbs := [⟨65537, 16⟩, ⟨786433, 241748⟩], special := [] }
  secretBound := 1
  inputNoise := 64
  keyNoise := 64
  outputNoise := 128

/-- An example BGV instance with 31-bit primes: `N = 2¹⁴`, words of `2¹³` coefficients, two 31-bit ciphertext
primes (`1073872897` and `1074266113`, both just above `2³⁰`) and one 31-bit special prime
(`1077477377`), all `≡ 1 (mod 2¹⁶)`, `t = 65537`, ternary secret. Used as the
non-vacuity witness for `ParamsOK` and as a test instance.

What the noise bounds represent. They are illustrative round numbers, not any library's.
`inputNoise = 2²¹` is the bound of a ciphertext whose phase is `p + t·e` with `p` a
representative of the message of norm at most `t − 1 = 65536` (a representative in `[0, t)`; a
centred one is at most `32768`) and an error `|e| ≤ 30`: `65536 + 65537·30 = 2031646 ≤ 2²¹`, as a
**secret-key encryption** with a narrow error would have (`|e| ≤ 19` gives
`65536 + 65537·19 = 1310739 ≈ 2^20.3`). `keyNoise = 2²¹` is the same reading of
a key-switching key's error `t·e` with `|e| ≤ 31`. It is below what OpenFHE's documented error
bound 39 gives (`65537·39 ≈ 2^21.3`): the tool's inputs for OpenFHE programs declare their own,
larger, bounds.

What it does not represent. It is *not* a public-key encryption: there the phase is
`p + t·(e·u + e₁ + e₂·s)` with `p` the stored plaintext polynomial (`Spec.Encrypt`), and with
errors within 19, `u` and `s` ternary its worst case is `Bp + t·19·(2N + 1)`
(`Spec.Encrypt.worstError`), about `2^35.2` at `Bp = t − 1`; the product of two such ciphertexts
(`N·B² ≈ 2^84.5`) is far beyond `Q/2 ≈ 2⁵⁹` on this two-prime chain. Nor is the chain
deep: `Q ≈ 2⁶⁰` supports one multiplication of fresh secret-key ciphertexts in the worst-case
analysis (`N·B² = 2⁵⁶`; a second one overflows), and the instance makes no claim about security
level. It is a test instance (ring dimension, word size, 31-bit NTT primes), not a production
parameter set. -/
def exampleBGV31 : FullParams where
  src := { kind := .bgv, N := 16384, qs := [1073872897, 1074266113], t := 65537 }
  store := {
    W := 8192
    limbs := [⟨1073872897, 2521228⟩, ⟨1074266113, 639594595⟩]
    special := [⟨1077477377, 242123675⟩] }
  secretBound := 1
  inputNoise := 2 ^ 21
  keyNoise := 2 ^ 21
  outputNoise := 2 ^ 29

end FullParams
end Spec
