import Spec.Correct
import Spec.Decrypt

/-!
# Spec.Encrypt — BGV public-key encryption as the libraries do it   (TRUSTED)

The noise headline is about input ciphertexts with noise at most `P.inputNoise`, whatever made
them. This file says what a *fresh public-key encryption* is, so that a bound on its noise can be
a theorem about the encryption randomness instead of an assumption.

**Which libraries this model describes.** OpenFHE's BGV public-key encryption, exactly
(`src/pke/lib/schemebase/base-pke.cpp:66-91`, `src/pke/lib/schemerns/rns-pke.cpp:55-70, 147-192`;
`harness/frontend/README.md`, "OpenFHE"): the public key is `(b, a)` with `b = −a·s + t·e_pk`; an
encryption draws `u` (ternary), `e₁`, `e₂` (the error sampler) and is

    (b·u + t·e₁ + p,  a·u + t·e₂)

modulo the ciphertext modulus, with no division afterwards, where `p` is the **stored plaintext
polynomial**: the integer polynomial the library's encoder produced and adds, coefficient by
coefficient, to the first component.

**The stored plaintext is not always the `[0, t)` lift of the message.** The message is
`p mod t` (`ofInt t p`), and that is all the encryption knows of it. Which representative `p` an
encoder stores is the encoder's business, and it differs between encodings:

* packed encoding (`src/pke/lib/encoding/packedencoding.cpp:70-77`): every coefficient in
  `[0, t)`, so `p = liftMsg m` and `‖p‖∞ ≤ t − 1`;
* coefficient-packed encoding: the centred lift, `‖p‖∞ ≤ ⌊t/2⌋`, with negative coefficients;
* under the scaling techniques `FLEXIBLEAUTO` and `FLEXIBLEAUTOEXT` the stored polynomial of a
  coefficient-packed plaintext is moreover multiplied by an integer scaling factor *without*
  reduction modulo `t`, so `‖p‖∞` can exceed `t − 1`.

So `encrypt` takes the stored polynomial `p` itself, and every statement about a fresh encryption
takes a **declared bound** `Bp` on `‖p‖∞` as an explicit parameter (`freshNoise t Bp ε`,
`Challenge.FreshNoise.FreshInputs`). `Bp = t − 1` is the instance for packed encoding
(`Challenge.FreshNoise.liftMsg_stored`), `Bp = ⌊t/2⌋` the one for a centred encoding
(`centered_stored`); a certificate declared at `t − 1` says nothing about a stored polynomial
that is larger (`Challenge.FreshNoise.encrypt_stored_exceeds`). The conformance harness executes
this definition on recorded OpenFHE encryptions, with the stored polynomial and the randomness
the library used, and compares the result with the library's ciphertext
(`harness/openfhe-pin/lean/README.md`, check `c.encrypt`).

**Not covered.** This file describes OpenFHE's public-key encryption only. Other libraries'
public-key encryption has a different shape and a different error, and nothing in this file or in
`Challenge.FreshNoise` is about it.

The phase of an encryption is `p + t·(e_pk·u + e₁ + e₂·s)` (`Challenge.FreshNoise.phase_encrypt`), so the centred
phase is at most `‖p‖∞ + t·‖e_pk·u + e₁ + e₂·s‖∞ ≤ Bp + t·ε`. The plaintext term is
deterministic: only the second term is random.

Everything here is computable and deterministic: the randomness `(u, e₁, e₂)` is an argument.
Probability enters only in the statements of `Challenge.FreshNoise`, which bound
`‖e_pk·u + e₁ + e₂·s‖∞` in the worst case (`worstError`) and with high probability over
`(u, e₁, e₂)` (`varProxy`, `epsFor`, `meanDrift`; and, from the `ℓ₂` norms of the key and
sub-Gaussian variance proxies of the samplers, `normSq`, `varProxyL2`, used by
`Challenge.FreshNoiseL2`).

**What the statements assume of the samplers.** The support-bound statements
(`Challenge.FreshNoise`) assume of the error sampler a support bound, and the `ℓ₂` statements
(`Challenge.FreshNoiseL2`) a sub-Gaussian variance proxy instead; both assume of its mean only a
bound `|E[X]| ≤ μ` (a rational `mn/md`), not that it is zero. The ternary sampler is taken to be
uniform on `{−1, 0, 1}` (mean zero). A nonzero mean shifts the tail bound by a deterministic drift
(`meanDrift`): coefficient `k` of `e_pk·u + e₁ + e₂·s` is a signed sum of the coordinates of
`(u, e₁, e₂)` with weights the coefficients of `e_pk`, one `1`, and the coefficients of `s`, so
its mean is at most `μ·(‖e_pk‖₁ + 1 + ‖s‖₁)` in absolute value. With `μ = 0` the drift is `0` and
the statements are those for mean-zero samplers.
-/

namespace Spec.Encrypt
open NPoly Scheme Source Correct

variable {N : ℕ}

/-- The message as an integer polynomial with coefficients in `[0, t)`. -/
def liftMsg {t : ℕ} (m : Poly t N) : IntPoly N := ⟨fun i => ((m.coeff i).val : ℤ)⟩

/-- `(b, a)` is a public key for the secret `s` with error `e`, modulo `Q`:
`b + a·s ≡ t·e (mod Q)`, i.e. `b = −a·s + t·e`. -/
def PublicKeyOK (t Q : ℕ) (s e b a : IntPoly N) : Prop :=
  ofInt Q (b + a * s) = ofInt Q ((t : ℤ) • e)

/-- BGV public-key encryption of the stored plaintext polynomial `p` under the public key
`(b, a)` with randomness `(u, e₁, e₂)`, as integer representatives:
`(b·u + t·e₁ + p, a·u + t·e₂)`. The message encrypted is `p mod t` (`ofInt t p`); `p` is whatever
representative of it the encoder stored (module docstring; `liftMsg m` for packed encoding). (A
ciphertext at a lower level is the same pair read modulo the shorter modulus.) -/
def encrypt (t : ℕ) (b a p u e₁ e₂ : IntPoly N) : List (IntPoly N) :=
  [b * u + (t : ℤ) • e₁ + p, a * u + (t : ℤ) • e₂]

/-- The error of a fresh encryption: its phase is `p + t · freshError`. -/
def freshError (s e u e₁ e₂ : IntPoly N) : IntPoly N := e * u + e₁ + e₂ * s

/-- The worst case of `‖freshError‖∞` for `‖s‖∞ ≤ Bs`, `‖e_pk‖∞ ≤ Bk`, `‖u‖∞ ≤ Bu`,
`‖e₁‖∞ ≤ B1`, `‖e₂‖∞ ≤ B2`: every one of the `2N + 1` terms of a coefficient at its extreme.
(OpenFHE: `Bs = Bu = 1`, `Bk = B1 = B2 = 39`, giving `39·(1 + 2N)`.) -/
def worstError (N Bs Bk Bu B1 B2 : ℕ) : ℕ := N * (Bk * Bu) + B1 + N * (B2 * Bs)

/-- The variance proxy of one coefficient of `freshError` when the `3N` coefficients of
`(u, e₁, e₂)` are independent and within their bounds: by Hoeffding's lemma each of the
`2N + 1` terms `c·X` with `|c| ≤ C`, `|X| ≤ B` is, after subtracting its mean, sub-Gaussian with
parameter `(C·B)²` (half the width of the range, squared: the mean plays no role).
(OpenFHE: `39²·(2N + 1)`.) -/
def varProxy (N Bs Bk Bu B1 B2 : ℕ) : ℕ := N * (Bk * Bu) ^ 2 + B1 ^ 2 + N * (B2 * Bs) ^ 2

/-- The squared `ℓ₂` norm of an integer polynomial: the sum of the squares of its coefficients. -/
def normSq (a : IntPoly N) : ℕ := ∑ i, (a.coeff i).natAbs ^ 2

/-- The variance proxy of one coefficient of `freshError` from `ℓ₂` norms
(`Challenge.FreshNoiseL2.freshError_tail_l2`): `V_u·E2 + V_1 + V_2·S2`, where `‖e_pk‖₂² ≤ E2`,
`‖s‖₂² ≤ S2` (`normSq`) and every coefficient of `u`, `e₁`, `e₂` is, about its mean, sub-Gaussian
with variance proxy at most `V_u`, `V_1`, `V_2`. A coefficient of `e_pk·u` is a signed sum of the `N`
coefficients of `u`, each taken once, weighted by the `N` coefficients of `e_pk`, each taken once;
so its proxy is `V_u·‖e_pk‖₂²`. Likewise `e₂·s`. With `E2 = N·B_k²`, `S2 = N·B_s²` and the
squares of the support bounds as proxies this is `varProxy`
(`Challenge.FreshNoiseL2.varProxyL2_support`). -/
def varProxyL2 (E2 S2 Vu V1 V2 : ℕ) : ℕ := Vu * E2 + V1 + V2 * S2

/-- The input-noise bound of a fresh encryption whose stored plaintext polynomial has
`‖p‖∞ ≤ Bp` and whose error is at most `ε`: `Bp + t·ε`. (Packed encoding: `Bp = t − 1`.) -/
def freshNoise (t Bp ε : ℕ) : ℕ := Bp + t * ε

/-- The drift of the tail bound for samplers whose coordinates have mean at most `mn/md` in
absolute value: `⌈(mn/md)·W⌉`, where `W` bounds the total weight `‖e_pk‖₁ + 1 + ‖s‖₁` with which
the coordinates enter one coefficient of `freshError` (`N·B_k + 1 + N·B_s` from support bounds;
`E2 + 1 + S2` from squared `ℓ₂` norms, since `|x| ≤ x²` for an integer `x`). It is `0` for
`mn = 0`. The denominator must be positive for this to mean anything (`certify?` checks it;
`Challenge.FreshNoise.meanDrift_spec`). -/
def meanDrift (W mn md : ℕ) : ℕ := (mn * W + (md - 1)) / md

/-- An error bound `ε` for which `count · exp(−ε² / (2·V)) ≤ 2^(−κ)`
(`Challenge.FreshNoise.epsFor_spec`): the least integer above
`√(2·V·(κ + ⌈log₂ count⌉)·0.6931471808)`, where `0.6931471808 > ln 2`. `V` is the variance proxy
and `count` the number of events in the union bound (`2N` per fresh encryption). -/
def epsFor (V count κ : ℕ) : ℕ :=
  Nat.sqrt (2 * V * (κ + Nat.clog 2 count) * 6931471808 / 10 ^ 10) + 1

/-- What the fresh-encryption certificates need of the program's inputs, as a compiled check.

* `fresh` is not empty (with no fresh encryption there is nothing probabilistic to say: use the
  worst-case certificate), and every name in it is a declared input.
* Every input named in `fresh` is declared as a two-component ciphertext under `s`, at a level
  whose modulus exceeds twice the input noise (so the phase of a fresh encryption does not wrap),
  and declares **no bound of its own** (`Program.bounds`). A declared bound on a fresh input would
  be an extra assumption on the encryption itself (the reference analysis starts every input at
  the smaller of its declared bound and the input noise), and the certificate would be about no
  encryption at all.
* Every other input is a one-component value (a plaintext operand) that declares its own bound,
  at most the input noise. -/
def freshOK? (P : FullParams) (prog : Program) (fresh : List Var) : Bool :=
  !fresh.isEmpty && (fresh.all fun x => prog.inputs.any fun d => d.name == x) &&
  prog.inputs.all fun d =>
    if d.name ∈ fresh then
      d.parts == 2 && d.key == 1 && (prog.boundOf d.name).isNone &&
        decide (2 * P.inputNoise < P.src.modulus d.level)
    else
      d.parts == 1 &&
        match prog.boundOf d.name with
        | some b => decide (b ≤ P.inputNoise)
        | none => false

/-! ### The outputs are decrypted under the secret key itself

`Spec.Correct.Encrypts` is about the key a value is recorded under: after an automorphism by `g`
and before the key switch, that is `σ_g(s)`, not `s`. A library decrypts with `s`. So a
certificate of decryption needs every output to be recorded under the Galois element 1. -/

/-- The Galois element of the key under which the program leaves output `o` (it does not depend
on the messages: `Challenge.FreshNoise.outputKey?_eq`), computed on all-zero messages. -/
def outputKey? (P : Params) (prog : Program) (o : Var) : Option ℕ := do
  let ρ ← eval P prog fun _ => .exact 0
  let v ← ρ o
  pure v.key

/-- Every output is under the secret key itself (Galois element 1). -/
def outputsUnderS? (P : Params) (prog : Program) : Bool :=
  prog.outputs.all fun o => outputKey? P prog o == some 1

/-- The computed precondition of a decryption certificate with the proved bound `B`: every output
is under the secret key itself, and, if the library decrypts by switching the phase to one limb
(`switched`; `Spec.Decrypt.bgvDecryptSwitched`), `Spec.Decrypt.decryptAllOK?` accepts `B`. -/
def certOK? (P : FullParams) (prog : Program) (B : ℕ) (switched : Bool) : Bool :=
  outputsUnderS? P.src prog && (!switched || Decrypt.decryptAllOK? P.src prog B)

end Spec.Encrypt
