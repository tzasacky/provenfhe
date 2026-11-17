import Spec.Certify
import Spec.CertifyBFV

/-!
# Spec.EncryptBFV — BFV public-key encryption as OpenFHE v1.6.1 does it   (TRUSTED)

The BFV noise theorems (`Challenge.BFV`, `Challenge.CertifyBFV`) are about input ciphertexts with
noise at most a number. This file says what a *fresh public-key encryption* is in OpenFHE's
BFVrns, so that the noise of an input can be computed from the bounds of the key and the
samplers instead of declared (`Challenge.BFVEncrypt`).

**What OpenFHE v1.6.1 computes** (commit b59e1f29; `ENCRYPTION_TECHNIQUE = STANDARD`, the
default):

* the public key (`src/pke/lib/scheme/bfvrns/bfvrns-pke.cpp:88-90`) is `(b, a)` with
  `b = ns·e − a·s`, `e` from the discrete Gaussian generator, and the noise scale `ns = 1` for
  BFV (`src/pke/include/scheme/bfvrns/gen-cryptocontext-bfvrns-internal.h:97`; the extractor refuses
  any other value): `b + a·s = e`, which is `Spec.Encrypt.PublicKeyOK 1 Q s e b a`;
* `PKEBFVRNS::Encrypt(DCRTPoly, PublicKey)` (`bfvrns-pke.cpp:167-223`) calls
  `PKERNS::EncryptZeroCore` (`src/pke/lib/schemerns/rns-pke.cpp:152-200`): with `v` from the
  ternary generator (any secret distribution but `GAUSSIAN`) and `e₀`, `e₁` from the Gaussian
  generator, `(c₀, c₁) = (b·v + ns·e₀, a·v + ns·e₁)` modulo the `ℓ` limbs of the plaintext's
  parameters (`CloneTowers` of the public key when `ℓ < L`: the public key read modulo
  `Q_ℓ = q₀⋯q_{ℓ−1}`). That is `Spec.Encrypt.encrypt 1 b a 0 v e₀ e₁`;
* then (`bfvrns-pke.cpp:194-206`) the stored plaintext polynomial `p` goes through
  `DCRTPoly::TimesQovert` (`src/core/include/lattice/hal/default/dcrtpoly-impl.h:918-935`): every
  residue `x` modulo `q_i` becomes `[[x·NegQModt]_t · t⁻¹]_{q_i}` with
  `NegQModt = t − (Q_ℓ mod t)` (`src/pke/lib/scheme/bfvrns/bfvrns-cryptoparameters.cpp:83-94`,
  indexed by the number of dropped limbs `L − ℓ`) and `tInvModq[i] = t⁻¹ mod q_i` (`:68`), and is
  added to `c₀`. When every residue of a coefficient is the same integer `p ∈ [0, min q_i)` this is
  the residue of the integer `z = (Q_ℓ·p + [−Q_ℓ·p]_t) / t = ⌈Q_ℓ·p/t⌉` (`t·z ≡ [−Q_ℓ p]_t ≡
  [p·NegQModt]_t (mod q_i)` because `q_i ∣ Q_ℓ`): `scaleUpCeil`, pinned against the per-limb
  computation by `Challenge.BFVEncrypt.scaleUpCeil_timesQovert`. (OpenFHE adds `⌈Q·p/t⌉`, not `⌊Q/t⌉·p` and not `⌊Q·p/t⌉`.)

So `encryptBFV t Q b a p u e₁ e₂ = (b·u + e₁ + ⌈Q·p/t⌉, a·u + e₂)`. Its phase under `s` is
`⌈Q·p/t⌉ + freshError s e u e₁ e₂` (`Challenge.BFVEncrypt.phase_encryptBFV`): the *same* error
`e·u + e₁ + e₂·s` as BGV's (`Spec.Encrypt.freshError`, with the factor `t` of BGV replaced by `1`),
so every bound on it (`worstError`, `varProxy`, `epsFor`, `meanDrift`, `varProxyL2`, and the tail
theorems of `Challenge.FreshNoise`, `Challenge.FreshNoiseL2`) applies unchanged.

**The stored plaintext.** For BFV both OpenFHE encoders store coefficients in `[0, t)`: the
packed encoding stores `v ≥ 0` as `v` and `v < 0` as `t − |v|`, after refusing `|v| ≥ t`, in a vector
modulo `t`, and multiplies by the scaling factor modulo `t` (`src/pke/lib/encoding/packedencoding.cpp:73-91`), and the
coefficient-packed encoding stores a negative value `v` as `t − |v|` for BFVrns
(`src/pke/lib/encoding/coefpackedencoding.cpp:56-60`); the scaling factor of BFV plaintexts is 1.
The only representative of a message `m` in `[0, t)` is `liftMsg m`, so a fresh BFV encryption
of `m` is `encryptBFV … (liftMsg m) …`, with no declared plaintext bound (unlike BGV's `Bp`).
That `TimesQovert` sees the same integer `p` in every limb is a condition of the model. The packed
encoder puts the `[0, t)` vector in limb 0 (`packedencoding.cpp:115-121`) and fills every other
limb with `NativeVector(values, q_j)` (`:125-131`), a CENTRED modulus switch from `q₀`
(`src/core/lib/math/hal/intnat/mubintvecnat.cpp:192-213`): a coefficient `x > ⌊q₀/2⌋` becomes
`x − q₀` there. The model, which takes the same integer in every limb, therefore
applies only when `t − 1 ≤ ⌊q₀/2⌋` (then every `x ∈ [0, t)` is kept, as the residue of the integer
`x`, in every limb) and `t ≤ q_i` for every limb (so that this residue is `x` itself, which
`TimesQovert` reduces modulo `t`);
`Challenge.CertifyBFV.Defs.certifyBFV?` checks it (item 5a, `certifyBFV?_encodeOK`), and so every
certificate, including `Challenge.BFVEncrypt.certifyBFVFresh?`'s, is about parameters where it
holds. (The coefficient-packed encoder converts a big-integer vector of values in `[0, t)` and
keeps the same integer in every limb whenever `t ≤ q_i`.)

**The BFV noise of a fresh encryption.** `BFVEncrypts` measures the noise against `⌊Q/t⌋·m`. Write
`r = Q mod t`; then `⌈Q·p/t⌉ = ⌊Q/t⌋·p + ⌈r·p/t⌉`, and for `p ∈ [0, t)` the deterministic term
`⌈r·p/t⌉` lies in `[0, ⌈r·(t−1)/t⌉]` (`encodeDev`). So the noise is at most
`freshNoiseBFV t Q ε = ε + encodeDev t Q` when `‖freshError‖∞ ≤ ε`: the rounding term is
accounted for exactly, once, and is not random.

**Not covered.** `ENCRYPTION_TECHNIQUE = EXTENDED` (encryption modulo `Q·r` followed by
`ScaleAndRoundPOverQ`, `bfvrns-pke.cpp:182-189, 197-200, 211-214`): this file does not describe
it, and the frontend refuses to derive a fresh-encryption certificate for it. Secret-key
encryption (`bfvrns-pke.cpp:109-165`), multiparty contexts, the `GAUSSIAN` secret distribution
(then `v` is Gaussian: covered only if the declared `Bu` bounds it), and the word-level modular
arithmetic and NTTs of the library (the definitions here are integer-level).

Everything here is computable and deterministic: the randomness is an argument.
-/

namespace Spec.EncryptBFV
open NPoly Scheme Source Correct Spec.Encrypt

variable {N : ℕ}

/-- The integer `TimesQovert` adds to `c₀` for a stored coefficient `p` (module docstring):
`(Q·p + [−Q·p]_t) / t`, which is `⌈Q·p/t⌉` (`Int.emod` is the representative in `[0, t)`). -/
def scaleUpCeil (t Q : ℕ) (p : IntPoly N) : IntPoly N :=
  ⟨fun i => ((Q : ℤ) * p.coeff i + (-((Q : ℤ) * p.coeff i)) % (t : ℤ)) / (t : ℤ)⟩

/-- **OpenFHE BFV public-key encryption** (`ENCRYPTION_TECHNIQUE = STANDARD`) of the stored
plaintext polynomial `p` modulo `Q` under the public key `(b, a)` with randomness `(u, e₁, e₂)`,
as integer representatives: `(b·u + e₁ + ⌈Q·p/t⌉, a·u + e₂)`. This is `Spec.Encrypt.encrypt` with
the factor `1` (noise scale 1) applied to the scaled plaintext. -/
def encryptBFV (t Q : ℕ) (b a p u e₁ e₂ : IntPoly N) : List (IntPoly N) :=
  encrypt 1 b a (scaleUpCeil t Q p) u e₁ e₂

/-- The largest deterministic deviation of the encoding from `⌊Q/t⌋·p`, for `p ∈ [0, t)`:
`⌈(Q mod t)·(t − 1)/t⌉`. -/
def encodeDev (t Q : ℕ) : ℕ := ((Q % t) * (t - 1) + (t - 1)) / t

/-- The BFV noise bound of a fresh encryption modulo `Q` whose error `freshError` is at most `ε`:
`ε + encodeDev t Q`. -/
def freshNoiseBFV (t Q ε : ℕ) : ℕ := ε + encodeDev t Q

/-- The input noise of a program whose inputs named in `fresh` are fresh encryptions with error
at most `ε`: `freshNoiseBFV` at the largest `encodeDev` over the levels of their declarations. -/
def freshInputNoise (P : FullParams) (prog : Program) (fresh : List Var) (ε : ℕ) : ℕ :=
  ε + ((prog.inputs.filter fun d => d.name ∈ fresh).map fun d =>
    encodeDev P.src.t (P.src.modulus d.level)).foldl max 0

/-- What the fresh-encryption certificates of BFV need of the program's inputs, as a compiled
check:

* `fresh` is not empty and every name in it is a declared input;
* every input named in `fresh` is declared as a two-component ciphertext under `s` (Galois element
  1) and declares **no bound of its own** (its noise is what the encryption gives, not a
  declaration);
* every other input is a one-component value (a plaintext operand, within its declared bound or
  `t − 1`: `Spec.TraceBFV.inputBound`). No ciphertext input of unknown origin is allowed: its
  noise would be the computed input noise, an assumption about something that is not a fresh
  encryption. -/
def freshOKBFV? (prog : Program) (fresh : List Var) : Bool :=
  !fresh.isEmpty && (fresh.all fun x => prog.inputs.any fun d => d.name == x) &&
  prog.inputs.all fun d =>
    if d.name ∈ fresh then d.parts == 2 && d.key == 1 && (prog.boundOf d.name).isNone
    else d.parts == 1

/-- Where the noise of the fresh inputs of a BFV program comes from (the mode of
`Challenge.BFVEncrypt.certifyBFVFresh?`). The numbers are assumptions about the key and the
samplers, named as hypotheses by the statements; no check discharges them. -/
inductive FreshModeBFV
  /-- Worst case over the supports: the public-key error is at most `Bk`, the encryption
  randomness `(u, e₁, e₂)` within `Bu`, `B1`, `B2`; `ε = worstError`. No probability. -/
  | worst (fresh : List Var) (Bk Bu B1 B2 : ℕ)
  /-- With the support bounds, independent coordinates of mean at most `mn/md` in absolute
  value; `κ` the exponent of the failure probability. `ε` is `Spec.Certify.freshEps` (the
  high-probability bound, or the worst case if that is not larger). -/
  | kappa (fresh : List Var) (Bk Bu B1 B2 mn md κ : ℕ)
  /-- In `ℓ₂`: squared norms of the public-key error and the secret at most `E2`, `S2`;
  sub-Gaussian proxies `Vu`, `V1`, `V2` of the randomness about means at most `mn/md`. -/
  | kappaL2 (fresh : List Var) (E2 S2 Vu V1 V2 mn md κ : ℕ)

/-- The inputs named by a mode. -/
def FreshModeBFV.fresh : FreshModeBFV → List Var
  | .worst f .. | .kappa f .. | .kappaL2 f .. => f

/-- What `Challenge.BFVEncrypt.certifyBFVFresh?` returns: the certificate of
`Challenge.CertifyBFV.certifyBFV?` at the analysed parameters, those parameters, and the error
bound of the fresh encryptions with what kind of bound it is. -/
structure FreshCertBFV where
  /-- The declared parameters with the input noise replaced by
  `freshInputNoise P prog fresh eps`. -/
  params : FullParams
  cert : CertifyBFV.CertificateBFV
  used : Certify.NoiseUsed
  /-- The bound on `‖freshError‖∞` of every fresh encryption (including `drift`). -/
  eps : ℕ
  /-- The part of `eps` that pays for the declared mean bound (`0` in the worst case). -/
  drift : ℕ

end Spec.EncryptBFV
