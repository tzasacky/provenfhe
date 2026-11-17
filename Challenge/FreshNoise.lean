import Spec.Encrypt
import Challenge.Headline.Defs
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Challenge.FreshNoise — the noise of a fresh encryption, worst case and with high probability   (LOCKED statements; proofs in `Validation/`)

`Spec.Encrypt` defines BGV public-key encryption of a stored plaintext polynomial `p` with its
randomness `(u, e₁, e₂)` as an argument. The error of a fresh encryption is `e_pk·u + e₁ + e₂·s`
(`freshError`). These pins:

1. `phase_encrypt`: the phase of `encrypt` is `p + t·freshError` (so `Spec.Encrypt.encrypt` is an
   encryption, with the signs right); `encrypt_encrypts`: it `BGVEncrypts` the message `p mod t`
   with noise `Bp + t·ε` whenever `‖p‖∞ ≤ Bp`, `‖freshError‖∞ ≤ ε` and the modulus is large
   enough. `liftMsg_stored`, `centered_stored`: the two standard stored representatives of a
   message, with `Bp = t − 1` and `Bp = ⌊t/2⌋`; `encrypt_stored_exceeds`: a stored polynomial
   larger than `t − 1` is not covered by the bound declared at `t − 1`.
2. `freshError_worst`: the deterministic bound `N·B_k·B_u + B₁ + N·B₂·B_s` (the frontends'
   formula `(t − 1) + t·39·(1 + 2N)` for OpenFHE's packed encoding is this at `Bp = t − 1`), and
   `freshError_worst_attained`: it is attained inside the sampler supports.
3. `freshError_tail`: for a *fixed* key, if the `3N` coefficients of `(u, e₁, e₂)` are
   independent, bounded and of mean at most `μ = mn/md` in absolute value (`SamplerOK`, over an
   arbitrary probability space), then
   `P[‖freshError‖∞ ≥ ε + μ·(N·B_k + 1 + N·B_s)] ≤ 2N·exp(−ε² / (2·V))` with `V = varProxy`
   (Hoeffding). For `μ = 0` this is the tail bound for mean-zero samplers; `meanDrift_spec`: the
   computed `Spec.Encrypt.meanDrift` is at least the drift term.
4. `fresh_sound` (deterministic) and `fresh_certified` (probabilistic): the noise headline for
   the reference analyzer with fresh encryptions as inputs.
5. `epsFor_spec`: the computed `Spec.Encrypt.epsFor` makes the failure bound at most `2^(−κ)`;
   `fresh_certified_kappa` puts 4 and 5 together.
6. `samplerOK_rademacher`: `SamplerOK` is satisfied by an explicit product measure (independent
   fair signs scaled to the bounds), and guards: at OpenFHE's default parameters the
   high-probability bound is below the worst case.
7. **One-program certificates**, each as one statement about *decryption under the secret key
   itself* (`OutputsDecrypt`), for one program and one bound. (`fhe_check` does not cite these
   as its verdict: it analyses each output with its own bound and cites the joint statements
   about the locked decision function, `Challenge.Certify.worst_certified`,
   `fresh_worst_certified`, `fresh_kappa_certified`, `fresh_l2_certified`, which are proved from
   these.) `certified_decrypts` (worst case, any inputs within
   the input noise), `fresh_worst_decrypts` (fresh encryptions, worst case of their error, no
   probability) and `fresh_kappa_decrypts` (fresh encryptions, failure probability at most
   `2^(−κ)`). Their computed preconditions are `refAnalyze`, `Spec.Encrypt.freshOK?` and
   `Spec.Encrypt.certOK?` (every output under the Galois element 1; for the library's switched
   decryption, `Spec.Decrypt.decryptAllOK?`).

**A fresh input declares no bound.** `Spec.Encrypt.freshOK?` rejects a fresh input with a declared
bound (`Program.bounds`), and `FreshInputs` assumes declared bounds only of the inputs that are
not fresh. Otherwise the declared bound would be an assumption on the encryption itself, and for
a bound below the noise of every encryption the statements would be vacuous (`freshOK?_spec` and
the guards at the end).

**What the probability is over, and the quantifier order.** In `fresh_certified` the secret key,
the public key and its error, the program and the parameters are fixed first. The probability
space carries the encryption randomness only. The event whose probability is bounded,
`FreshFails`, is "there EXIST messages (and plaintext operands within their declared bounds) for
which some output of some run is wrong". So with probability at least `1 − δ` over the
encryption randomness, the outputs are right *for every choice of messages simultaneously*, in
particular for messages chosen by an adversary, even one who knows the randomness: the error of a
fresh encryption does not depend on the message. Evaluation is worst case: every run meeting the
`Spec.Trace` contracts, no probability.

**What is not proved.** (a) That any library's sampler satisfies `SamplerOK` (independence, the
mean bound, the support bounds): this is a hypothesis. (b) Anything about a randomness distribution that depends
on the messages or on an adversary's choices, e.g. an adversary who can make the encryptor
re-draw or discard encryptions, or choose adaptively which or how many encryptions enter the
program: the randomness families `u, e₁, e₂` and the list `fresh` are fixed before the
probability is taken. (c) Any statement about keys drawn at random (the key is universally
quantified within its bounds, which is stronger) or about security.
-/

namespace Challenge.FreshNoise
open Spec NPoly Scheme Source Correct Spec.Encrypt Challenge.Headline MeasureTheory ProbabilityTheory

variable {N : ℕ}

/-! ## 1. The phase of a fresh encryption -/

/-- **Phase identity.** Under a public key `(b, a)` with `b + a·s ≡ t·e`, the phase of
`encrypt t b a p u e₁ e₂` is `p + t·(e·u + e₁ + e₂·s)` modulo `Q`. -/
theorem phase_encrypt (t Q : ℕ) (s e b a p u e₁ e₂ : IntPoly N)
    (hpk : PublicKeyOK t Q s e b a) :
    phase (ofInt Q s) ((encrypt t b a p u e₁ e₂).map (ofInt Q)) =
      ofInt Q (p + (t : ℤ) • freshError s e u e₁ e₂) := sorry

/-- A fresh encryption of a stored plaintext polynomial `p` with `‖p‖∞ ≤ Bp` whose error is at
most `ε` encrypts the message `p mod t` with noise at most `Bp + t·ε`, provided the phase does
not wrap modulo `Q`. -/
theorem encrypt_encrypts (t Q Bp ε : ℕ) (ht : 2 ≤ t) (s e b a p u e₁ e₂ : IntPoly N)
    (hpk : PublicKeyOK t Q s e b a) (hp : normInf p ≤ Bp)
    (hε : normInf (freshError s e u e₁ e₂) ≤ ε) (hQ : 2 * freshNoise t Bp ε < Q) :
    BGVEncrypts t (freshNoise t Bp ε) s ((encrypt t b a p u e₁ e₂).map (ofInt Q)) (ofInt t p) :=
  sorry

/-- **The canonical stored plaintext** (packed encoding): the lift of `m` to `[0, t)` is a stored
polynomial for the message `m`, of norm at most `t − 1`. -/
theorem liftMsg_stored (t : ℕ) (ht : 0 < t) (m : Poly t N) :
    ofInt t (liftMsg m) = m ∧ normInf (liftMsg m) ≤ t - 1 := sorry

/-- **The centred stored plaintext** (a centred encoding): the centred lift of `m` is a stored
polynomial for the message `m`, of norm at most `⌊t/2⌋`. -/
theorem centered_stored (t : ℕ) (ht : 0 < t) (m : Poly t N) :
    ofInt t (centered m) = m ∧ normInf (centered m) ≤ t / 2 := sorry

/-- **A stored plaintext larger than `t − 1` is not covered by the bound declared at `t − 1`.**
`t = 17`, `Q = 65537`, `N = 1`; the stored polynomial is `−40` (as a coefficient-packed `−8`
multiplied by a scaling factor `5` without reduction modulo `t`), a representative of the
message `11`. With the key `s = 0`, `(b, a) = (0, 0)` and all encryption randomness zero (error
`0`), the encryption of `−40` does not encrypt its message within `freshNoise 17 (17 − 1) 0`,
the bound a certificate declared for the `[0, t)` lift is about; it does within
`freshNoise 17 40 0`. (And the `[0, t)` lift of the same message, `11`, is within the first.) -/
theorem encrypt_stored_exceeds :
    PublicKeyOK 17 65537 (0 : IntPoly 1) 0 0 0 ∧
    ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1) = ofInt 17 (⟨fun _ => 11⟩ : IntPoly 1) ∧
    ¬ BGVEncrypts 17 (freshNoise 17 (17 - 1) 0) (0 : IntPoly 1)
        ((encrypt 17 0 0 (⟨fun _ => -40⟩ : IntPoly 1) 0 0 0).map (ofInt 65537))
        (ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (freshNoise 17 40 0) (0 : IntPoly 1)
        ((encrypt 17 0 0 (⟨fun _ => -40⟩ : IntPoly 1) 0 0 0).map (ofInt 65537))
        (ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (freshNoise 17 (17 - 1) 0) (0 : IntPoly 1)
        ((encrypt 17 0 0 (⟨fun _ => 11⟩ : IntPoly 1) 0 0 0).map (ofInt 65537))
        (ofInt 17 (⟨fun _ => -40⟩ : IntPoly 1)) := sorry

/-! ## 2. The worst case -/

/-- **Worst-case bound** on the error of a fresh encryption. -/
theorem freshError_worst (s e u e₁ e₂ : IntPoly N) (Bs Bk Bu B1 B2 : ℕ) (hs : normInf s ≤ Bs)
    (he : normInf e ≤ Bk) (hu : normInf u ≤ Bu) (h1 : normInf e₁ ≤ B1) (h2 : normInf e₂ ≤ B2) :
    normInf (freshError s e u e₁ e₂) ≤ worstError N Bs Bk Bu B1 B2 := sorry

/-- The worst case is attained: with every coefficient at its bound, the top coefficient of the
error is `N·B_k·B_u + B₁ + N·B₂·B_s`. (So a worst-case analysis cannot do better than
`worstError` without a hypothesis on how the randomness is distributed.) -/
theorem freshError_worst_attained (hN : 0 < N) (Bs Bk Bu B1 B2 : ℕ) :
    normInf (freshError (⟨fun _ => (Bs : ℤ)⟩ : IntPoly N) ⟨fun _ => Bk⟩ ⟨fun _ => Bu⟩
      ⟨fun _ => B1⟩ ⟨fun _ => B2⟩) = worstError N Bs Bk Bu B1 B2 := sorry

-- The frontends' formula for OpenFHE's packed encoding (`harness/frontend/README.md`):
-- `(t − 1) + t·39·(1 + 2N)`.
#guard freshNoise 65537 (65537 - 1) (worstError 16384 1 39 1 39 39) ==
  (65537 - 1) + 65537 * 39 * (1 + 2 * 16384)
-- The stored-plaintext bound enters additively, once: a centred encoding saves `t − 1 − ⌊t/2⌋`,
-- and a stored polynomial of norm `(t/2)·(t − 1)` (a scaled coefficient-packed plaintext) costs
-- far more than the bound at `t − 1` covers.
#guard freshNoise 65537 (65537 / 2) 99749 + (65537 - 1 - 65537 / 2) == freshNoise 65537 (65537 - 1) 99749
#guard freshNoise 65537 (65537 - 1) 0 < freshNoise 65537 (65537 / 2 * (65537 - 1)) 0
#guard worstError 16384 1 39 1 39 39 == 1277991

/-! ## 3. The tail bound -/

/-- The `3N` coefficients of the encryption randomness `(u, e₁, e₂)`, as one family. -/
def coords {Ω : Type*} (u e₁ e₂ : Ω → IntPoly N) : Fin N ⊕ Fin N ⊕ Fin N → Ω → ℤ :=
  Sum.elim (fun i ω => (u ω).coeff i)
    (Sum.elim (fun i ω => (e₁ ω).coeff i) (fun i ω => (e₂ ω).coeff i))

/-- The bound of each coordinate: `Bu` for `u`, `B1` for `e₁`, `B2` for `e₂`. -/
def coordBound (N Bu B1 B2 : ℕ) : Fin N ⊕ Fin N ⊕ Fin N → ℕ :=
  Sum.elim (fun _ => Bu) (Sum.elim (fun _ => B1) (fun _ => B2))

/-- What is assumed of one encryption's randomness, on an arbitrary probability space: its `3N`
coefficients are (jointly) independent random variables, each almost surely within its bound and
with mean at most `mn/md` in absolute value (`mn = 0`: mean zero). No distribution is named: a
uniform ternary `u` and a truncated discrete Gaussian for `e₁`, `e₂` are of this form if the
sampler draws coefficients independently. (A sampler whose mean is not exactly zero meets `mean`
with a nonzero `mn/md`, not with `mn = 0`.) -/
structure SamplerOK {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Bu B1 B2 mn md : ℕ)
    (u e₁ e₂ : Ω → IntPoly N) : Prop where
  indep : iIndepFun (fun j ω => (coords u e₁ e₂ j ω : ℝ)) μ
  meas : ∀ j, AEMeasurable (fun ω => (coords u e₁ e₂ j ω : ℝ)) μ
  mean : ∀ j, |∫ ω, (coords u e₁ e₂ j ω : ℝ) ∂μ| ≤ (mn : ℝ) / md
  bound : ∀ j, ∀ᵐ ω ∂μ, |coords u e₁ e₂ j ω| ≤ (coordBound N Bu B1 B2 j : ℤ)

/-- **Tail bound** (Hoeffding). For any fixed secret and public-key error within their bounds and
any randomness meeting `SamplerOK` with mean bound `μ = mn/md`:
`P[‖e_pk·u + e₁ + e₂·s‖∞ ≥ ε + μ·(N·B_k + 1 + N·B_s)] ≤ 2N·exp(−ε² / (2·V))` for every `ε ≥ 0`,
with `V = N·(B_k·B_u)² + B₁² + N·(B₂·B_s)²`. Each coefficient of the error is a signed sum of `N`
terms `e_pk,j·u_k`, one term `e₁,k` and `N` terms `e₂,j·s_k`, independent, of ranges `B_k·B_u`,
`B₁`, `B₂·B_s` (so each, minus its mean, is sub-Gaussian with the square of its range: Hoeffding's
lemma does not need mean zero), and the mean of the sum is at most
`μ·(‖e_pk‖₁ + 1 + ‖s‖₁) ≤ μ·(N·B_k + 1 + N·B_s)` in absolute value. With `mn = 0` the drift term
vanishes: `P[‖e_pk·u + e₁ + e₂·s‖∞ ≥ ε] ≤ 2N·exp(−ε² / (2·V))`. -/
theorem freshError_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hN : 0 < N) (s e : IntPoly N) (Bs Bk Bu B1 B2 mn md : ℕ) (hs : normInf s ≤ Bs)
    (he : normInf e ≤ Bk) (u e₁ e₂ : Ω → IntPoly N) (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε + (mn : ℝ) / md * (N * Bk + 1 + N * Bs : ℕ) ≤
        (normInf (freshError s e (u ω) (e₁ ω) (e₂ ω)) : ℝ)} ≤
      2 * N * Real.exp (-ε ^ 2 / (2 * (varProxy N Bs Bk Bu B1 B2 : ℝ))) := sorry

/-- **`meanDrift` is at least the drift term**, for a positive denominator: `(mn/md)·W ≤
meanDrift W mn md`. -/
theorem meanDrift_spec (W mn md : ℕ) (hmd : 0 < md) :
    (mn : ℝ) / md * (W : ℝ) ≤ (meanDrift W mn md : ℝ) := sorry

/-- For mean-zero samplers there is no drift. -/
theorem meanDrift_zero (W md : ℕ) : meanDrift W 0 md = 0 := sorry

/-- The drift is the least such integer: it is below `(mn/md)·W + 1`. -/
theorem meanDrift_lt (W mn md : ℕ) (hmd : 0 < md) :
    (meanDrift W mn md : ℝ) < (mn : ℝ) / md * (W : ℝ) + 1 := sorry

/-- The variance proxy for a ternary secret and `u` and one error bound `B` (OpenFHE: `B = 39`)
is `B²·(2N + 1)`. -/
theorem varProxy_ternary (N B : ℕ) : varProxy N 1 B 1 B B = B ^ 2 * (2 * N + 1) := sorry

/-! ## 4. The noise headline with fresh encryptions as inputs -/

/-- Every output of every run is right (the conclusion of `NoiseSoundBGV`), for the exact
messages `m` and the input ciphertexts `cts`. -/
def OutputsExact (P : FullParams) (E : Trace.Budget) (prog : Program) (B : ℕ)
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∃ ρ, Source.eval P.src prog (fun x => .exact (m x)) = some ρ ∧
    ∀ σ, Trace.Run P E s prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct

/-- The inputs named in `fresh` are the encryptions under `(b, a)`, with the randomness
`(u x, e₁ x, e₂ x)`, of stored plaintext polynomials `p x` that represent their messages
(`p x mod t = m x`) and have norm at most the declared bound `Bp`; the other inputs (plaintext
operands) meet their declared bounds. Nothing else is assumed of a fresh input: a bound declared for it is not assumed (and
`freshOK?` rejects the program). -/
def FreshInputs (P : FullParams) (prog : Program) (fresh : List Var) (Bp : ℕ)
    (s b a : IntPoly P.src.N) (u e₁ e₂ p : Var → IntPoly P.src.N)
    (m : Var → Poly P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N)) : Prop :=
  (∀ x ∈ fresh, cts x = encrypt P.src.t b a (p x) (u x) (e₁ x) (e₂ x) ∧
      ofInt P.src.t (p x) = m x ∧ normInf (p x) ≤ Bp) ∧
    ∀ x d bd, x ∉ fresh → prog.inputs.find? (·.name = x) = some d → prog.boundOf x = some bd →
      Encrypts P s bd (inputVal P (fun x => .exact (m x)) d) (cts x)

/-- **Deterministic core.** If the reference analysis accepts at an input noise of at least
`Bp + t·ε`, the inputs pass `freshOK?`, and the error of every fresh encryption is at most
`ε`, then every output of every run is right, for all messages and all stored plaintext
polynomials within `Bp`. -/
theorem fresh_sound (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp ε : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hnoise : freshNoise P.src.t Bp ε ≤ P.inputNoise)
    (fresh : List Var) (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (s e b a : IntPoly P.src.N)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly P.src.N)
    (hgood : ∀ x ∈ fresh, normInf (freshError s e (u x) (e₁ x) (e₂ x)) ≤ ε)
    (p : Var → IntPoly P.src.N)
    (m : Var → Poly P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : FreshInputs P prog fresh Bp s b a u e₁ e₂ p m cts) :
    OutputsExact P E prog B s m cts := sorry

/-- The failure event: for this draw `ω` of the encryption randomness there are stored plaintext
polynomials within `Bp`, messages (and plaintext operands within their bounds) for which some
output of some run is wrong. -/
def FreshFails (P : FullParams) (E : Trace.Budget) (prog : Program) (B : ℕ) (fresh : List Var)
    (Bp : ℕ) (s b a : IntPoly P.src.N) {Ω : Type*} (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (ω : Ω) : Prop :=
  ∃ (p : Var → IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N)
      (cts : Var → List (IntPoly P.src.N)),
    FreshInputs P prog fresh Bp s b a (fun x => u x ω) (fun x => e₁ x ω) (fun x => e₂ x ω)
        p m cts ∧
      ¬ OutputsExact P E prog B s m cts

/-- **The noise headline with probabilistic fresh noise.** Fix valid BGV parameters, a program
the reference analysis accepts at input noise at least `Bp + t·(ε + D)`, whose inputs pass
`freshOK?`, where `D` is at least the mean drift `μ·(N·B_k + 1 + N·B_s)`, `μ = mn/md`; any secret
within the secret bound, any public key for it with error at most `B_k`; and, on any probability
space, for each fresh input a randomness triple meeting `SamplerOK` (the triples of different
inputs need not be independent of each other). Then the probability that *there exist* stored
plaintext polynomials within `Bp` and messages for which some output of some run fails to
encrypt (hence decrypt to) the value `Source.eval` computes, with noise at most `B`, is at most
`n · 2N · exp(−ε² / (2·V))`, `n` the number of fresh inputs. (For mean-zero samplers, `mn = 0`,
take `D = 0`.) See the module docstring for what this does and does not say about adaptively
chosen messages. -/
theorem fresh_certified (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp ε D : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hnoise : freshNoise P.src.t Bp (ε + D) ≤ P.inputNoise)
    (fresh : List Var) (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (Bk Bu B1 B2 mn md : ℕ)
    (hD : (mn : ℝ) / md * (P.src.N * Bk + 1 + P.src.N * P.secretBound : ℕ) ≤ D)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤
      fresh.length * (2 * P.src.N *
        Real.exp (-(ε : ℝ) ^ 2 / (2 * (varProxy P.src.N P.secretBound Bk Bu B1 B2 : ℝ)))) :=
  sorry

/-! ## 5. From a security exponent to an error bound -/

/-- **`epsFor` is large enough.** For a positive variance proxy,
`count · exp(−epsFor² / (2·V)) ≤ 2^(−κ)`. -/
theorem epsFor_spec (V count κ : ℕ) (hV : 0 < V) :
    (count : ℝ) * Real.exp (-(epsFor V count κ : ℝ) ^ 2 / (2 * (V : ℝ))) ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-- **The tail bound behind `fhe_check --kappa κ`** (one program, one bound; the tool's verdict
cites `Challenge.Certify.fresh_kappa_certified`). With
`ε = epsFor V (n·2N) κ + meanDrift (N·B_k + 1 + N·B_s) mn md`, `V = varProxy` (positive) and a
positive denominator `md`, the failure probability of `fresh_certified` is at most `2^(−κ)`. -/
theorem fresh_certified_kappa (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp κ : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (Bk Bu B1 B2 mn md : ℕ)
    (hV : 0 < varProxy P.src.N P.secretBound Bk Bu B1 B2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxy P.src.N P.secretBound Bk Bu B1 B2)
        (fresh.length * (2 * P.src.N)) κ +
      meanDrift (P.src.N * Bk + 1 + P.src.N * P.secretBound) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-! ## 6. Non-vacuity and discrimination -/

/-- A fair sign scaled to `B`. -/
def coin (B : ℕ) (x : Bool) : ℤ := if x then B else -B

/-- **`SamplerOK` is satisfiable** by an explicit product measure: `3N` independent fair coins,
each coefficient `±` its bound (the fair coin is `½·(δ_true + δ_false)`), for every declared
mean bound `mn/md` (the coins have mean zero). (So `freshError_tail` and `fresh_certified` are
about something; this sampler also has the largest variance the bounds allow.) -/
theorem samplerOK_rademacher (N Bu B1 B2 mn md : ℕ) :
    SamplerOK (N := N)
      (Measure.pi fun _ : Fin N ⊕ Fin N ⊕ Fin N =>
        ((2⁻¹ : NNReal) • (Measure.dirac true + Measure.dirac false) : Measure Bool))
      Bu B1 B2 mn md
      (fun ω => ⟨fun i => coin Bu (ω (.inl i))⟩)
      (fun ω => ⟨fun i => coin B1 (ω (.inr (.inl i)))⟩)
      (fun ω => ⟨fun i => coin B2 (ω (.inr (.inr i)))⟩) := sorry

-- OpenFHE's defaults at depth 2 (`N = 2¹⁴`, `t = 65537`, error bound 39, ternary `u` and `s`),
-- two fresh inputs, `κ = 128`: the error bound is 99749 (`2^16.6`) against the worst case
-- 1277991 (`2^20.3`), so the input noise drops from `2^36.29` to `2^32.61` (mean-zero samplers,
-- packed encoding: `Bp = t − 1`).
#guard varProxy 16384 1 39 1 39 39 == 39 ^ 2 * (2 * 16384 + 1)
#guard epsFor (varProxy 16384 1 39 1 39 39) (2 * (2 * 16384)) 128 == 99749
#guard epsFor (varProxy 16384 1 39 1 39 39) (2 * (2 * 16384)) 64 == 74348
#guard epsFor (varProxy 16384 1 39 1 39 39) (2 * (2 * 16384)) 40 == 62204
#guard epsFor (varProxy 16384 1 39 1 39 39) (2 * (2 * 16384)) 128 < worstError 16384 1 39 1 39 39
#guard freshNoise 65537 65536 99749 == 6537315749
#guard freshNoise 65537 65536 99749 < freshNoise 65537 65536 1277991
-- A mean bound of `3431/2⁶⁴` costs a drift of 1
-- in `ε` at these parameters (the real drift is about `1.2·10⁻¹⁰`; `meanDrift` rounds up): the
-- input noise rises by `t`. A mean bound of `2⁻²⁰` would cost 1 as well, one of `1/100` 6554.
#guard meanDrift (16384 * 39 + 1 + 16384 * 1) 3431 (2 ^ 64) == 1
#guard meanDrift (16384 * 39 + 1 + 16384 * 1) 0 1 == 0
#guard meanDrift (16384 * 39 + 1 + 16384 * 1) 1 (2 ^ 20) == 1
#guard meanDrift (16384 * 39 + 1 + 16384 * 1) 1 100 == 6554
#guard freshNoise 65537 65536 (99749 + 1) == 6537315749 + 65537
-- The bound grows with `κ` and with the number of events, and is not below the standard
-- deviation scale `√V` (`39·√32769 ≈ 7060`).
#guard epsFor (varProxy 16384 1 39 1 39 39) (2 * (2 * 16384)) 0 == 33250
#guard epsFor (varProxy 16384 1 39 1 39 39) 1 0 == 1
-- For very large `κ` the high-probability bound exceeds the worst case: the tool must take the
-- smaller of the two (there is no gain, and no loss, from asking for too much).
#guard worstError 16384 1 39 1 39 39 < epsFor (varProxy 16384 1 39 1 39 39) (2 * (2 * 16384)) 30000
-- `freshOK?`: a fresh input must be a 2-component ciphertext under `s` whose modulus exceeds
-- twice the input noise, with no declared bound; any other input must be a 1-component value
-- that declares a bound.
#guard freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 16)],
    body := [.addPlain "c" "a" "p"], outputs := ["c"] } ["a"]
#guard !freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.add "c" "a" "b"], outputs := ["c"] } ["a"]
#guard !freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 3, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] } ["a"]
#guard !freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 3⟩], body := [.copy "c" "a"], outputs := ["c"] } ["a"]
#guard !freshOK? { Spec.FullParams.tinyBGV with inputNoise := 2 ^ 40 }
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] } ["a"]

-- A fresh input that also declares a bound is rejected. (Before this clause, a fresh input with
-- declared bound 0 passed, the reference analysis ran at noise 0 and accepted four squarings that
-- it rejects at the real input noise, and `FreshInputs` assumed the encryption had noise 0.)
#guard !freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩], bounds := [("a", 0)],
    body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
    outputs := ["c"] } ["a"]
#guard refAnalyze Spec.FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], bounds := [("a", 0)],
    body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
    outputs := ["c"] } == some 0
#guard refAnalyze Spec.FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩],
    body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
    outputs := ["c"] } == none
-- An input that is not fresh must be a 1-component value: a 2-component ciphertext with a
-- declared bound is not a plaintext operand.
#guard !freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], bounds := [("b", 16)],
    body := [.add "c" "a" "b"], outputs := ["c"] } ["a"]
-- No fresh input at all, or a fresh name that is not an input: rejected.
#guard !freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 16)],
    body := [.copy "c" "p"], outputs := ["c"] } []
#guard !freshOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] } ["a", "ghost"]

/-! ## 7. One-program certificates: decryption under the secret key itself

The noise headline concludes `Encrypts P s B v ct`, which is about the key the value `v` is
recorded under, `σ_g(s)` for the Galois element `g = v.key`. A library decrypts with `s`. The
statements below add the computed check `Spec.Encrypt.certOK?` (every output has `g = 1`; for the
switched decryption, `decryptAllOK?`) and conclude decryption with `s`. Each is about one
program with one bound; `Challenge.Certify` states the per-output, all-outputs-jointly versions
about `certify?`, which are the statements `fhe_check` cites. -/

/-- `freshOK?` implies what its docstring says of the fresh inputs: there is at least one, each
is a declared input, and none declares a bound. -/
theorem freshOK?_spec (P : FullParams) (prog : Program) (fresh : List Var)
    (h : freshOK? P prog fresh = true) :
    fresh ≠ [] ∧ ∀ x ∈ fresh, (∃ d ∈ prog.inputs, d.name = x) ∧ prog.boundOf x = none := sorry

/-- The key of an output is the same for all messages. -/
theorem outputKey?_eq (P : Params) (hk : P.kind = .bgv) (prog : Program)
    (msgs : Var → Msg P.t P.N) (ρ : Env P) (h : eval P prog msgs = some ρ) (o : Var) (v : Val P)
    (ho : ρ o = some v) : outputKey? P prog o = some v.key := sorry

/-- **What CERTIFIED means for the outputs.** The program is well formed and, at the end of every
run meeting the contracts, each output is a ciphertext under the secret key `s` itself whose
textbook decryption *with `s`* at its own level is the message `Source.eval` computes; and, if
`switched`, whose decryption *with `s`* by the library's switched decryption is that message
times `decScale` at the output's level. -/
def OutputsDecrypt (P : FullParams) (E : Trace.Budget) (prog : Program) (switched : Bool)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
    ∀ σ, Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
        v.key = 1 ∧
        bgvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m ∧
        (switched = true →
          Decrypt.bgvDecryptSwitched P.src.t (P.src.qs.take v.level) s
              (ct.map (ofInt (P.src.qs.take v.level).prod)) =
            Decrypt.decScale P.src v.level • m)

/-- **The worst-case certificate for one program and one bound** (the tool's worst-case verdict
cites `Challenge.Certify.worst_certified`, proved from this). If the reference analysis
accepts with `B` and `certOK?` accepts, then for every integer polynomial `s` as the secret (no
`SecretOK` hypothesis), all messages and all input
ciphertexts within the input noise (and their declared bounds), every output of every run
decrypts with `s`. -/
theorem certified_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program) (B : ℕ)
    (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    OutputsDecrypt P E prog switched s msgs cts := sorry

/-- **The fresh-encryption certificate, worst case, for one program and one bound** (the tool's
fallback verdict cites `Challenge.Certify.fresh_worst_certified`). No probability, and no
assumption on the means: if the reference analysis accepts at an input noise of at least
`Bp + t·worstError`, the inputs pass `freshOK?` and `certOK?` accepts, then for every secret
within `secretBound`, every public key for it with error at most `Bk`, all encryption
randomness within the bounds, all stored plaintext polynomials within `Bp` and all messages,
every output of every run decrypts with `s`. -/
theorem fresh_worst_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp : ℕ)
    (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (Bk Bu B1 B2 : ℕ)
    (hnoise : freshNoise P.src.t Bp (worstError P.src.N P.secretBound Bk Bu B1 B2) ≤
      P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly P.src.N)
    (hrand : ∀ x ∈ fresh, normInf (u x) ≤ Bu ∧ normInf (e₁ x) ≤ B1 ∧ normInf (e₂ x) ≤ B2)
    (p : Var → IntPoly P.src.N)
    (m : Var → Poly P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : FreshInputs P prog fresh Bp s b a u e₁ e₂ p m cts) :
    OutputsDecrypt P E prog switched s (fun x => .exact (m x)) cts := sorry

/-- The failure event of the probabilistic certificate: for this draw `ω` of the encryption
randomness there are stored plaintext polynomials within `Bp`, messages (and plaintext operands
within their bounds) for which `OutputsDecrypt` fails: some output of some run is not under `s`,
or does not decrypt with `s` to the value the program computes. -/
def DecryptFails (P : FullParams) (E : Trace.Budget) (prog : Program) (switched : Bool)
    (fresh : List Var) (Bp : ℕ) (s b a : IntPoly P.src.N) {Ω : Type*}
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N) (ω : Ω) : Prop :=
  ∃ (p : Var → IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N)
      (cts : Var → List (IntPoly P.src.N)),
    FreshInputs P prog fresh Bp s b a (fun x => u x ω) (fun x => e₁ x ω) (fun x => e₂ x ω)
        p m cts ∧
      ¬ OutputsDecrypt P E prog switched s (fun x => .exact (m x)) cts

/-- **The probabilistic certificate for one program and one bound**, with decryption, as one
statement (the tool's `--kappa` verdict cites `Challenge.Certify.fresh_kappa_certified`).
Under the hypotheses of `fresh_certified_kappa` and `certOK?`, the probability over the
encryption randomness that there exist stored plaintext polynomials within `Bp` and messages for
which some output of some run fails to
decrypt with `s` (textbook; and switched, if `switched`) is at most `2^(−κ)`. -/
theorem fresh_kappa_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp κ : ℕ)
    (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (Bk Bu B1 B2 mn md : ℕ)
    (hV : 0 < varProxy P.src.N P.secretBound Bk Bu B1 B2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxy P.src.N P.secretBound Bk Bu B1 B2)
        (fresh.length * (2 * P.src.N)) κ +
      meanDrift (P.src.N * Bk + 1 + P.src.N * P.secretBound) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s e b a : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | DecryptFails P E prog switched fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

-- Outputs under a rotated key are refused: after an automorphism the value is under `σ_5(s)`
-- until the key switch; an input declared under the Galois element 3 is under `σ_3(s)`.
#guard outputKey? Spec.FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5], outputs := ["o"] } "o" == some 5
#guard !outputsUnderS? Spec.FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5], outputs := ["o"] }
#guard outputsUnderS? Spec.FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5, .keySwitch "o" "o"],
    outputs := ["o"] }
#guard !outputsUnderS? Spec.FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 3⟩], body := [.copy "o" "a"], outputs := ["o"] }
#guard !outputsUnderS? Spec.FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["nope"] }
-- The reference analysis alone accepts the rotated-key program; `certOK?` is what refuses it.
#guard (refAnalyze Spec.FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5], outputs := ["o"] }).isSome
#guard !certOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5], outputs := ["o"] } 64 false
#guard certOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] } 64 true
-- `certOK?` with `switched` also needs `decryptAllOK?` (bound from `Challenge.Decrypt`'s guards).
#guard certOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] } 25765000000 false
#guard !certOK? Spec.FullParams.tinyBGV
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] } 25765000000 true

end Challenge.FreshNoise
