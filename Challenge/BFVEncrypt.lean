import Challenge.BFVEncrypt.Defs
import Challenge.CertifyBFV
import Challenge.FreshNoise
import Challenge.FreshNoiseL2

/-!
# Challenge.BFVEncrypt — fresh OpenFHE BFV encryptions, and certificates computed from them   (LOCKED statements; proofs in `Validation/`)

`Spec.EncryptBFV.encryptBFV` is OpenFHE's BFV public-key encryption (`STANDARD`). These pins:

1. **The encryption.** `scaleUpCeil_spec`: the scaled plaintext is `⌈Q·p/t⌉`;
   `scaleUpCeil_timesQovert`: its residue modulo every limb is what `DCRTPoly::TimesQovert`
   computes from the stored coefficient (`[[x·NegQModt]_t · t⁻¹]_q`, NegQModt = `t − Q mod t`);
   `phase_encryptBFV`: the phase is `⌈Q·p/t⌉ + freshError` (the BGV error with factor 1);
   `encryptBFV_encrypts`: a fresh encryption of `m` (stored as `liftMsg m`) `BFVEncrypts` `m`
   with noise `freshNoiseBFV t Q ε = ε + encodeDev t Q` when the error is at most `ε` and that
   bound passes the decryption condition `decOK`. `encodeDev_needed`: the deterministic encoding
   term cannot be dropped (a fresh encryption with zero error whose noise is `encodeDev`, not
   `0`). The worst case and the tail bounds of the error are the BGV ones
   (`Challenge.FreshNoise.freshError_worst`, `freshError_tail`,
   `Challenge.FreshNoiseL2.freshError_tail_l2`), applied to the same `freshError`.
2. **The certificate** `certifyBFVFresh?` (`Challenge.BFVEncrypt.Defs`):
   `certifyBFVFresh?_spec` (what was analysed: `certifyBFV?` at the declared parameters with the
   input noise replaced by `freshInputNoise … fc.eps`), `_worst_eps`, `_kappa_eps`, `_kappaL2_eps`
   (which `ε`); `certifyBFVFresh?_worst` (no probability: every output of every run decrypts with
   `s` to the message the program computes, with noise at most its own bound, for every key and
   all encryption randomness within the support bounds and all messages);
   `certifyBFVFresh?_kappa`, `_kappaL2` (the probability over the encryption randomness that
   there exist messages for which some output of some run fails is at most `2^(−κ)`).
3. Discrimination and non-vacuity: `#guard`s and closed pins at the end.

**What the probability is over, and what is not claimed** (as for BGV, `Challenge.FreshNoise`).
The secret, the public key and its error, the program and the parameters are fixed first; the
probability space carries the encryption randomness of the fresh inputs only. The event is
"there EXIST messages (and plaintext operands within their bounds) for which some output of some
run is wrong": the error of a fresh encryption does not depend on the message, so the statement
holds for messages chosen after the randomness, by anyone. The bound `2^(−κ)` comes from a union
bound over **`n·2N` events** (`n = fresh.length` fresh encryptions, `2N` one-sided tail events of
the `N` coefficients of each error; `epsFor V (n·2N) κ`); it is the failure probability **per
execution of the program on one set of fresh encryptions**. Evaluation is worst case: every run
meeting the `Spec.TraceBFV` contracts within the certified budget, no probability. Not covered: a
party who can make the encryptor re-draw, discard or choose among encryptions (against a party
choosing among `Q` encryptions or executions, `κ` must be raised by `log₂ Q`); random keys (the
key is universally quantified within its bounds); anything about security; whether a library's
sampler meets `SamplerOK`/`SubGaussSamplerOK` (hypotheses); EXTENDED encryption (`Spec.EncryptBFV`, module docstring).
-/

namespace Challenge.BFVEncrypt
open Spec NPoly Scheme Source Correct Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
open Challenge.BFV Challenge.CertifyBFV Challenge.FreshNoise Challenge.FreshNoiseL2
open MeasureTheory ProbabilityTheory

variable {N : ℕ}

/-! ## 1. The encryption -/

/-- **The scaled plaintext is `⌈Q·p/t⌉`**: `0 ≤ t·z − Q·p < t` for every coefficient `z`. -/
theorem scaleUpCeil_spec (t Q : ℕ) (ht : 0 < t) (p : IntPoly N) (i : Fin N) :
    0 ≤ (t : ℤ) * (scaleUpCeil t Q p).coeff i - (Q : ℤ) * p.coeff i ∧
      (t : ℤ) * (scaleUpCeil t Q p).coeff i - (Q : ℤ) * p.coeff i < t := sorry

/-- **`scaleUpCeil` is what `DCRTPoly::TimesQovert` computes** (`dcrtpoly-impl.h:918-935`): for a
limb `q` of `Q` coprime to `t` and a stored coefficient `p ∈ [0, q)` (its residue `x = p`), the
residue of `⌈Q·p/t⌉` modulo `q` is `[[x · (t − Q mod t)]_t · t⁻¹]_q`. -/
theorem scaleUpCeil_timesQovert (t Q q : ℕ) (ht : 0 < t) (hq : q ∣ Q) (hcop : Nat.Coprime t q)
    (p : IntPoly N) (i : Fin N) (hp0 : 0 ≤ p.coeff i) (hpq : p.coeff i < q) :
    (((scaleUpCeil t Q p).coeff i : ℤ) : ZMod q) =
      (((p.coeff i).toNat % q * (t - Q % t) % t : ℕ) : ZMod q) * (t : ZMod q)⁻¹ := sorry

/-- **Phase identity.** Under a public key with `b + a·s ≡ e (mod Q)` (noise scale 1), the phase of
`encryptBFV t Q b a p u e₁ e₂` is `⌈Q·p/t⌉ + (e·u + e₁ + e₂·s)` modulo `Q`. -/
theorem phase_encryptBFV (t Q : ℕ) (s e b a p u e₁ e₂ : IntPoly N)
    (hpk : PublicKeyOK 1 Q s e b a) :
    phase (ofInt Q s) ((encryptBFV t Q b a p u e₁ e₂).map (ofInt Q)) =
      ofInt Q (scaleUpCeil t Q p + freshError s e u e₁ e₂) := sorry

/-- **A fresh encryption encrypts its message.** If the error is at most `ε` and the bound
`freshNoiseBFV t Q ε` passes the decryption condition at `Q`, the encryption of the stored
plaintext `liftMsg m` (the only representative in `[0, t)`, which both OpenFHE encoders store
for BFV) `BFVEncrypts` `m` with noise at most `freshNoiseBFV t Q ε`. -/
theorem encryptBFV_encrypts (t Q ε : ℕ) (ht : 2 ≤ t) (s e b a u e₁ e₂ : IntPoly N)
    (m : Poly t N) (hpk : PublicKeyOK 1 Q s e b a)
    (hε : normInf (freshError s e u e₁ e₂) ≤ ε) (hdec : decOK t Q (freshNoiseBFV t Q ε) = true) :
    BFVEncrypts t (freshNoiseBFV t Q ε) s
      ((encryptBFV t Q b a (liftMsg m) u e₁ e₂).map (ofInt Q)) m := sorry

/-- **The encoding term is needed.** `N = 1`, `t = 3`, `Q = 100` (`⌊Q/t⌋ = 33`, `Q mod t = 1`),
message `2`, zero key and zero randomness (error `0`): the encryption adds `⌈200/3⌉ = 67`, so its
noise relative to `33·2 = 66` is `1 = encodeDev 3 100`; it encrypts `2` within
`freshNoiseBFV 3 100 0 = 1` and not within `0`. -/
theorem encodeDev_needed :
    PublicKeyOK 1 100 (0 : IntPoly 1) 0 0 0 ∧ freshNoiseBFV 3 100 0 = 1 ∧
    BFVEncrypts 3 (freshNoiseBFV 3 100 0) (0 : IntPoly 1)
      ((encryptBFV 3 100 0 0 (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) 0 0 0).map (ofInt 100))
      ⟨fun _ => 2⟩ ∧
    ¬ BFVEncrypts 3 0 (0 : IntPoly 1)
      ((encryptBFV 3 100 0 0 (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) 0 0 0).map (ofInt 100))
      ⟨fun _ => 2⟩ := sorry

-- OpenFHE at `N = 2¹⁴`, `t = 65537`, error bound 39, ternary `u` and `s`: the worst case of the
-- error is the frontend's `Be·(1 + 2N·Bs)`, and the input noise adds `encodeDev`.
#guard worstError 16384 1 39 1 39 39 == 39 * (1 + 2 * 16384)
#guard encodeDev 65537 (65537 * 3 + 5) == 5
#guard encodeDev 65537 (65537 * 3) == 0
#guard encodeDev 3 100 == 1 && encodeDev 3 101 == 2 && encodeDev 7 1000 == 6

/-! ## 2. The inputs -/

/-- `freshOKBFV?` implies what its docstring says. -/
theorem freshOKBFV?_spec (prog : Program) (fresh : List Var) (h : freshOKBFV? prog fresh = true) :
    fresh ≠ [] ∧ (∀ x ∈ fresh, ∃ d ∈ prog.inputs, d.name = x) ∧
    ∀ d ∈ prog.inputs,
      (d.name ∈ fresh → d.parts = 2 ∧ d.key = 1 ∧ prog.boundOf d.name = none) ∧
      (d.name ∉ fresh → d.parts = 1) := sorry

/-- The inputs named in `fresh` are OpenFHE encryptions (`encryptBFV` at the modulus of the level
of their first declaration) under `(b, a)`, with the randomness `(u x, e₁ x, e₂ x)`, of their
messages `m x` (stored as `liftMsg (m x)`); the other inputs are plaintext operands within their
bounds (`Spec.TraceBFV.PlainOK` at `Spec.TraceBFV.inputBound`, as `TraceBFV.InputsOK` has them). -/
def FreshInputsBFV (P : FullParams) (prog : Program) (fresh : List Var)
    (s b a : IntPoly P.src.N) (u e₁ e₂ : Var → IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  (∀ x ∈ fresh, ∀ d, prog.inputs.find? (·.name = x) = some d →
      cts x = encryptBFV P.src.t (P.src.modulus d.level) b a (liftMsg (m x)) (u x) (e₁ x) (e₂ x)) ∧
    ∀ x d, x ∉ fresh → prog.inputs.find? (·.name = x) = some d →
      TraceBFV.PlainOK P s (TraceBFV.inputBound P prog d)
        (inputVal P (fun y => .exact (m y)) d) (cts x)

/-! ## 3. The certificate -/

/-- **What `certifyBFVFresh?` analysed.** The parameters are the declared ones with the input
noise replaced by `freshInputNoise x.P x.prog fresh fc.eps`, the inputs pass `freshOKBFV?`, and
`fc.cert` is the certificate of `certifyBFV?` at those parameters (so every statement of
`Challenge.CertifyBFV` applies to it). -/
theorem certifyBFVFresh?_spec (x : InputBFV) (mode : FreshModeBFV) (fc : FreshCertBFV)
    (h : certifyBFVFresh? x mode = some fc) :
    fc.params = { x.P with inputNoise := freshInputNoise x.P x.prog mode.fresh fc.eps } ∧
    freshOKBFV? x.prog mode.fresh = true ∧
    certifyBFV? { x with P := fc.params } = some fc.cert := sorry

/-- **The worst-case mode uses the worst case of the error.** -/
theorem certifyBFVFresh?_worst_eps (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 : ℕ) (h : certifyBFVFresh? x (.worst fresh Bk Bu B1 B2) = some fc) :
    fc.eps = worstError x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ fc.used = .freshWorst ∧
      fc.drift = 0 := sorry

/-- **The `κ` mode: which error bound** (as `Challenge.Certify.certify?_fresh`): the variance proxy
and the denominator are positive, and `fc.eps` is `epsFor V (n·2N) κ + meanDrift …` below the
worst case (`.freshKappa`), or the worst case (`.freshWorst`, no drift). -/
theorem certifyBFVFresh?_kappa_eps (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 mn md κ : ℕ) (h : certifyBFVFresh? x (.kappa fresh Bk Bu B1 B2 mn md κ) = some fc) :
    0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ 0 < md ∧
    ((fc.used = .freshKappa ∧
        fc.drift = meanDrift (x.P.src.N * Bk + 1 + x.P.src.N * x.P.secretBound) mn md ∧
        fc.eps = epsFor (varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
          (fresh.length * (2 * x.P.src.N)) κ + fc.drift ∧
        fc.eps < worstError x.P.src.N x.P.secretBound Bk Bu B1 B2) ∨
      (fc.used = .freshWorst ∧ fc.drift = 0 ∧
        fc.eps = worstError x.P.src.N x.P.secretBound Bk Bu B1 B2)) := sorry

/-- **The `ℓ₂` mode: which error bound.** -/
theorem certifyBFVFresh?_kappaL2_eps (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (E2 S2 Vu V1 V2 mn md κ : ℕ)
    (h : certifyBFVFresh? x (.kappaL2 fresh E2 S2 Vu V1 V2 mn md κ) = some fc) :
    0 < varProxyL2 E2 S2 Vu V1 V2 ∧ 0 < md ∧ fc.used = .freshKappaL2 ∧
    fc.drift = meanDrift (E2 + 1 + S2) mn md ∧
    fc.eps = epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + fc.drift :=
  sorry

/-- **The worst-case BFV certificate with computed input noise** (`fhe_check` on a BFV program
without `--kappa`). If `certifyBFVFresh?` accepts in the mode `worst fresh Bk Bu B1 B2`, then for
every secret within the secret bound, every public key `(b, a)` for it with error at most `Bk`
(noise scale 1, at the top-level modulus), all encryption randomness within `Bu`, `B1`, `B2` and
all messages (and plaintext operands within their bounds): every output of every run within
`fc.cert.budget` is under `s`, decrypts with `s` to the message the program computes, and has
noise at most its own bound in `fc.cert.outputs`. No probability, no assumption on the means;
the declared input noise does not occur. -/
theorem certifyBFVFresh?_worst (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 : ℕ) (h : certifyBFVFresh? x (.worst fresh Bk Bu B1 B2) = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : SecretOK fc.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly fc.params.src.N)
    (hrand : ∀ y ∈ fresh, normInf (u y) ≤ Bu ∧ normInf (e₁ y) ≤ B1 ∧ normInf (e₂ y) ≤ B2)
    (m : Var → Poly fc.params.src.t fc.params.src.N) (cts : Var → List (IntPoly fc.params.src.N))
    (hin : FreshInputsBFV fc.params x.prog fresh s b a u e₁ e₂ m cts) :
    OutputsCertifiedBFV fc.params fc.cert.budget x.prog fc.cert.outputs s
      (fun y => .exact (m y)) cts := sorry

/-- The failure event: for this draw `ω` of the encryption randomness there are messages (and
plaintext operands within their bounds) for which **some** output of some run is not under `s`,
or does not decrypt with `s` to the value the program computes, or has noise above its own bound. -/
def FreshFailsBFV (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) (bounds : List (Var × ℕ))
    (fresh : List Var) (s b a : IntPoly P.src.N) {Ω : Type*}
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N) (ω : Ω) : Prop :=
  ∃ (m : Var → Poly P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N)),
    FreshInputsBFV P prog fresh s b a (fun y => u y ω) (fun y => e₁ y ω) (fun y => e₂ y ω) m cts ∧
      ¬ OutputsCertifiedBFV P E prog bounds s (fun y => .exact (m y)) cts

/-- **The probabilistic BFV certificate** (`fhe_check --kappa κ` on a BFV program). If
`certifyBFVFresh?` accepts in the mode `kappa fresh Bk Bu B1 B2 mn md κ` (whichever error bound it
used), then for every secret within the bound and every public key for it with error at most
`Bk`, on any probability space carrying, for each fresh input, randomness meeting `SamplerOK`
(independent coefficients within `Bu`, `B1`, `B2`, means at most `mn/md` in absolute value; the
triples of different inputs need not be independent of each other): the probability that there
exist messages for which some output of some run fails (not under `s`, wrong decryption, or noise
above its own bound in `fc.cert.outputs`) is at most `2^(−κ)`. Per execution; a union bound over
`n·2N` events (module docstring). -/
theorem certifyBFVFresh?_kappa (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 mn md κ : ℕ) (h : certifyBFVFresh? x (.kappa fresh Bk Bu B1 B2 mn md κ) = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : SecretOK fc.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly fc.params.src.N)
    (hsamp : ∀ y ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | FreshFailsBFV fc.params fc.cert.budget x.prog fc.cert.outputs fresh s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-- **The probabilistic BFV certificate in `ℓ₂`** (`fhe_check --kappa κ --l2`): the same, for a
key with `normSq s ≤ S2`, `normSq e ≤ E2` and randomness meeting `SubGaussSamplerOK` with the
proxies `Vu`, `V1`, `V2` and the mean bound `mn/md`. (The secret is not assumed within
`secretBound` here: the runs are those within the certified budget.) -/
theorem certifyBFVFresh?_kappaL2 (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (E2 S2 Vu V1 V2 mn md κ : ℕ)
    (h : certifyBFVFresh? x (.kappaL2 fresh E2 S2 Vu V1 V2 mn md κ) = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly fc.params.src.N)
    (hsamp : ∀ y ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | FreshFailsBFV fc.params fc.cert.budget x.prog fc.cert.outputs fresh s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-- **A run exists** for fresh inputs whose errors are within `fc.eps`, under a secret within
the secret bound: the statements above are not about an empty set of runs. -/
theorem certifyBFVFresh?_run_exists (x : InputBFV) (mode : FreshModeBFV) (fc : FreshCertBFV)
    (h : certifyBFVFresh? x mode = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : SecretOK fc.params.secretBound s)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly fc.params.src.N)
    (hgood : ∀ y ∈ mode.fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ fc.eps)
    (m : Var → Poly fc.params.src.t fc.params.src.N) (cts : Var → List (IntPoly fc.params.src.N))
    (hin : FreshInputsBFV fc.params x.prog mode.fresh s b a u e₁ e₂ m cts) :
    ∃ σ, TraceBFV.RunAt fc.params fc.cert.budget s 0 x.prog.body
      (initEnv fc.params.src x.prog fun y => .exact (m y)) (Trace.initCt fc.params x.prog cts) σ :=
  sorry

/-! ## 4. Discrimination

At `tinyBFV` (`N = 4`, `t = 17`, `Q = 65537·786433`, declared `inputNoise = 64`), `mulProg` (a
product of two fresh inputs, relinearized), with error bounds 2: `ε = worstError 4 1 2 1 2 2 = 18`
and the input noise analysed is `18 + encodeDev 17 Q`, whatever `inputNoise` is declared. -/

/-- `mulProg` at `tinyBFV` with textbook multiplication, the declared input noise set to `d`. -/
def tinyFresh (d : ℕ) : InputBFV :=
  ⟨{ tinyBFV with inputNoise := d }, Budget.uniformLayout 1, mulProg, some .textbook, false,
    none, true, []⟩

#guard encodeDev 17 (65537 * 786433) == 9
#guard ((certifyBFVFresh? (tinyFresh 0) (.worst ["a", "b"] 2 1 2 2)).map
  fun fc => (fc.params.inputNoise, fc.eps, fc.cert.bound)) ==
  ((certifyBFV? (tinyFresh 27)).map fun c => (27, 18, c.bound))
-- The declared input noise is not used: 0 and 2⁶⁰ give the same certificate.
#guard ((certifyBFVFresh? (tinyFresh 0) (.worst ["a", "b"] 2 1 2 2)).map (·.cert.bound)) ==
  ((certifyBFVFresh? (tinyFresh (2 ^ 60)) (.worst ["a", "b"] 2 1 2 2)).map (·.cert.bound))
-- REJECTED: sampler bounds whose worst case does not decrypt after the product.
#guard (certifyBFVFresh? (tinyFresh 0) (.worst ["a", "b"] 2000000 1 2000000 2000000)).isNone
#guard (certifyBFVFresh? (tinyFresh 0) (.worst ["a", "b"] 200000 1 200000 200000)).isSome
-- REJECTED: a fresh input that declares a bound; a fresh list missing a ciphertext input; an
-- empty fresh list; a fresh name that is not an input; a fresh input under a rotated key.
#guard (certifyBFVFresh? { tinyFresh 0 with prog := { mulProg with bounds := [("a", 0)] } }
  (.worst ["a", "b"] 2 1 2 2)).isNone
#guard (certifyBFVFresh? (tinyFresh 0) (.worst ["a"] 2 1 2 2)).isNone
#guard (certifyBFVFresh? (tinyFresh 0) (.worst [] 2 1 2 2)).isNone
#guard (certifyBFVFresh? (tinyFresh 0) (.worst ["a", "b", "ghost"] 2 1 2 2)).isNone
#guard (certifyBFVFresh? { tinyFresh 0 with
  prog := { mulProg with inputs := [⟨"a", 2, 2, 1, 3⟩, ⟨"b", 2, 2, 1, 1⟩] } }
  (.worst ["a", "b"] 2 1 2 2)).isNone
-- The `κ` mode: a zero variance proxy or a zero denominator is refused; at these tiny
-- parameters the high-probability bound is not below the worst case, which is used.
#guard (certifyBFVFresh? (tinyFresh 0) (.kappa ["a", "b"] 0 0 0 0 0 1 40)).isNone
#guard (certifyBFVFresh? (tinyFresh 0) (.kappa ["a", "b"] 2 1 2 2 0 0 40)).isNone
#guard ((certifyBFVFresh? (tinyFresh 0) (.kappa ["a", "b"] 2 1 2 2 0 1 40)).map
  fun fc => (fc.used, fc.eps)) == some (.freshWorst, 18)
-- At OpenFHE's `N = 2¹⁴`, error bound 39, two fresh inputs, `κ = 128`: the error bound is
-- 99749 instead of the worst case 1277991 (about 3.7 bits of noise saved).
#guard Spec.Certify.freshEps { sealBFV with src := { sealBFV.src with N := 16384 } }
  2 39 1 39 39 0 1 128 == (99749, .freshKappa, 0)

/-- `certifyBFVFresh?` accepts `mulProg` in the worst-case mode, analysing input noise
`18 + encodeDev 17 Q = 27` whatever input noise is declared. -/
theorem certifyBFVFresh?_accepts_mulProg :
    (certifyBFVFresh? (tinyFresh 0) (.worst ["a", "b"] 2 1 2 2)).map
      (fun fc => (fc.params.inputNoise, fc.eps)) = some (27, 18) := sorry

/-- `certifyBFVFresh?` rejects a fresh input that declares a bound of its own. -/
theorem certifyBFVFresh?_rejects_declaredBound :
    (certifyBFVFresh? { tinyFresh 0 with prog := { mulProg with bounds := [("a", 0)] } }
      (.worst ["a", "b"] 2 1 2 2)).isSome = false := sorry

/-- `certifyBFVFresh?` rejects a ciphertext input that is not named fresh. -/
theorem certifyBFVFresh?_rejects_unnamedCiphertext :
    (certifyBFVFresh? (tinyFresh 0) (.worst ["a"] 2 1 2 2)).isSome = false := sorry

end Challenge.BFVEncrypt
