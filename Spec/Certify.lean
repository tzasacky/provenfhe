import Spec.Budget
import Spec.Encrypt

/-!
# Spec.Certify — what a certificate is decided from, and what it contains   (TRUSTED)

The data of the decision `Challenge.Certify.certify?` (a locked definition: it runs the locked
reference analyzer, so it cannot live here): its input (`Input`: parameters, key-switching
layout, program, decryption, the `Mode` that says where the input noise comes from, and the
declared modulus-switching method `MSMethod`) and its result (`Certificate`, `NoiseUsed`), with
the computations that do not involve the analyzer (`freshDrift`, `freshEps`, `layoutOK?`,
`keysRestrict?`). Nothing here is a claim; the statements are in
`Challenge.Certify`.
-/

namespace Spec.Certify
open Spec Spec.Source Spec.Budget Spec.Encrypt

/-- Where the noise of the inputs comes from. -/
inductive Mode
  /-- Worst case over the declared input noise `P.inputNoise`: any input ciphertexts within it
  (and within their declared bounds). -/
  | worstCase
  /-- The inputs named in `fresh` are fresh public-key encryptions (`Spec.Encrypt.encrypt`) of
  stored plaintext polynomials of norm at most `Bp` (`t − 1` for a packed encoding: module
  docstring of `Spec.Encrypt`); the public-key error is at most `Bk`, the encryption randomness
  `(u, e₁, e₂)` within `Bu`, `B1`, `B2`, and every one of its coefficients has mean at most
  `mn/md` in absolute value (`mn = 0`: mean-zero samplers); `κ` is the exponent of the failure
  probability asked for. All of these are assumptions about the encoder, the key and the
  samplers: the statements name them as hypotheses, and no check discharges them. The declared
  `P.inputNoise` is not used. -/
  | fresh (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
  /-- The inputs named in `fresh` are fresh public-key encryptions of stored plaintext
  polynomials of norm at most `Bp`, described in `ℓ₂` (`Challenge.FreshNoiseL2`): the squared
  `ℓ₂` norms of the public-key error and of the secret are at most `E2`, `S2`, and the
  coefficients of the encryption randomness `(u, e₁, e₂)` have mean at most `mn/md` in absolute
  value and are, about their means, sub-Gaussian with variance proxies at most `Vu`, `V1`, `V2`;
  `κ` is the exponent of the failure probability asked for. All of these numbers are assumptions
  about the encoder, the key and the samplers: the statements name them as hypotheses, and no
  check discharges them. The declared `P.inputNoise` is not used. (No support bounds are given
  in this mode, so there is no worst case to fall back to.) -/
  | freshL2 (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)

/-- The modulus-switching method an input declares: which representative of `[−c·t⁻¹]_q` the
t-corrected switch (also the one inside the switched decryption) takes. The certified budgets
`Spec.Budget.msBudgetAt` hold for the centred one only (module docstring of `Spec.Budget`), and
`certify?` returns nothing for any other declaration. -/
inductive MSMethod
  /-- The representative of least absolute value (OpenFHE `ModReduce`). -/
  | centred
  /-- The representative in `[0, q)`. -/
  | canonical
  /-- Anything else. -/
  | other
  deriving DecidableEq, Repr

/-- What `certify?` decides about: the decoded data, nothing else. -/
structure Input where
  /-- Parameters: ring dimension, plaintext modulus, modulus chain, special primes, secret bound,
  key noise, and (worst-case mode) the input noise. -/
  P : FullParams
  /-- The digits of hybrid key switching at every level, and which representatives it uses. -/
  lay : KSLayout
  prog : Program
  /-- Which decryption the outputs get: `false` for textbook decryption at the output's level,
  `true` if moreover the library's decryption with the phase switched to one limb
  (`Spec.Decrypt.bgvDecryptSwitched`) must be exact. -/
  switched : Bool
  mode : Mode
  /-- The declared modulus-switching method. A declaration, like `lay.canonical` for key
  switching: that the library does what is declared is not checked. -/
  msMethod : MSMethod

/-- The input noise a certificate is about. -/
inductive NoiseUsed
  /-- The declared `P.inputNoise` (mode `worstCase`). -/
  | declared
  /-- `freshNoise t Bp ε` with `ε = epsFor … + meanDrift …`: holds with probability at least
  `1 − 2^(−κ)`. -/
  | freshKappa
  /-- `freshNoise t Bp ε` with `ε = worstError …`: holds for all randomness within the bounds. -/
  | freshWorst
  /-- `freshNoise t Bp ε` with `ε = epsFor (varProxyL2 …) … + meanDrift …` (mode `freshL2`): holds
  with probability at least `1 − 2^(−κ)`. -/
  | freshKappaL2
  deriving DecidableEq, Repr

/-- What `certify?` returns: everything the tool prints about an accepted input. -/
structure Certificate where
  /-- The parameters the analysis was run at: `x.P`, with the input noise replaced by
  `freshNoise t Bp eps` in the fresh-encryption modes. -/
  params : FullParams
  /-- The budget the analysis was run at: `Spec.Budget.certified params x.lay`. -/
  budget : Trace.Budget
  used : NoiseUsed
  /-- The bound on the error of a fresh encryption (`0` in the worst-case mode, where it plays no
  role). In the probabilistic cases it includes `drift`. -/
  eps : ℕ
  /-- The part of `eps` that pays for the declared mean bound of the samplers:
  `Spec.Encrypt.meanDrift …` (`0` when the declared mean bound is `0`, in the worst-case mode,
  and when the worst case of the fresh error was used). -/
  drift : ℕ
  /-- What `refAnalyze` returns on the whole program. -/
  bound : ℕ
  /-- Each output, in order, with its own noise bound: what `refAnalyze` returns on the program
  with that output alone. -/
  outputs : List (Var × ℕ)

/-- The mean drift of the support-bound mode: `meanDrift` at the weight `N·B_k + 1 + N·B_s`. -/
def freshDrift (P : FullParams) (Bk mn md : ℕ) : ℕ :=
  meanDrift (P.src.N * Bk + 1 + P.src.N * P.secretBound) mn md

/-- The error bound of a fresh encryption, what kind of bound it is, and the drift it contains:
the high-probability bound `epsFor V (n·2N) κ + freshDrift` if it is below the worst case
`worstError`, else the worst case (which holds whatever the means are: drift `0`). -/
def freshEps (P : FullParams) (n Bk Bu B1 B2 mn md κ : ℕ) : ℕ × NoiseUsed × ℕ :=
  let drift := freshDrift P Bk mn md
  let epsK := epsFor (varProxy P.src.N P.secretBound Bk Bu B1 B2) (n * (2 * P.src.N)) κ + drift
  let worst := worstError P.src.N P.secretBound Bk Bu B1 B2
  if worst ≤ epsK then (worst, .freshWorst, 0) else (epsK, .freshKappa, drift)

/-- The key-switching layout restricts from the top level `L` of the chain to every level
`1, …, L` (`Spec.Budget.restrictsTo`): it is usable at the top level, and the digits of every
level are the top-level digits cut down. In particular it is usable at every level
(`Challenge.Budget.restrictsTo_okAt`). -/
def layoutOK? (P : FullParams) (lay : KSLayout) : Bool :=
  (List.range P.src.qs.length).all fun i => restrictsTo lay P.src.qs.length (i + 1)

/-- The size condition under which a top-level BGV key is a valid key at every lower level
(hypothesis 2 in the docstring of `Spec.Budget.KSLayout`), at the smallest modulus `q₀·P`:
`2·(⌊keyNoise/t⌋·t) < q₀·P`. -/
def keysRestrict? (P : FullParams) : Bool :=
  decide (2 * (P.keyNoise / P.src.t * P.src.t) < P.src.modulus 1 * specialProd P)

end Spec.Certify
