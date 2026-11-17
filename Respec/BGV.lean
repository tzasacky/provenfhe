import Respec.RNS

/-!
# Respec.BGV — the BGV scheme as the literature and the libraries define it

Sources:
* [BGV12] Brakerski, Gentry, Vaikuntanathan, *(Leveled) Fully Homomorphic Encryption without
  Bootstrapping*, ITCS 2012, ePrint 2011/277. §3.1 (basic scheme `E`), §3.2 (key switching),
  §3.3 / Lemma 4 (modulus switching `Scale`), §4 (FHE scheme, `FHE.Refresh`).
* [GHS12] Gentry, Halevi, Smart, *Homomorphic Evaluation of the AES Circuit*, CRYPTO 2012,
  ePrint 2012/099. §2.2 (the BGV variant with `t`-multiples of noise, "critical quantity"
  `[⟨c,s⟩]_q`), §3.1 (key switching with a special modulus `P`), §3.2 (modulus switching with
  `δ ≡ −c mod q_ℓ`, `δ ≡ 0 mod t`), App. D (noise estimates).
* [HS20] Halevi, Shoup, *Design and implementation of HElib*, ePrint 2020/1481, §5 (BGV with
  the `intFactor`/correction factor).
* [KPZ21] Kim, Polyakov, Zucca, ePrint 2021/204, §2 (BGV: `c = (c₀,c₁)`, `c₀ + c₁s = m + t·e`),
  §4 / App. B (noise bounds, hybrid key switching, modulus switching with message scaling).
* [HES18] *Homomorphic Encryption Standard* (HomomorphicEncryption.org, Nov. 2018), §2.1.1 "BGV".
* OpenFHE v1.2.3: `src/pke/lib/schemebase/base-pke.cpp` (KeyGen l.43-96),
  `src/pke/lib/schemerns/rns-pke.cpp` (EncryptZeroCore l.108-196, DecryptCore l.198-222),
  `src/pke/lib/scheme/bgvrns/bgvrns-pke.cpp` (Decrypt l.44-99),
  `src/pke/lib/scheme/bgvrns/bgvrns-leveledshe.cpp` (ModReduceInternalInPlace l.45-77,
  AdjustLevelsAndDepthInPlace l.87-228, EvalMultCoreInPlace l.240-253),
  `src/pke/lib/scheme/bgvrns/bgvrns-cryptoparameters.cpp` (precomputations l.86-136),
  `src/pke/lib/schemebase/base-leveledshe.cpp` (EvalMultKeyGen l.135-148,
  EvalAutomorphismKeyGen l.380-418, EvalAutomorphism l.421-469),
  `src/pke/lib/keyswitch/keyswitch-hybrid.cpp`, `src/core/lib/math/nbtheory2.cpp`
  (FindAutomorphismIndex2n l.191-225).
* Microsoft SEAL v4.1.2: `native/src/seal/util/rlwe.cpp` (encrypt_zero_asymmetric l.189-280,
  encrypt_zero_symmetric l.282-390), `keygenerator.cpp` (generate_one_kswitch_key l.300-336),
  `util/rns.cpp` (mod_t_and_divide_q_last_ntt_inplace l.1203-1246), `evaluator.cpp`
  (mod_switch_scale_to_next l.1201-1290, apply_galois_inplace l.2362-2450), `decryptor.cpp`
  (bgv_decrypt l.189-230), `util/galois.cpp` (get_elt_from_step l.53-95),
  `util/scalingvariant.cpp` (l.90-105).
* Lattigo v6.1.0: `core/rlwe/keygenerator.go` (GenGaloisKey l.139-171), `core/rlwe/params.go`
  (GaloisElement l.577-580), `core/rlwe/gadgetciphertext.go` (l.180-220).

## Convention table (the places where another formalization may have diverged)

| item | BGV12/GHS12 | HES18 | OpenFHE | SEAL |
|---|---|---|---|---|
| decryption equation | `⟨c,s⟩`, `s=(1,s')` | `c₀+c₁s` | `c₀+c₁s` (rns-pke.cpp:198-222) | `c₀+c₁s` |
| public key | `b = a·s' + t·e` given as `A=(b,−a)` | `(−(a·s+t·e), a)` | `(t·e − a·s, a)` (base-pke.cpp:80-82) | `(−(a·s+t·e), a)` (rlwe.cpp:331) |
| sk-encryption of 0 | — | — | `(a·s + t·e, −a)` (rns-pke.cpp:130-136) | `(−(a·s+t·e), a)` |
| noise | `m + t·e` (LSB message) | same | same (`ns = t`) | same |
| plaintext lift into `R_Q` | `{0,1}` | n/a | `[0,t)` (packedencoding.cpp:59-98) | `[0,t)` |
| modulus switch `δ` | closest with `c' ≡ c (t)`; needs `q_ℓ ≡ 1 (t)` | — | `t·[−c·t⁻¹]_{q_ℓ}` centred | `−([c]_{q_ℓ} + q_ℓ·[−[c]_{q_ℓ}q_ℓ⁻¹]_t)` canonical |
| message after mod switch | unchanged (`q_ℓ ≡ 1 mod t`) | — | `q_ℓ⁻¹·m`, tracked in `scalingFactorInt` (FLEXIBLE*); `q_ℓ ≡ 1 (t)` in FIXED* | `q_ℓ⁻¹·m`, tracked in `correction_factor` |
| final decryption | `[[·]_q]_2` | `[·]_q mod t` | mod-switch down to `q₀` first, then `[[·]_{q₀}]_t` | exact conversion `[·]_Q mod t` |
| Galois key for `g` | — | — | from `s` to `σ_{g⁻¹}(s)`; key switch, **then** `σ_g` | from `σ_g(s)` to `s`; `σ_g`, **then** key switch |
| slot generator | — | — | `5` | `3` |
| `level` | counts down | — | `GetLevel()` counts **up** (#dropped limbs) | chain index counts down |
-/

namespace Respec.BGV

open Spec Respec

variable {N : ℕ}

/-! ## 1. Keys, ciphertexts, decryption -/

/-- A secret key: a small integer polynomial `s` (the key vector is `(1, s, s², …)`).
Source: BGV12 §3.1 `E.SecretKeyGen` (`sk = s = (1, s')`); GHS12 §2.2; HES18 §2.1.1
(`BGV.SecretKeyGen`); OpenFHE base-pke.cpp:60-76 (Gaussian, uniform ternary or sparse ternary). -/
abbrev SecretKey (N : ℕ) := IntPoly N

/-- Ternary secret: coefficients in `{-1, 0, 1}`. Source: HES18 §2.1.1 / Table 1 (the
"uniform ternary" distribution); OpenFHE `UNIFORM_TERNARY`. -/
def IsTernary (s : IntPoly N) : Prop := NPoly.normInf s ≤ 1

instance (s : IntPoly N) : Decidable (IsTernary s) := by unfold IsTernary; infer_instance

/-- A ciphertext: a vector `(c₀, c₁, …, c_d)` of ring elements modulo `Q`. Fresh ciphertexts
have two components; a tensor product has three.
Source: BGV12 §3.1 (`c ∈ R_q^2`), §3.2 (the "long" ciphertext `c₁ ⊗ c₂` under `s ⊗ s`);
OpenFHE `CiphertextImpl::m_elements`. -/
abbrev Ct (Q N : ℕ) := List (Poly Q N)

/-- The phase / inner product `⟨ct, (1, s, s², …)⟩ = Σ_i c_i·s^i mod Q`.
Source: BGV12 §3.1 `E.Dec` (`⟨c, s⟩`); OpenFHE `PKERNS::DecryptCore` rns-pke.cpp:198-222
(`b = c₀; b += sPower·c_i; sPower *= s`). **Sign**: all of BGV12, HES18, OpenFHE, SEAL, Lattigo use
`c₀ + c₁·s`; the `c₀ − c₁·s` form occurs in FHEW/TFHE-style (LWE) descriptions only. -/
def phase {Q : ℕ} (s : IntPoly N) (ct : Ct Q N) : Poly Q N :=
  psum (ct.zipIdx.map fun ci => ci.1 ⊠ ppow (red Q s) ci.2)

/-- **The critical quantity** `[⟨ct, s⟩]_Q`: the centred lift of the phase, an integer polynomial
with coefficients in `(-Q/2, Q/2]`. For a valid ciphertext it equals `m + t·e`.
Source: GHS12 §2.2 ("we call `[⟨c,s⟩]_q` the *noise* of `c`"); KPZ21 §2.2
("critical quantity"/`v = m + t·e`). -/
def crit {Q : ℕ} (s : IntPoly N) (ct : Ct Q N) : IntPoly N := liftC (phase s ct)

/-- **BGV decryption** `m = [[⟨ct, (1,s,s²,…)⟩]_Q]_t`. The inner bracket is the centred lift
`(-Q/2, Q/2]` and is essential; the outer reduction is returned as an element of `ℤ_t`, so its
choice of representative is immaterial (BGV12 writes `[·]_2` centred; OpenFHE
`DecryptionCRTInterpolate` poly-impl.h:564-572 returns `[0,t)`).
Source: BGV12 §3.1 `E.Dec(sk, c)`: "`m ← [[⟨c, s⟩]_q]_2`"; HES18 §2.1.1 `BGV.Decrypt`;
OpenFHE `PKEBGVRNS::Decrypt` bgvrns-pke.cpp:44-99 (which first mod-switches down to one limb,
l.56-60, then reduces the centred value mod `t`, l.96; test `ctL0` in `Respec/BGVTest.lean`
reproduces that route). -/
def decrypt {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : Ct Q N) : Poly t N := red t (crit s ct)

/-- The **wrong** decryption that uses the canonical lift `[0,Q)` for the inner reduction.
Recorded because it is the single most common error: it agrees with `decrypt` exactly when every
coefficient of `m + t·e` is non-negative, or when `Q ≡ 0 (mod t)` (never the case here, as
`gcd(t, Q) = 1`). -/
def decryptCanonicalWRONG {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : Ct Q N) : Poly t N :=
  red t (liftN (phase s ct))

/-- **"`ct` encrypts `m` with noise at most `B`"** (decidable form). The critical quantity
`v = [⟨ct,s⟩]_Q` satisfies `v ≡ m (mod t)` and `‖v‖∞ ≤ B`.
Because `v` is by definition the centred representative, `‖v‖∞ ≤ Q/2` always, and the statement
has content only for `B < Q/2`.
Source: GHS12 §2.2; KPZ21 §2.2 & §4 ("a ciphertext is valid as long as `‖m + t·e‖∞ < Q/2`");
BGV12 §3.1 (correctness of `E.Dec` when the noise has norm `< q/2`). -/
def Encrypts {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : Ct Q N) (m : Poly t N) (B : ℕ) : Prop :=
  NPoly.ofInt t (crit s ct) = m ∧ NPoly.normInf (crit s ct) ≤ B

instance {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : Ct Q N) (m : Poly t N) (B : ℕ) :
    Decidable (Encrypts t s ct m B) := by unfold Encrypts; infer_instance

/-- **The same invariant in the existential form cryptographers write**: there is an integer
polynomial `e` with `⟨ct, s⟩ ≡ m̃ + t·e (mod Q)` and `‖m̃ + t·e‖∞ ≤ B`, where `m̃` is the lift of
the message chosen by `ml`.
*Relation to `Encrypts`*: if `2·B < Q` the two are equivalent (the witness `m̃ + t·e` is then
forced to be the centred lift). Without `2·B < Q` this form is strictly weaker and does **not**
determine `m` (take `e` so that `m̃ + t·e` wraps); a formalization that states the invariant
existentially and forgets `2B < Q` proves nothing about decryption.
Source: KPZ21 §2.2 (`c₀ + c₁·s = m + t·e (mod Q)`); GHS12 §2.2. -/
def EncryptsEx {Q : ℕ} (ml : Lift) (t : ℕ) (s : IntPoly N) (ct : Ct Q N) (m : Poly t N)
    (B : ℕ) : Prop :=
  ∃ e : IntPoly N,
    phase s ct = NPoly.ofInt Q (liftBy ml m + zscale t e) ∧
      NPoly.normInf (liftBy ml m + zscale t e) ≤ B

/-- The invariant with an explicit **integer scaling factor** `sf ∈ ℤ_t^×`: the ciphertext
carries `sf·m`, and the decryptor returns `sf⁻¹·decrypt`.
Source: OpenFHE `scalingFactorInt` (encode multiplies by it, packedencoding.cpp:61-85; decode
multiplies by its inverse, packedencoding.cpp:202-207; `DecryptResult` returns it,
bgvrns-pke.cpp:98); SEAL `Ciphertext::correction_factor()` (decryptor.cpp:215-222: multiply by
the inverse); HS20 §5 (`intFactor`). -/
def EncryptsSF {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : Ct Q N) (m : Poly t N) (sf : ZMod t)
    (B : ℕ) : Prop :=
  Encrypts t s ct (sf • m) B

instance {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : Ct Q N) (m : Poly t N) (sf : ZMod t) (B : ℕ) :
    Decidable (EncryptsSF t s ct m sf B) := by unfold EncryptsSF; infer_instance

/-- Decryption followed by removal of the scaling factor. -/
def decryptSF {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : Ct Q N) (sf : ZMod t) : Poly t N :=
  sf⁻¹ ⊡ decrypt t s ct

/-! ## 2. Key generation and encryption (OpenFHE form, with the other sign conventions) -/

/-- A public key `(b, a)`. -/
structure PublicKey (Q N : ℕ) where
  /-- `pk[0]` -/
  b : Poly Q N
  /-- `pk[1]` -/
  a : Poly Q N

/-- **OpenFHE public key**: `pk = (b, a)` with `b = t·e − a·s`, so `b + a·s = t·e`.
Source: OpenFHE `PKEBase::KeyGenInternal` base-pke.cpp:80-82
(`Element b(ns * e - a * s)`, `ns = t` for BGV). -/
def pkGen {Q : ℕ} (t : ℕ) (s a e : IntPoly N) : PublicKey Q N where
  b := ((t : ℕ) : ZMod Q) ⊡ red Q e ⊟ red Q a ⊠ red Q s
  a := red Q a

/-- **HES18 / SEAL public key**: `pk = (−(a·s + t·e), a)`, so `b + a·s = −t·e` (error enters with
the opposite sign). Source: HES18 §2.1.1 `BGV.PublicKeyGen`; SEAL `encrypt_zero_symmetric`
rlwe.cpp:330-331 & 356-357 ("`(c[0], c[1]) = ([-(as+pe)]_q, a)` in BGV"). -/
def pkGenStd {Q : ℕ} (t : ℕ) (s a e : IntPoly N) : PublicKey Q N where
  b := pneg (red Q a ⊠ red Q s ⊞ ((t : ℕ) : ZMod Q) ⊡ red Q e)
  a := red Q a

/-- Embedding of a plaintext `m ∈ R_t` into `R_Q` through a lift. OpenFHE and SEAL use the
canonical lift `[0,t)` (OpenFHE packedencoding.cpp:59-98: negative inputs are stored as
`t − |v|` and the vector is re-labelled modulo `q₀`); most papers bound `‖m‖∞ ≤ t/2` (centred).
The choice does not affect correctness, only the constant in the fresh-noise bound. -/
def embed (ml : Lift) {t : ℕ} (Q : ℕ) (m : Poly t N) : Poly Q N := red Q (liftBy ml m)

/-- **Public-key encryption** (same shape in OpenFHE, SEAL and HES18):
`c₀ = b·u + t·e₀ + m`, `c₁ = a·u + t·e₁`, with `u` ternary (or Gaussian) and `e₀, e₁` errors.
Source: OpenFHE `PKERNS::EncryptZeroCore(publicKey)` rns-pke.cpp:169-193
(`c0 = p0*v + ns*e0; c1 = p1*v + ns*e1`) and `PKERNS::Encrypt` l.60 (`(*ba)[0] += plaintext`);
SEAL `encrypt_zero_asymmetric` rlwe.cpp:219, 248 ("`c[j] = public_key[j]*u + p*e[j]` in BGV");
HES18 §2.1.1 `BGV.Encrypt`. -/
def encrypt {Q t : ℕ} (ml : Lift) (pk : PublicKey Q N) (m : Poly t N) (u e0 e1 : IntPoly N) :
    Ct Q N :=
  [pk.b ⊠ red Q u ⊞ ((t : ℕ) : ZMod Q) ⊡ red Q e0 ⊞ embed ml Q m,
   pk.a ⊠ red Q u ⊞ ((t : ℕ) : ZMod Q) ⊡ red Q e1]

/-- **Secret-key encryption, OpenFHE**: `(a·s + t·e + m, −a)`.
Source: OpenFHE `PKERNS::EncryptZeroCore(privateKey)` rns-pke.cpp:124-136. -/
def encryptSym {Q t : ℕ} (ml : Lift) (s : IntPoly N) (m : Poly t N) (a e : IntPoly N) : Ct Q N :=
  [red Q a ⊠ red Q s ⊞ ((t : ℕ) : ZMod Q) ⊡ red Q e ⊞ embed ml Q m,
   pneg (red Q a)]

/-- **The fresh critical quantity** of `encrypt` under `pkGen` (OpenFHE signs):
`c₀ + c₁·s = (t·e − a·s)·u + t·e₀ + m + (a·u + t·e₁)·s = m + t·(e·u + e₀ + e₁·s)`.
With `pkGenStd` the term `e·u` enters with a minus sign: `m + t·(−e·u + e₀ + e₁·s)`.
Source: derivation from rns-pke.cpp:169-193 and base-pke.cpp:82; KPZ21 §2.2. -/
def freshCrit (ml : Lift) {t : ℕ} (m : Poly t N) (s e u e0 e1 : IntPoly N) : IntPoly N :=
  liftBy ml m ⊞ zscale t (e ⊠ u ⊞ e0 ⊞ e1 ⊠ s)

/-- The fresh critical quantity under the HES18/SEAL public key. -/
def freshCritStd (ml : Lift) {t : ℕ} (m : Poly t N) (s e u e0 e1 : IntPoly N) : IntPoly N :=
  liftBy ml m ⊞ zscale t (pneg (e ⊠ u) ⊞ e0 ⊞ e1 ⊠ s)

/-! ## 3. Homomorphic operations on ciphertext vectors -/

/-- Component-wise addition (the shorter vector is padded with zeros).
Source: BGV12 §4 `FHE.Add`; OpenFHE `LeveledSHEBase::EvalAddCore`. -/
def add {Q : ℕ} : Ct Q N → Ct Q N → Ct Q N
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a ⊞ b) :: add as bs

/-- Negation. -/
def neg {Q : ℕ} (a : Ct Q N) : Ct Q N := a.map pneg

/-- Multiplication by an integer constant (multiplies the critical quantity by the constant).
Source: OpenFHE `LeveledSHEBGVRNS::EvalMultCoreInPlace` bgvrns-leveledshe.cpp:240-253. -/
def mulConst {Q : ℕ} (c : ℤ) (a : Ct Q N) : Ct Q N := a.map (zsmul c)

/-- **Tensor product** (multiplication without relinearization): the coefficients of
`(Σ a_i Y^i)·(Σ b_j Y^j)`; for two 2-component inputs `(a₀b₀, a₀b₁ + a₁b₀, a₁b₁)`.
Then `⟨a⊗b, (1,s,s²)⟩ = ⟨a,(1,s)⟩·⟨b,(1,s)⟩`.
Source: BGV12 §3.2/§4 `FHE.Mult` step 1 ("the coefficient vector of the long linear equation
`L^long_{c₁,c₂}(x ⊗ x)`"); OpenFHE `LeveledSHERNS::EvalMultCore`. -/
def mulTensor {Q : ℕ} (a b : Ct Q N) : Ct Q N :=
  forceAll ((List.range (a.length + b.length - 1)).map fun k =>
    psum ((List.range (k + 1)).map fun i =>
      match a[i]?, b[k - i]? with
      | some x, some y => x ⊠ y
      | _, _ => 0))

/-- The Galois automorphism applied to every component. The result decrypts under `σ_g(s)` to
`σ_g(m)`. Source: GHS12 §2.3 / App. B (`κ_g`); OpenFHE base-leveledshe.cpp:465-466. -/
def automorphCt {Q : ℕ} (g : ℕ) (a : Ct Q N) : Ct Q N := a.map (pauto g)

/-! ## 4. Key-switching keys: the gadget, the validity predicate -/

/-- `Q̂_j = Q / Q_j` for a list of digit moduli `Q_0, …, Q_{d-1}` (pairwise coprime, product `Q`). -/
def qhat (Qs : List ℕ) (j : ℕ) : ℕ := (Qs.eraseIdx j).prod

/-- **Gadget factor, OpenFHE / SEAL / Lattigo form**:
`g_j = P · Q̂_j · [Q̂_j⁻¹]_{Q_j}  (mod Q·P)`, i.e. `P` times the CRT idempotent of digit `j`:
`g_j ≡ P (mod q_i)` for the limbs of digit `j`, `g_j ≡ 0` modulo every other `q_i` and modulo `P`.
The matching decomposition is the plain residue `[c]_{Q_j}` (`decompOF`).
Source: OpenFHE keyswitch-hybrid.cpp:113-125 (`PModq[i] * sOld` on the limbs of the part only);
SEAL keygenerator.cpp:327-332 (`factor = key_modulus.back() mod q_i`, added to limb `i` only);
Lattigo gadgetciphertext.go:204-212 ("`(pt·P)·(q_star·q_tild) = pt·P mod q[…], else 0`"). -/
def gadgetOF (P : ℕ) (Qs : List ℕ) (j : ℕ) : ℤ :=
  (P : ℤ) * (qhat Qs j : ℤ) * ((((qhat Qs j : ℕ) : ZMod (Qs.getD j 1))⁻¹).val : ℤ)

/-- **Gadget factor, Han–Ki form**: `g_j = P · Q̂_j`. The matching decomposition is
`[c · Q̂_j⁻¹]_{Q_j}` (`decompHK`).
Source: HK19 §3.2 (the generalized key-switching key `swk_j` encrypts `P·Q̂_j·s'` and the
decomposition is `([a·Q̂_j⁻¹]_{Q_j})_j`); KPZ21 App. B.2.3 follows this presentation. -/
def gadgetHK (P : ℕ) (Qs : List ℕ) (j : ℕ) : ℤ := (P : ℤ) * (qhat Qs j : ℤ)

/-- RNS digit decomposition, OpenFHE form: `D_j(c) = [c]_{Q_j}` (lifted by `c`).
Source: OpenFHE keyswitch-hybrid.cpp:373-377. -/
def decompOF (c : Lift) {Q : ℕ} (Qs : List ℕ) (j : ℕ) (x : Poly Q N) : IntPoly N :=
  force ⟨fun i => c.rep (((x.coeff i).val : ℕ) : ZMod (Qs.getD j 1))⟩

/-- RNS digit decomposition, Han–Ki form: `D_j(c) = [c·Q̂_j⁻¹]_{Q_j}`. Source: HK19 §3.2. -/
def decompHK (c : Lift) {Q : ℕ} (Qs : List ℕ) (j : ℕ) (x : Poly Q N) : IntPoly N :=
  force ⟨fun i => c.rep ((((x.coeff i).val : ℕ) : ZMod (Qs.getD j 1)) *
    ((qhat Qs j : ℕ) : ZMod (Qs.getD j 1))⁻¹)⟩

/-- **The gadget identity** `Σ_j D_j(x)·g_j ≡ P·x (mod Q·P)`, for a decomposition/gadget pair.
Holds for (`decompOF`, `gadgetOF`) and for (`decompHK`, `gadgetHK`) but for neither mixed pair. -/
def GadgetIdentity {Q : ℕ} (P : ℕ) (d : ℕ) (decomp : ℕ → Poly Q N → IntPoly N) (gad : ℕ → ℤ)
    (x : Poly Q N) : Prop :=
  psum ((List.range d).map fun j => zsmul (gad j) (red (Q * P) (decomp j x)))
    = zsmul (P : ℤ) (red (Q * P) (liftN x))

instance {Q : ℕ} (P d : ℕ) (decomp : ℕ → Poly Q N → IntPoly N) (gad : ℕ → ℤ) (x : Poly Q N) :
    Decidable (GadgetIdentity P d decomp gad x) := by unfold GadgetIdentity; infer_instance

/-- One digit `(b_j, a_j)` of a key-switching key, modulo `M = Q·P`. -/
structure KskDigit (M N : ℕ) where
  /-- `b_j` -/
  b : Poly M N
  /-- `a_j` -/
  a : Poly M N

/-- The centred "error" of one key digit: `[b_j + a_j·sTo − g_j·sFrom]_{QP}`. For a valid BGV key
it equals `t·e_j`. -/
def kskErr {M : ℕ} (g : ℤ) (sFrom sTo : IntPoly N) (kd : KskDigit M N) : IntPoly N :=
  liftC (kd.b ⊞ kd.a ⊠ red M sTo ⊟ zsmul g (red M sFrom))

/-- **A valid hybrid key-switching key from `sFrom` to `sTo`** (BGV; `sFrom = s²` for
relinearization, `sFrom = σ_g(s)` or `sTo = σ_{g⁻¹}(s)` for automorphisms): a list of digits
`(b_j, a_j) ∈ R_{QP}²` such that for every `j`

  `b_j + a_j·sTo = g_j·sFrom + t·e_j  (mod Q·P)`,  `‖e_j‖∞ ≤ B`,

with `g_j` the gadget factor (`gadgetOF P Qs` or `gadgetHK P Qs`).
Source: GHS12 §3.1 (single digit: `b = −a·s + P·s' + 2e mod P·q`); HK19 §3.2;
KPZ21 App. B.2.3; OpenFHE keyswitch-hybrid.cpp:103-127. Sign variant: SEAL has
`b_j + a_j·sTo = g_j·sFrom − t·e_j`, which satisfies this predicate with `−e_j`. -/
def IsKsk {M : ℕ} (t : ℕ) (gad : ℕ → ℤ) (sFrom sTo : IntPoly N) (ksk : List (KskDigit M N))
    (B : ℕ) : Prop :=
  ∀ j (h : j < ksk.length), ∃ e : IntPoly N, NPoly.normInf e ≤ B ∧
    (ksk[j]).b + (ksk[j]).a * NPoly.ofInt M sTo
      = NPoly.ofInt M (zscale t e) + zsmul (gad j) (NPoly.ofInt M sFrom)

/-- Decidable sufficient check for `IsKsk` (and equivalent to it when `2·t·B < Q·P`): the centred
error of every digit is divisible by `t` and at most `t·B`. -/
def kskCheck {M : ℕ} (t : ℕ) (gad : ℕ → ℤ) (sFrom sTo : IntPoly N) (ksk : List (KskDigit M N))
    (B : ℕ) : Bool :=
  ksk.zipIdx.all fun kj =>
    let err := kskErr (gad kj.2) sFrom sTo kj.1
    decide (DivisibleBy t err) && decide (NPoly.normInf err ≤ t * B)

/-- CRT of two coprime moduli: the element of `ℤ_{QP}` with the given residues. -/
def crt2 (Q P : ℕ) (a : ZMod Q) (b : ZMod P) : ZMod (Q * P) :=
  ((a.val * P * (((P : ℕ) : ZMod Q)⁻¹).val + b.val * Q * (((Q : ℕ) : ZMod P)⁻¹).val : ℕ) :
    ZMod (Q * P))

/-- Coefficient-wise `crt2`. -/
def crt2Poly {Q P : ℕ} (a : Poly Q N) (b : Poly P N) : Poly (Q * P) N :=
  force ⟨fun n => crt2 Q P (a.coeff n) (b.coeff n)⟩

/-- The element of `R_{QP}` with the given limbs over `Q ∪ P`. -/
def joinQP {k l : ℕ} (q : Basis k) (p : Basis l) (xQ : RnsPoly q N) (xP : RnsPoly p N) :
    Poly (q.prod * p.prod) N :=
  crt2Poly (ofRns q xQ) (ofRns p xP)

/-- View an RNS hybrid key (limbs over `Q ∪ P`) as a list of digits modulo `Q·P`. -/
def keyToBig {k l d : ℕ} {q : Basis k} {p : Basis l} (key : HybridKey q p d N) :
    List (KskDigit (q.prod * p.prod) N) :=
  (List.finRange d).map fun j =>
    ⟨joinQP q p (key.bQ j) (key.bP j), joinQP q p (key.aQ j) (key.aP j)⟩

/-- BGV ModDown of one element of `R_{QP}` in arbitrary precision: `(X − δ)/P mod Q` with
`δ = t·[X·t⁻¹]_P` (lifted by `c`). Source: GHS12 §3.1; KPZ21 App. B.2.3. -/
def modDownBigElt (c : Lift) (t Q P : ℕ) (y : Poly (Q * P) N) : Poly Q N :=
  force ⟨fun i =>
    let X : ℤ := ((y.coeff i).val : ℤ)
    let δ : ℤ := (t : ℤ) * c.rep ((X : ZMod P) * ((t : ℕ) : ZMod P)⁻¹)
    (((X - δ) / (P : ℤ) : ℤ) : ZMod Q)⟩

/-- **Hybrid key switching, arbitrary-precision reference** (exact digits, no ModUp overflow):
`x_b = Σ_j D_j(x)·b_j`, `x_a = Σ_j D_j(x)·a_j` in `R_{QP}`; then each is divided by `P` after
subtracting `δ = t·[x·t⁻¹]_P` (so that `δ ≡ x mod P`, `δ ≡ 0 mod t`).
Output `(k₀, k₁)` with `k₀ + k₁·sTo ≡ x·sFrom + t·(Σ_j D_j(x)·e_j − δ'(sTo))/P (mod Q)`.
Source: GHS12 §3.1 (one digit); HK19 §3.2; KPZ21 App. B.2.3. The RNS algorithm
`Respec.hybridKeySwitch` differs from this one only by multiples of `Q_j` in the digits and of `P`
in `δ` (the fast-base-conversion overflows). -/
def keySwitchBig (c : Lift) (t Q P : ℕ) (decomp : ℕ → Poly Q N → IntPoly N)
    (ksk : List (KskDigit (Q * P) N)) (x : Poly Q N) : Poly Q N × Poly Q N :=
  (modDownBigElt c t Q P
      (psum (ksk.zipIdx.map fun kj => red (Q * P) (decomp kj.2 x) ⊠ kj.1.b)),
   modDownBigElt c t Q P
      (psum (ksk.zipIdx.map fun kj => red (Q * P) (decomp kj.2 x) ⊠ kj.1.a)))

/-! ## 5. Modulus switching -/

/-- Which correction `δ` a modulus switch from `Q = Q'·q_ℓ` to `Q'` adds before the exact division
by `q_ℓ`. All satisfy `δ ≡ −c (mod q_ℓ)`. -/
inductive MSVariant
  /-- GHS12 §3.2 / OpenFHE `ModReduce` (dcrtpoly-impl.h:758-777): `δ = t·[−c·t⁻¹]_{q_ℓ}`,
  with the given lift of the residue (OpenFHE: centred). `δ ≡ 0 (mod t)`. -/
  | ghs (c : Lift)
  /-- SEAL `mod_t_and_divide_q_last_ntt_inplace` (util/rns.cpp:1203-1246):
  `δ = −(r + q_ℓ·[−r·q_ℓ⁻¹]_t)` with `r = [c]_{q_ℓ}` and both residues canonical.
  `δ ≡ 0 (mod t)`, `|δ| < t·q_ℓ`. -/
  | seal
  /-- BGV12 Lemma 4 (`Scale`): the `δ` with `|δ| ≤ t·q_ℓ/2` such that `c' = (c+δ)/q_ℓ` satisfies
  `c' ≡ c (mod t)`, i.e. `δ ≡ (q_ℓ − 1)·c (mod t)`. Equals `ghs .centred` when `q_ℓ ≡ 1 (mod t)`,
  which is the hypothesis under which BGV12 proves correctness. -/
  | bgv12
  deriving DecidableEq, Repr

/-- The correction `δ` for one coefficient with canonical value `x ∈ [0, Q)`. -/
def msDeltaZ (v : MSVariant) (t ql : ℕ) (x : ℤ) : ℤ :=
  match v with
  | .ghs c => (t : ℤ) * c.rep (-(x : ZMod ql) * ((t : ℕ) : ZMod ql)⁻¹)
  | .seal =>
      let r : ℤ := x % ql
      let w : ℤ := (((-(r : ZMod t)) * ((ql : ℕ) : ZMod t)⁻¹).val : ℤ)
      Int.neg (r + (ql : ℤ) * w)
  | .bgv12 =>
      -- CRT of (−x mod q_ℓ, (q_ℓ−1)·x mod t), centred modulo t·q_ℓ
      let a : ℤ := (-(x : ZMod ql)).val
      let b : ℤ := ((((ql : ℤ) - 1) * x : ℤ) : ZMod t).val
      let tinv : ℤ := (((t : ℕ) : ZMod ql)⁻¹).val
      let qinv : ℤ := (((ql : ℕ) : ZMod t)⁻¹).val
      cmod (a * t * tinv + b * ql * qinv) (t * ql)

/-- The correction polynomial `δ` of a ring element. -/
def msDelta {Q : ℕ} (v : MSVariant) (t ql : ℕ) (c : Poly Q N) : IntPoly N :=
  force ⟨fun i => msDeltaZ v t ql ((c.coeff i).val : ℤ)⟩

/-- **BGV modulus switching of one ring element, exact output formula**:
`c' = (c + δ) / q_ℓ  mod Q'`, where `Q = Q'·q_ℓ`, `c` is taken in `[0,Q)`, `δ = msDelta v t q_ℓ c`
and the division is exact.
Source: GHS12 §3.2 ("`c' = (c + δ)/q_t`"); OpenFHE dcrtpoly-impl.h:746-755 & 758-777;
KPZ21 §2.3 (`ModSwitch`). -/
def modSwitchElt {Q : ℕ} (v : MSVariant) (t ql Q' : ℕ) (c : Poly Q N) : Poly Q' N :=
  force ⟨fun i =>
    let x : ℤ := ((c.coeff i).val : ℤ)
    (((x + msDeltaZ v t ql x) / (ql : ℤ) : ℤ) : ZMod Q')⟩

/-- **BGV modulus switching of a ciphertext.** With `v' = [⟨ct', s⟩]_{Q'}` and
`v = [⟨ct, s⟩]_Q`:

  `v' = (v + δ₀ + δ₁·s + …)/q_ℓ`  (as integers, provided `‖v‖∞ + ‖δ(s)‖∞ < Q/2`),

hence for the `ghs`/`seal` variants `v' ≡ q_ℓ⁻¹·v (mod t)`: **the message is multiplied by
`q_ℓ⁻¹ mod t`**, and `‖v'‖∞ ≤ ‖v‖∞/q_ℓ + ‖δ(s)‖∞/q_ℓ`.
Source: GHS12 §3.2; KPZ21 §2.3 & App. B.2.2; OpenFHE
`LeveledSHEBGVRNS::ModReduceInternalInPlace` bgvrns-leveledshe.cpp:45-77. -/
def modSwitch {Q : ℕ} (v : MSVariant) (t ql Q' : ℕ) (ct : Ct Q N) : Ct Q' N :=
  ct.map (modSwitchElt v t ql Q')

/-! ## 6. Ciphertexts in RNS form; relinearization and automorphisms with hybrid keys -/

/-- A ciphertext in RNS form. -/
abbrev RCt {k : ℕ} (q : Basis k) (N : ℕ) := List (RnsPoly q N)

section Rns
variable {k l d : ℕ}

/-- RNS → big-modulus ciphertext. -/
def RCt.toBig {q : Basis k} (ct : RCt q N) : Ct q.prod N := ct.map (ofRns q)

/-- Big-modulus → RNS ciphertext. -/
def toRCt {M : ℕ} (q : Basis k) (ct : Ct M N) : RCt q N := ct.map (castRns q)

/-- **Relinearization / key switching of a ciphertext in place**: for `(c₀, c₁, c₂)` and a key
from `s²` to `s`, `(k₀,k₁) = KeySwitch(c₂)` and the result is `(c₀ + k₀, c₁ + k₁)`; for
`(c₀, c₁)` and a key from `s` to `s'`, `(k₀,k₁) = KeySwitch(c₁)` and the result is `(c₀ + k₀, k₁)`.
Source: OpenFHE `KeySwitchHYBRID::KeySwitchInPlace` keyswitch-hybrid.cpp:212-228. -/
def keySwitchInPlace (c : Lift) (t : ℕ) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d)
    (key : HybridKey q p d N) (ct : RCt q N) : RCt q N :=
  match ct with
  | [c0, c1] =>
      match hybridKeySwitch c (some t) q p dig key c1 with
      | (k0, k1) => [radd c0 k0, k1]
  | [c0, c1, c2] =>
      match hybridKeySwitch c (some t) q p dig key c2 with
      | (k0, k1) => [radd c0 k0, radd c1 k1]
  | other => other

/-- The relinearization key: a key-switching key from `s²` to `s`.
Source: OpenFHE `EvalMultKeyGen` base-leveledshe.cpp:135-148
(`KeySwitchGen(privateKeySquared, privateKey)`); BGV12 §4 `FHE.KeyGen`
(`τ_{s''→s}` with `s'' = s ⊗ s`). -/
def relinKeyGen (t : ℕ) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d) (s : IntPoly N)
    (a e : Fin d → IntPoly N) : HybridKey q p d N :=
  hybridKeyGen t q p dig (s ⊠ s) s a e

/-- Inverse of a Galois element modulo `2N`. -/
def galoisInv (N g : ℕ) : ℕ := (((g : ℕ) : ZMod (2 * N))⁻¹).val

/-- **Galois key for `g`, OpenFHE / Lattigo convention**: a key-switching key from `s` to
`σ_{g⁻¹}(s)`, stored under index `g`.
Source: OpenFHE `EvalAutomorphismKeyGen` base-leveledshe.cpp:409-414
(`index = g⁻¹ mod 2N; privateKeyPermuted = s.AutomorphismTransform(index);
evalKeys[g] = KeySwitchGen(privateKey, privateKeyPermuted)`); Lattigo keygenerator.go:150-154
("We encrypt `[-a·π_{k⁻¹}(sk) + sk, a]` … first apply the gadget product … then `π_k`"). -/
def galoisKeyGenOF (t : ℕ) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d) (g : ℕ)
    (s : IntPoly N) (a e : Fin d → IntPoly N) : HybridKey q p d N :=
  hybridKeyGen t q p dig s (pauto (galoisInv N g) s) a e

/-- **Galois key for `g`, SEAL / textbook convention**: a key-switching key from `σ_g(s)` to `s`.
Source: SEAL `KeyGenerator::create_galois_keys` keygenerator.cpp:162-216 (l.207
`apply_galois_ntt(secret_key, …, galois_elt, rotated_secret_key)`, l.214
`generate_one_kswitch_key(rotated_secret_key, …)`); GHS12 §2.3 / App. B. -/
def galoisKeyGenSEAL (t : ℕ) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d) (g : ℕ)
    (s : IntPoly N) (a e : Fin d → IntPoly N) : HybridKey q p d N :=
  hybridKeyGen t q p dig (pauto g s) s a e

/-- **`EvalAutomorphism`, OpenFHE order**: key switch `(c₀,c₁)` from `s` to `σ_{g⁻¹}(s)` with
the key stored for `g`, **then** apply `σ_g` to both components. Result: an encryption of
`σ_g(m)` under `s`.
Source: OpenFHE `LeveledSHEBase::EvalAutomorphism` base-leveledshe.cpp:461-466. -/
def evalAutomorphismOF (c : Lift) (t : ℕ) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d)
    (g : ℕ) (key : HybridKey q p d N) (ct : RCt q N) : RCt q N :=
  (keySwitchInPlace c t q p dig key ct).map (rautomorph g)

/-- **`apply_galois`, SEAL order**: apply `σ_g` to both components (giving a ciphertext under
`σ_g(s)`), **then** key switch from `σ_g(s)` to `s`.
Source: SEAL `Evaluator::apply_galois_inplace` evaluator.cpp:2412-2450
(`apply_galois` on both polynomials, then `switch_key_inplace`). -/
def evalAutomorphismSEAL (c : Lift) (t : ℕ) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d)
    (g : ℕ) (key : HybridKey q p d N) (ct : RCt q N) : RCt q N :=
  keySwitchInPlace c t q p dig key (ct.map (rautomorph g))

/-- BGV modulus switching of an RNS ciphertext (drop the last limb), OpenFHE algorithm. -/
def modSwitchRns (c : Lift) (t : ℕ) (q : Basis (k + 1)) (ct : RCt q N) : RCt q.init N :=
  ct.map (modSwitchBGVRns c t q)

end Rns

/-! ## 7. Rotation / Galois bookkeeping -/

/-- **Galois element for a rotation by `r` slots, OpenFHE (and Lattigo, HElib)**: generator `5`:
`g = 5^r mod 2N` for `r ≥ 0` and `(5⁻¹)^{|r|} mod 2N` for `r < 0`; `r > 0` rotates left.
Source: OpenFHE `FindAutomorphismIndex2n` nbtheory2.cpp:191-225 (for `|r| < N/2`);
Lattigo params.go:577-580 (`GaloisGen = 5`, `GaloisElement(k) = 5^k mod 2N`). -/
def galoisEltOF (N : ℕ) (r : ℤ) : ℕ :=
  if 0 ≤ r then ((5 : ZMod (2 * N)) ^ r.toNat).val
  else (((5 : ZMod (2 * N))⁻¹) ^ (-r).toNat).val

/-- **Galois element for a rotation by `r` slots, SEAL**: generator `3`: `3^r mod 2N` for
`r > 0` (left rotation), `3^{N/2 − |r|}` for `r < 0`, and **`2N − 1` for `r = 0`** (which SEAL
uses for the column swap / conjugation).
Source: SEAL `GaloisTool::get_elt_from_step` util/galois.cpp:53-95, `generator_ = 3`
util/galois.h:169. -/
def galoisEltSEAL (N : ℕ) (r : ℤ) : ℕ :=
  if r = 0 then 2 * N - 1
  else if 0 < r then ((3 : ZMod (2 * N)) ^ r.toNat).val
  else ((3 : ZMod (2 * N)) ^ (N / 2 - (-r).toNat)).val

/-- The Galois element of the row swap / conjugation: `2N − 1` (`X ↦ X⁻¹`). -/
def galoisEltConj (N : ℕ) : ℕ := 2 * N - 1

/-! ## 8. The effect of each operation on message, level and scaling factor -/

/-- What a BGV ciphertext means, as bookkeeping data.
`ct` with state `st` satisfies: `[⟨ct, (1, s', s'², …)⟩]_{Q_limbs} ≡ sf·msg (mod t)` where
`s' = σ_keyElt(s)` and `Q_limbs = q_0 ⋯ q_{limbs-1}`.

**Level conventions**: `limbs` is the number of RNS limbs still present. OpenFHE's
`Ciphertext::GetLevel()` is the number of limbs *dropped* (it is incremented by `ModReduce`,
bgvrns-leveledshe.cpp:67); Lattigo's `Level()` is `limbs − 1`; SEAL's chain index decreases
towards 0; BGV12 numbers levels `L` (fresh) down to `0`. -/
structure State (t N : ℕ) where
  /-- the plaintext the user means -/
  msg : Poly t N
  /-- integer scaling factor: the ciphertext actually carries `sf·msg` -/
  sf : ZMod t
  /-- number of RNS limbs present -/
  limbs : ℕ
  /-- number of components minus one (1 = linear, 2 = after a tensor product) -/
  deg : ℕ
  /-- the ciphertext decrypts under `σ_keyElt(s)`; `1` for the canonical key -/
  keyElt : ℕ

/-- Fresh encryption at the top level: scaling factor 1.
(OpenFHE FLEXIBLEAUTO* actually encodes fresh plaintexts with a level-dependent factor
`m_scalingFactorsInt[level]`, bgvrns-cryptoparameters.cpp:104-115; the invariant is the same.) -/
def State.fresh {t : ℕ} (m : Poly t N) (limbs : ℕ) : State t N :=
  { msg := m, sf := 1, limbs := limbs, deg := 1, keyElt := 1 }

/-- Addition is defined when limbs, scaling factors and keys agree; messages add.
Source: OpenFHE `AdjustLevelsAndDepthInPlace` bgvrns-leveledshe.cpp:87-228 brings both operands to
this situation first (by `mulConst` with `sf₂·sf₁⁻¹` and mod/level reductions);
SEAL evaluator.cpp:197-213 (`balance_correction_factors`). -/
def State.add {t : ℕ} (a b : State t N) : Option (State t N) :=
  if a.limbs = b.limbs ∧ a.sf = b.sf ∧ a.keyElt = b.keyElt then
    some { a with msg := a.msg + b.msg, deg := max a.deg b.deg }
  else none

/-- Tensor multiplication: messages multiply, **scaling factors multiply**, degrees add, level
unchanged. Source: SEAL evaluator.cpp:839-840 (`correction_factor = cf₁·cf₂ mod t`); OpenFHE
packedencoding.cpp:61-64 / the `noiseScaleDeg` power of the scaling factor. -/
def State.mul {t : ℕ} (a b : State t N) : Option (State t N) :=
  if a.limbs = b.limbs ∧ a.keyElt = b.keyElt then
    some { a with msg := a.msg * b.msg, sf := a.sf * b.sf, deg := a.deg + b.deg }
  else none

/-- Multiplying the ciphertext by an integer constant `c`, *viewed as a change of scaling factor*
(the message is unchanged, `sf ↦ c·sf`). Viewed as plaintext arithmetic instead, it is
`msg ↦ c·msg` with `sf` unchanged; the two views describe the same ciphertext.
Source: OpenFHE `EvalMultCoreInPlace` bgvrns-leveledshe.cpp:240-253. -/
def State.mulConstSF {t : ℕ} (c : ℤ) (a : State t N) : State t N :=
  { a with sf := (c : ZMod t) * a.sf }

/-- **Modulus switching** dropping the prime `q_ℓ`: the carried plaintext `sf·msg` is multiplied by
`q_ℓ⁻¹ mod t`. Tracked as `sf ↦ sf·q_ℓ⁻¹`, message unchanged, one limb fewer.
If no factor is tracked (BGV12, OpenFHE FIXEDMANUAL/FIXEDAUTO) one must have `q_ℓ ≡ 1 (mod t)`
(OpenFHE bgvrns-parametergeneration.cpp:141-155 & 500-514: "For ModulusSwitching to work we need
the moduli to be also congruent to 1 modulo ptm").
Source: OpenFHE bgvrns-leveledshe.cpp:70-76 (`sf ← sf·(q_ℓ mod t)⁻¹`); SEAL evaluator.cpp:1277-1278
(`correction_factor ← cf·inv_q_last_mod_t`); KPZ21 §2.3. -/
def State.modSwitch {t : ℕ} (ql : ℕ) (a : State t N) : State t N :=
  { a with sf := a.sf * ((ql : ℕ) : ZMod t)⁻¹, limbs := a.limbs - 1 }

/-- Dropping a limb **without** scaling (OpenFHE `LevelReduce`, bgvrns-leveledshe.cpp:79-85):
neither the message nor the scaling factor changes; the noise is unchanged in absolute terms. -/
def State.levelReduce {t : ℕ} (a : State t N) : State t N := { a with limbs := a.limbs - 1 }

/-- Relinearization (key switch of the `s²` component): only the degree changes. The added error
is a multiple of `t`, so the message and scaling factor are untouched. -/
def State.relin {t : ℕ} (a : State t N) : State t N := { a with deg := 1 }

/-- Applying `σ_g` to the components without key switching: message `σ_g(msg)`, same scaling
factor (σ fixes integers), key becomes `σ_g(σ_keyElt(s)) = σ_{g·keyElt}(s)`. -/
def State.automorphRaw {t : ℕ} (g : ℕ) (a : State t N) : State t N :=
  { a with msg := NPoly.automorph g a.msg, keyElt := (g * a.keyElt) % (2 * N) }

/-- Key switching from `σ_keyElt(s)` to `σ_{g'}(s)`: only the key changes. -/
def State.keySwitchTo {t : ℕ} (g' : ℕ) (a : State t N) : State t N := { a with keyElt := g' }

/-- `EvalAutomorphism(g)` in the OpenFHE order (`keySwitchTo g⁻¹`, then `automorphRaw g`) and in
the SEAL order (`automorphRaw g`, then `keySwitchTo 1`) have the same effect on the state. -/
def State.evalAutomorphism {t : ℕ} (g : ℕ) (a : State t N) : State t N :=
  ((a.keySwitchTo (galoisInv N g)).automorphRaw g)

/-- The invariant tying a ciphertext to its bookkeeping state (decidable). -/
def Holds {Q t : ℕ} (s : IntPoly N) (ct : Ct Q N) (st : State t N) (B : ℕ) : Prop :=
  ct.length = st.deg + 1 ∧
    EncryptsSF t (pauto st.keyElt s) ct st.msg st.sf B

instance {Q t : ℕ} (s : IntPoly N) (ct : Ct Q N) (st : State t N) (B : ℕ) :
    Decidable (Holds s ct st B) := by unfold Holds; infer_instance

end Respec.BGV
