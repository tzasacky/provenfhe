import Respec.BGV

/-!
# Respec.BFV — the Brakerski / Fan–Vercauteren scheme and its RNS multiplications

Sources:
* [FV12] Fan, Vercauteren, *Somewhat Practical Fully Homomorphic Encryption*, ePrint 2012/144.
  §3 (LPR encryption with `Δ = ⌊q/t⌋`), §4 (`FV.SH.Decrypt`: `[⌊t·[c₀ + c₁·s]_q / q⌉]_t`;
  Lemma 1; `FV.SH.Mul`: `[⌊t·(ct₁ ⊗ ct₂)/q⌉]_q`; relinearization versions 1 and 2).
* [BEHZ16] Bajard, Eynard, Hasan, Zucca, ePrint 2016/510. §3.1 eq. (2) (`FastBconv`), §3.2
  Lemma 2/Alg. 1 (RNS decryption), §4.1-4.3 (small Montgomery reduction `SmMRq_m̃`, Alg. 2), §4.4
  Lemma 6 (fast RNS floor), §4.5 Lemma 7 / Alg. 3 (`FastBconvSK`, Shenoy–Kumaresan).
* [HPS18] Halevi, Polyakov, Shoup, ePrint 2018/117. §2.2 eq. (3) (CRT basis extension), §2.3
  (simple scaling, used for decryption), §2.4 (complex scaling), §4.3-4.5 (multiplication).
* [KPZ21] Kim, Polyakov, Zucca, ePrint 2021/204. §3 (BFV with the encoding `⌈Q·m/t⌋` and
  its noise analysis), §3.4 (HPS variants in OpenFHE).
* SEAL manual: K. Laine, *Simple Encrypted Arithmetic Library 2.3.1*, §4 ("invariant noise").
* OpenFHE v1.2.3: `src/pke/lib/scheme/bfvrns/bfvrns-pke.cpp` (Encrypt l.99-213, Decrypt
  l.215-271), `bfvrns-leveledshe.cpp` (EvalMult l.182-430: HPS l.210-222 & 356-371, BEHZ
  l.291-314 & 405-420), `dcrtpoly-impl.h` (`TimesQovert` l.889-907, `ScaleAndRound` l.1240-1560 &
  1562-1678, `FastBaseConvqToBskMontgomery` l.1744-1836, `FastRNSFloorq` l.1841-1890,
  `FastBaseConvSK` l.1895-1979).

## Variants recorded

* **Plaintext encoding.** FV12: `Δ·m` with `Δ = ⌊Q/t⌋`. SEAL ≥ 3.4 and KPZ21 §3: `⌊Q·m/t⌉`.
  OpenFHE `TimesQovert`: `t⁻¹·[−Q·m]_t mod Q` with `[·]_t` canonical, which is the **ceiling**
  `⌈Q·m/t⌉`. All three decrypt identically; their noise terms differ by at most `r_t(Q)·‖m‖/t`.
* **Sign conventions** are those of BGV with `t` replaced by 1 in the error terms
  (OpenFHE `ns = 1`): `pk = (e − a·s, a)`, `ct = (pk₀·u + e₀ + enc(m), pk₁·u + e₁)`.
* **Multiplication.** FV12 lifts both ciphertexts to `ℤ` with centred representatives, tensors,
  scales by `t/Q` with rounding and reduces mod `Q`. HPS18 does the same computation *exactly*
  in RNS (up to floating-point error in the two rounding steps, not modelled here). BEHZ16
  replaces rounding by flooring and tolerates bounded overflows; its result differs from FV12's
  by a small additive term in each component.
-/

namespace Respec.BFV

open Spec Respec

variable {N : ℕ}

/-! ## Encoding, encryption, decryption -/

/-- How a plaintext coefficient `m` is scaled into `ℤ_Q`. -/
inductive Encoding
  /-- `⌊Q/t⌋·m` — FV12 §3 (`Δ·m`). -/
  | floorDelta
  /-- `⌊Q·m/t⌉` (ties up) — KPZ21 §3; SEAL `multiply_add_plain_with_scaling_variant`
  util/scalingvariant.cpp:90-105 ("`floor((q·m + floor((t+1)/2)) / t)`"). -/
  | round
  /-- `⌈Q·m/t⌉ = (Q·m + [−Q·m]_t)/t` — OpenFHE `TimesQovert` dcrtpoly-impl.h:889-907
  (`x ← [x·(−Q mod t)]_t ∈ [0,t)`, then `x ← x·t⁻¹ mod q_i`). -/
  | ceil
  deriving DecidableEq, Repr

/-- The scaled value of one integer plaintext coefficient. -/
def encodeZ (enc : Encoding) (t Q : ℕ) (m : ℤ) : ℤ :=
  match enc with
  | .floorDelta => ((Q / t : ℕ) : ℤ) * m
  | .round => rdiv ((Q : ℤ) * m) t
  | .ceil => ((Q : ℤ) * m + (-(Q : ℤ) * m) % (t : ℤ)) / (t : ℤ)

/-- Encode a plaintext polynomial into `R_Q` (lifted from `ℤ_t` by `ml`). -/
def encode (enc : Encoding) (ml : Lift) {t : ℕ} (Q : ℕ) (m : Poly t N) : Poly Q N :=
  force ⟨fun i => ((encodeZ enc t Q (ml.rep (m.coeff i)) : ℤ) : ZMod Q)⟩

/-- OpenFHE's residue-level formula for the same encoding: `t⁻¹·[−Q·m]_t mod Q`.
Source: OpenFHE dcrtpoly-impl.h:902-903. -/
def encodeOpenFHE {t : ℕ} (Q : ℕ) (m : Poly t N) : Poly Q N :=
  force ⟨fun i => ((t : ℕ) : ZMod Q)⁻¹ * ((((-(Q : ℤ) : ZMod t) * m.coeff i).val : ℕ) : ZMod Q)⟩

/-- BFV public key `(e − a·s, a)` (OpenFHE base-pke.cpp:82 with `ns = 1`). FV12 §3 and
HES18 §2.1.2 write `(−(a·s + e), a)`. -/
def pkGen {Q : ℕ} (s a e : IntPoly N) : BGV.PublicKey Q N := BGV.pkGen 1 s a e

/-- **BFV public-key encryption**: `(pk₀·u + e₀ + enc(m), pk₁·u + e₁)`.
Source: FV12 §3 `FV.SH.Encrypt` (`([p₀·u + e₁ + Δ·m]_q, [p₁·u + e₂]_q)`);
OpenFHE `PKEBFVRNS::Encrypt` bfvrns-pke.cpp:182-196. -/
def encrypt {Q t : ℕ} (enc : Encoding) (ml : Lift) (pk : BGV.PublicKey Q N) (m : Poly t N)
    (u e0 e1 : IntPoly N) : BGV.Ct Q N :=
  [pk.b ⊠ red Q u ⊞ red Q e0 ⊞ encode enc ml Q m, pk.a ⊠ red Q u ⊞ red Q e1]

/-- **BFV decryption** `m = [⌊t·[⟨ct,(1,s,…)⟩]_Q / Q⌉]_t`: centred lift of the phase, exact
rational scaling by `t/Q`, rounding to nearest, reduction mod `t`.
Source: FV12 §4 `FV.SH.Decrypt(sk, ct)`: "`[⌊t·[c₀ + c₁·s]_q / q⌉]_t`"; HES18 §2.1.2;
OpenFHE `PKEBFVRNS::Decrypt` bfvrns-pke.cpp:215-271. -/
def decrypt {Q : ℕ} (t : ℕ) (s : IntPoly N) (ct : BGV.Ct Q N) : Poly t N :=
  force ⟨fun i => ((rdiv ((t : ℤ) * (BGV.crit s ct).coeff i) Q : ℤ) : ZMod t)⟩

/-- **HPS RNS decryption ("simple scaling")** from the residues of the phase:
`m = [⌊Σ_i y_i·(t/q_i)⌉]_t` with `y_i = [x_i·(Q/q_i)⁻¹]_{q_i}`; exact because
`t·x/Q = Σ_i y_i·t/q_i − υ·t` and `υ·t ≡ 0 (mod t)`. (Libraries evaluate the fractional parts in
floating point; here the sum is exact.)
Source: HPS18 §2.3 eq. (5)-(6); OpenFHE `ScaleAndRound` dcrtpoly-impl.h:1240-1560. -/
def decryptHPSZ {k : ℕ} (t : ℕ) (q : Basis k) (x : Residues q) : ZMod t :=
  ((rdiv ((t : ℤ) * fastBConvZ .canonical q Basis.all x) q.prod : ℤ) : ZMod t)

/-- HPS decryption of a phase given in RNS form. -/
def decryptHPS {k : ℕ} (t : ℕ) (q : Basis k) (ph : RnsPoly q N) : Poly t N :=
  force ⟨fun j => decryptHPSZ t q (ph.res j)⟩

/-! ## The noise invariants -/

/-- **`Δ`-form noise**: `v = [⟨ct,s⟩ − enc(m)]_Q`, so that `⟨ct,s⟩ = enc(m) + v (mod Q)`.
Source: FV12 §4 Lemma 1 ("`[ct(s)]_q = Δ·m + v`"). -/
def noiseDelta {Q t : ℕ} (enc : Encoding) (ml : Lift) (s : IntPoly N) (ct : BGV.Ct Q N)
    (m : Poly t N) : IntPoly N :=
  liftC (BGV.phase s ct ⊟ encode enc ml Q m)

/-- "`ct` encrypts `m` with (`Δ`-form) noise at most `B`": `⟨ct,s⟩ = enc(m) + v (mod Q)` with
`‖v‖∞ ≤ B`. Source: FV12 Lemma 1; KPZ21 §3. -/
def EncryptsDelta {Q t : ℕ} (enc : Encoding) (ml : Lift) (s : IntPoly N) (ct : BGV.Ct Q N)
    (m : Poly t N) (B : ℕ) : Prop :=
  NPoly.normInf (noiseDelta enc ml s ct m) ≤ B

instance {Q t : ℕ} (enc : Encoding) (ml : Lift) (s : IntPoly N) (ct : BGV.Ct Q N) (m : Poly t N)
    (B : ℕ) : Decidable (EncryptsDelta enc ml s ct m B) := by unfold EncryptsDelta; infer_instance

/-- Reduce a rational modulo `t` into `[-t/2, t/2)`. -/
def qcmod (x : ℚ) (t : ℕ) : ℚ := x - t * ⌊x / t + 1 / 2⌋

/-- **Invariant noise**: the polynomial `v ∈ ℚ[X]/(X^N+1)` of smallest norm with
`(t/Q)·ct(s) = m + v + t·a` for some integer polynomial `a`. Decryption is correct iff
`‖v‖∞ < 1/2`.
Source: SEAL manual (Laine, v2.3.1) Definition 2 ("invariant noise") and Lemma 1;
KPZ21 §3.2 uses the same quantity scaled by `Q/t`. -/
def invNoise {Q t : ℕ} (s : IntPoly N) (ct : BGV.Ct Q N) (m : Poly t N) : NPoly ℚ N :=
  force ⟨fun i =>
    qcmod (((t : ℚ) * (BGV.crit s ct).coeff i) / Q - ((m.coeff i).val : ℚ)) t⟩

/-- "`ct` encrypts `m` with invariant noise at most `B`". -/
def EncryptsInv {Q t : ℕ} (s : IntPoly N) (ct : BGV.Ct Q N) (m : Poly t N) (B : ℚ) : Prop :=
  NPoly.BoundedQ (invNoise s ct m) B

instance {Q t : ℕ} (s : IntPoly N) (ct : BGV.Ct Q N) (m : Poly t N) (B : ℚ) :
    Decidable (EncryptsInv s ct m B) := by unfold EncryptsInv; infer_instance

/-- **The relation between the two forms.** If `⟨ct,s⟩ = Δ·m̃ + v` with `Δ = ⌊Q/t⌋` and
`r = Q mod t` (so `Q = Δ·t + r`), then `(t/Q)·(Δ·m̃ + v) = m̃ + (t·v − r·m̃)/Q`, i.e. the invariant
noise is

  `v_inv = (t·v − r_t(Q)·m̃) / Q`      (as long as its norm is `< t/2`),

and decryption is correct iff `‖t·v − r_t(Q)·m̃‖∞ < Q/2`. In particular the often quoted
criterion "`‖v‖∞ < Δ/2`" (FV12 Lemma 1 as usually cited) is *not* sufficient by itself: the
`r_t(Q)·m̃` term must be accounted for (sufficient: `‖v‖∞ < Δ/2 − r_t(Q)·‖m̃‖∞/t`, e.g.
`‖v‖∞ < (Δ − r_t(Q))/2` for centred `m̃`). A counterexample at tiny parameters is in the tests.
Source: SEAL manual §4; FV12 proof of Lemma 1. -/
def invFromDelta (t Q : ℕ) (v mLift : IntPoly N) : NPoly ℚ N :=
  force ⟨fun i => (((t : ℤ) * v.coeff i - ((Q % t : ℕ) : ℤ) * mLift.coeff i : ℤ) : ℚ) / Q⟩

/-! ## Textbook multiplication -/

/-- `⌊t·x/Q⌉` coefficient-wise. -/
def scaleRound (t Q : ℕ) (x : IntPoly N) : IntPoly N :=
  force ⟨fun i => rdiv ((t : ℤ) * x.coeff i) Q⟩

/-- **Textbook BFV multiplication (without relinearization)**: lift both ciphertexts to `ℤ` with
centred representatives, tensor over `ℤ`, scale every component by `t/Q` with rounding, reduce
mod `Q`: `c̃_k = [⌊t·(Σ_{i+j=k} c_i·c'_j)/Q⌉]_Q`.
Source: FV12 §4 `FV.SH.Mul` / eq. for `c₀, c₁, c₂` ("Basic Multiplication");
HES18 §2.1.2 `BFV.EvalMult`. -/
def mulTextbook {Q : ℕ} (t : ℕ) (a b : BGV.Ct Q N) : BGV.Ct Q N :=
  (forceAll (tensorWith pmul padd 0 (a.map liftC) (b.map liftC))).map fun x =>
    red Q (scaleRound t Q x)

/-! ## HPS RNS multiplication -/

section HPS
variable {k l : ℕ}

/-- **HPS complex scaling**, one coefficient: from the residues of `x` in `Q ∪ P` compute
`⌊t·x/Q⌉ mod p_j`:

  `[ ⌊Σ_i y_i·(t·P/q_i)⌉ + y'_j·t·(P/p_j) ]_{p_j}`,
  `y_i = [x_i·((QP)/q_i)⁻¹]_{q_i}`,  `y'_j = [x'_j·((QP)/p_j)⁻¹]_{p_j}`.

(HPS split `t·P/q_i = ω_i + θ_i` into integer and fractional parts and evaluate `Σ y_i θ_i` in
floating point; here the rational sum `Σ_i y_i·t·P/q_i = (Σ_i y_i·t·P·(Q/q_i))/Q` is exact.)
Source: HPS18 §2.4 eq. (7)-(8); OpenFHE `ScaleAndRound` dcrtpoly-impl.h:1562-1678. -/
def hpsScaleZ (t : ℕ) (q : Basis k) (p : Basis l) (xq : Residues q) (xp : Residues p)
    (j : Fin l) : ZMod (p j) :=
  let P : ℤ := p.prod
  let S : ℤ := ∑ i, (((xq i * (((q.hat i * p.prod : ℕ) : ZMod (q i)))⁻¹).val : ℕ) : ℤ) *
    (t : ℤ) * P * (q.hat i : ℤ)
  let y' : ℤ := ((xp j * (((q.prod * p.hat j : ℕ) : ZMod (p j)))⁻¹).val : ℕ)
  ((rdiv S q.prod + y' * (t : ℤ) * (p.hat j : ℤ) : ℤ) : ZMod (p j))

/-- HPS complex scaling of a polynomial given over `Q ∪ P`; the result is over `P`. -/
def hpsScale (t : ℕ) (q : Basis k) (p : Basis l) (xQ : RnsPoly q N) (xP : RnsPoly p N) :
    RnsPoly p N :=
  rmk fun j => ⟨fun n => hpsScaleZ t q p (xQ.res n) (xP.res n) j⟩

/-- Tensor product of RNS ciphertexts, limb-wise. -/
def rtensor {m : ℕ} {q : Basis m} (a b : List (RnsPoly q N)) : List (RnsPoly q N) :=
  (tensorWith rmul radd ⟨fun _ => 0⟩ a b).map rforce

/-- **HPS RNS multiplication** (without relinearization), as an algorithm on residues:
1. extend both ciphertexts from `Q` to `P` with the exact (centred) basis extension;
2. tensor limb-wise in `Q ∪ P` (no reduction modulo `Q` or `P` happens: `Q·P` must exceed twice
   the tensor coefficients, `Q·P > N·Q²`);
3. complex scaling `⌊t·x/Q⌉` to basis `P` (valid when `P > t·N·Q`);
4. exact basis extension back from `P` to `Q`.
With exact rounding this equals `mulTextbook` (checked in the tests).
Source: HPS18 §4.3-4.5 (and Table 1); OpenFHE `LeveledSHEBFVRNS::EvalMult`
bfvrns-leveledshe.cpp:210-222 (`ExpandCRTBasis`), l.356-371 (`ScaleAndRound`, `SwitchCRTBasis`). -/
def mulHPS (t : ℕ) (q : Basis k) (p : Basis l) (a b : List (RnsPoly q N)) : List (RnsPoly q N) :=
  let tQ := rtensor a b
  let tP := rtensor (a.map (exactBConvBasis q p)) (b.map (exactBConvBasis q p))
  (List.zip tQ tP).map fun xx => exactBConvBasis p q (hpsScale t q p xx.1 xx.2)

end HPS

/-! ## BEHZ RNS multiplication -/

section BEHZ
variable {k l : ℕ}

/-- An element in the extended base `q ∪ B ∪ {m_sk}` of BEHZ16 §4. -/
structure Ext (q : Basis k) (B : Basis l) (msk N : ℕ) where
  /-- residues in base `q` -/
  xq : RnsPoly q N
  /-- residues in base `B` -/
  xB : RnsPoly B N
  /-- residue modulo `m_sk` -/
  xsk : Poly msk N

/-- **Step 1 (integer meaning): fast conversion of `m̃·x` followed by the small Montgomery
reduction modulo `q`.** With `ζ = FastBconv([m̃·x]_q, q, ·) = [m̃ x]_q + α·q` and
`r = [−ζ·q⁻¹]_m̃` (centred in `[-m̃/2, m̃/2)`), return the integer `(ζ + q·r)/m̃` (exact division).
It is `≡ x (mod q)` and of size `≲ q/2·(1 + k/m̃·…)`; its residues modulo `B_sk` are the output.
Source: BEHZ16 §4.2-4.3, Alg. 2 (`SmMRq_m̃`), Lemma 4; OpenFHE `FastBaseConvqToBskMontgomery`
dcrtpoly-impl.h:1778-1821. -/
def behzExtendZ (q : Basis k) (mt : ℕ) (x : Residues q) : ℤ :=
  let ζ : ℤ := fastBConvZ .canonical q Basis.all fun i => ((mt : ℕ) : ZMod (q i)) * x i
  let r0 : ℤ := (((-(ζ : ZMod mt)) * ((q.prod : ℕ) : ZMod mt)⁻¹).val : ℕ)
  let r : ℤ := if (mt : ℤ) ≤ 2 * r0 then r0 - mt else r0
  (ζ + (q.prod : ℤ) * r) / (mt : ℤ)

/-- Step 1 as computed on residues, for one target modulus `m ∈ B_sk`:
`[(ζ mod m + (q mod m)·r)·m̃⁻¹]_m`. Source: OpenFHE dcrtpoly-impl.h:1798-1821. -/
def behzExtendRes (q : Basis k) (mt : ℕ) (x : Residues q) (m : ℕ) : ZMod m :=
  let ζ : ℤ := fastBConvZ .canonical q Basis.all fun i => ((mt : ℕ) : ZMod (q i)) * x i
  let r0 : ℤ := (((-(ζ : ZMod mt)) * ((q.prod : ℕ) : ZMod mt)⁻¹).val : ℕ)
  let r : ℤ := if (mt : ℤ) ≤ 2 * r0 then r0 - mt else r0
  ((ζ : ZMod m) + ((q.prod : ℕ) : ZMod m) * (r : ZMod m)) * ((mt : ℕ) : ZMod m)⁻¹

/-- Step 1 for a polynomial: extend from base `q` to `q ∪ B ∪ {m_sk}`. -/
def behzExtend (q : Basis k) (B : Basis l) (msk mt : ℕ) (x : RnsPoly q N) : Ext q B msk N where
  xq := x
  xB := rmk fun j => ⟨fun n => behzExtendRes q mt (x.res n) (B j)⟩
  xsk := force ⟨fun n => behzExtendRes q mt (x.res n) msk⟩

/-- Product in the extended base. -/
def Ext.mul {q : Basis k} {B : Basis l} {msk : ℕ} (a b : Ext q B msk N) : Ext q B msk N :=
  ⟨rmul a.xq b.xq, rmul a.xB b.xB, a.xsk ⊠ b.xsk⟩

/-- Sum in the extended base. -/
def Ext.add {q : Basis k} {B : Basis l} {msk : ℕ} (a b : Ext q B msk N) : Ext q B msk N :=
  ⟨radd a.xq b.xq, radd a.xB b.xB, a.xsk ⊞ b.xsk⟩

/-- **Step 3: fast RNS floor**, one coefficient and one target modulus `m ∈ B_sk`:
`(t·x_m − FastBconv([t·x]_q, q, m))·q⁻¹ mod m`. As an integer this is `⌊t·x/q⌋ − α` with
`0 ≤ α ≤ k−1` the fast-base-conversion overflow.
Source: BEHZ16 §4.4 Lemma 6; OpenFHE `FastRNSFloorq` dcrtpoly-impl.h:1856-1888. -/
def behzFloorRes (t : ℕ) (q : Basis k) (xq : Residues q) (m : ℕ) (xm : ZMod m) : ZMod m :=
  (((t : ℕ) : ZMod m) * xm -
      fastBConv .canonical q Basis.all (fun i => ((t : ℕ) : ZMod (q i)) * xq i) m) *
    ((q.prod : ℕ) : ZMod m)⁻¹

/-- **Step 4: Shenoy–Kumaresan exact conversion from `B_sk` to `q`**, one coefficient:
`v = FastBconv(y, B, ·) = y + α·M`; `α_sk = [(v − y_sk)·M⁻¹]_{m_sk}` centred; output
`[v − α_sk·M]_{q_i}`. Exact when `|y| < M·(m_sk/2 − l)`.
Source: BEHZ16 §4.5 Lemma 7 / Alg. 3 (`FastBconvSK`); Shenoy–Kumaresan 1989;
OpenFHE `FastBaseConvSK` dcrtpoly-impl.h:1919-1966. -/
def behzSKRes (B : Basis l) (msk : ℕ) (yB : Residues B) (ysk : ZMod msk) (m : ℕ) : ZMod m :=
  let v : ℤ := fastBConvZ .canonical B Basis.all yB
  let α : ℤ := (((v : ZMod msk) - ysk) * ((B.prod : ℕ) : ZMod msk)⁻¹).valMinAbs
  ((v - α * (B.prod : ℤ) : ℤ) : ZMod m)

/-- Steps 3 and 4 for a polynomial in the extended base: the result is `≈ ⌊t·x/q⌋` in base `q`. -/
def behzFloorAndBack (t : ℕ) {q : Basis k} {B : Basis l} {msk : ℕ} (x : Ext q B msk N) :
    RnsPoly q N :=
  rmk fun i => ⟨fun n =>
    behzSKRes B msk
      (fun j => behzFloorRes t q (x.xq.res n) (B j) ((x.xB j).coeff n))
      (behzFloorRes t q (x.xq.res n) msk (x.xsk.coeff n))
      (q i)⟩

/-- Memoize an element of the extended base. -/
def Ext.force {q : Basis k} {B : Basis l} {msk : ℕ} (a : Ext q B msk N) : Ext q B msk N :=
  ⟨rforce a.xq, rforce a.xB, Respec.force a.xsk⟩

/-- **BEHZ RNS multiplication** (without relinearization), as an algorithm on residues:
1. for every ciphertext component, `FastBconv` of `m̃·c` to `B_sk ∪ {m̃}` and small Montgomery
   reduction (`behzExtend`);
2. tensor in `q ∪ B_sk`;
3. fast RNS floor of `t·x/q` in `B_sk` (`behzFloorRes`);
4. Shenoy–Kumaresan conversion back to `q` (`behzSKRes`).
The result is `⌊t·(c ⊗ c')/q⌋ + (small error)` per component, where the tensor is of the
*Montgomery-reduced* representatives (`≡ c mod q`, not the centred ones).
Source: BEHZ16 §4, Alg. 3 ("RNS variant of FV multiplication") and Theorem/Prop. in §4.6;
OpenFHE bfvrns-leveledshe.cpp:291-314 & 405-420. -/
def mulBEHZ (t : ℕ) (q : Basis k) (B : Basis l) (msk mt : ℕ) (a b : List (RnsPoly q N)) :
    List (RnsPoly q N) :=
  ((tensorWith Ext.mul Ext.add ⟨⟨fun _ => 0⟩, ⟨fun _ => 0⟩, 0⟩
      (a.map (behzExtend q B msk mt)) (b.map (behzExtend q B msk mt))).map Ext.force).map
    (behzFloorAndBack t)

end BEHZ

/-! ## Relinearization -/

/-- BFV relinearization with a hybrid key from `s²` to `s` (`ns = 1`, plain ModDown):
`(c₀ + k₀, c₁ + k₁)` with `(k₀,k₁) = KeySwitch(c₂)`.
Source: FV12 §4 "Relinearisation Version 2" (one digit, modulus `p·q`); OpenFHE
`KeySwitchHYBRID::KeySwitchInPlace` with `t = 0`. -/
def relin {k l d : ℕ} (c : Lift) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d)
    (key : HybridKey q p d N) (ct : List (RnsPoly q N)) : List (RnsPoly q N) :=
  match ct with
  | [c0, c1, c2] =>
      match hybridKeySwitch c none q p dig key c2 with
      | (k0, k1) => [radd c0 k0, radd c1 k1]
  | other => other

end Respec.BFV
