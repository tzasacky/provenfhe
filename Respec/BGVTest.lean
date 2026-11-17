import Respec.Noise

/-!
# Respec.BGVTest — end-to-end sanity tests at tiny parameters

`N = 4`, `t = 5`, `Q = 97·113·193` (three limbs, two digits `{97,113}`, `{193}`),
`P = 257·337`. Everything below is executed by `#guard` with the definitions of this library only.
The moduli are deliberately **not** `≡ 1 (mod t)` (`97 ≡ 2`, `113 ≡ 3`, `193 ≡ 3 mod 5`), so the
`q_ℓ⁻¹ mod t` message scaling is visible.
-/

namespace Respec.BGV.Test

open Spec Respec Respec.BGV Respec.Noise

/-- plaintext modulus -/
abbrev t : ℕ := 5
/-- ciphertext modulus `Q = 2115473` -/
abbrev Q : ℕ := tq.prod
/-- digit assignment: limbs 0,1 ↦ digit 0, limb 2 ↦ digit 1 -/
def dig : Fin 3 → Fin 2 := ![0, 0, 1]
/-- digit moduli -/
def Qs : List ℕ := [97 * 113, 193]

def s : IntPoly 4 := zpoly [1, -1, 0, 1]
def aPk : IntPoly 4 := zpoly [1234567, 891011, 1213141, 516171]
def ePk : IntPoly 4 := zpoly [1, -2, 0, 1]
def pk : PublicKey Q 4 := pkGen t s aPk ePk

def m1 : Poly t 4 := red t (zpoly [1, 2, 3, 4])
def m2 : Poly t 4 := red t (zpoly [4, 0, 2, 1])
def u1 : IntPoly 4 := zpoly [1, 0, -1, 1]
def u2 : IntPoly 4 := zpoly [-1, 1, 1, 0]
def e10 : IntPoly 4 := zpoly [2, -1, 0, -2]
def e11 : IntPoly 4 := zpoly [-1, 0, 2, 1]
def e20 : IntPoly 4 := zpoly [0, 1, -2, 1]
def e21 : IntPoly 4 := zpoly [1, 1, -1, 0]

def ct1 : Ct Q 4 := encrypt .canonical pk m1 u1 e10 e11
def ct2 : Ct Q 4 := encrypt .canonical pk m2 u2 e20 e21

/-- worst-case fresh noise: `4 + 5·(4·2·1 + 2 + 4·2·1) = 94` -/
def Bfresh : ℕ := freshBound .canonical 4 t 1 2 1

/-! ### Keys and fresh encryption -/

#guard IsTernary s ∧ IsTernary u1 ∧ IsTernary u2
-- OpenFHE key equation b + a·s = t·e ; HES18/SEAL key equation b + a·s = −t·e.
#guard liftC (pk.b ⊞ pk.a ⊠ red Q s) = zscale 5 ePk
#guard liftC ((pkGenStd (Q := Q) t s aPk ePk).b ⊞ (pkGenStd (Q := Q) t s aPk ePk).a ⊠ red Q s)
  = zscale (-5) ePk
-- the fresh critical quantity is exactly m + t(e·u + e0 + e1·s)
#guard crit s ct1 = freshCrit .canonical m1 s ePk u1 e10 e11
#guard crit s ct2 = freshCrit .canonical m2 s ePk u2 e20 e21
#guard crit s (encrypt .centred pk m1 u1 e10 e11) = freshCrit .centred m1 s ePk u1 e10 e11
#guard crit s (encrypt (Q := Q) .canonical (pkGenStd t s aPk ePk) m1 u1 e10 e11)
  = freshCritStd .canonical m1 s ePk u1 e10 e11
#guard Bfresh = 94
#guard decrypt t s ct1 = m1 ∧ decrypt t s ct2 = m2
#guard Encrypts t s ct1 m1 Bfresh ∧ Encrypts t s ct2 m2 Bfresh
-- the fresh noise has negative coefficients, so the canonical inner lift decrypts wrongly:
#guard (coeffs (crit s ct1)).any (· < 0)
#guard decryptCanonicalWRONG t s ct1 ≠ m1
-- secret-key encryption (a·s + t·e + m, −a)
#guard crit s (encryptSym (Q := Q) .canonical s m1 aPk ePk) = liftN m1 ⊞ zscale 5 ePk

/-! ### Addition, constants, tensor product -/

def ctAdd : Ct Q 4 := add ct1 ct2
#guard decrypt t s ctAdd = m1 ⊞ m2
#guard Encrypts t s ctAdd (m1 ⊞ m2) (addBound Bfresh Bfresh)
#guard decrypt t s (mulConst 3 ct1) = (3 : ZMod 5) ⊡ m1

/-- the product plaintext -/
def mm : Poly t 4 := m1 ⊠ m2

def ct3 : Ct Q 4 := mulTensor ct1 ct2
#guard ct3.length = 3
#guard crit s ct3 = crit s ct1 ⊠ crit s ct2
#guard decrypt t s ct3 = mm
#guard Encrypts t s ct3 (mm) (mulBound 4 Bfresh Bfresh)
#guard 2 * mulBound 4 Bfresh Bfresh < Q

/-! ### Key-switching keys -/

def aK : Fin 2 → IntPoly 4 :=
  ![zpoly [123456789012, 98765432101, 55555555555, 31415926535],
    zpoly [27182818284, 16180339887, 141421356237, 173205080756]]
def eK : Fin 2 → IntPoly 4 := ![zpoly [1, -1, 2, 0], zpoly [-2, 0, 1, 1]]
def aG : Fin 2 → IntPoly 4 :=
  ![zpoly [11111111111, 22222222222, 33333333333, 44444444444],
    zpoly [99999999999, 88888888888, 77777777777, 66666666666]]
def eG : Fin 2 → IntPoly 4 := ![zpoly [0, 2, -1, 1], zpoly [1, -2, 0, -1]]

/-- relinearization key `s² → s` -/
def rk : HybridKey tq tp 2 4 := relinKeyGen t tq tp dig s aK eK
/-- Galois key for `g = 3`, OpenFHE convention (`s → σ_{3⁻¹}(s)`) -/
def gkOF : HybridKey tq tp 2 4 := galoisKeyGenOF t tq tp dig 3 s aG eG
/-- Galois key for `g = 3`, SEAL convention (`σ_3(s) → s`) -/
def gkSEAL : HybridKey tq tp 2 4 := galoisKeyGenSEAL t tq tp dig 3 s aG eG

-- The gadget: OpenFHE factors are P·(CRT idempotents); Han–Ki factors are P·Q̂_j.
#guard gadgetOF tp.prod Qs 0 % (97 * 113) = tp.prod % (97 * 113) ∧ gadgetOF tp.prod Qs 0 % 193 = 0
#guard gadgetOF tp.prod Qs 1 % 193 = tp.prod % 193 ∧ gadgetOF tp.prod Qs 1 % (97 * 113) = 0
#guard GadgetIdentity tp.prod 2 (decompOF .canonical Qs) (gadgetOF tp.prod Qs) (ct3.getD 2 0)
#guard GadgetIdentity tp.prod 2 (decompOF .centred Qs) (gadgetOF tp.prod Qs) (ct3.getD 2 0)
#guard GadgetIdentity tp.prod 2 (decompHK .centred Qs) (gadgetHK tp.prod Qs) (ct3.getD 2 0)
-- the mixed pairs are NOT gadget decompositions:
#guard ¬ GadgetIdentity tp.prod 2 (decompOF .centred Qs) (gadgetHK tp.prod Qs) (ct3.getD 2 0)
#guard ¬ GadgetIdentity tp.prod 2 (decompHK .centred Qs) (gadgetOF tp.prod Qs) (ct3.getD 2 0)

-- The RNS key produced by the OpenFHE algorithm is a valid key in the big-modulus sense for the
-- OpenFHE gadget, with errors exactly t·e_j, and is not one for the Han–Ki gadget.
#guard kskCheck t (gadgetOF tp.prod Qs) (s ⊠ s) s (keyToBig rk) 2
#guard (keyToBig rk).zipIdx.all fun kj =>
  kskErr (gadgetOF tp.prod Qs kj.2) (s ⊠ s) s kj.1 = zscale 5 (eK ⟨kj.2 % 2, Nat.mod_lt _ (by decide)⟩)
#guard !kskCheck t (gadgetHK tp.prod Qs) (s ⊠ s) s (keyToBig rk) 2
#guard kskCheck t (gadgetOF tp.prod Qs) s (pauto (galoisInv 4 3) s) (keyToBig gkOF) 2
#guard kskCheck t (gadgetOF tp.prod Qs) (pauto 3 s) s (keyToBig gkSEAL) 2
#guard galoisInv 4 3 = 3 ∧ galoisInv 4 5 = 5 ∧ galoisInv 8 3 = 11

/-! ### Relinearization (hybrid key switching on limbs) -/

def ct3R : RCt tq 4 := toRCt tq ct3
#guard ct3R.toBig = ct3

def ctRelC : Ct Q 4 := (keySwitchInPlace .centred t tq tp dig rk ct3R).toBig
def ctRelN : Ct Q 4 := (keySwitchInPlace .canonical t tq tp dig rk ct3R).toBig

#guard ctRelC.length = 2 ∧ ctRelN.length = 2
#guard decrypt t s ctRelC = mm ∧ decrypt t s ctRelN = mm
-- the added error is a multiple of t and within the derived worst-case bound
def ksAddC : IntPoly 4 := crit s ctRelC ⊟ crit s ct3
def ksAddN : IntPoly 4 := crit s ctRelN ⊟ crit s ct3
def ksBoundC : ℚ := ksAddedBound .centred 4 t 1 2 [[97, 113], [193]] [257, 337]
def ksBoundN : ℚ := ksAddedBound .canonical 4 t 1 2 [[97, 113], [193]] [257, 337]
#guard DivisibleBy 5 ksAddC ∧ DivisibleBy 5 ksAddN
#guard (NPoly.normInf ksAddC : ℚ) ≤ ksBoundC ∧ (NPoly.normInf ksAddN : ℚ) ≤ ksBoundN
#guard ksBoundC < 31 ∧ ksBoundN < 61
-- the two lift conventions give different (both valid) ciphertexts
#guard ctRelC ≠ ctRelN

-- the arbitrary-precision reference key switch with exact digits is also correct ...
def ksBig : Poly Q 4 × Poly Q 4 :=
  keySwitchBig .centred t Q tp.prod (decompOF .canonical Qs) (keyToBig rk) (ct3.getD 2 0)
def ctRelBig : Ct Q 4 := [ct3.getD 0 0 ⊞ ksBig.1, ct3.getD 1 0 ⊞ ksBig.2]
#guard decrypt t s ctRelBig = mm
#guard DivisibleBy 5 (crit s ctRelBig ⊟ crit s ct3)
-- ... while using the Han–Ki decomposition with the OpenFHE key gives a ciphertext that does not decrypt to the message:
def ksBigBad : Poly Q 4 × Poly Q 4 :=
  keySwitchBig .centred t Q tp.prod (decompHK .canonical Qs) (keyToBig rk) (ct3.getD 2 0)
#guard decrypt t s [ct3.getD 0 0 ⊞ ksBigBad.1, ct3.getD 1 0 ⊞ ksBigBad.2] ≠ mm

-- Using plain (non-t-corrected) ModDown in BGV destroys the plaintext:
#guard
  let ks := hybridKeySwitch .centred none tq tp dig rk (ct3R.getD 2 default)
  let bad : Ct Q 4 := [ct3.getD 0 0 ⊞ ofRns tq ks.1, ct3.getD 1 0 ⊞ ofRns tq ks.2]
  decrypt t s bad ≠ mm

/-! ### Modulus switching (drop `q_2 = 193`) -/

/-- level-1 modulus `Q' = 97·113` -/
abbrev Q1 : ℕ := tq.init.prod

def ctRelR : RCt tq 4 := keySwitchInPlace .centred t tq tp dig rk ct3R
def ctMsR : RCt tq.init 4 := modSwitchRns .centred t tq ctRelR
def ctMs : Ct Q1 4 := ctMsR.toBig

#guard Q1 = 10961
-- the RNS algorithm equals the exact formula c' = (c + δ)/q_ℓ
#guard ctMs = modSwitch (.ghs .centred) t 193 Q1 ctRelC
-- δ ≡ −c (mod q_ℓ), δ ≡ 0 (mod t), |δ| ≤ t·q_ℓ/2
#guard ctRelC.all fun c =>
  let δ := msDelta (.ghs .centred) t 193 c
  DivisibleBy 193 (liftN c ⊞ δ) ∧ DivisibleBy 5 δ ∧ 2 * NPoly.normInf δ ≤ 5 * 193
-- the critical quantity transforms as v' = (v + δ₀ + δ₁·s)/q_ℓ, exactly:
#guard zscale 193 (crit s ctMs)
  = crit s ctRelC ⊞ msDelta (.ghs .centred) t 193 (ctRelC.getD 0 0)
      ⊞ msDelta (.ghs .centred) t 193 (ctRelC.getD 1 0) ⊠ s
-- the message is multiplied by q_ℓ⁻¹ mod t  (193⁻¹ = 3⁻¹ = 2 mod 5):
#guard decrypt t s ctMs = (2 : ZMod 5) ⊡ mm
#guard decrypt t s ctMs ≠ mm
#guard decryptSF t s ctMs (((193 : ℕ) : ZMod 5)⁻¹) = mm
-- noise bound
#guard (NPoly.normInf (crit s ctMs) : ℚ) ≤ modSwitchBound (.ghs .centred) 4 t 1 193 1 (NPoly.normInf (crit s ctRelC))

-- SEAL's correction: also exact, also scales the message by q_ℓ⁻¹, larger δ.
def ctMsSeal : Ct Q1 4 := modSwitch .seal t 193 Q1 ctRelC
#guard ctRelC.all fun c =>
  let δ := msDelta .seal t 193 c
  DivisibleBy 193 (liftN c ⊞ δ) ∧ DivisibleBy 5 δ ∧ NPoly.normInf δ < 5 * 193
#guard decrypt t s ctMsSeal = (2 : ZMod 5) ⊡ mm
#guard ctMsSeal ≠ ctMs
#guard (NPoly.normInf (crit s ctMsSeal) : ℚ) ≤ modSwitchBound .seal 4 t 1 193 1 (NPoly.normInf (crit s ctRelC))
-- BGV12's Scale (c' ≡ c mod t) is exact but does NOT give a meaningful plaintext here,
-- because q_ℓ = 193 ≢ 1 (mod 5):
def ctMsBgv12 : Ct Q1 4 := modSwitch .bgv12 t 193 Q1 ctRelC
#guard ctRelC.all fun c => DivisibleBy 193 (liftN c ⊞ msDelta .bgv12 t 193 c)
#guard (List.zip ctRelC ctMsBgv12).all fun cc => red t (liftN cc.1) = red t (liftN cc.2)
#guard decrypt t s ctMsBgv12 ≠ mm ∧ decrypt t s ctMsBgv12 ≠ (2 : ZMod 5) ⊡ mm

/-! ### Automorphism at the lower level, with the key restricted by dropping limbs -/

def dig1 : Fin 2 → Fin 2 := fun i => dig i.castSucc
def gkOF1 : HybridKey tq.init tp 2 4 := gkOF.restrict (show 2 ≤ 3 by decide)

/-- `σ_3` of the level-1 ciphertext, OpenFHE order (key switch, then automorphism) -/
def ctAutR : RCt tq.init 4 := evalAutomorphismOF .centred t tq.init tp dig1 3 gkOF1 ctMsR
def ctAut : Ct Q1 4 := ctAutR.toBig

#guard decrypt t s ctAut = (2 : ZMod 5) ⊡ pauto 3 mm
#guard decryptSF t s ctAut 2 = pauto 3 mm
-- σ_g permutes coefficients up to sign, so the noise grows only by the key-switching term
-- (level-1 digits: {97,113} and the empty digit):
#guard (NPoly.normInf (crit s ctAut) : ℚ)
  ≤ NPoly.normInf (crit s ctMs) + ksAddedBound .centred 4 t 1 2 [[97, 113], []] [257, 337]

-- SEAL order at the top level (automorphism, then key switch from σ_3(s) to s):
def ct1R : RCt tq 4 := toRCt tq ct1
#guard decrypt t s (evalAutomorphismSEAL .centred t tq tp dig 3 gkSEAL ct1R).toBig = pauto 3 m1
#guard decrypt t s (evalAutomorphismOF .centred t tq tp dig 3 gkOF ct1R).toBig = pauto 3 m1
-- the two conventions' keys are NOT interchangeable:
#guard decrypt t s (evalAutomorphismSEAL .centred t tq tp dig 3 gkOF ct1R).toBig ≠ pauto 3 m1
#guard decrypt t s (evalAutomorphismOF .centred t tq tp dig 3 gkSEAL ct1R).toBig ≠ pauto 3 m1
-- without key switching, σ_3(ct) decrypts under σ_3(s):
#guard decrypt t (pauto 3 s) (automorphCt 3 ct1) = pauto 3 m1

/-! ### OpenFHE-style decryption: mod-switch down to one limb first -/

/-- level-0 ciphertext (modulus `97`) -/
def ctL0 : Ct (tq.init.init.prod) 4 := (modSwitchRns .centred t tq.init ctAutR).toBig
#guard tq.init.init.prod = 97
-- two primes dropped since the tensor product: scaling factor (193·113)⁻¹ = (3·3)⁻¹ = 4 mod 5
#guard decryptSF t s ctL0 ((((193 * 113 : ℕ) : ZMod 5))⁻¹) = pauto 3 mm
#guard NPoly.normInf (crit s ctL0) < 97 / 2

/-! ### Bookkeeping: the `State` invariant along the whole pipeline -/

def st1 : State t 4 := State.fresh m1 3
def st2 : State t 4 := State.fresh m2 3
def st3 : State t 4 := (st1.mul st2).getD st1
def stRel : State t 4 := st3.relin
def stMs : State t 4 := stRel.modSwitch 193
def stAut : State t 4 := stMs.evalAutomorphism 3
def stL0 : State t 4 := stAut.modSwitch 113

#guard Holds s ct1 st1 Bfresh ∧ Holds s ct2 st2 Bfresh
#guard Holds s ct3 st3 (mulBound 4 Bfresh Bfresh)
#guard Holds s ctRelC stRel (mulBound 4 Bfresh Bfresh + 31)
#guard Holds s ctMs stMs 300
#guard Holds s ctAut stAut 300
#guard Holds s ctL0 stL0 48
#guard stL0.sf = 4 ∧ stL0.limbs = 1 ∧ stL0.keyElt = 1 ∧ stL0.deg = 1
#guard (st1.add st2).isSome ∧ (stMs.add st1).isNone
-- raw automorphism changes the key: σ_3(ct1) satisfies the invariant with keyElt = 3
#guard Holds s (automorphCt 3 ct1) (st1.automorphRaw 3) Bfresh

/-! ### A chain with `q_ℓ ≡ 1 (mod t)`: BGV12's `Scale` preserves the message -/

/-- `Q = 97·41`, and `41 ≡ 1 (mod 5)` -/
def qB : Basis 2 := ![97, 41]
def ctB : Ct qB.prod 4 := encrypt .canonical (pkGen t s aPk ePk) m1 u1 e10 e11
#guard decrypt t s ctB = m1
#guard decrypt t s (modSwitch .bgv12 t 41 97 ctB) = m1
#guard modSwitch .bgv12 t 41 97 ctB = modSwitch (.ghs .centred) t 41 97 ctB
#guard (modSwitchRns .centred t qB (toRCt qB ctB)).toBig = modSwitch (.ghs .centred) t 41 qB.init.prod ctB

/-! ### Rotation bookkeeping -/

-- N = 8 (2N = 16): OpenFHE/Lattigo use 5, SEAL uses 3.
#guard (List.range 4).map (fun r => galoisEltOF 8 r) = [1, 5, 9, 13]
#guard galoisEltOF 8 (-1) = 13 ∧ galoisEltOF 8 (-1) = galoisInv 8 5
#guard [galoisEltSEAL 8 1, galoisEltSEAL 8 2, galoisEltSEAL 8 (-1), galoisEltSEAL 8 0] = [3, 9, 11, 15]
#guard galoisEltConj 8 = 15

end Respec.BGV.Test
