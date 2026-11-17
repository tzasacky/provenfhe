import Respec.BFV

/-!
# Respec.BFVTest — sanity tests for BFV at tiny parameters

`N = 4`, `t = 5`, `Q = 97·113·193`, auxiliary basis `257·337·353·401` (HPS `P`, BEHZ `B`),
`m_sk = 409`, `m̃ = 2^16`, key-switching `P = 257·337`.
-/

namespace Respec.BFV.Test

open Spec Respec Respec.BFV

abbrev t : ℕ := 5
abbrev Q : ℕ := tq.prod
/-- auxiliary basis for HPS (`P`) and BEHZ (`B`) -/
def aux : Basis 4 := ![257, 337, 353, 401]
def dig : Fin 3 → Fin 2 := ![0, 0, 1]

#guard aux.IsCRT ∧ tq.Coprime aux ∧ Nat.Coprime 409 aux.prod ∧ Nat.Coprime 409 Q
-- HPS needs P > t·N·Q (scaled tensor fits) and Q·P > N·Q² (tensor fits)
#guard aux.prod > t * 4 * Q

def s : IntPoly 4 := zpoly [1, -1, 0, 1]
def aPk : IntPoly 4 := zpoly [1234567, 891011, 1213141, 516171]
def ePk : IntPoly 4 := zpoly [1, -2, 0, 1]
def pk : BGV.PublicKey Q 4 := pkGen s aPk ePk
def m1 : Poly t 4 := red t (zpoly [1, 2, 3, 4])
def m2 : Poly t 4 := red t (zpoly [4, 0, 2, 1])
def mm : Poly t 4 := m1 ⊠ m2
def u1 : IntPoly 4 := zpoly [1, 0, -1, 1]
def u2 : IntPoly 4 := zpoly [-1, 1, 1, 0]
def e10 : IntPoly 4 := zpoly [2, -1, 0, -2]
def e11 : IntPoly 4 := zpoly [-1, 0, 2, 1]
def e20 : IntPoly 4 := zpoly [0, 1, -2, 1]
def e21 : IntPoly 4 := zpoly [1, 1, -1, 0]

def ct1 : BGV.Ct Q 4 := encrypt .floorDelta .canonical pk m1 u1 e10 e11
def ct2 : BGV.Ct Q 4 := encrypt .floorDelta .canonical pk m2 u2 e20 e21

/-! ### Encoding, encryption, decryption, noise forms -/

#guard Q / t = 423094 ∧ Q % t = 3
#guard encodeZ .floorDelta 5 Q 4 = 1692376 ∧ encodeZ .round 5 Q 4 = 1692378 ∧ encodeZ .ceil 5 Q 4 = 1692379
-- OpenFHE's residue formula t⁻¹·[−Q·m]_t is the ceiling encoding
#guard encodeOpenFHE Q m1 = encode .ceil .canonical Q m1
#guard encodeOpenFHE Q m1 ≠ encode .round .canonical Q m1
#guard decrypt t s ct1 = m1 ∧ decrypt t s ct2 = m2
#guard [Encoding.floorDelta, .round, .ceil].all fun enc =>
  [Lift.canonical, .centred].all fun ml => decrypt t s (encrypt enc ml pk m1 u1 e10 e11) = m1
-- Δ-form noise of a fresh ciphertext is exactly e·u + e0 + e1·s
#guard noiseDelta .floorDelta .canonical s ct1 m1 = ePk ⊠ u1 ⊞ e10 ⊞ e11 ⊠ s
#guard EncryptsDelta .floorDelta .canonical s ct1 m1 (4 * 2 * 1 + 2 + 4 * 2 * 1)
-- invariant noise: v_inv = (t·v − r_t(Q)·m̃)/Q, and it is < 1/2
#guard invNoise s ct1 m1 = invFromDelta t Q (noiseDelta .floorDelta .canonical s ct1 m1) (liftN m1)
#guard EncryptsInv s ct1 m1 (1 / 1000) ∧ ¬ EncryptsInv s ct1 m2 (1 / 2)
-- HPS simple-scaling decryption from the residues of the phase
#guard decryptHPS t tq (castRns tq (BGV.phase s ct1)) = m1

-- "‖v‖∞ < Δ/2" alone does not guarantee correct decryption when the r_t(Q)·m term is ignored:
-- trivial ciphertext (Δ·4 + v, 0) with v = −(Δ/2 − 1).
def vBad : ℤ := -((Q / t : ℕ) / 2 - 1 : ℤ)
def ctBad : BGV.Ct Q 4 := [red Q (zpoly [((Q / t : ℕ) : ℤ) * 4 + vBad]), 0]
def mBad : Poly t 4 := red t (zpoly [4])
#guard noiseDelta .floorDelta .canonical s ctBad mBad = zpoly [vBad]
#guard 2 * vBad.natAbs < Q / t
#guard decrypt t s ctBad ≠ mBad
#guard ¬ EncryptsInv s ctBad mBad (1 / 2)

/-! ### Textbook multiplication -/

def ct3 : BGV.Ct Q 4 := mulTextbook t ct1 ct2
#guard ct3.length = 3
#guard decrypt t s ct3 = mm
#guard EncryptsInv s ct3 mm (1 / 100)

/-! ### HPS RNS multiplication equals the textbook one -/

def ct1R : List (RnsPoly tq 4) := BGV.toRCt tq ct1
def ct2R : List (RnsPoly tq 4) := BGV.toRCt tq ct2
def ct3HPS : BGV.Ct Q 4 := BGV.RCt.toBig (mulHPS t tq aux ct1R ct2R)
#guard ct3HPS = ct3
-- the exact basis extension gives the centred representative
#guard (ofRns aux (exactBConvBasis tq aux (ct1R.getD 0 default))).coeff 0
  = (((liftC (ct1.getD 0 0)).coeff 0 : ℤ) : ZMod aux.prod)
-- complex scaling on integers: ⌊t·x/Q⌉ mod p_j
#guard (List.range 200).all fun n =>
  let x : ℤ := 1000003 * (n : ℤ) * 77777 - 7000000000000
  (List.finRange 4).all fun j =>
    hpsScaleZ t tq aux (toRes tq x) (toRes aux x) j = ((rdiv (t * x) Q : ℤ) : ZMod (aux j))

/-! ### BEHZ RNS multiplication -/

def ct3BEHZ : BGV.Ct Q 4 := BGV.RCt.toBig (mulBEHZ t tq aux 409 65536 ct1R ct2R)
#guard ct3BEHZ.length = 3
#guard decrypt t s ct3BEHZ = mm
#guard EncryptsInv s ct3BEHZ mm (1 / 100)
-- BEHZ and FV12 produce different ciphertexts (different representatives are tensored) ...
#guard ct3BEHZ ≠ ct3

-- ... but BEHZ is, up to an error of at most k = 3 per coefficient, the *floor* of t/Q times the
-- integer tensor of the Montgomery-reduced representatives (ζ + q·r)/m̃.
def montLift (c : RnsPoly tq 4) : IntPoly 4 := force ⟨fun n => behzExtendZ tq 65536 (c.res n)⟩
def behzRef : BGV.Ct Q 4 :=
  (forceAll (tensorWith pmul padd 0 (ct1R.map montLift) (ct2R.map montLift))).map fun x =>
    red Q (force ⟨fun i => ((t : ℤ) * x.coeff i) / (Q : ℤ)⟩)
#guard (List.zip ct3BEHZ behzRef).all fun cc => NPoly.normInf (liftC (cc.1 ⊟ cc.2)) ≤ 3
-- the Montgomery representative is ≡ c (mod q), small, and its residues are what the RNS
-- algorithm computes
#guard ct1R.all fun c => red Q (montLift c) = ofRns tq c
#guard ct1R.all fun c => 2 * NPoly.normInf (montLift c) ≤ Q + Q / 1000
#guard ct1R.all fun c => (List.finRange 4).all fun n =>
  behzExtendRes tq 65536 (c.res n) 409 = ((behzExtendZ tq 65536 (c.res n) : ℤ) : ZMod 409)
-- fast RNS floor on integers: ⌊t·x/q⌋ − α with 0 ≤ α ≤ k−1
#guard (List.range 200).all fun n =>
  let x : ℤ := 1000003 * (n : ℤ) * 77777 - 7000000000000
  let f : ℤ := (behzFloorRes t tq (toRes tq x) 1000000007 (x : ZMod 1000000007)).valMinAbs
  let a := (t * x) / Q - f
  -- compare modulo the large prime 1000000007: the difference is a small α
  ((a % 1000000007 + 1000000007) % 1000000007) ≤ 2
-- Shenoy–Kumaresan conversion is exact for |y| well below M·m_sk/2
#guard (List.range 200).all fun n =>
  let y : ℤ := 1000003 * (n : ℤ) * 7777 - 700000000000
  (List.finRange 3).all fun i =>
    behzSKRes aux 409 (toRes aux y) (y : ZMod 409) (tq i) = (y : ZMod (tq i))

/-! ### Relinearization with a hybrid key (`ns = 1`, plain ModDown) -/

def aK : Fin 2 → IntPoly 4 :=
  ![zpoly [123456789012, 98765432101, 55555555555, 31415926535],
    zpoly [27182818284, 16180339887, 141421356237, 173205080756]]
def eK : Fin 2 → IntPoly 4 := ![zpoly [1, -1, 2, 0], zpoly [-2, 0, 1, 1]]
def rk : HybridKey tq tp 2 4 := hybridKeyGen 1 tq tp dig (s ⊠ s) s aK eK

def ctRel : BGV.Ct Q 4 := BGV.RCt.toBig (relin .centred tq tp dig rk (BGV.toRCt tq ct3))
def ctRelBEHZ : BGV.Ct Q 4 := BGV.RCt.toBig (relin .canonical tq tp dig rk (BGV.toRCt tq ct3BEHZ))
#guard ctRel.length = 2 ∧ decrypt t s ctRel = mm ∧ decrypt t s ctRelBEHZ = mm
#guard EncryptsInv s ctRel mm (1 / 100)
-- the key-switching error is tiny compared with Δ (here ≤ 10 in absolute value)
#guard NPoly.normInf (BGV.crit s ctRel ⊟ BGV.crit s ct3) ≤ 10

end Respec.BFV.Test
