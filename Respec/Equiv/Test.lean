import Respec.BGVTest
import Respec.Equiv.Gadget
import Respec.Equiv.Bookkeeping
import Spec.Decrypt

/-!
# Respec.Equiv.Test — TESTED (compiled `#guard` evaluation, not proofs)

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

Every check below runs A's and B's definitions on B's test instance (`Respec/BGVTest.lean`:
`N = 4`, `t = 5`, chain `97·113·193`, digits `{97,113},{193}`, special `257·337`) or on small
parameter sweeps. Counts are stated with each check.

1. **uniformLayout is nested** (hypothesis of `Gadget.gadgetReq_restrict`): for 6 chains
   (lengths 1–6, primes `≡ 1 mod 8` below 2000) × `α ∈ {0,…,4}` × every pair of levels `ℓ ≤ L`:
   `(digitModuli ℓ)[j] ∣ (digitModuli L)[j]` for every digit `j` — 6·5·(Σ pairs) checks, all true.
   The non-nested layout `[1,2] / [2]` fails it. (The general statement is now proved:
   `Gadget.uniformLayout_nested`; the test is kept as a check of the definitions it runs.)
2. **B's OpenFHE-style keys meet A's `KeyValid` with `keyNoise = t·Be`**: B's relinearization
   key `rk` (top level, `hybridKeyGen`) for both of A's level-3 digit requirements
   (`gadgetReq … 3 .square j`, `j = 0, 1`), and B's `HybridKey.restrict` of it to level 2 for A's
   level-2 requirement (`j = 0`): 3 checks, all true. With the Han–Ki factor they fail.
3. **Rotation orders, limb for limb** (`g = 3`, input `ct1`): B's OpenFHE order with the OpenFHE
   key `gkOF` vs A's order (automorph, then key switch with the key `σ₃(gkOF)`, which is A-valid
   for target `galois 3`): identical ciphertexts with centred lifts (odd moduli); **different**
   ciphertexts with canonical lifts (the canonical lift of `−x` is not `−lift x`, so key switching
   does not commute with `σ_g`), both decrypting to `σ₃(m₁)`.
4. **A's switched decryption vs B's ciphertext-switch decryption** (item 9): on B's level-2
   ciphertext `ctAut`, A's `bgvDecryptSwitched 5 [97, 113]` equals B's `decrypt` of the
   ciphertext switched to one limb (`ctL0`), both `= (193·113)⁻¹ • σ₃(m₁m₂)`.
-/

namespace Respec.Equiv.Test

open Spec Spec.Budget Spec.Scheme Respec Respec.BGV Respec.BGV.Test

/-! ### 1. uniformLayout nesting -/

def mkP (qs : List ℕ) : FullParams where
  src := { kind := .bgv, N := 4, qs := qs, t := 5 }
  store := { W := 1, limbs := [], special := [⟨257, 0⟩, ⟨337, 0⟩] }
  secretBound := 1
  inputNoise := 2
  keyNoise := 10
  outputNoise := 0

def nestedOK (P : FullParams) (lay : KSLayout) : Bool :=
  (List.range (P.src.qs.length + 1)).all fun L => (List.range (L + 1)).all fun ℓ =>
    let dl := digitModuli P lay ℓ
    let dL := digitModuli P lay L
    decide (dl.length ≤ dL.length) &&
      (List.range dl.length).all fun j => dL.getD j 1 % dl.getD j 1 == 0

def chains : List (List ℕ) :=
  [[97], [97, 113], [97, 113, 193], [17, 41, 73, 89, 97], [97, 113, 193, 241, 257, 337],
   [1153, 1201, 1217, 1249, 1297, 1361]]

#guard chains.all fun qs => (List.range 5).all fun α => nestedOK (mkP qs) (uniformLayout α)
#guard !(nestedOK (mkP [97, 113, 193]) ⟨fun ℓ => if ℓ = 3 then [1, 2] else if ℓ = 2 then [2] else [ℓ], false⟩)

/-! ### 2. B's keys under A's `KeyValid` -/

/-- The body of A's `KeyValid .bgv t B s req b a`, as a Boolean (`keyValidB_iff`). -/
def keyValidB {N : ℕ} (t B : ℕ) (s : IntPoly N) (req : KeyReq N) (b a : Poly req.modulus N) : Bool :=
  let e := NPoly.centered (b + a * NPoly.ofInt req.modulus s -
    req.factor * NPoly.ofInt req.modulus (req.target.eval s))
  decide (NPoly.normInf e ≤ B) && (List.finRange N).all fun i => decide ((t : ℤ) ∣ e.coeff i)

theorem keyValidB_iff {N : ℕ} (t B : ℕ) (s : IntPoly N) (req : KeyReq N) (b a : Poly req.modulus N) :
    keyValidB t B s req b a = true ↔ KeyValid .bgv t B s req b a := by
  unfold keyValidB KeyValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_const]

def Ptest : FullParams := mkP [97, 113, 193]

/-- A's validity of digit `j` of a B key (moved to A's modulus, numerically equal). -/
def validA {M : ℕ} (ℓ : ℕ) (j : ℕ) (kd : KskDigit M 4) : Bool :=
  let req := gadgetReq Ptest (uniformLayout 2) ℓ .square j
  keyValidB 5 10 s req (castPoly req.modulus kd.b) (castPoly req.modulus kd.a)

#guard (Ptest.src.modulus 3 * specialProd Ptest) = tq.prod * tp.prod
#guard validA 3 0 ((keyToBig rk).getD 0 ⟨0, 0⟩) && validA 3 1 ((keyToBig rk).getD 1 ⟨0, 0⟩)
#guard validA 2 0 ((keyToBig (rk.restrict (show 2 ≤ 3 by decide))).getD 0 ⟨0, 0⟩)
-- the Han–Ki factor is not A's
#guard !(keyValidB 5 10 s
  ⟨tq.prod * tp.prod, NPoly.const ((gadgetHK tp.prod Qs 0 : ℤ) : ZMod (tq.prod * tp.prod)), .square⟩
  ((keyToBig rk).getD 0 ⟨0, 0⟩).b ((keyToBig rk).getD 0 ⟨0, 0⟩).a)

/-! ### 3. Rotation orders -/

/-- `σ_g` applied to every limb of a key. -/
def keyAuto {k l d N : ℕ} {q : Respec.Basis k} {p : Respec.Basis l} (g : ℕ)
    (key : HybridKey q p d N) : HybridKey q p d N where
  bQ j := rautomorph g (key.bQ j)
  bP j := rautomorph g (key.bP j)
  aQ j := rautomorph g (key.aQ j)
  aP j := rautomorph g (key.aP j)

def gkA : HybridKey tq tp 2 4 := keyAuto 3 gkOF

-- σ₃(gkOF) is a valid key from σ₃(s) to s (A's target `galois 3`):
#guard kskCheck t (gadgetOF tp.prod Qs) (pauto 3 s) s (keyToBig gkA) 2

def rotOFc : RCt tq 4 := evalAutomorphismOF .centred t tq tp dig 3 gkOF ct1R
def rotAc : RCt tq 4 := evalAutomorphismSEAL .centred t tq tp dig 3 gkA ct1R
def rotOFn : RCt tq 4 := evalAutomorphismOF .canonical t tq tp dig 3 gkOF ct1R
def rotAn : RCt tq 4 := evalAutomorphismSEAL .canonical t tq tp dig 3 gkA ct1R

#guard rotOFc = rotAc
#guard rotOFn ≠ rotAn
#guard decrypt t s rotOFn.toBig = pauto 3 m1 ∧ decrypt t s rotAn.toBig = pauto 3 m1
#guard decrypt t s rotOFc.toBig = pauto 3 m1

/-! ### 4. Switched decryption -/

#guard Spec.Decrypt.bgvDecryptSwitched 5 [97, 113] s (ctAut.map (castPoly ([97, 113].prod)))
  = decrypt t s ctL0
#guard decrypt t s ctL0 = ((((193 * 113 : ℕ) : ZMod 5))⁻¹) ⊡ pauto 3 mm

end Respec.Equiv.Test
