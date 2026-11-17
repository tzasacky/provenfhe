import Challenge.BFVMul.HPS
import Spec.BudgetBFVRns

/-!
# Challenge.BFVMul.BEHZ — BFV multiplication in RNS, Bajard–Eynard–Hasan–Zucca   (LOCKED definitions)

The integer-only RNS multiplication of Bajard, Eynard, Hasan and Zucca ("A full RNS variant of
FV-like somewhat homomorphic encryption schemes", ePrint 2016/510), limb by limb, in the form
OpenFHE runs for `MultiplicationTechnique == BEHZ` (`LeveledSHEBFVRNS::EvalMult`,
`src/pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:200`, BEHZ branches at `:302-324` and `:407-428`;
line numbers are those of upstream OpenFHE v1.6.1, commit b59e1f29; `EvalSquare` runs
the same three routines on one operand, `:527`, `:689`, `:696`). This file contains definitions only; that `behzMul` meets the `mul`
contract of `Spec.TraceBFV` under `behzAuxOK?`, with the slacks `Spec.BudgetBFV.behzSlack`, is
proved in `Validation/BFVMul/BEHZ.lean`.

**The algorithm.** `qs = [q₁, …, q_k]` is the ciphertext basis, `Q = ∏ qᵢ`; `bs = [b₁, …, b_m]`
the auxiliary basis, `B = ∏ bⱼ`; `msk` one more modulus (`Bsk = bs ++ [msk]`); `mt` (`m̃`,
`2¹⁶` in OpenFHE) a small even modulus. An RNS polynomial is the list of its limbs, one
polynomial with coefficients in `[0, m)` per modulus `m`. Write `Q̂ᵢ = Q/qᵢ`, `B̂ⱼ = B/bⱼ`.

1. *Extend with a small Montgomery reduction* (`BEHZ.smmrq`; `FastBaseConvqToBskMontgomery`,
   `dcrtpoly-impl.h:1719-1810`, called at `bfvrns-leveledshe.cpp:304` and `:315`), every component
   of both operands, from `qs` to `qs ++ Bsk`. With `yᵢ = [xᵢ·[m̃·Q̂ᵢ⁻¹]_{qᵢ}]_{qᵢ} ∈ [0, qᵢ)`
   (`:1753-1765`), the integer `c″ = Σᵢ yᵢ·Q̂ᵢ` is congruent to `m̃·x` modulo `Q` and lies in
   `[0, k·Q)`: the *fast* base conversion, not reduced modulo `Q`. Its residue modulo `m̃` gives
   `r = [−c″·Q⁻¹]_{m̃}` (`:1766-1770`), read in `[−m̃/2, m̃/2)` (`:1791-1793`); then `m̃` divides
   `c″ + Q·r` and the limb modulo `b ∈ Bsk` is `(c″ + r·Q)·m̃⁻¹ mod b` (`:1780-1796`). The limbs
   are those of `A = (c″ + Q·r)/m̃`, an integer congruent to `x` modulo `Q` with
   `−Q/2 ≤ A < Q/2 + (k−1)·Q/m̃`.
2. *Tensor* (`HPS.tensor`; `bfvrns-leveledshe.cpp:351-361`): limb-wise negacyclic products in the
   basis `qs ++ Bsk` (OpenFHE multiplies in the evaluation representation; the model multiplies
   coefficient vectors, which is the same map on limbs).
3. *Fast floor* (`BEHZ.floorq`; `FastRNSFloorq`, `dcrtpoly-impl.h:1815-1864`, called at
   `bfvrns-leveledshe.cpp:413`), from `qs ++ Bsk` to `Bsk`. With `yᵢ = [xᵢ·[t·Q̂ᵢ⁻¹]_{qᵢ}]_{qᵢ}`
   (`:1830-1838`), the limb modulo `b` is `x_b·[t·Q⁻¹]_b − Σᵢ yᵢ·[qᵢ⁻¹]_b mod b`
   (`:1847-1861`): the residue of `(t·x − Σᵢ yᵢ·Q̂ᵢ)/Q = ⌊t·x/Q⌋ − v` for some `v ∈ [0, k−1]`.
4. *Shenoy–Kumaresan conversion* (`BEHZ.convSK`; `FastBaseConvSK`, `dcrtpoly-impl.h:1869-1953`,
   called at `bfvrns-leveledshe.cpp:420`), from `Bsk` to `qs`. With
   `zⱼ = [xⱼ·B̂ⱼ⁻¹]_{bⱼ}` (`:1903`), `α = [(Σⱼ zⱼ·B̂ⱼ − x_sk)·B⁻¹]_{msk}` (`:1897-1911`), read as
   `α − msk` when `α > ⌊msk/2⌋` (`:1936-1937`); the limb modulo `q` is `Σⱼ zⱼ·B̂ⱼ − α·B mod q`
   (`:1918-1939`). It is exact when `|x|/B + m ≤ (msk − 1)/2`.

Tables, `bfvrns-cryptoparameters.cpp`: `:713-724` (`t·Q̂ᵢ⁻¹ mod qᵢ`), `:726-738` (`Q̂ᵢ mod b`,
`Q̂ᵢ mod m̃`), `:740-746` (`qᵢ⁻¹ mod b`), `:748-761` (`m̃·Q̂ᵢ⁻¹ mod qᵢ`), `:763-766`
(`−Q⁻¹ mod m̃`, as `(m̃−1)·Q⁻¹ mod m̃`), `:768-776` (`Q mod b`), `:778-786` (`m̃⁻¹ mod b`),
`:788-797` (`t·Q⁻¹ mod b`), `:799-810` (`B̂ⱼ⁻¹ mod bⱼ`), `:812-821` (`B̂ⱼ mod q`), `:823-828`
(`B̂ⱼ mod msk`), `:830-832` (`B⁻¹ mod msk`), `:834-840` (`B mod q`). The auxiliary basis is
chosen at `:672-695` (`m = k` moduli below the ciphertext moduli, then `msk`).

**What is idealised / not modelled.** The algorithm is integer-only: there is no floating point
and nothing is rounded approximately, so the arithmetic content of the four steps is modelled
exactly. Not modelled: machine-word arithmetic — Barrett and Shoup reductions, 128-bit
accumulation (`Mul128`, `BarrettUint128ModUint64`), lazy reductions and the order of
intermediate reductions (the model reduces once per limb where the code reduces after every
operation; the residues are the same), and two places where the code relies on the sizes of the
words: `r` is moved into `[0, b)` as `r + b − m̃` (`dcrtpoly-impl.h:1793`, which needs `m̃ < b`)
and `α − msk` into `[0, q)` by `ModSubFast` (`:1937`, which needs `msk − α ≤ q`); the model takes
the residue of the signed integer. Both are checked separately, with the moduli sizes the word
routines assume, by `behzWordOK?` (`Challenge/BFVMul/BEHZWord.lean`; the model's arithmetic is
exact only when it holds).
Also not modelled: the NTT (the code holds limbs in the
evaluation representation between steps and reuses the `qs`-limbs of the input, `:1802-1809`),
OpenMP scheduling, and the generic component count (the model multiplies two-component
ciphertexts).

**The side condition** (`behzAuxOK?`): all moduli of `qs ++ bs ++ [msk]` positive and pairwise
coprime; `m̃` coprime to each of them (it is inverted modulo every `b ∈ Bsk`, and `Q` modulo
`m̃`); `msk > 2m`; and `(Spec.BudgetBFV.behzSlack t N Q B msk k m m̃).ok`, that is `m̃ > 0`,
`gcd(m̃, Q) = 1`, `2(k−1) ≤ m̃`, `m̃` even (the code reads `r` in `[−m̃/2, m̃/2)` with
`m̃/2 = m̃ >> 1`; for odd `m̃` the lift bound below fails by `Q/(2m̃)`) and the size condition

  `t·N·Q·(m̃ + 2(k−1))² + 2k·m̃² ≤ m̃²·B·(msk − 1 − 2m)`.

Derivation of the size condition: the lifts satisfy `2·m̃·|A| ≤ Q·(m̃ + 2(k−1))`, so every
coefficient of the three components of the tensor product has
`4·m̃²·|T| ≤ 2N·Q²·(m̃ + 2(k−1))²`; the fast floor `F = (t·T − S)/Q` with `0 ≤ S ≤ k·Q` has
`2|F| ≤ 2t|T|/Q + 2k ≤ t·N·Q·(m̃ + 2(k−1))²/m̃² + 2k`; step 4 recovers `F` from its residues iff
the integer `α' = (Σⱼ zⱼ·B̂ⱼ − F)/B`, which satisfies `|α'| ≤ m + |F|/B`, is in the centred range
of `msk`, for which `2|F| ≤ B·(msk − 1 − 2m)` suffices. (`msk > 2m` is implied by the size
condition whenever `qs` is nonempty; it is listed so that the natural-number subtraction is a
real one.) Under the side condition the result is congruent modulo `Q` to `F`, and
`t·T/Q − F ∈ [0, k)`: lift excess `⌈2(k−1)·Q/m̃⌉`, rounding slack `2k`.
-/

namespace Challenge.BFVMul
open Spec NPoly Scheme

variable {N : ℕ}

namespace BEHZ
open HPS

/-- `yᵢ = [xᵢ·[c·(Q/qᵢ)⁻¹]_{qᵢ}]_{qᵢ}`: the residues `x` modulo `qs` twisted by the table
`[c·(Q/qᵢ)⁻¹]_{qᵢ}` (`c = m̃`: `mtildeQHatInvModq`, `dcrtpoly-impl.h:1755-1765`; `c = t`:
`tQHatInvModq`, `:1830-1838`). -/
def twist (c : ℕ) (qs : List ℕ) (x : List ℤ) : List ℤ :=
  List.zipWith (fun q xi => xi * ((c : ℤ) * invMod (qs.prod / q) q % q) % q) qs x

/-- The fast base conversion sum `Σᵢ yᵢ·[Q/qᵢ]_m` (tables `QHatModbsk`, `QHatModmtilde`,
`BHatModq`, `BHatModmsk`), not reduced. -/
def convSum (qs : List ℕ) (y : List ℤ) (m : ℕ) : ℤ :=
  (List.zipWith (fun q yi => yi * ((qs.prod / q % m : ℕ) : ℤ)) qs y).sum

/-- `r = [−c″·Q⁻¹]_{m̃}` read in `[−m̃/2, m̃/2)`, from the twisted residues `y`
(`result_mtilde`, `dcrtpoly-impl.h:1763-1770`; centred at `:1791-1793`). `−Q⁻¹ mod m̃` is the
table `negQInvModmtilde = (m̃ − 1)·Q⁻¹ mod m̃`. -/
def mtRem (qs : List ℕ) (mt : ℕ) (y : List ℤ) : ℤ :=
  let r := convSum qs y mt % mt * (((mt - 1 : ℕ) : ℤ) * invMod qs.prod mt % mt) % mt
  if ((mt / 2 : ℕ) : ℤ) ≤ r then r - mt else r

/-- Small Montgomery reduction of one value: from its residues `x` modulo `qs`, the residue
modulo `b` of `(c″ + Q·r)/m̃`: `(Σᵢ yᵢ·[Q/qᵢ]_b + r·[Q]_b)·[m̃⁻¹]_b mod b`
(`dcrtpoly-impl.h:1780-1796`). -/
def smmrq1 (qs : List ℕ) (mt : ℕ) (x : List ℤ) (b : ℕ) : ℤ :=
  let y := twist mt qs x
  (convSum qs y b % b + mtRem qs mt y * ((qs.prod % b : ℕ) : ℤ)) * invMod mt b % b

/-- `FastBaseConvqToBskMontgomery` (`dcrtpoly-impl.h:1719`): from the limbs of an RNS polynomial
in the basis `qs`, its limbs in the basis `bsk`. -/
def smmrq (qs bsk : List ℕ) (mt : ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  bsk.map fun b => ⟨fun i => smmrq1 qs mt (residues x i) b⟩

/-- Base extension from `qs` to `qs ++ bsk`: the limbs modulo `qs` are kept
(`dcrtpoly-impl.h:1802-1809`), those modulo `bsk` come from `smmrq`. -/
def extend (qs bsk : List ℕ) (mt : ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  x ++ smmrq qs bsk mt x

/-- Fast floor of one value: from its residues `xq` modulo `qs` and its residue `xb` modulo `b`,
`x_b·[t·Q⁻¹]_b − Σᵢ yᵢ·[qᵢ⁻¹]_b mod b` (`dcrtpoly-impl.h:1847-1861`; tables `tQInvModbsk`,
`qInvModbsk`). -/
def floor1 (t : ℕ) (qs : List ℕ) (xq : List ℤ) (b : ℕ) (xb : ℤ) : ℤ :=
  let y := twist t qs xq
  (xb * ((t : ℤ) * invMod qs.prod b % b) - (List.zipWith (fun q yi => yi * invMod q b) qs y).sum)
    % b

/-- `FastRNSFloorq` (`dcrtpoly-impl.h:1815`): from the limbs of an RNS polynomial in the basis
`qs ++ bsk`, the limbs in the basis `bsk` of `⌊t·x/Q⌋ − v`, `v ∈ [0, k−1]`. -/
def floorq (t : ℕ) (qs bsk : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  List.zipWith
    (fun b xb => ⟨fun i => floor1 t qs (residues (x.take qs.length) i) b (xb.coeff i)⟩)
    bsk (x.drop qs.length)

/-- Shenoy–Kumaresan conversion of one value: from its residues `xb` modulo `bs` and its residue
`xsk` modulo `msk`, the residue modulo `q` of `Σⱼ zⱼ·(B/bⱼ) − α·B`, where `zⱼ = [xⱼ·(B/bⱼ)⁻¹]_{bⱼ}`
and `α = [(Σⱼ zⱼ·(B/bⱼ) − x_sk)·B⁻¹]_{msk}` is read as `α − msk` when `α > ⌊msk/2⌋`
(`dcrtpoly-impl.h:1897-1939`; tables `BHatInvModb`, `BHatModmsk`, `BInvModmsk`, `BHatModq`,
`BModq`). -/
def sk1 (bs : List ℕ) (msk : ℕ) (xb : List ℤ) (xsk : ℤ) (q : ℕ) : ℤ :=
  let z := digits bs xb
  let α := (convSum bs z msk % msk - xsk) * invMod bs.prod msk % msk
  let αc := if ((msk / 2 : ℕ) : ℤ) < α then α - msk else α
  (convSum bs z q - αc * ((bs.prod % q : ℕ) : ℤ)) % q

/-- `FastBaseConvSK` (`dcrtpoly-impl.h:1869`): from the limbs of an RNS polynomial in the basis
`bs ++ [msk]`, its limbs in the basis `qs`. -/
def convSK (qs bs : List ℕ) (msk : ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  qs.map fun q =>
    ⟨fun i => sk1 bs msk (residues (x.take bs.length) i) ((x.getD bs.length 0).coeff i) q⟩

end BEHZ

/-- **BEHZ multiplication** of two 2-component BFV ciphertexts at ciphertext basis `qs`, with
auxiliary basis `bs`, extra modulus `msk` and Montgomery modulus `mt` (module docstring). The
operands are integer representatives, read modulo each `q ∈ qs`; the result is the three
components, reconstructed from their final `qs`-limbs with coefficients in `[0, Q)`. Everything
in between is on limbs. -/
def behzMul (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ) (c d : List (IntPoly N)) : List (IntPoly N) :=
  let bsk := bs ++ [msk]
  let ext := fun a : IntPoly N => BEHZ.extend qs bsk mt (HPS.toLimbs qs a)
  (HPS.tensor (qs ++ bsk) (c.map ext) (d.map ext)).map fun x =>
    HPS.reconstruct qs (BEHZ.convSK qs bs msk (BEHZ.floorq t qs bsk x))

/-- The side condition under which `behzMul` has the slacks of `Spec.BudgetBFV.behzSlack` (module
docstring): all moduli of `qs ++ bs ++ [msk]` positive and pairwise coprime, `mt` coprime to
each of them, `msk > 2·|bs|`, and the conditions of `behzSlack` (`mt > 0`, `gcd(mt, Q) = 1`,
`2(k−1) ≤ mt`, `mt` even, the size condition). -/
def behzAuxOK? (t N : ℕ) (qs bs : List ℕ) (msk mt : ℕ) : Bool :=
  (qs ++ bs ++ [msk]).all (fun m => decide (0 < m)) &&
  decide ((qs ++ bs ++ [msk]).Pairwise Nat.Coprime) &&
  (qs ++ bs ++ [msk]).all (fun m => decide (Nat.Coprime mt m)) &&
  decide (2 * bs.length + 1 ≤ msk) &&
  (BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).ok

/-! ## Checks at tiny parameters

`N = 4`, `t = 5`, `qs = [7, 11]` (`Q = 77`), `bs = [13, 17]` (`B = 221`), `msk = 19`, `m̃ = 16`:
the side condition holds (`5·4·77·18² + 4·16² = 499 984 ≤ 16²·221·14 = 792 064`), with lift excess
`⌈2·77/16⌉ = 10` and rounding slack `4`. -/

#guard behzAuxOK? 5 4 [7, 11] [13, 17] 19 16
#guard BudgetBFV.behzSlack 5 4 77 221 19 2 2 16 == ⟨10, 4, true⟩

-- Agreement with a direct computation on integers (no limbs): the lifts `A = (c″ + Q·r)/m̃`
-- (`(Q/7)⁻¹ = 2 mod 7`, `(Q/11)⁻¹ = 8 mod 11`, `−Q⁻¹ = 11 mod 16`), their integer tensor product
-- `T`, and the fast floor `F = (t·T − S)/Q`. The lifts are congruent to the operands modulo `Q`
-- and within `2·|A| ≤ Q + 10`; `t·T − Q·F ∈ [0, 2Q)`; the result is `F mod Q`.
#guard
  let c : List (IntPoly 4) := [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩]
  let d : List (IntPoly 4) := [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩]
  let lift : ℤ → ℤ := fun x =>
    let c2 := x * 16 * 2 % 7 * 11 + x * 16 * 8 % 11 * 7
    let r := c2 * 11 % 16
    (c2 + 77 * (if 8 ≤ r then r - 16 else r)) / 16
  let floor : ℤ → ℤ := fun T => (5 * T - (T * 5 * 2 % 7 * 11 + T * 5 * 8 % 11 * 7)) / 77
  let coeffs := fun (x : List (IntPoly 4)) =>
    x.map fun a => (List.finRange 4).map fun i => a.coeff i
  let A : List (IntPoly 4) := c.map fun a => ⟨fun i => lift (a.coeff i)⟩
  let B : List (IntPoly 4) := d.map fun a => ⟨fun i => lift (a.coeff i)⟩
  let T := coeffs (Challenge.Source.tensor A B)
  coeffs A = [[3, -1, -36, 20], [-22, 9, 0, -9]] &&
  coeffs B = [[38, 39, 1, -7], [12, 33, -13, 5]] &&
  (coeffs A).map (·.map (· % 77)) = (coeffs c).map (·.map (· % 77)) &&
  (coeffs B).map (·.map (· % 77)) = (coeffs d).map (·.map (· % 77)) &&
  (coeffs A ++ coeffs B).all (·.all fun v => decide (2 * v.natAbs ≤ 77 + 10)) &&
  T.all (·.all fun v => decide (0 ≤ 5 * v - 77 * floor v ∧ 5 * v - 77 * floor v < 2 * 77)) &&
  coeffs (behzMul 5 [7, 11] [13, 17] 19 16 c d) = T.map (·.map fun v => floor v % 77)

-- Agreement with the limb-level Python model of the OpenFHE routines
-- (`harness/bfv-rns/rnsbfv.py`, `mul_behz`): the same inputs, their square, and inputs at the
-- extremes `0`, `1`, `(Q ± 1)/2`, `Q − 1`.
#guard
  let c : List (IntPoly 4) := [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩]
  let d : List (IntPoly 4) := [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩]
  let coeffs := fun (x : List (IntPoly 4)) =>
    x.map fun a => (List.finRange 4).map fun i => a.coeff i
  coeffs (behzMul 5 [7, 11] [13, 17] 19 16 c d)
    = [[35, 64, 71, 33], [55, 0, 54, 5], [75, 29, 40, 54]] &&
  coeffs (behzMul 5 [7, 11] [13, 17] 19 16 c c)
    = [[72, 15, 36, 12], [43, 41, 47, 51], [41, 51, 0, 25]]

#guard
  let c : List (IntPoly 4) := [⟨![0, 76, 0, 1]⟩, ⟨![39, 0, 1, 0]⟩]
  let d : List (IntPoly 4) := [⟨![76, 37, 37, 1]⟩, ⟨![0, 1, 1, 39]⟩]
  let coeffs := fun (x : List (IntPoly 4)) =>
    x.map fun a => (List.finRange 4).map fun i => a.coeff i
  coeffs (behzMul 5 [7, 11] [13, 17] 19 16 c d)
    = [[74, 74, 73, 73], [73, 16, 13, 4], [76, 0, 1, 21]]

-- Decryption. `N = 2`, `t = 2`, `qs = [3, 5]` (`Q = 15`, `Δ = 7`), `bs = [7]`, `msk = 23`,
-- `m̃ = 4`, secret `s = 1 − X`: `c` encrypts `1 + X` (phase `Δ·(1 + X) + 1`), `d` encrypts `X`
-- (phase `Δ·X + 1 − X`); the product decrypts to `(1 + X)·X = 1 + X` and the square of `c` to
-- `(1 + X)² = 0` in `Z_2[X]/(X² + 1)`.
#guard behzAuxOK? 2 2 [3, 5] [7] 23 4

#guard
  let s : IntPoly 2 := ⟨![1, -1]⟩
  let c : List (IntPoly 2) := [⟨![3, 11]⟩, ⟨![12, 8]⟩]
  let d : List (IntPoly 2) := [⟨![14, 8]⟩, ⟨![2, 0]⟩]
  let dec := fun (x : List (IntPoly 2)) =>
    (List.finRange 2).map fun i => ((bfvDecrypt 2 s (x.map (ofInt 15))).coeff i).val
  dec c = [1, 1] && dec d = [0, 1] &&
  dec (behzMul 2 [3, 5] [7] 23 4 c d) = [1, 1] &&
  dec (behzMul 2 [3, 5] [7] 23 4 c c) = [0, 0]

-- A too-small `msk` is rejected, and the Shenoy–Kumaresan step really fails: with `msk = 5`
-- (`msk − 1 − 2m = 0`) the second component differs from the one computed with `msk = 19`
-- (which is the fast floor modulo `Q`).
#guard !behzAuxOK? 5 4 [7, 11] [13, 17] 5 16

#guard
  let c : List (IntPoly 4) := [⟨![0, 37, 37, 39]⟩, ⟨![37, 39, 1, 39]⟩]
  let d : List (IntPoly 4) := [⟨![1, 38, 37, 76]⟩, ⟨![76, 38, 76, 37]⟩]
  let coeffs := fun (x : List (IntPoly 4)) =>
    x.map fun a => (List.finRange 4).map fun i => a.coeff i
  coeffs (behzMul 5 [7, 11] [13, 17] 19 16 c d)
    = [[48, 64, 19, 28], [31, 65, 28, 28], [38, 11, 76, 8]] &&
  coeffs (behzMul 5 [7, 11] [13, 17] 5 16 c d)
    = [[48, 64, 19, 28], [58, 65, 28, 28], [38, 11, 76, 8]]

-- An auxiliary basis one modulus short is rejected (`B = 13`: `499 984 > 16²·13·16 = 53 248`).
#guard !behzAuxOK? 5 4 [7, 11] [13] 19 16

-- An odd `m̃` is rejected, and the lift bound really fails: `Q = 97`, `m̃ = 3`, `x = 33` is lifted
-- to `−64` (read modulo `10007`), and `2·64 > Q + ⌈2(k−1)·Q/m̃⌉ = 97`.
#guard !behzAuxOK? 2 2 [97] [101] 103 3
#guard behzAuxOK? 2 2 [97] [101] 103 2
#guard BEHZ.smmrq1 [97] 3 [33] 10007 == 10007 - 64
#guard (BudgetBFV.behzSlack 2 2 97 101 103 1 1 3).e == 0

-- `m̃` sharing a factor with an auxiliary modulus is rejected (`m̃⁻¹ mod b` does not exist).
#guard !behzAuxOK? 5 4 [7, 11] [13, 17] 19 26

end Challenge.BFVMul
