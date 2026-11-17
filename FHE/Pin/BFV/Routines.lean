import FHE.Pin.BFV.AlgoMutants

/-!
# FHE.Pin.BFV.Routines — mirrors of the BFV routines that have no project definition
(UNTRUSTED glue; `impl = "mirror-only"` in the result lines)

* `decHpsF`: `DCRTPolyImpl::ScaleAndRound` to a `NativePoly` modulo `t`
  (`dcrtpoly-impl.h:1220-1445`), the decryption of the HPS family. **All `double`** (there is no
  `long double` in v1.6.1's decryption): eight branches, by whether `t` is a power of two, whether
  `qMSB + sizeQMSB < 52` (else every residue is split at `qMSB/2` bits and a second table is used),
  and whether the integer part is accumulated with or without reduction modulo `t`.
* `decBehzF`: the `γ`-corrected integer procedure (`dcrtpoly-impl.h:1652-1696`), BEHZ.
* `decSmallF`: decryption of a ciphertext with fewer limbs than the chain
  (`bfvrns-pke.cpp:254-275`): `DropLastElementAndScale` down to one limb, then
  `NativeVector::MultiplyAndRound(t, q)`, which is `(uint64)(t·(x/q) + 0.5)` **in `double`** on the
  centred value (`ubintnat.h:657-661`, `mubintvecnat.cpp:539-553`), then a centred switch to `t`.
* `bvDigits`: `DCRTPolyImpl::CRTDecompose` (`dcrtpoly-impl.h:249-309`): the digits of BV key
  switching.
-/

namespace FHE.Pin.BFV

def bitLen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

def isPow2 (n : Nat) : Bool := n != 0 && 2 ^ Nat.log2 n == n

/-- Which branch of the decryption `ScaleAndRound` is taken. -/
def decBranch (t : Nat) (qs : Array Nat) : String :=
  let qMSB := bitLen (qs.foldl max 0)
  let tMSB := bitLen t
  let sMSB := bitLen qs.size
  let split := !(qMSB + sMSB < 52)
  let h := qMSB / 2
  (if isPow2 t then "pow2" else "general") ++ (if split then "/split" else "/whole") ++
  (if isPow2 t then
    (if (if split then h + tMSB + sMSB < 62 else qMSB + sMSB + tMSB < 63) then "/unreduced" else "/reduced")
   else
    (if (if split then h + tMSB + sMSB < 52 else qMSB + tMSB + sMSB < 52) then "/unreduced" else "/reduced"))

/-- `PKEBFVRNS::Decrypt`'s `ScaleAndRound` for HPS, HPSPOVERQ, HPSPOVERQLEVELED, from the limbs
`x` of the phase over the full chain `qs`. `exact`: the float sum replaced by its exact value
(variant). `intApart`: VARIANT, the integer part kept out of the `double` (the fractional sum
rounded alone and added to the integer part modulo `t`): isolates the precision lost by
`floatSum += intSum` (`dcrtpoly-impl.h:1369`, `:1385`, `:1411`, `:1436`). -/
def decHpsF (fma exact : Bool) (t : Nat) (qs : Array Nat) (x : RP) (intApart : Bool := false) : Array Nat :=
  let Q := prodL qs
  let k := qs.size
  let qMSB := bitLen (qs.foldl max 0)
  let tMSB := bitLen t
  let sMSB := bitLen k
  let h := qMSB / 2
  let split := !(qMSB + sMSB < 52)
  let pow2 := isPow2 t
  let tq := qs.map fun q => inv (Q / q) q * t
  let tabT := (Array.range k).map fun i => tq[i]! / qs[i]! % t
  let nums := (Array.range k).map fun i => tq[i]! % qs[i]!
  let frac := (Array.range k).map fun i => D.div (D.ofNat nums[i]!) (D.ofNat qs[i]!)
  let tqB := tq.map (· <<< h)
  let tabTB := (Array.range k).map fun i => tqB[i]! / qs[i]! % t
  let numsB := (Array.range k).map fun i => tqB[i]! % qs[i]!
  let fracB := (Array.range k).map fun i => D.div (D.ofNat numsB[i]!) (D.ofNat qs[i]!)
  let unreduced := if split then h + tMSB + sMSB < 52 else qMSB + tMSB + sMSB < 52
  let td := D.ofNat t
  let tInv := D.div (D.ofNat 1) td
  let N := if h0 : 0 < x.size then x[0].size else 0
  (Array.range N).map fun c =>
    let init : D := if pow2 then D.half else ⟨0, 0⟩
    let (fs, is, ex) := (Array.range k).foldl (fun (acc : D × Nat × ℚ) i =>
      let (fs, is, ex) := acc
      let xi := (x[i]!)[c]!
      if !split then
        let m := xi * tabT[i]!
        (D.mulAdd fma fs (D.ofNat xi) frac[i]!, is + (if pow2 || unreduced then m else m % t),
         if exact then ex + (xi : ℚ) * ((nums[i]! : Nat) : ℚ) / ((qs[i]! : Nat) : ℚ) else ex)
      else
        let hi := xi >>> h
        let lo := xi - (hi <<< h)
        let m1 := lo * tabT[i]!
        let m2 := hi * tabTB[i]!
        (D.mulAdd fma (D.mulAdd fma fs (D.ofNat lo) frac[i]!) (D.ofNat hi) fracB[i]!,
         is + (if pow2 || unreduced then m1 + m2 else m1 % t + m2 % t),
         if exact then ex + (lo : ℚ) * ((nums[i]! : Nat) : ℚ) / ((qs[i]! : Nat) : ℚ) + (hi : ℚ) * ((numsB[i]! : Nat) : ℚ) / ((qs[i]! : Nat) : ℚ)
         else ex))
      (init, 0, 0)
    if exact then
      -- the float sum replaced by its exact value: ⌊1/2 + Σ⌋ + integer part, modulo t
      ((is : Int) + ⌊(1 / 2 : ℚ) + ex⌋).toNat % t
    else if pow2 then (is + (D.floor fs).toNat) % t
    else if intApart then (is + (D.floor (D.add fs D.half)).toNat) % t
    else
      let fs := D.add fs (D.ofNat is)
      let q := (D.floor (D.mul fs tInv)).toNat
      let fs2 := if fma then D.fma (D.neg td) (D.ofNat q) fs else D.sub fs (D.mul td (D.ofNat q))
      (D.floor (D.add fs2 D.half)).toNat

/-- `PKEBFVRNS::Decrypt`'s `ScaleAndRound` for BEHZ (`γ = 2²⁶` hard-coded in the routine). The
result is not reduced modulo `t` by the library (it can be `t`). -/
def decBehzF (t gamma : Nat) (qs : Array Nat) (x : RP) : Array Nat :=
  let Q := prodL qs
  let k := qs.size
  let tg := t * gamma
  let c1 := qs.map fun q => (inv (Q / q) q * gamma % q) * t % q
  let c2 := qs.map fun q => (tg - 1) * inv q tg % tg
  let N := if h0 : 0 < x.size then x[0].size else 0
  (Array.range N).map fun c =>
    let s := (Array.range k).foldl (fun acc i =>
      (acc + ((x[i]!)[c]! * c1[i]! % qs[i]!) * c2[i]! % tg) % tg) 0
    (s + (s &&& (2 ^ 26 - 1))) >>> 26

/-- `NativeInteger::MultiplyAndRound(t, q)` in `double`. -/
def marD (fma : Bool) (t q v : Nat) : Nat :=
  let r := D.div (D.ofNat v) (D.ofNat q)
  let s := if fma then D.fma (D.ofNat t) r D.half else D.add (D.mul (D.ofNat t) r) D.half
  (D.floor s).toNat

/-- Decryption of a phase with fewer limbs than the chain: `DropLastElementAndScale` to one limb
(`floorDrop`: MUTANT), `MultiplyAndRound(t, q)` (`exact`: exact rounding half away from zero
instead of `double`), centred switch to `t`. -/
def decSmallF (fma exact floorDrop : Bool) (t : Nat) (qs : Array Nat) (phi : RP) : Array Nat := Id.run do
  let mut cur := phi
  let mut ms := qs
  for _ in [0:qs.size - 1] do
    cur := dropLastScaleF floorDrop ms cur
    ms := ms.pop
  let q := ms[0]!
  let half := q / 2
  let mar := fun (v : Nat) => if exact then (2 * v * t + q) / (2 * q) else marD fma t q v
  return cur[0]!.map fun x =>
    let r := if x > half then q - mar (q - x) else mar x % q
    cenTo q t r

/-! ## BV digits -/

/-- The signed digits of one residue `x` modulo `q` in base `2^w`
(`NativeVector::BaseDecompose`, `mubintvecnat.cpp:602-657`): balanced digits in `[−2^{w−1}, 2^{w−1})`
of the centred value (the top window takes what is left) when `nW·w + 1 ≤ 64`, plain unsigned
windows otherwise. -/
def baseDigits (unbalanced : Bool) (w q : Nat) (x : Nat) : Array Int :=
  let nW := (bitLen q + w - 1) / w
  let mask := 2 ^ w - 1
  if unbalanced || nW * w + 1 > 64 || q ≤ 1 then
    (Array.range nW).map fun i => (((x >>> (i * w)) &&& mask : Nat) : Int)
  else
    let h := 2 ^ (w - 1)
    let H := (Array.range nW).foldl (fun acc i => acc + (h <<< (i * w))) 0
    -- biased = x~ + H ≥ 0 with x~ the centred value
    let biased : Nat := if x > q / 2 then x + H - q else x + H
    (Array.range nW).map fun i =>
      let v := if i + 1 < nW then (biased >>> (i * w)) &&& mask else biased >>> (i * w)
      (v : Int) - (h : Int)

/-- `CRTDecompose(w)` of `d` (limbs over `qs`): the digits, each as limbs over `qs`.
`w = 0`: digit `j` is limb `j`, read centred in every other limb (`canon`: MUTANT, read in
`[0, q_j)`). `w > 0`: per limb, the base-`2^w` digits of `baseDigits`, reduced in every limb. -/
def bvDigits (canon unbalanced : Bool) (w : Nat) (qs : Array Nat) (d : RP) : Array RP :=
  if w == 0 then
    (Array.range qs.size).map fun j =>
      (Array.range qs.size).map fun k =>
        if k == j then d[j]! else
          d[j]!.map fun v => if canon then v % qs[k]! else cenTo qs[j]! qs[k]! v
  else
    ((Array.range qs.size).map fun i =>
      let q := qs[i]!
      let ds := d[i]!.map (baseDigits unbalanced w q)
      let nW := (bitLen q + w - 1) / w
      (Array.range nW).map fun win =>
        (Array.range qs.size).map fun k =>
          ds.map fun (dv : Array Int) => (dv[win]! % ((qs[k]! : Nat) : Int)).toNat).flatten

/-- `Σ_j a_j·b_j` modulo `X^N + 1` and `m`. -/
def innerNeg (m : Nat) (a b : Array Limb) : Limb :=
  if a.size == 0 then #[] else
  let N := a[0]!.size
  let w := slotW N m a.size
  let P := (Array.range a.size).foldl (fun acc j => acc + pack a[j]! w 0 N * pack b[j]! w 0 N) 0
  foldNeg N m w P

/-! ## HYBRID key switching on arrays (mirror of `keySwitchBGVOpenFHE` at plaintext modulus 1)

Canonical fast base conversion `FBC(x; S → m) = Σ_{i∈S} [xᵢ·(Q_S/qᵢ)⁻¹]_{qᵢ}·(Q_S/qᵢ) mod m`
(`ApproxSwitchCRTBasis`, `dcrtpoly-impl.h:938-985`). ModUp of digit `j` (limbs `S_j`, contiguous,
in the order of `sizes`): the limbs of `S_j` kept, every other limb of `Q_ℓ ∪ P` by `FBC`. Inner
products with the key over `Q_ℓ ∪ P` (Kronecker products). ModDown (`ApproxModDown` with `t = 0`,
`:1020-1056`): `(x_q − FBC(x_P; P → q))·P⁻¹`. Cross-checked against the proved staged execution
(`FHE.Pin.AlgoStage.ksStaged`, equal to `keySwitchBGVOpenFHE`) by `algo.relin.fast-vs-staged`. -/

/-- `FBC(x; ms → m)` of every coefficient. -/
def fbcF (ms : Array Nat) (x : RP) (m : Nat) : Limb :=
  let M := prodL ms
  let N := if h : 0 < x.size then x[0].size else 0
  let y : RP := (Array.range ms.size).map fun i =>
    let q := ms[i]!
    let c := inv (M / q) q
    x[i]!.map fun v => v * c % q
  let h := ms.map fun q => M / q % m
  (Array.range N).map fun c =>
    (Array.range ms.size).foldl (fun acc i => acc + (y[i]!)[c]! * h[i]!) 0 % m

/-- HYBRID key switch of `d` (limbs over `qs`) with the key digits `kb`, `ka` (limbs over
`qs ++ ps`): `(KS₀, KS₁)` over `qs`. -/
def hybridKSF (K : Nat) (qs ps : Array Nat) (sizes : List Nat) (d : RP) (kb ka : Array RP) : RP × RP :=
  let ℓ := qs.size
  let all := qs ++ ps
  let starts := (sizes.foldl (fun (acc : Array Nat × Nat) s => (acc.1.push acc.2, acc.2 + s)) (#[], 0)).1
  let sz := sizes.toArray
  let up : Array RP := (Array.range sz.size).map fun j =>
    let lo := starts[j]!
    let hi := lo + sz[j]!
    let S := qs.extract lo hi
    let xs := d.extract lo hi
    parMap K all.size fun m => if lo ≤ m && m < hi then d[m]! else fbcF S xs all[m]!
  let inner := fun (key : Array RP) =>
    parMap K all.size fun m => innerNeg all[m]! (up.map (·[m]!)) (key.map (·[m]!))
  let down := fun (x : RP) =>
    let xp := x.extract ℓ (ℓ + ps.size)
    let P := prodL ps
    parMap K ℓ fun i =>
      let q := qs[i]!
      let f := fbcF ps xp q
      let pi := inv P q
      (Array.range (x[i]!).size).map fun c => ((x[i]!)[c]! + q - f[c]!) * pi % q
  (down (inner kb), down (inner ka))

end FHE.Pin.BFV
