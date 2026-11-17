import FHE.Pin.BFV.Float64
import FHE.Pin.Load

/-!
# FHE.Pin.BFV.Fast — array mirrors of the BFV RNS routines   (UNTRUSTED glue)

The locked definitions of `Challenge/BFVMul/{HPS,POverQ,BEHZ,Float}.lean` are functions on
`IntPoly N` (closures; nothing is memoised), so they can be executed literally only at very small
`N`. This file mirrors them on arrays of residues (`RP = limbs[limb][coefficient]`, canonical
residues as `Nat`), with the tables computed once per call and the negacyclic limb products done
by Kronecker substitution (one big-integer product per polynomial product; exact `Nat`
arithmetic). **Nothing here is proved equal to the definitions**: the mirrors are cross-checked by
`FHE.Pin.BFV.Algo` against the literal definitions (small `N`), against the proved-equal forced
pipelines of `FHE.Pin.BFV.Stage` (medium `N`), and coefficient-wise against the locked scalar
functions with `A64` on samples (every `N`).

`Conv` selects the conventions; its default is what the definitions (and OpenFHE) do, every other
value is a variant or a mutant.
-/

namespace FHE.Pin.BFV
open FHE.Pin (invMod)

abbrev Limb := Array Nat
abbrev RP := Array Limb

def prodL (a : Array Nat) : Nat := a.foldl (· * ·) 1

/-- `(Array.range n).map f`, one task per index if `K > 1`. -/
@[inline] def parMap {α : Type} (K n : Nat) (f : Nat → α) : Array α :=
  if K ≤ 1 || n ≤ 1 then (Array.range n).map f
  else ((Array.range n).map fun i => Task.spawn fun _ => f i).map Task.get

/-- `a⁻¹ mod m` (`0` if none), `a` reduced first. -/
@[inline] def inv (a m : Nat) : Nat := invMod (a % m) m

/-- Conventions of the mirrored routines. The default is OpenFHE's (and the locked definitions'). -/
structure Conv where
  /-- `s += a * b` is one fused multiply-add. -/
  fma : Bool := false
  /-- the overflow sum of `SwitchCRTBasis` in exact arithmetic -/
  exactSw : Bool := false
  /-- the fractional sum of `ScaleAndRound` in exact arithmetic -/
  exactSr : Bool := false
  /-- MUTANT: `nu` of `SwitchCRTBasis` starts at `0` instead of `0.5` -/
  swNoHalf : Bool := false
  /-- MUTANT: `nu` of `ScaleAndRound` starts at `0` (floor instead of round) -/
  srNoHalf : Bool := false
  /-- MUTANT: centred digits in the fast scaling `ApproxSwitchCRTBasis` of P-over-Q -/
  fastCentred : Bool := false
  /-- MUTANT: BEHZ without the small Montgomery reduction (`r = 0`) -/
  behzNoMont : Bool := false
  /-- MUTANT: BEHZ without the Shenoy–Kumaresan correction (`α = 0`) -/
  behzNoSK : Bool := false
  /-- MUTANT: BEHZ with the canonical (not centred) `α` -/
  behzSKCanon : Bool := false
  deriving Inhabited

/-! ## Negacyclic products by Kronecker substitution -/

/-- `Σ_{lo ≤ i < hi} a[i]·2^{w(i−lo)}`. -/
partial def pack (a : Array Nat) (w lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi == lo + 1 then a[lo]!
  else
    let mid := (lo + hi) / 2
    pack a w lo mid + (pack a w mid hi <<< ((mid - lo) * w))

/-- The `n` slots of `w` bits of `x`, low first, appended to `acc` (the top slot takes what is
left). -/
partial def unpack (x : Nat) (w n : Nat) (acc : Array Nat) : Array Nat :=
  if n == 0 then acc
  else if n == 1 then acc.push x
  else
    let h := n / 2
    let hi := x >>> (h * w)
    let lo := x - (hi <<< (h * w))
    unpack hi w (n - h) (unpack lo w h acc)

/-- Slot width for sums of `terms` products of polynomials with coefficients below `m`. -/
def slotW (N m terms : Nat) : Nat := 2 * (Nat.log2 m + 1) + (Nat.log2 N + 1) + (Nat.log2 terms + 1) + 1

/-- Reduce a packed product modulo `X^N + 1` and `m`. -/
def foldNeg (N m w : Nat) (P : Nat) : Limb :=
  let u := unpack P w (2 * N) (Array.mkEmpty (2 * N))
  (Array.range N).map fun i => (u[i]! % m + m - u[i + N]! % m) % m

/-- Negacyclic product of two limbs modulo `m`. -/
def mulNeg (m : Nat) (a b : Limb) : Limb :=
  let N := a.size
  let w := slotW N m 1
  foldNeg N m w (pack a w 0 N * pack b w 0 N)

/-- Schoolbook negacyclic product (reference for `mulNeg`). -/
def mulNegSchool (m : Nat) (a b : Limb) : Limb := Id.run do
  let N := a.size
  let mut out : Array Int := Array.replicate N 0
  for i in [0:N] do
    for j in [0:N] do
      let v : Int := ((a[i]! * b[j]! : Nat) : Int)
      if i + j < N then out := out.set! (i + j) (out[i + j]! + v)
      else out := out.set! (i + j - N) (out[i + j - N]! - v)
  return out.map fun v => (v % (m : Int)).toNat

/-- The convolution `out_k = Σ_{i+j=k} a_i·b_j` of two lists of limbs modulo `m` (`X^N + 1`). -/
def tensorLimb (m : Nat) (a b : Array Limb) : Array Limb :=
  if a.size == 0 || b.size == 0 then #[] else
  let N := a[0]!.size
  let w := slotW N m (min a.size b.size)
  let pa := a.map fun x => pack x w 0 N
  let pb := b.map fun x => pack x w 0 N
  (Array.range (a.size + b.size - 1)).map fun k =>
    let P := (Array.range a.size).foldl (fun acc i =>
      if i ≤ k && k - i < b.size then acc + pa[i]! * pb[k - i]! else acc) 0
    foldNeg N m w P

/-- `x[limb][part] ↦ x[part][limb]`. -/
def transposeN (perLimb : Array (Array Limb)) : Array RP :=
  let nparts := (perLimb.map (·.size)).foldl max 0
  (Array.range nparts).map fun p => perLimb.map fun l => l[p]!

/-- Tensor product of two ciphertexts held as RNS polynomials in the basis `ms`
(`a[part][limb]`): any numbers of parts. -/
def tensorF (K : Nat) (ms : Array Nat) (a b : Array RP) : Array RP :=
  transposeN <| parMap K ms.size fun i => tensorLimb ms[i]! (a.map (·[i]!)) (b.map (·[i]!))

/-! ## `SwitchCRTBasis` -/

/-- The digits `yᵢ = [xᵢ·(Q/qᵢ)⁻¹]_{qᵢ}` of every coefficient. -/
def digitsF (qs : Array Nat) (x : RP) : RP :=
  let Q := prodL qs
  (Array.range qs.size).map fun i =>
    let q := qs[i]!
    let c := inv (Q / q) q
    x[i]!.map fun v => v * c % q

/-- The overflow count of one coefficient: `⌊nu⌋` (`Fl.nuSw`), or the exact `⌊1/2 + Σ yᵢ/qᵢ⌋`. -/
@[inline] def swOne (cv : Conv) (qs : Array Nat) (qInvD : Array D) (hat : Array Nat) (Q : Nat)
    (y : RP) (c : Nat) : Int :=
  if cv.exactSw then
    let s := (Array.range qs.size).foldl (fun acc i => acc + (y[i]!)[c]! * hat[i]!) 0
    (((if cv.swNoHalf then 2 * s else Q + 2 * s) / (2 * Q) : Nat) : Int)
  else
    let nu := (Array.range qs.size).foldl
      (fun (acc : D) i => D.mulAdd cv.fma acc (D.ofNat (y[i]!)[c]!) qInvD[i]!)
      (if cv.swNoHalf then ⟨0, 0⟩ else D.half)
    D.floor nu

/-- The overflow counts of every coefficient of `x` (limbs over `qs`). -/
def swAll (cv : Conv) (qs : Array Nat) (y : RP) : Array Int :=
  let Q := prodL qs
  let hat := qs.map (Q / ·)
  let qInvD := qs.map fun q => D.div (D.ofNat 1) (D.ofNat q)
  let N := if h : 0 < y.size then y[0].size else 0
  (Array.range N).map fun c => swOne cv qs qInvD hat Q y c

/-- `SwitchCRTBasis` from the basis `qs` to the basis `ps` (mirror of `Fl.switchBasis`). -/
def switchF (cv : Conv) (K : Nat) (qs ps : Array Nat) (x : RP) : RP :=
  let Q := prodL qs
  let hat := qs.map (Q / ·)
  let y := digitsF qs x
  let v := swAll cv qs y
  let N := v.size
  parMap K ps.size fun j =>
    let p := ps[j]!
    let h := hat.map (· % p)
    let Qp : Int := ((Q % p : Nat) : Int)
    (Array.range N).map fun c =>
      let s := (Array.range qs.size).foldl (fun acc i => acc + (y[i]!)[c]! * h[i]!) 0
      ((((s % p : Nat) : Int) - v[c]! * Qp) % (p : Int)).toNat

/-! ## `ScaleAndRound` -/

/-- The truncated fractional sums of every coefficient (`Fl.nuSr` floored, or exact), for the
input moduli `ms`, table numerators `ns` and residues `x`. -/
def srAll (cv : Conv) (N : Nat) (ms ns : Array Nat) (x : RP) : Array Nat :=
  let M := prodL ms
  let hat := ms.map (M / ·)
  let fr := (Array.range ms.size).map fun i => D.div (D.ofNat ns[i]!) (D.ofNat ms[i]!)
  (Array.range N).map fun c =>
    if cv.exactSr then
      let s := (Array.range ms.size).foldl (fun acc i => acc + (x[i]!)[c]! * ns[i]! * hat[i]!) 0
      (if cv.srNoHalf then 2 * s else M + 2 * s) / (2 * M)
    else
      let nu := (Array.range ms.size).foldl
        (fun (acc : D) i => D.mulAdd cv.fma acc fr[i]! (D.ofNat (x[i]!)[c]!))
        (if cv.srNoHalf then ⟨0, 0⟩ else D.half)
      (D.floor nu).toNat

/-- `θᵢ = t·O·[(I·O/mᵢ)⁻¹]_{mᵢ}` for the input moduli `ins` (`HPS.theta t ins outs`). -/
def thetaF (t : Nat) (ins outs : Array Nat) : Array Nat :=
  let IO := prodL ins * prodL outs
  ins.map fun m => t * prodL outs * inv (IO / m) m

/-- `ScaleAndRound` with input basis `ins` and output basis `outs`: `⌊t·x/I⌉ mod o` (mirror of
`Fl.scaleRoundOut`; `Fl.scaleRound t qs ps x` is `scaleF t qs ps (x.take k) (x.drop k)`). -/
def scaleF (cv : Conv) (K : Nat) (t : Nat) (ins outs : Array Nat) (xin xout : RP) : RP :=
  let IO := prodL ins * prodL outs
  let O := prodL outs
  let θ := thetaF t ins outs
  let ns := (Array.range ins.size).map fun i => θ[i]! % ins[i]!
  let N := if h : 0 < xout.size then xout[0].size else 0
  let sr := srAll cv N ins ns xin
  parMap K outs.size fun j =>
    let o := outs[j]!
    let tab := (Array.range ins.size).map fun i => θ[i]! / ins[i]! % o
    let ω := t * O * inv (IO / o) o / o % o
    let xo := xout[j]!
    (Array.range N).map fun c =>
      let s := (Array.range ins.size).foldl (fun acc i => acc + (xin[i]!)[c]! * tab[i]!) 0
      (s + xo[c]! * ω + sr[c]!) % o

/-! ## P-over-Q -/

/-- The fast scaling by `P/Q` (`POverQ.fastScale`): limbs over `ps`. -/
def fastScaleF (cv : Conv) (K : Nat) (qs ps : Array Nat) (x : RP) : RP :=
  let Q := prodL qs
  let P := prodL ps
  let y : RP := (Array.range qs.size).map fun i =>
    let q := qs[i]!
    let c := (q - P * inv (Q / q) q % q) % q
    x[i]!.map fun v => v * c % q
  let N := if h : 0 < x.size then x[0].size else 0
  parMap K ps.size fun j =>
    let p := ps[j]!
    let tab := qs.map fun q => inv q p
    (Array.range N).map fun c =>
      if cv.fastCentred then
        let s : Int := (Array.range qs.size).foldl (fun (acc : Int) i =>
          let yi : Int := (((y[i]!)[c]! : Nat) : Int)
          let yc : Int := if 2 * (y[i]!)[c]! > qs[i]! then yi - ((qs[i]! : Nat) : Int) else yi
          acc + yc * ((tab[i]! : Nat) : Int)) 0
        (s % (p : Int)).toNat
      else
        (Array.range qs.size).foldl (fun acc i => acc + (y[i]!)[c]! * tab[i]!) 0 % p

/-- `ExpandCRTBasisQlHat` (`POverQ.expandQlHat`): limbs over `qs` of `(Q/Q_l)·x`. -/
def expandQlHatF (qs ql : Array Nat) (x : RP) : RP :=
  let D := prodL qs / prodL ql
  let N := if h : 0 < x.size then x[0].size else 0
  (Array.range qs.size).map fun i =>
    if i < ql.size then
      let q := qs[i]!
      let c := D % q
      x[i]!.map fun v => v * c % q
    else Array.replicate N 0

/-! ## BEHZ -/

/-- `[xᵢ·[c·(Q/qᵢ)⁻¹]_{qᵢ}]_{qᵢ}` (`BEHZ.twist`). -/
def twistF (c : Nat) (qs : Array Nat) (x : RP) : RP :=
  let Q := prodL qs
  (Array.range qs.size).map fun i =>
    let q := qs[i]!
    let k := c * inv (Q / q) q % q
    x[i]!.map fun v => v * k % q

/-- `FastBaseConvqToBskMontgomery` (`BEHZ.smmrq`): limbs over `bsk`. -/
def smmrqF (cv : Conv) (K : Nat) (qs bsk : Array Nat) (mt : Nat) (x : RP) : RP :=
  let Q := prodL qs
  let hat := qs.map (Q / ·)
  let y := twistF mt qs x
  let N := if h : 0 < x.size then x[0].size else 0
  let hm := hat.map (· % mt)
  let neg := (mt - 1) * inv Q mt % mt
  let r : Array Int := (Array.range N).map fun c =>
    if cv.behzNoMont then 0 else
    let s := (Array.range qs.size).foldl (fun acc i => acc + (y[i]!)[c]! * hm[i]!) 0
    let r := s % mt * neg % mt
    if mt / 2 ≤ r then (r : Int) - (mt : Int) else (r : Int)
  parMap K bsk.size fun j =>
    let b := bsk[j]!
    let h := hat.map (· % b)
    let Qb : Int := ((Q % b : Nat) : Int)
    let mi : Int := ((inv mt b : Nat) : Int)
    (Array.range N).map fun c =>
      let s := (Array.range qs.size).foldl (fun acc i => acc + (y[i]!)[c]! * h[i]!) 0
      (((((s % b : Nat) : Int) + r[c]! * Qb) * mi) % (b : Int)).toNat

/-- `FastRNSFloorq` (`BEHZ.floorq`): from limbs over `qs` (`xq`) and `bsk` (`xb`), limbs over
`bsk`. -/
def floorqF (K : Nat) (t : Nat) (qs bsk : Array Nat) (xq xb : RP) : RP :=
  let Q := prodL qs
  let y := twistF t qs xq
  let N := if h : 0 < xq.size then xq[0].size else 0
  parMap K bsk.size fun j =>
    let b := bsk[j]!
    let tq := t * inv Q b % b
    let tab := qs.map fun q => inv q b
    let xj := xb[j]!
    (Array.range N).map fun c =>
      let s := (Array.range qs.size).foldl (fun acc i => acc + (y[i]!)[c]! * tab[i]!) 0
      ((((xj[c]! * tq : Nat) : Int) - ((s : Nat) : Int)) % (b : Int)).toNat

/-- `FastBaseConvSK` (`BEHZ.convSK`): from limbs over `bs ++ [msk]`, limbs over `qs`. -/
def convSKF (cv : Conv) (K : Nat) (qs bs : Array Nat) (msk : Nat) (x : RP) : RP :=
  let B := prodL bs
  let hat := bs.map (B / ·)
  let z := digitsF bs (x.extract 0 bs.size)
  let xsk := x[bs.size]!
  let N := xsk.size
  let hs := hat.map (· % msk)
  let Bi : Int := ((inv B msk : Nat) : Int)
  let α : Array Int := (Array.range N).map fun c =>
    if cv.behzNoSK then 0 else
    let s := (Array.range bs.size).foldl (fun acc j => acc + (z[j]!)[c]! * hs[j]!) 0
    let a := ((((s % msk : Nat) : Int) - ((xsk[c]! : Nat) : Int)) * Bi) % (msk : Int)
    if !cv.behzSKCanon && ((msk / 2 : Nat) : Int) < a then a - (msk : Int) else a
  parMap K qs.size fun i =>
    let q := qs[i]!
    let h := hat.map (· % q)
    let Bq : Int := ((B % q : Nat) : Int)
    (Array.range N).map fun c =>
      let s := (Array.range bs.size).foldl (fun acc j => acc + (z[j]!)[c]! * h[j]!) 0
      ((((s % q : Nat) : Int) - α[c]! * Bq) % (q : Int)).toNat

/-! ## The four multiplications -/

/-- Mirror of `Fl.hpsMul` (sums by `cv`): operands and result `[part][limb over qs]`. -/
def hpsF (cv : Conv) (K : Nat) (t : Nat) (qs ps : Array Nat) (c d : Array RP) : Array RP :=
  let k := qs.size
  let ext := fun (a : RP) => a ++ switchF cv K qs ps a
  (tensorF K (qs ++ ps) (c.map ext) (d.map ext)).map fun x =>
    switchF cv K ps qs (scaleF cv K t qs ps (x.extract 0 k) (x.extract k (k + ps.size)))

/-- Mirror of `Fl.poverqMul`. -/
def poverqF (cv : Conv) (K : Nat) (t : Nat) (qs ps : Array Nat) (c d : Array RP) : Array RP :=
  let k := qs.size
  let a := c.map fun (x : RP) => x ++ switchF cv K qs ps x
  let b := d.map fun (x : RP) => let w := fastScaleF cv K qs ps x; switchF cv K ps qs w ++ w
  (tensorF K (qs ++ ps) a b).map fun x =>
    scaleF cv K t ps qs (x.extract k (k + ps.size)) (x.extract 0 k)

/-- Mirror of `Fl.leveledMul`. -/
def leveledF (cv : Conv) (K : Nat) (t : Nat) (qs ps : Array Nat) (drop : Nat) (c d : Array RP) :
    Array RP :=
  let k := qs.size
  let l := k - drop
  let ql := qs.extract 0 l
  let pl := ps.extract 0 l
  let a := c.map fun (x : RP) =>
    let x' := scaleF cv K 1 (qs.extract l k) ql (x.extract l k) (x.extract 0 l)
    x' ++ switchF cv K ql pl x'
  let b := d.map fun (x : RP) => let w := fastScaleF cv K qs pl x; switchF cv K pl ql w ++ w
  (tensorF K (ql ++ pl) a b).map fun x =>
    expandQlHatF qs ql (scaleF cv K t pl ql (x.extract ql.size (ql.size + pl.size)) (x.extract 0 ql.size))

/-- Mirror of `behzMul`. -/
def behzF (cv : Conv) (K : Nat) (t : Nat) (qs bs : Array Nat) (msk mt : Nat) (c d : Array RP) :
    Array RP :=
  let k := qs.size
  let bsk := bs.push msk
  let ext := fun (a : RP) => a ++ smmrqF cv K qs bsk mt a
  (tensorF K (qs ++ bsk) (c.map ext) (d.map ext)).map fun x =>
    convSKF cv K qs bs msk (floorqF K t qs bsk (x.extract 0 k) (x.extract k (k + bsk.size)))

/-! ## Other limb routines -/

/-- The centred lift of a residue modulo `q` reduced modulo `p` (`NativeVector(v, modulus)`,
`SwitchModulus`, `mubintvecnat.cpp:192-237`: `x > ⌊q/2⌋` is read as `x − q`). -/
@[inline] def cenTo (q p : Nat) (x : Nat) : Nat :=
  if x > q / 2 then ((((x : Nat) : Int) - (q : Int)) % (p : Int)).toNat else x % p

/-- `DropLastElementAndScale` (`dcrtpoly-impl.h:737-754`): `(xᵢ − [x_last]_{centred}) · q_last⁻¹`.
`canon`: MUTANT, the last limb read in `[0, q)` (floor instead of round). -/
def dropLastScaleF (canon : Bool) (ms : Array Nat) (x : RP) : RP :=
  let l := ms.size - 1
  let ql := ms[l]!
  let last := x[l]!
  (Array.range l).map fun i =>
    let q := ms[i]!
    let c := inv ql q
    let xi := x[i]!
    (Array.range last.size).map fun j =>
      let r := if canon then last[j]! % q else cenTo ql q last[j]!
      (xi[j]! + q - r) * c % q

/-- `TimesQovert` (`dcrtpoly-impl.h:918-935`) of one limb: `[[x·(−Q)]_t · t⁻¹]_q` with
`negQ = t − (Q mod t)`. -/
def timesQovertF (t negQ q : Nat) (x : Limb) : Limb :=
  let ti := inv t q
  x.map fun v => (v * negQ % t) * ti % q

/-- `σ_g` on one limb: `X^i ↦ X^{i·g mod 2N}`, `X^N = −1`. -/
def autoF (g q : Nat) (a : Limb) : Limb := Id.run do
  let N := a.size
  let mut out := Array.replicate N 0
  for i in [0:N] do
    let k := i * g % (2 * N)
    if k < N then out := out.set! k a[i]!
    else out := out.set! (k - N) ((q - a[i]!) % q)
  return out

def addF (q : Nat) (a b : Limb) : Limb := (Array.range a.size).map fun i => (a[i]! + b[i]!) % q
def subF (q : Nat) (a b : Limb) : Limb := (Array.range a.size).map fun i => (a[i]! + q - b[i]!) % q

end FHE.Pin.BFV
