import FHE.Check.Report
import FHE.Check.Security

set_option autoImplicit false

/-!
# FHE.Check.Recommend — `fhe_check recommend`: concrete parameters that ARE certified   (UNTRUSTED search)

`fhe_check FILE` answers CERTIFIED / NOT CERTIFIED for a program at the parameters in `FILE`.
`fhe_check recommend FILE` keeps the program (inputs, operations, levels, rotations, plaintext
operations; the number of ciphertext limbs `L` is fixed by the levels the program uses) and
searches for a modulus chain that the verified pipeline certifies:

* it generates ACTUAL primes by a deterministic search that mirrors the target library's own
  generator (OpenFHE: `LastPrime`/`PreviousPrime`/`FirstPrime` with step `2N·t`; HEIR: upward
  `FirstPrime`/`NextPrime` with step `2N`, excluding `t` and earlier primes; neutral: the largest
  primes below `2^b` with `q ≡ 1 (mod 2N)`), with library file:line references below;
* it applies a security cap to `log₂(Q·P)` taken from the HomomorphicEncryption.org standard table
  (an INPUT ASSUMPTION, `secTable`), plus OpenFHE's own estimate when the target is OpenFHE;
* every candidate is judged by `FHE.Check.runCheck`, the same pipeline as a plain check
  (`Spec.schemeParamsOK?`, `Spec.Budget.specialOK?`, the certified budget, `refAnalyze`,
  `Spec.Encrypt.certOK?`); and the parameters finally recommended are written as an
  `fhe-check/v1` file, DECODED AGAIN and checked again by `runCheck`. The verdict printed is that
  of the plain check of the emitted file, so the recommendation is itself a CERTIFIED result.

What is searched is a family: `[f, s, s, …, s]` ciphertext-prime sizes (OpenFHE's
`SetFirstModSize`/`SetScalingModSize`), the number of key-switching digits, the ring dimension;
for HEIR/neutral targets each limb size and the special-prime size are then lowered one at a
time. For each ring dimension and digit count the search minimises `log₂(Q·P)` by bisection
over the family; among those candidates the objective chooses (`Objective`): by default the
least TIME PROXY (`costProxy`, a model of the evaluation time fitted on measured times; the
file's digit count is kept unless another is predicted faster by more than the model's error),
or the least `log₂(Q·P)` (`size`, the original objective). For the OpenFHE target only ring
dimensions that packed encoding allows for the file's `t` are proposed (`batchOK`: `t ≡ 1 mod 2N`).
**Optimality is not claimed**: a cheaper certified chain may exist. **Soundness of the returned
parameters is**: they are certified by the verified definitions exactly as for any input file
(the search and the proxy only choose WHICH parameters the plain check is run on).

Nothing in this file decides a verdict. Unverified glue that affects a verdict is labelled
`UNVERIFIED GLUE` here and in the output:
* the input noise at a new ring dimension or a new special prime (`noiseAt`): for OpenFHE files
  it is `Spec.Encrypt.freshNoise t Bp (Spec.Encrypt.worstError N …)` from the file's own sampler
  bounds (verified functions; the formula is the extractor's, so the excess of the file's value
  over it, if any, is kept); for HEIR/Lattigo files it is the Lattigo formula of
  `harness/frontend/heir/extract_bgv.py` evaluated at the new `N` and `p₀` (an assumption, as in
  the extractor);
* the Galois elements of rotations at a new ring dimension (`remapG`: `±5^e mod 2N ↦ ±5^e mod 2N'`).
-/

namespace FHE.Check
namespace Rec
open Lean Spec Spec.Source

/-! ## 1. Security table: `FHE.Check.secTable` (`FHE.Check.Security`; INPUT ASSUMPTION, not proved here) -/

/-- Bit length of `x` (`0` for `0`). -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-! ## 2. Primes (deterministic; the chain is re-checked by `Spec.schemeParamsOK?`) -/

-- `powModF`: `FHE.Check.Security`.

def mrBases : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- Miller–Rabin with the first twelve primes as bases: deterministic below 3.18·10^23
(Sorenson–Webster 2015), far above the 61-bit candidates here. Used only to FIND candidates; the
ciphertext primes are re-checked by the verified `Spec.primeOK?` inside `schemeParamsOK?`. -/
def isPrime (n : Nat) : Bool := Id.run do
  if n < 2 then return false
  for p in mrBases do
    if n % p == 0 then return n == p
  let mut d := n - 1
  let mut s := 0
  while d % 2 == 0 do
    d := d / 2
    s := s + 1
  for a in mrBases do
    let mut x := powModF a d n
    if x == 1 || x == n - 1 then continue
    let mut composite := true
    for _ in [1:s] do
      x := x * x % n
      if x == n - 1 then
        composite := false
        break
    if composite then return false
  return true

/-- Steps allowed in one prime walk (a prime turns up every ~40 steps at 60 bits). -/
def walkFuel : Nat := 100000

/-- First prime in `n, n − M, n − 2M, …` (none below `M`). -/
def walkDown (n M : Nat) : Option Nat := Id.run do
  let mut x := n
  for _ in [0:walkFuel] do
    if x < M || x < 2 then return none
    if isPrime x then return some x
    x := x - M
  return none

/-- First prime in `n, n + M, n + 2M, …`. -/
def walkUp (n M : Nat) : Option Nat := Id.run do
  let mut x := n
  for _ in [0:walkFuel] do
    if isPrime x then return some x
    x := x + M
  return none

/-- OpenFHE `LastPrime<NativeInteger>(b, M)` (`src/core/include/math/nbtheory-impl.h:357-380` in v1.6.1):
the largest prime `≡ 1 (mod M)` below `2^b`, which must have exactly `b` bits. -/
def lastPrime (b M : Nat) : Option Nat := do
  let q := 2 ^ b
  guard (M < q)
  let r := q % M
  let n := q + 1 - r
  let n := if r < 2 then n - M else n
  let p ← walkDown n M
  guard (bitLen p = b)
  pure p

/-- OpenFHE `PreviousPrime(q, M)` (`nbtheory-impl.h:393-402`). -/
def prevPrime (q M : Nat) : Option Nat := if q ≤ M then none else walkDown (q - M) M

/-- OpenFHE `FirstPrime<NativeInteger>(b, M)` (`nbtheory-impl.h:336-354`): the smallest prime
`≡ 1 (mod M)` above `2^b`. -/
def firstPrime (b M : Nat) : Option Nat :=
  let q := 2 ^ b
  let r := q % M
  let n := q + 1 - r
  walkUp (if r > 0 then n + M else n) M

/-- OpenFHE `NextPrime(q, M)`. -/
def nextPrime (q M : Nat) : Option Nat := walkUp (q + M) M

/-! ## 3. The targets and their generators -/

inductive Target | openfhe | heir | neutral
  deriving BEq, Repr

def Target.name : Target → String
  | .openfhe => "openfhe" | .heir => "heir" | .neutral => "neutral"

def Target.title : Target → String
  | .openfhe => "OpenFHE BGVRNS, FIXEDMANUAL scaling (v1.6.1)"
  | .heir => "HEIR (Lattigo backend, bgv.schemeParam)"
  | .neutral => "neutral (no library prime rule; q = 1 mod 2N, largest primes below 2^b)"

/-- OpenFHE's prime step for BGV (v1.6.1 `bgvrns-parametergeneration.cpp:514-528` for Q,
`bgvrns-cryptoparameters.cpp:148-165` `FindAuxPrimeStep` for P): `max(2N, 2-part of t)` times the
odd part of `t`. So every prime is `≡ 1 (mod 2N)` (NTT) and `≡ 1 (mod t)`, which keeps every
FIXEDMANUAL scale at 1 (the program does not depend on the primes). -/
def openfheStep (N t : Nat) : Nat := Id.run do
  let mut o := t
  let mut p2 := 1
  for _ in [0:64] do
    if o == 0 || o % 2 != 0 then break
    o := o / 2
    p2 := p2 * 2
  return (max p2 (2 * N)) * o

/-- Consecutive digits of `α` limbs out of `L` (`uniformLayout`): the digit products. -/
def digitProds (Q : List Nat) (α : Nat) : List Nat :=
  if α = 0 then [Q.prod] else
  (List.range ((Q.length + α - 1) / α)).map fun j => ((Q.drop (j * α)).take α).prod

/-- `α = ⌈L/dnum⌉`, and whether OpenFHE accepts `dnum` digits for `L` towers
(v1.6.1 `rns-cryptoparameters.cpp:89-96`: it throws when `L ≤ α·(dnum − 1)`). -/
def openfheAlpha (L dnum : Nat) : Option Nat :=
  if dnum = 0 then none else
  let α := (L + dnum - 1) / dnum
  if L ≤ α * (dnum - 1) then none else some α

/-- The primes OpenFHE v1.6.1 generates in FIXEDMANUAL mode for `L` towers, first modulus size
`f`, scaling modulus size `s`, `dnum` digits (`src/pke/lib/scheme/bgvrns/bgvrns-parametergeneration.cpp:514-545`;
`src/pke/lib/schemerns/rns-cryptoparameters.cpp:135-190`; special-prime size
`auxBits = DCRT_MODULUS::MAX_SIZE = 60`, `bgvrns-parametergeneration.cpp:439`):
* `q₀ = LastPrime(f, M)`; `q₁ = PreviousPrime(LastPrime(s, M))` if `f ≠ s`, else
  `PreviousPrime(q₀)`; `qᵢ = PreviousPrime(qᵢ₋₁)`;
* `k = ⌈maxbits / 60⌉` special primes, `maxbits` = the largest bit length of a digit product, and
  one more if `60k − maxbits < 4` (a 4-bit margin, new in v1.6.0: `rns-cryptoparameters.cpp:145-155`;
  v1.3.1 had no margin); from `FirstPrime(60, M)` downward by `PreviousPrime`, skipping primes of
  the chain (`:175-190`).
Returns `(Q, P, α)`. -/
def genOpenFHE (N t L f s dnum : Nat) : Except String (List Nat × List Nat × Nat) := do
  let M := openfheStep N t
  let some α := openfheAlpha L dnum
    | throw s!"OpenFHE cannot distribute {L} towers into {dnum} digits (rns-cryptoparameters.cpp:89-96)"
  let some q0 := lastPrime f M | throw s!"no {f}-bit prime = 1 mod {M}"
  let mut Q := #[q0]
  if L > 1 then
    let some q := (if f ≠ s then lastPrime s M else some q0) | throw s!"no {s}-bit prime = 1 mod {M}"
    let some q1 := prevPrime q M | throw "PreviousPrime failed"
    Q := Q.push q1
    for _ in [2:L] do
      let some qi := prevPrime Q.back! M | throw "PreviousPrime failed"
      Q := Q.push qi
  let Ql := Q.toList
  let maxBits := (digitProds Ql α).foldl (fun m d => max m (bitLen d)) 0
  let k := (maxBits + 59) / 60
  let k := if k * 60 - maxBits < 4 then k + 1 else k
  let some p0 := firstPrime 60 M | throw "FirstPrime(60) failed"
  let mut pPrev := p0
  let mut P := #[]
  for _ in [0:k] do
    let mut found := false
    for _ in [0:64] do
      let some p := prevPrime pPrev M | throw "PreviousPrime (special) failed"
      pPrev := p
      if !Ql.contains p then
        P := P.push p
        found := true
        break
    unless found do throw "special prime search exhausted"
  return (Ql, P.toList, α)

/-- OpenFHE's own estimate of `log₂(Q·P)` for FIXEDMANUAL with HYBRID key switching, which it
compares with its security table to choose or check the ring dimension (v1.6.1
`bgvrns-parametergeneration.cpp:439-472`, `rns-cryptoparameters.cpp:433-504` `EstimateLogP`).
For FIXEDMANUAL `addOne` is false (`bgvrns-parametergeneration.cpp:450-458`): `f + (L−1)·s` with no
extra bit, the largest digit's size sum with no extra bit, `⌈maxbits/60⌉` special primes plus
one if the margin `60k − maxbits` is below 4 bits (`:494-501`). With `SetRingDim(N)`, OpenFHE
throws if this exceeds the cap at `N` (`bgvrns-parametergeneration.cpp:52-80`). -/
def openfheEstimate (L f s dnum : Nat) : Nat :=
  let qb := f + (L - 1) * s
  let np := min dnum L
  let α := (L + np - 1) / np
  let qi := f :: List.replicate (L - 1) s
  let maxBits := (List.range np).foldl (fun m j => max m ((qi.drop (j * α)).take α).sum) 0
  let k := (maxBits + 59) / 60
  let k := if k * 60 - maxBits < 4 then k + 1 else k
  qb + k * 60

/-- HEIR's prime choice (HEIR's `lib/Parameters/RLWEParams.cpp:57-83` `findPrime` and
`:115-133`): for a size parameter `b`, `FirstPrime(b, 2N)` (the smallest prime `≡ 1 (mod 2N)`
above `2^b`, so `b + 1` bits), then `NextPrime` while it equals `t` or an earlier prime. -/
def heirPrime (b N : Nat) (avoid : List Nat) : Option Nat := do
  let mut p ← firstPrime b (2 * N)
  for _ in [0:64] do
    if !avoid.contains p then return p
    p ← nextPrime p (2 * N)
  none

def genHeir (N t : Nat) (bits : List Nat) (k pBits : Nat) : Except String (List Nat × List Nat) := do
  let mut ex := [t]
  let mut Q := #[]
  for b in bits do
    let some p := heirPrime b N ex | throw s!"no prime above 2^{b} = 1 mod 2N"
    Q := Q.push p
    ex := p :: ex
  let mut P := #[]
  for _ in [0:k] do
    let some p := heirPrime pBits N ex | throw s!"no prime above 2^{pBits} = 1 mod 2N"
    P := P.push p
    ex := p :: ex
  return (Q.toList, P.toList)

/-- Neutral generator: for each size `b`, the largest prime `≡ 1 (mod 2N)` below `2^b` not used
yet and not dividing `t`. -/
def neutralPrime (b N t : Nat) (avoid : List Nat) : Option Nat := do
  let mut p ← lastPrime b (2 * N)
  for _ in [0:64] do
    if !avoid.contains p && t % p != 0 then return p
    p ← prevPrime p (2 * N)
  none

def genNeutral (N t : Nat) (bits : List Nat) (k pBits : Nat) : Except String (List Nat × List Nat) := do
  let mut ex := []
  let mut Q := #[]
  for b in bits do
    let some p := neutralPrime b N t ex | throw s!"no {b}-bit prime = 1 mod 2N"
    Q := Q.push p
    ex := p :: ex
  let mut P := #[]
  for _ in [0:k] do
    let some p := neutralPrime pBits N t ex | throw s!"no {pBits}-bit prime = 1 mod 2N"
    P := P.push p
    ex := p :: ex
  return (Q.toList, P.toList)

/-! ## 4. Rotations at another ring dimension: `remapG`, `remapProg` (`FHE.Check.Security`; UNVERIFIED GLUE) -/

/-! ## 5. Options, context, candidates -/

/-- How the key-switching digits are chosen: keep the file's, search, or a given count (OpenFHE:
the number of digits `dnum`; HEIR/neutral: the number of special primes, which is the number of
limbs per digit in Lattigo). -/
inductive DigitsOpt | keep | any | fixed (d : Nat)

/-- What the search minimises among certified candidates: `time`, a time proxy (`costProxy`, a
MODEL of the evaluation time fitted on the library's measured times; the default), or `size`,
`log₂(Q·P)` (the original objective). Either way the result is re-checked by the plain pipeline. -/
inductive Objective | time | size
  deriving BEq, Repr

structure Opts where
  target : Option Target := none
  objective : Objective := .time
  /-- `none`: the smallest `N` meeting the security level. -/
  ringDim : Option Nat := none
  security : Nat := 128
  digits : DigitsOpt := .keep
  kappa : Option Nat := none
  /-- Least margin in bits (default 0: CERTIFIED is the requirement). -/
  margin : Nat := 0
  /-- Evaluate these sizes instead of searching (OpenFHE: `[f, s]` or `[f]`; HEIR/neutral: one per
  limb, or `[f, s]`), with this special-prime size (HEIR/neutral). -/
  sizes : Option (List Nat) := none
  specialSize : Option Nat := none

structure Ctx where
  target : Target
  base : Input
  baseJson : Json
  L : Nat
  N0 : Nat
  t : Nat
  sec : Nat
  kappa : Option Nat
  digits : DigitsOpt
  /-- The file's `dnum` (OpenFHE) and number of special primes. -/
  baseDnum : Nat
  baseK : Nat
  /-- The file's ring dimension may be changed (the input noise can be recomputed). -/
  nFree : Bool
  /-- Least margin (bits) required of every output, at its level and after the decryption switch. -/
  margin : Nat := 0
  objective : Objective := .time
  /-- Only ring dimensions with `t ≡ 1 (mod 2N)` (packed encoding; see `batchOK`). -/
  batch : Bool := false

structure Cand where
  N : Nat
  bits : List Nat
  pBits : Nat := 0
  /-- OpenFHE: `dnum`; HEIR/neutral: number of special primes. -/
  d : Nat

structure Eval where
  cand : Cand
  Q : List Nat
  P : List Nat
  digits : DigitSpec
  inp : Input
  /-- OpenFHE's own `log₂(Q·P)` estimate (OpenFHE target). -/
  estimate : Option Nat := none

def Eval.qp (e : Eval) : Nat := e.Q.prod * e.P.prod

/-- The input noise at ring dimension `N` with special primes `P` (UNVERIFIED GLUE; see the
module docstring). -/
def noiseAt (ctx : Ctx) (N : Nat) (P : List Nat) : Except String Nat := do
  let t := ctx.t
  match ctx.target with
  | .heir =>
    -- harness/frontend/heir/extract_bgv.py:186-193 (Lattigo v6.1.0 encrypts mod Q*p0, divides by p0)
    let f := fun (N p0 : Nat) => (t - 1) + t * ((2 * 19 * (2 * N + 1) + (N + 1) * (p0 - 1)) / (2 * p0))
    let p0 := ctx.base.P.store.special.headD ⟨1, 0⟩ |>.q
    unless f ctx.N0 p0 = ctx.base.P.inputNoise do
      throw "the file's inputNoise is not the Lattigo formula of extract_bgv.py (another frontend version?); cannot recompute it"
    return f N (P.headD 1)
  | _ =>
    let some n := freshNoiseAt ctx.base N
      | throw "the file has no freshEncryption section, so its inputNoise cannot be recomputed at another ring dimension"
    return n

/-- The candidate as an `Input` for the verified pipeline. -/
def candInput (ctx : Ctx) (N : Nat) (Q P : List Nat) (digits : DigitSpec) : Except String Input := do
  let some prog := remapProg ctx.base.prog ctx.N0 N
    | throw "a Galois element is not of the form +-5^e mod 2N; cannot move the program to another ring dimension"
  let inputNoise ← noiseAt ctx N P
  let b := ctx.base
  return { b with
    P := { b.P with src := { b.P.src with N, qs := Q }
                    store := { W := N, limbs := Q.map (⟨·, 0⟩), special := P.map (⟨·, 0⟩) }
                    inputNoise }
    prog, ks := { b.ks with digits }
    -- neutral target: no library's prime rule, so not a library extraction any more (the emitted
    -- file says so too, `emitJson`): its scaling bookkeeping is dropped, phase level at most
    sourceTool := if ctx.target == .neutral then "fhe_check recommend (neutral target: no library prime rule)" else b.sourceTool
    scaling := if ctx.target == .neutral then none else b.scaling }

def sizeRange (ctx : Ctx) (N : Nat) : Nat × Nat :=
  match ctx.target with
  | .openfhe => (max 20 (bitLen (openfheStep N ctx.t) + 1), 60)
  | .heir => (20, 59)
  | .neutral => (max 20 (bitLen (2 * N) + 1), 60)

def mkCand (ctx : Ctx) (N f s d : Nat) : Cand :=
  { N, bits := f :: List.replicate (ctx.L - 1) s, pBits := max f s, d }

/-- Generate the primes of a candidate (no check). -/
def genEval (ctx : Ctx) (c : Cand) : Option Eval := do
  let (Q, P, digits, est) ← match ctx.target with
    | .openfhe =>
      let f := c.bits.headD 0
      let s := (c.bits.drop 1).headD f
      match genOpenFHE c.N ctx.t ctx.L f s c.d with
      | .ok (Q, P, α) => some (Q, P, DigitSpec.consecutive α, some (openfheEstimate ctx.L f s c.d))
      | .error _ => none
    | .heir =>
      match genHeir c.N ctx.t c.bits c.d c.pBits with
      | .ok (Q, P) => some (Q, P, DigitSpec.consecutive c.d, none)
      | .error _ => none
    | .neutral =>
      match genNeutral c.N ctx.t c.bits c.d c.pBits with
      | .ok (Q, P) => some (Q, P, (match ctx.digits with
          | .keep => ctx.base.ks.digits
          | _ => DigitSpec.consecutive c.d), none)
      | .error _ => none
  let inp ← (candInput ctx c.N Q P digits).toOption
  pure { cand := c, Q, P, digits, inp, estimate := est }

/-- Generate the primes of a candidate and judge it with the verified pipeline (`runCheck`, the
same function a plain check runs). `none` if anything fails. The security cap is `capOK`. -/
def evalCand (ctx : Ctx) (c : Cand) : Option Eval := do
  let e ← genEval ctx c
  let r := runCheck e.inp { kappa := ctx.kappa, suggest := false }
  guard (r.verdict == .certified)
  -- the margin the user asked for (default 0: CERTIFIED is the requirement)
  let q0 := e.Q.headD 0
  guard (r.outputs.all fun o =>
    log2F o.Q - 1 - log2F o.bound ≥ ctx.margin.toFloat &&
    (o.decBound.all fun db => log2F q0 - 1 - log2F db ≥ ctx.margin.toFloat))
  pure e

/-- The security cap on `Q·P` (the standard's table; INPUT ASSUMPTION), and, for OpenFHE, its own
estimate (so that `SetRingDim(N)` is accepted). -/
def capOK (ctx : Ctx) (e : Eval) : Bool :=
  match capOf ctx.sec e.cand.N with
  | none => false
  | some cap => decide (e.qp < 2 ^ cap) && e.estimate.all (· ≤ cap)

def better (e : Eval) : Option Eval → Bool
  | none => true
  | some b => e.qp < b.qp

/-- Packed encoding (the only encoding the OpenFHE BGV extractor accepts, `extract.py`
`check_packed`) needs a primitive `2N`-th root of unity mod `t`, i.e. `t ≡ 1 (mod 2N)` for a prime
`t` (OpenFHE v1.6.1 throws in `RootOfUnity` otherwise: with `t = 65537`, `N ≤ 2^15`). Applied when
`ctx.batch` (OpenFHE target, and the file's own `N` satisfies it). -/
def batchOK (ctx : Ctx) (N : Nat) : Bool := !ctx.batch || (ctx.t - 1) % (2 * N) == 0

/-! ### Time proxy (a MODEL; it orders certified candidates, it decides nothing) -/

/-- Operation features of the time proxy, summed over the program at each operation's level `ℓ`
(the number of limbs its operand uses, tracked from the declared input levels through
`modSwitch`/`dropLimbs`): `A` = Σ ℓ over multiplications (`mul`, `square`), automorphisms
(rotations) and modulus switches;
`B` = Σ `d(ℓ)·(ℓ + K)` over key switches (`relin`, `keySwitch`), with `d(ℓ) = ⌈ℓ/α⌉` digits of
`α` limbs and `K` special primes (the work of a hybrid key switch: each digit is extended to
`ℓ + K` limbs). The same definition is `harness/eval/frontier/costmodel.py` `features`. -/
def costFeatures (prog : Program) (α K : Nat) : Nat × Nat := Id.run do
  let α := max α 1
  let mut lv : Std.HashMap Var Nat := {}
  for d in prog.inputs do lv := lv.insert d.name d.level
  let mut A := 0
  let mut B := 0
  for ins in prog.body do
    let g := fun (v : Var) => lv.getD v 0
    match ins with
    | .mul dst a b => let l := min (g a) (g b); A := A + l; lv := lv.insert dst l
    | .square dst a => A := A + g a; lv := lv.insert dst (g a)
    | .modSwitch dst a => A := A + g a; lv := lv.insert dst (g a - 1)
    | .relin dst a | .keySwitch dst a =>
      let l := g a
      B := B + ((l + α - 1) / α) * (l + K); lv := lv.insert dst l
    | .dropLimbs dst a k => lv := lv.insert dst (g a - k)
    | .add dst a b | .sub dst a b => lv := lv.insert dst (min (g a) (g b))
    | .addPlain dst a _ | .subPlain dst a _ | .mulPlain dst a _ => lv := lv.insert dst (g a)
    | .automorph dst a _ => A := A + g a; lv := lv.insert dst (g a)
    | .mulConst dst a _ | .copy dst a | .toEval dst a | .toCoeff dst a =>
      lv := lv.insert dst (g a)
  return (A, B)

/-- Fitted coefficients `(a, b)` of `T ≈ N·log₂N·(a·A + b·B)` (milliseconds) for OpenFHE v1.6.1
BGVRNS with HYBRID key switching, single thread, pristine build; fitted by
`harness/eval/frontier/timing_fit.py` (data and fit residuals in
`harness/eval/frontier/RESULTS.md`): 28 FIXEDMANUAL contexts (chain and poly programs, depth
2-12, N = 2^13..2^15, every digit count from 1 to L), largest relative error 7.6%. A MODEL. -/
def costCoeffs : Float × Float := (5.0019e-6, 1.4675e-6)

/-- The largest relative error of the fitted model on its measured points (`timing_fit.py`),
rounded up. -/
def costModelError : Float := 0.08

/-- The time proxy (milliseconds, MODELLED) of `prog` at ring dimension `N` with `K` special
primes and digits of `α` limbs. -/
def costProxy (prog : Program) (N α K : Nat) : Float :=
  let (A, B) := costFeatures prog α K
  N.toFloat * Float.log2 N.toFloat * (costCoeffs.1 * A.toFloat + costCoeffs.2 * B.toFloat)

/-- Limbs per digit of a digit layout (`1` for an explicit layout: a rough proxy). -/
def digitAlpha : DigitSpec → Nat
  | .consecutive α => α
  | .explicit _ => 1

/-- The time proxy of a candidate. -/
def Eval.cost (e : Eval) : Float :=
  costProxy e.inp.prog e.cand.N (digitAlpha e.digits) e.P.length

/-- The digit settings searched. -/
def digitOpts (ctx : Ctx) : List Nat :=
  match ctx.target, ctx.digits with
  | .openfhe, .keep => [ctx.baseDnum]
  | .openfhe, .any => (List.range ctx.L).map (· + 1)
  | _, .keep => [ctx.baseK]
  | _, .any => (List.range ctx.L).map (· + 1)
  | _, .fixed d => [d]

/-- The search at one ring dimension (see the module docstring; not proved optimal). The
bisections run on certification alone; the security cap is applied to what they return.
* OpenFHE (two sizes): for each `dnum` and each scaling size `s` (ascending), the least first
  size `f` that certifies.
* HEIR / neutral (a size per limb and one for the special primes): from all sizes at the
  maximum, the least uniform size, then each coordinate lowered in turn (three passes). -/
def searchAtWith (ctx : Ctx) (N : Nat) (ds : List Nat) : Option Eval := Id.run do
  let (lo, hi) := sizeRange ctx N
  let some cap := capOf ctx.sec N | return none
  -- every candidate has at least L + 1 primes of at least lo - 1 bits
  if (ctx.L + 1) * (lo - 1) ≥ cap then return none
  let mut best : Option Eval := none
  if ctx.target == .openfhe then
    let sRange := if ctx.L ≤ 1 then [lo] else (List.range (hi + 1 - lo)).map (· + lo)
    for d in ds do
      for s in sRange do
        let lb := (ctx.L - 1) * (s - 1) + (lo - 1) + 59
        if let some b := best then
          if lb ≥ bitLen b.qp then break
        if lb ≥ cap then break
        match leastTrue (fun f => (evalCand ctx (mkCand ctx N f s d)).isSome) lo hi with
        | some f =>
          if let some e := evalCand ctx (mkCand ctx N f s d) then
            if capOK ctx e && better e best then best := some e
        | none => pure ()
    return best
  for d in ds do
    let uni := fun (v : Nat) => ({ N, bits := List.replicate ctx.L v, pBits := v, d } : Cand)
    let some v := leastTrue (fun v => (evalCand ctx (uni v)).isSome) lo hi | continue
    let mut c := uni v
    let some e0 := evalCand ctx c | continue
    let mut cur := e0
    for _ in [0:3] do
      let mut changed := false
      for i in [0:ctx.L + 1] do
        let get := fun (c : Cand) => if i < ctx.L then c.bits.getD i lo else c.pBits
        let set := fun (c : Cand) (v : Nat) =>
          if i < ctx.L then { c with bits := c.bits.set i v } else { c with pBits := v }
        let top := get c
        if top ≤ lo then continue
        match leastTrue (fun v => (evalCand ctx (set c v)).isSome) lo top with
        | some v =>
          if v < top then
            if let some e := evalCand ctx (set c v) then
              if e.qp < cur.qp then
                c := set c v
                cur := e
                changed := true
        | none => pure ()
      if !changed then break
    if capOK ctx cur && better cur best then best := some cur
  return best

/-- Time objective at one ring dimension: the size search for each digit setting separately, then
the least time proxy. The file's own digit count is kept unless another one is predicted faster
by more than the model's error (`costModelError`): the proxy is a fit, and the library's choice
is the measured default. -/
def searchAtTime (ctx : Ctx) (N : Nat) : Option Eval := Id.run do
  let cands := (digitOpts ctx).filterMap fun d => (searchAtWith ctx N [d]).map (d, ·)
  let some first := cands.head? | return none
  let best := cands.foldl (fun b c => if c.2.cost < b.2.cost then c else b) first
  let own := cands.find? fun c => match ctx.target with
    | .openfhe => c.1 == ctx.baseDnum
    | _ => c.1 == ctx.baseK
  match own with
  | some o => if o.2.cost ≤ best.2.cost * (1 + costModelError) then some o.2 else some best.2
  | none => some best.2

/-- The search at one ring dimension, for the objective of `ctx`. Ring dimensions that packed
encoding cannot use (`batchOK`) have no candidates. -/
def searchAt (ctx : Ctx) (N : Nat) : Option Eval :=
  if !batchOK ctx N then none
  else if ctx.objective == .size then searchAtWith ctx N (digitOpts ctx)
  else searchAtTime ctx N

/-- Ring dimensions in the table, ascending. -/
def ringDims : List Nat := secTable.map (·.1)

/-! ## 6. The recommendation -/

structure Outcome where
  /-- The parameters recommended (at the requested `N`, or the smallest feasible one). -/
  found : Option Eval
  /-- With a fixed `N` that has no certified parameters within the cap: the smallest feasible
  larger `N`, if any. -/
  fallback : Option Eval := none
  /-- Ring dimensions tried. -/
  tried : List Nat

def search (ctx : Ctx) (ringDim : Option Nat) : Outcome := Id.run do
  match ringDim with
  | some N =>
    if let some e := searchAt ctx N then return { found := some e, tried := [N] }
    if !ctx.nFree then return { found := none, tried := [N] }
    let mut tried := [N]
    for N' in ringDims.filter (fun n => n > N && batchOK ctx n) do
      tried := tried ++ [N']
      if let some e := searchAt ctx N' then return { found := none, fallback := some e, tried }
    return { found := none, tried }
  | none =>
    let Ns := (if ctx.nFree then ringDims else [ctx.N0]).filter (batchOK ctx)
    let mut tried := []
    for N in Ns do
      tried := tried ++ [N]
      if let some e := searchAt ctx N then
        -- time objective with the digits searched: the next ring dimension may be faster (fewer
        -- digits there can outweigh 2N); compared by the proxy
        if ctx.objective == .time && (match ctx.digits with | .keep => false | _ => true) then
          if let some N' := (Ns.filter (· > N)).head? then
            tried := tried ++ [N']
            if let some e' := searchAt ctx N' then
              if e'.cost < e.cost then return { found := some e', tried }
        return { found := some e, tried }
    return { found := none, tried }

/-! ## 7. The emitted file -/

def strJ (n : Nat) : Json := Json.str (toString n)

/-- The recommended parameters as an `fhe-check/v1` file: the input file with `params`, the
key-switching digits, rotated Galois elements and input noise replaced. -/
def emitJson (ctx : Ctx) (e : Eval) (opts : Opts) : Json := Id.run do
  let j := ctx.baseJson
  let N := e.cand.N
  let p := j.getObjValD "params"
  let p := p.setObjVal! "N" (toJson N)
  let p := p.setObjVal! "limbs" (Json.arr (e.Q.map fun q => Json.mkObj [("q", strJ q)]).toArray)
  let p := p.setObjVal! "special" (Json.arr (e.P.map fun q => Json.mkObj [("q", strJ q)]).toArray)
  let p := p.setObjVal! "inputNoise" (strJ e.inp.P.inputNoise)
  let mut j := j.setObjVal! "params" p
  let ks := j.getObjValD "keySwitching"
  let dj := match e.digits with
    | .consecutive α =>
      let base := [("kind", Json.str "consecutive"), ("towersPerDigit", toJson α)]
      Json.mkObj (if ctx.target == .openfhe then base ++ [("dnum", toJson e.cand.d)] else base)
    | .explicit _ => ks.getObjValD "digits"
  j := j.setObjVal! "keySwitching" (ks.setObjVal! "digits" dj)
  -- rotations at the new ring dimension
  let prog := j.getObjValD "program"
  let body := match prog.getObjValD "body" with
    | .arr a => Json.arr (a.map fun ins =>
        match ins.getObjValAs? Nat "g", ins.getObjValAs? String "op" with
        | .ok g, .ok "automorph" => ins.setObjVal! "g" (toJson ((remapG g ctx.N0 N).getD g))
        | _, _ => ins)
    | b => b
  let inputs := match prog.getObjValD "inputs" with
    | .arr a => Json.arr (a.map fun d =>
        match d.getObjValAs? Nat "key" with
        | .ok k => d.setObjVal! "key" (toJson ((remapG k ctx.N0 N).getD k))
        | .error _ => d)
    | b => b
  j := j.setObjVal! "program" ((prog.setObjVal! "body" body).setObjVal! "inputs" inputs)
  -- what the library run recorded no longer describes these parameters
  j := match j with
    | .obj kvs => Json.obj (kvs.erase "crossCheck")
    | x => x
  let nd := j.getObjValD "noiseDerivation"
  if !nd.isNull then
    j := j.setObjVal! "noiseDerivation" (nd.setObjVal! "recommend"
      (Json.str (if N = ctx.N0 && ctx.target != .heir then "inputNoise is the file's own (same ring dimension)"
        else if ctx.target == .heir then s!"inputNoise recomputed by fhe_check recommend with the Lattigo formula of extract_bgv.py at N = {N}, p0 = {e.P.headD 0} (UNVERIFIED GLUE)"
        else s!"inputNoise recomputed by fhe_check recommend at N = {N}: Spec.Encrypt.freshNoise t Bp (worstError N ...) from the freshEncryption bounds, plus the file's excess over that formula at its own N")))
  j := j.setObjVal! "recommendation" (Json.mkObj [
    ("by", Json.str "fhe_check recommend (an untrusted search; the verdict is fhe_check's plain check of this file)"),
    ("target", Json.str ctx.target.name), ("security", toJson ctx.sec),
    ("securityTable", Json.str "HomomorphicEncryption.org standard (2018), ternary secret, classical (INPUT ASSUMPTION)"),
    ("ringDimensionPolicy", Json.str (match opts.ringDim with | some n => s!"fixed {n}" | none => "smallest N meeting the security level")),
    ("sizes", toJson e.cand.bits), ("specialSize", toJson e.cand.pBits), ("digits", toJson e.cand.d),
    ("kappa", toJson opts.kappa),
    ("checkWith", Json.str (match opts.kappa with | some k => s!"fhe_check --kappa {k} THIS_FILE" | none => "fhe_check THIS_FILE")),
    ("fromFile", Json.str ((ctx.baseJson.getObjValD "source").getObjValD "artifact" |>.getStr? |>.toOption.getD ""))])
  -- The neutral target's primes follow no library's rule: the emitted file no longer describes
  -- what a library would run (its scaling bookkeeping is the old parameters'), so it is not
  -- presented as a library extraction; fhe_check certifies it at phase level at most.
  if ctx.target == .neutral then
    j := match j with
      | .obj kvs => Json.obj (kvs.erase "scaling")
      | x => x
    j := j.setObjVal! "source" ((j.getObjValD "source").setObjVal! "tool"
      (Json.str "fhe_check recommend (neutral target: no library prime rule)"))
  return j

/-! ## 8. Library configuration -/

def openfheSnippet (ctx : Ctx) (e : Eval) : List String :=
  let f := e.cand.bits.headD 0
  let s := (e.cand.bits.drop 1).headD f
  let secName := if ctx.sec = 192 then "HEStd_192_classic" else if ctx.sec = 256 then "HEStd_256_classic" else "HEStd_128_classic"
  ["CCParams<CryptoContextBGVRNS> parameters;",
   s!"parameters.SetPlaintextModulus({ctx.t});",
   s!"parameters.SetMultiplicativeDepth({ctx.L - 1});   // a chain of {ctx.L} primes (gen-cryptocontext-bgvrns-internal.h:102)",
   "parameters.SetScalingTechnique(FIXEDMANUAL);",
   s!"parameters.SetFirstModSize({f});",
   s!"parameters.SetScalingModSize({s});",
   s!"parameters.SetNumLargeDigits({e.cand.d});",
   "parameters.SetKeySwitchTechnique(HYBRID);",
   s!"parameters.SetSecurityLevel({secName});   // OpenFHE re-checks N against its own table",
   s!"parameters.SetRingDim({e.cand.N});",
   "CryptoContext<DCRTPoly> cc = GenCryptoContext(parameters);"]

def heirSnippet (ctx : Ctx) (e : Eval) : List String :=
  let enc := ((ctx.baseJson.getObjValD "source").getObjValAs? String "encryptionTechnique").toOption.getD "extended"
  let lst := fun (l : List Nat) => String.intercalate ", " (l.map toString)
  [s!"module attributes {"{"}bgv.schemeParam = #bgv.scheme_param<logN = {Nat.log2 e.cand.N}, Q = [{lst e.Q}], P = [{lst e.P}], plaintextModulus = {ctx.t}, encryptionTechnique = {enc}>{"}"} {"{"}",
   "  ... the program's func.func, unchanged ...",
   "}",
   "heir-opt --annotate-module=\"backend=lattigo scheme=bgv\" --mlir-to-bgv=\"noise-model=bgv-noise-by-bound-coeff-worst-case\" prog.mlir"]

def lattigoSnippet (ctx : Ctx) (e : Eval) : List String :=
  let lst := fun (l : List Nat) => String.intercalate ", " (l.map toString)
  ["bgv.NewParametersFromLiteral(bgv.ParametersLiteral{",
   s!"  LogN: {Nat.log2 e.cand.N}, Q: []uint64{"{"}{lst e.Q}{"}"}, P: []uint64{"{"}{lst e.P}{"}"}, PlaintextModulus: {ctx.t},",
   "})"]

/-! ## 9. Entry point -/

/-- What the caller prints. -/
structure Report where
  verdict : Verdict
  headline : String
  lines : List String := []
  json : Json := Json.null
  emitted : Option Json := none

def fmtBits (x : Nat) : String := fmt2 (log2F x)

def ctBytes (N L : Nat) : Nat := 2 * N * L * 8

def kib (b : Nat) : String := s!"{b / 1024} KiB"

/-- Margins of the outputs of a certified result (bits): `(name, level margin, decryption margin)`. -/
def margins (r : Result) : List (String × Float × Option Float) :=
  let q0 := (r.input.map (·.P.src.qs.headD 0)).getD 0
  r.outputs.map fun o =>
    (o.name, log2F o.Q - 1 - log2F o.bound, o.decBound.map fun db => log2F q0 - 1 - log2F db)

def scalingOf (j : Json) : String :=
  ((j.getObjValD "source").getObjValAs? String "scaling").toOption.getD ""

/-- Why an OpenFHE automatic-mode file gets no recommendation, and what a user can do. -/
def autoModeText (sc : String) : List String :=
  [s!"OpenFHE {sc}: the extracted program itself depends on the primes (the library inserts its own",
   "  modulus switches and multiplies by constants c = sf2*sf1^-1*q mod t chosen from the primes,",
   "  bgvrns-leveledshe.cpp:101-266; FLEXIBLEAUTOEXT adds an extra limb), so certifying this program",
   "  body on other primes would certify a program OpenFHE does not run. And OpenFHE refuses",
   "  SetScalingModSize/SetFirstModSize outside FIXEDMANUAL (gen-cryptocontext-params-validation.cpp:124-133).",
   "What a user CAN do:",
   "  (a) switch to FIXEDMANUAL (SetScalingTechnique(FIXEDMANUAL), with ModReduce after each",
   "      multiplication), trace and extract that program, and run `fhe_check recommend` on it;",
   "  (b) stay in this mode and raise SetEvalAddCount, one of the inputs that size the primes",
   "      OpenFHE picks (bgvrns-parametergeneration.cpp:101-280), then re-extract and re-check: see",
   "      harness/frontend/recommend/roundtrip.sh --auto for what this achieves on the default programs."]

def recommend (path : String) (j : Json) (inp : Input) (opts : Opts) : Report := Id.run do
  let tool := ((j.getObjValD "source").getObjValAs? String "tool").toOption.getD "unknown"
  let target := opts.target.getD (if tool == "openfhe" then .openfhe else if tool == "heir" then .heir else .neutral)
  let sc := scalingOf j
  if tool == "openfhe" && sc != "" && sc != "FIXEDMANUAL" then
    return { verdict := .unsupported,
             headline := s!"no recommendation for an OpenFHE {sc} program (only FIXEDMANUAL programs keep their meaning when the primes change)",
             lines := autoModeText sc }
  if target == .openfhe && inp.ks.variant != .openfhe then
    return { verdict := .unsupported, headline := "--target openfhe needs a file from the OpenFHE extractor (key-switching variant openfhe)" }
  if target == .heir && tool != "heir" then
    return { verdict := .unsupported, headline := "--target heir needs a file from the HEIR extractor (its input noise depends on HEIR/Lattigo's encryption)" }
  let L := inp.P.src.qs.length
  let N0 := inp.P.src.N
  let baseDnum := (((j.getObjValD "keySwitching").getObjValD "digits").getObjValAs? Nat "dnum").toOption.getD
    (match inp.ks.digits with | .consecutive α => if α = 0 then 1 else (L + α - 1) / α | .explicit _ => 1)
  let nFree := target == .heir || inp.fresh.isSome
  let ctx : Ctx := { target, base := inp, baseJson := j, L, N0, t := inp.P.src.t, sec := opts.security,
                     kappa := opts.kappa, digits := opts.digits, baseDnum, margin := opts.margin,
                     baseK := inp.P.store.special.length, nFree, objective := opts.objective,
                     batch := target == .openfhe && inp.P.src.t ≥ 2 && (inp.P.src.t - 1) % (2 * N0) == 0 }
  -- the largest ring dimension packed encoding allows for this t (OpenFHE target)
  let batchMax := (ringDims.filter (batchOK ctx)).foldl max 0
  let batchTxt := s!"packed encoding needs t = 1 mod 2N (OpenFHE v1.6.1 throws in RootOfUnity otherwise), so for t = {inp.P.src.t} N <= {batchMax}"
  if let some N := opts.ringDim then
    if !nFree && N != N0 then
      return { verdict := .invalid, headline := s!"--ring-dim {N}: this file has no freshEncryption section, so its input noise cannot be recomputed at another ring dimension; only N = {N0} is possible" }
    if !batchOK ctx N then
      return { verdict := .notCertified, headline := s!"--ring-dim {N}: not usable with this plaintext modulus: {batchTxt}" }
  if let .fixed d := opts.digits then
    if d = 0 || d > L then
      return { verdict := .invalid, headline := s!"--digits {d}: must be between 1 and the number of limbs {L}" }
  if inp.P.src.t < 2 then
    return { verdict := .invalid, headline := s!"t = {inp.P.src.t}: the plaintext modulus must be at least 2" }
  if target == .openfhe && bitLen (openfheStep (ringDims.headD 1024) inp.P.src.t) + 1 > 60 then
    let M := openfheStep (ringDims.headD 1024) inp.P.src.t
    return { verdict := .notCertified,
             headline := s!"t = {inp.P.src.t} cannot be used with OpenFHE FIXEDMANUAL: every prime must be = 1 mod 2N*t (bgvrns-parametergeneration.cpp:514-528), and already at N = 1024 that step is {M} (2^{fmt2 (log2F M)}), so no prime of at most 60 bits (MAX_MODULUS_SIZE) exists; choose a smaller t" }
  -- the library's own parameters, for comparison (the plain check)
  let baseR := runCheck inp { kappa := opts.kappa, suggest := false }
  -- `--sizes`: evaluate the given sizes (the primes the library would generate), no search
  let fixedCand : Option Cand := opts.sizes.map fun sz =>
    let f := sz.headD 0
    let sc := (sz.drop 1).headD f
    let bits := if target != .openfhe && sz.length = L then sz else f :: List.replicate (L - 1) sc
    let d := match opts.digits, target with
      | .fixed d, _ => d
      | _, .openfhe => baseDnum
      | _, _ => inp.P.store.special.length
    { N := opts.ringDim.getD N0, bits, pBits := opts.specialSize.getD (bits.foldl max 0), d }
  let out : Outcome := match fixedCand with
    | some c => { found := genEval ctx c, tried := [c.N] }
    | none => search ctx opts.ringDim
  if let some c := fixedCand then
    if out.found.isNone then
      return { verdict := .notCertified,
               headline := s!"--sizes {c.bits}: the {target.name} prime rule cannot generate these primes at N = {c.N} (or the program cannot be moved to this N)" }
  let polName := match opts.ringDim with
    | some n => s!"fixed N = {n}"
    | none => if nFree then s!"smallest N meeting {opts.security}-bit classical security" else s!"the file's N = {N0} (no freshEncryption section: the input noise is only known at this N)"
  let some e := out.found
    | let msg := match opts.ringDim, out.fallback with
        | some n, some fb =>
          s!"no parameters at N = {n} within the {opts.security}-bit cap (log2(Q*P) < {(capOf opts.security n).getD 0}) that the verified pipeline certifies; smallest feasible N is {fb.cand.N} (log2(Q*P) = {fmtBits fb.qp}; run again with --ring-dim {fb.cand.N} or without --ring-dim)"
        | some n, none =>
          if ringDims.any (fun m => m > n && !batchOK ctx m) then
            s!"no certified parameters within N <= {batchMax} for this plaintext modulus: none at N = {n} within the {opts.security}-bit cap that the verified pipeline certifies, nor at any larger N tried ({out.tried}); {batchTxt}"
          else
          s!"no parameters at N = {n} within the {opts.security}-bit cap that the verified pipeline certifies, and none at any larger N in the table ({out.tried})"
        | none, _ =>
          if ringDims.any (fun m => !batchOK ctx m) then
            s!"no certified parameters within N <= {batchMax} for this plaintext modulus: none within the {opts.security}-bit cap that the verified pipeline certifies at any N tried ({out.tried}; primes of at most {(sizeRange ctx N0).2} bits); {batchTxt}"
          else
          s!"no parameters within the {opts.security}-bit cap that the verified pipeline certifies at any N tried ({out.tried}; primes of at most {(sizeRange ctx N0).2} bits)"
      -- a plaintext modulus too large for any prime the target allows: say so
      let msMin := Budget.msBudget { inp.P with src := { inp.P.src with N := ringDims.headD 1024 } }
      let hasMs := inp.prog.body.any fun | .modSwitch .. => true | _ => false
      let hasMul := inp.prog.body.any fun | .mul .. | .square .. => true | _ => false
      let msg := if hasMs && hasMul && msMin * msMin ≥ 2 ^ (sizeRange ctx N0).2 then
          msg ++ s!". Likely reason, t = {inp.P.src.t}: one modulus switch leaves noise up to msBudget = ceil(t*(1+N)/2) = {pow2 msMin} already at N = 1024, and a product of two such ciphertexts (at least msBudget^2 = {pow2 (msMin * msMin)}) exceeds every prime of at most {(sizeRange ctx N0).2} bits; choose a smaller t"
        else msg
      return { verdict := .notCertified, headline := msg,
               lines := [s!"Searched: target {target.title}; {L} ciphertext limbs (fixed by the program's levels); ring dimension policy: {polName}.",
                         "This is the outcome of a search, not a theorem: a chain outside the family searched may exist."],
               json := Json.mkObj [("tool", "fhe_check"), ("format", "fhe-check-recommend/v1"), ("input", Json.str path),
                 ("verdict", Json.str Verdict.notCertified.label), ("summary", Json.str msg),
                 ("triedRingDims", toJson out.tried),
                 ("smallestFeasibleN", match out.fallback with | some fb => toJson fb.cand.N | none => Json.null)] }
  -- the emitted file, decoded again and checked by the plain pipeline: this is the verdict
  let ej := emitJson ctx e opts
  let final : Result := match decode ej with
    | .ok (.ok inp') => runCheck inp' { kappa := opts.kappa, suggest := false }
    | .ok (.unsupported w _ why) => { verdict := .unsupported, headline := s!"re-decoding the emitted file: {w}: {why}" }
    | .error err => { verdict := .invalid, headline := s!"re-decoding the emitted file: {err}" }
  if fixedCand.isSome && (final.verdict != .certified || !capOK ctx e) then
    let lst := fun (l : List Nat) => String.intercalate ", " (l.map fun q => s!"{q} ({bitLen q} bits)")
    let capTxt := s!"log2(Q*P) = {fmtBits e.qp}, {opts.security}-bit cap at N = {e.cand.N}: {(capOf opts.security e.cand.N).getD 0}{match e.estimate with | some x => s!", OpenFHE's estimate {x}" | none => ""}: {if capOK ctx e then "within" else "EXCEEDED"}"
    return { verdict := .notCertified,
             headline := s!"the given sizes are NOT a certified, in-cap choice: plain check {final.label} ({final.headline}); {capTxt}",
             lines := [s!"Predicted primes ({target.title}) at N = {e.cand.N}:", s!"  Q = [{lst e.Q}]", s!"  P = [{lst e.P}]"],
             json := Json.mkObj [("tool", "fhe_check"), ("format", "fhe-check-recommend/v1"), ("input", Json.str path),
               ("verdict", Json.str Verdict.notCertified.label), ("summary", Json.str final.headline),
               ("N", toJson e.cand.N), ("limbs", toJson (e.Q.map toString)), ("special", toJson (e.P.map toString)),
               ("plainCheck", Json.str final.verdict.label), ("capOK", toJson (capOK ctx e))],
             emitted := some ej }
  if final.verdict != .certified then
    return { verdict := .notCertified,
             headline := s!"INTERNAL: the search accepted parameters that the plain check of the emitted file does not certify ({final.label}: {final.headline}); no recommendation",
             emitted := some ej }
  let some fi := final.input | return { verdict := .invalid, headline := "INTERNAL: no input" }
  let P' := fi.P
  let Q := P'.src.qs
  let Pp := (P'.store.special.map (·.q))
  let qp := Q.prod * Pp.prod
  let cap := (capOf opts.security e.cand.N).getD 0
  let baseQP := inp.P.src.qs.prod * (inp.P.store.special.map (·.q)).prod
  let ms := margins final
  let minMargin := ms.foldl (fun m (_, a, b) => min m (match b with | some d => min a d | none => a)) (1.0 / 0.0)
  let f := e.cand.bits.headD 0
  let s := (e.cand.bits.drop 1).headD f
  let mut L' : Array String := #[]
  L' := L'.push (if fixedCand.isSome then s!"Target: {target.title}. Sizes given by --sizes (no search); ring dimension N = {e.cand.N}." else
    s!"Target: {target.title}. Search: {L} ciphertext limbs (fixed by the program's levels), sizes [f, s, ..., s]{if target != .openfhe then " then each limb and the special-prime size lowered one at a time" else ""}, digits {match opts.digits with | .keep => "kept from the file" | .any => "searched" | .fixed d => s!"fixed at {d}"}; ring dimension policy: {polName}.")
  let timeMode := opts.objective == .time && fixedCand.isNone
  let baseCost := costProxy inp.prog N0 (digitAlpha inp.ks.digits) inp.P.store.special.length
  if timeMode then
    L' := L' ++ #[s!"Objective: least predicted evaluation time (a MODEL, T ~ N log2 N (a*A + b*B) over the program's multiplications and",
                  s!"key switches, fitted on measured times with error up to {fmt2 (costModelError * 100)}%; the file's digit count is kept unless another is",
                  "predicted faster by more than that). NOT claimed: optimality (per ring dimension and digit count the search minimises",
                  "log2(Q*P) over a family, by bisection). Claimed: the verdict below, which is fhe_check's plain check of the emitted parameters."]
  else
    L' := L' ++ #["NOT claimed: optimality (the search minimises log2(Q*P) over a family, by bisection). Claimed: the verdict below,",
                  "which is fhe_check's plain check of the emitted parameters."]
  L' := L'.push ""
  L' := L'.push s!"Ring dimension N = {e.cand.N}; plaintext modulus t = {ctx.t}"
  L' := L'.push s!"Ciphertext primes ({Q.length}; log2 Q = {fmtBits Q.prod}):"
  for h : i in [:Q.length] do
    L' := L'.push s!"  q{i} = {Q[i]}  ({bitLen Q[i]} bits)"
  L' := L'.push s!"Special primes ({Pp.length}; log2 P = {fmtBits Pp.prod}):"
  for h : i in [:Pp.length] do
    L' := L'.push s!"  p{i} = {Pp[i]}  ({bitLen Pp[i]} bits)"
  L' := L'.push s!"Key switching: {match e.digits with
    | .consecutive α => s!"digits of {α} consecutive limbs" ++ (if target == Target.openfhe then s!" (dnum = {e.cand.d})" else "")
    | .explicit _ => "the file's explicit digit layout"}"
  L' := L'.push s!"Prime rule: {match target with
    | .openfhe => s!"OpenFHE FIXEDMANUAL, step M = {openfheStep e.cand.N ctx.t} (q = 1 mod 2N and q = 1 mod t; bgvrns-parametergeneration.cpp:514-545, rns-cryptoparameters.cpp:135-190; v1.6.1), sizes f = {f}, s = {s}"
    | .heir => s!"HEIR findPrime: smallest prime = 1 mod 2N above 2^b (RLWEParams.cpp:57-83), sizes b = {e.cand.bits}, special b = {e.cand.pBits}"
    | .neutral => s!"largest prime = 1 mod 2N below 2^b, sizes b = {e.cand.bits}, special {e.cand.pBits} bits"}"
  L' := L'.push ""
  L' := L'.push s!"Security (INPUT ASSUMPTION, not proved here): HomomorphicEncryption.org standard (2018), ternary secret,"
  L' := L'.push s!"  {opts.security}-bit classical: log2(Q*P) must stay below {cap} at N = {e.cand.N}{if secRowIsExtension e.cand.N then " (row from OpenFHE's extension of the table, not the 2018 standard)" else ""}; this chain: log2(Q*P) = {fmtBits qp}."
  if let some est := e.estimate then
    L' := L'.push s!"  OpenFHE's own estimate (v1.6.1 bgvrns-parametergeneration.cpp:439-472): {est} bits <= {cap}, so SetRingDim({e.cand.N}) is accepted."
  if target == .heir && opts.security = 128 then
    let hc := ((heirTable128.find? (·.1 = e.cand.N)).map (·.2)).getD 0
    L' := L'.push s!"  HEIR's own 128-bit table (RLWESecurityParams.cpp:11-14, informational): {hc} bits at N = {e.cand.N}: {if qp < 2 ^ hc then "met" else "NOT met (HEIR does not check a user-supplied schemeParam)"}."
  L' := L'.push ""
  L' := L'.push s!"VERDICT ON THESE EXACT PARAMETERS (fhe_check's plain check of the emitted file): {final.label}: {final.headline}"
  L' := L'.push s!"  certificate theorem: {certificateTheorem final.kappa}"
  for (nm, a, b) in ms do
    L' := L'.push s!"  {nm}: margin {fmt2 a} bits at its level{match b with | some d => s!", {fmt2 d} bits after the decryption switch to one limb" | none => ""}"
  L' := L'.push ""
  L' := L'.push s!"Compared with the file's own parameters ({tool}{if sc != "" then s!", {sc}" else ""}): {baseR.label} there."
  L' := L'.push s!"  N {N0} -> {e.cand.N}; log2 Q {fmtBits inp.P.src.qs.prod} -> {fmtBits Q.prod}; log2(Q*P) {fmtBits baseQP} -> {fmtBits qp}"
  L' := L'.push s!"  fresh ciphertext in memory (2 x N x L words of 64 bits): {kib (ctBytes N0 L)} -> {kib (ctBytes e.cand.N L)} (ratio {fmt2 ((ctBytes e.cand.N L).toFloat / (ctBytes N0 L).toFloat)})"
  L' := L'.push s!"  ciphertext information size (2 x N x log2 Q bits): ratio {fmt2 ((e.cand.N.toFloat * log2F Q.prod) / (N0.toFloat * log2F inp.P.src.qs.prod))}"
  if timeMode then
    L' := L'.push s!"  evaluation time, MODELLED (not measured): ratio {fmt2 (e.cost / baseCost)} (digits {e.cand.d} vs the file's {if target == .openfhe then baseDnum else ctx.baseK})"
  L' := L'.push ""
  L' := L'.push "LIBRARY CONFIGURATION"
  match target with
  | .openfhe =>
    L' := L'.push "OpenFHE C++ (v1.6.1). OpenFHE generates its OWN primes of these sizes; the primes above are the ones"
    L' := L'.push "its generator produces as read from its source, so the certificate must be re-established on what it"
    L' := L'.push "actually generates (trace, extract, fhe_check; harness/frontend/recommend/roundtrip.sh does this):"
    for l in openfheSnippet ctx e do L' := L'.push s!"  {l}"
    L' := L'.push s!"  (bgv_demo: run DIR --scal FIXEDMANUAL --depth {ctx.L - 1} --firstbits {f} --qbits {s} --dnum {e.cand.d} --ringdim {e.cand.N})"
  | .heir =>
    L' := L'.push "HEIR: give the program module these exact primes; HEIR then skips its own parameter generation"
    L' := L'.push "(GenerateParamBGV.cpp:146-149) and the Lattigo backend uses them (ConfigureCryptoContext.cpp:136-142):"
    for l in heirSnippet ctx e do L' := L'.push s!"  {l}"
    L' := L'.push "Lattigo (Go) directly, if you write the program by hand (LattigoEmitter.cpp:1992-2005 emits the same literal):"
    for l in lattigoSnippet ctx e do L' := L'.push s!"  {l}"
  | .neutral =>
    L' := L'.push "neutral target: no library configuration; the primes above are the parameters."
  L' := L'.push ""
  L' := L'.push "UNVERIFIED GLUE that affects this verdict (also stated in the emitted file):"
  L' := L'.push s!"  - input noise: {if e.cand.N = N0 && target != .heir then "the file's own value (same N)" else if target == .heir then s!"Lattigo formula of extract_bgv.py at N = {e.cand.N}, p0 = {Pp.headD 0}" else s!"recomputed at N = {e.cand.N} from the file's freshEncryption bounds (Spec.Encrypt.freshNoise/worstError)"}"
  if e.cand.N != N0 && inp.prog.body.any (fun | .automorph .. => true | _ => false) then
    L' := L'.push s!"  - rotations: Galois elements moved from N = {N0} to N = {e.cand.N} as +-5^e (remapG)"
  L' := L'.push "  - the search, prime generation and this text; and every assumption of the plain check (run"
  L' := L'.push s!"    `fhe_check{match opts.kappa with | some k => s!" --kappa {k}" | none => ""}` on the emitted file for the full certificate statement)."
  let mj := Json.arr (ms.map fun (nm, a, b) => Json.mkObj ([("name", Json.str nm), ("marginBits", jsonF a)] ++
    (match b with | some d => [("decMarginBits", jsonF d)] | none => []))).toArray
  let js := Json.mkObj [
    ("tool", "fhe_check"), ("format", "fhe-check-recommend/v1"), ("input", Json.str path),
    ("verdict", Json.str final.verdict.label), ("verdictLabel", Json.str final.label), ("summary", Json.str final.headline),
    ("target", Json.str target.name), ("security", toJson opts.security),
    ("N", toJson e.cand.N), ("t", toJson ctx.t), ("limbs", toJson (Q.map toString)), ("special", toJson (Pp.map toString)),
    ("limbBits", toJson (Q.map bitLen)), ("specialBits", toJson (Pp.map bitLen)),
    ("sizes", toJson e.cand.bits), ("specialSize", toJson e.cand.pBits), ("digits", toJson e.cand.d),
    ("firstModSize", toJson f), ("scalingModSize", toJson s),
    ("log2Q", jsonF (log2F Q.prod)), ("log2QP", jsonF (log2F qp)), ("cap", toJson cap),
    ("openfheEstimate", toJson e.estimate),
    ("certificateTheorem", Json.str (certificateTheorem final.kappa)),
    ("outputs", mj), ("minMarginBits", jsonF minMargin),
    ("base", Json.mkObj [("verdict", Json.str baseR.verdict.label), ("N", toJson N0),
      ("limbBits", toJson (inp.P.src.qs.map bitLen)), ("specialBits", toJson (inp.P.store.special.map (bitLen ·.q))),
      ("log2Q", jsonF (log2F inp.P.src.qs.prod)), ("log2QP", jsonF (log2F baseQP)), ("dnum", toJson baseDnum)]),
    ("ctBytes", toJson (ctBytes e.cand.N L)), ("baseCtBytes", toJson (ctBytes N0 L)),
    ("triedRingDims", toJson out.tried),
    ("optimality", Json.str "not claimed")] |>
    fun js => if timeMode then (js.setObjVal! "objective" (Json.str "time")).setObjVal! "timeModel"
      (Json.mkObj [("predictedRatio", jsonF (e.cost / baseCost)), ("proxyMs", jsonF e.cost), ("baseProxyMs", jsonF baseCost),
                   ("baseDigits", toJson (if target == .openfhe then baseDnum else ctx.baseK)), ("modelError", jsonF costModelError),
                   ("model", Json.str "T ~ N log2 N (a*A + b*B), FHE.Check.Rec.costProxy; MODELLED, not measured")]) else js
  return { verdict := .certified,
           headline := s!"parameters found that fhe_check certifies (minimum margin {fmt2 minMargin} bits)",
           lines := L'.toList, json := js, emitted := some ej }

end Rec
end FHE.Check
