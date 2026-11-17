import FHE.Pin.Algo
import FHE.Pin.BFV.Routines
import FHE.Pin.BFV.NTT
import FHE.Pin.BFV.Stage
import FHE.KeySwitch.Hybrid
import Challenge.BFV.Defs
import Challenge.BFVMul.KSLeveled
import Spec.EncryptBFV
import FHE.Float.RNE
import FHE.Pin.BFV.AlgoLibrary
import FHE.Pin.BFV.ChecksEnc

/-!
# FHE.Pin.BFV.Algo — the BFV algorithms against OpenFHE, limb by limb   (UNTRUSTED glue)

The BFV counterpart of `FHE.Pin.Algo`: for every ciphertext-producing call of a dumped
`CryptoContextBFVRNS` run (`trace.jsonl`, `harness/openfhe-pin/FORMAT.md`, "BFV cases"), the
recorded inputs are fed to a Lean algorithm and the result is compared with the recorded output,
every limb, every coefficient. `impl` says what was run:

* `literal`: the locked definition itself (`Challenge.BFVMul.Fl.hpsMul`, `Fl.poverqMul`,
  `Fl.leveledMul`, `behzMul`; `N ≤ litMaxN`);
* `forced`: the locked definition with its intermediates forced, **proved equal** to it
  (`FHE.Pin.BFV.Stage`: `hpsForced_eq`, …; `N ≤ 16·litMaxN`);
* `staged`: an array mirror (`FHE.Pin.BFV.Fast`), cross-checked against `literal`/`forced` where
  those run and against the locked scalar functions on sampled coefficients (`algo.mul.spot`) at
  every `N`; for HYBRID key switching `staged` is the proved-equal staged execution of
  `FHE.Pin.AlgoStage` (`keySwitchBGVOpenFHE` at plaintext modulus 1);
* `mirror-only`: a transcription of the library routine for which the project has **no
  definition** (BV key switching, the leveled key switch, `TimesQovert`, encryption, decryption,
  products of other than 2 × 2 components);
* `limb`, `crt`: ring-homomorphic operations run by the trusted `Spec.NPoly` operations per limb /
  on CRT lifts, as in `FHE.Pin.Algo`.

The binary64 sums are computed in `A64` (round to nearest even, uncontracted) or `A64fma`
according to `pin.json`'s `build.float.fmaContraction`; the other contraction choice and the
exact arithmetic (`Fl.exactSums`) are run as `algo.variant.mul` lines (never failures) that count
the coefficients on which they differ from OpenFHE.
-/

namespace FHE.Pin.BFV.Algo
open Lean Spec Spec.NPoly FHE.RNS FHE.KeySwitch FHE.Pin FHE.Pin.Algo Challenge.BFVMul

def toN (p : Array (Array (Array Int))) : Array RP := p.map (·.map (·.map Int.toNat))
def toZ (p : Array RP) : Array (Array (Array Int)) :=
  p.map (·.map (·.map fun (v : Nat) => (v : Int)))
def toZ1 (p : RP) : Array (Array Int) := p.map (·.map fun (v : Nat) => (v : Int))

def natArr (j : Json) (k : String) : Array Nat :=
  match natList j k with
  | .ok l => l.toArray
  | .error _ => #[]

def natOf (j : Json) (k : String) : Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => s.toNat!
  | .ok v => (v.getNat?.toOption).getD 0
  | _ => 0

/-- The BFV context of one case. -/
structure BX where
  x : FHE.Pin.Algo.Cx
  mult : String
  ksT : String
  enc : String
  aux : Array Nat
  bsk : Array Nat
  mt : Nat
  gamma : Nat
  extPrime : Nat
  fmaBuild : Bool
  dnum : Nat
  alpha : Nat
  digitSize : Nat
  m : AlgoMut
  L : Nat
  s : Array Int
  nLit : IO.Ref Nat
  /-- Ciphertexts that are not encryptions under `s`: the output of the `RelinearizeCore` inside
  an `EvalAutomorphism` (before `σ_g`), which decrypts under `σ_g⁻¹(s)`. -/
  notUnderS : IO.Ref (Std.HashMap String String)
  /-- Per ciphertext id, per component: is the component held in COEFFICIENT representation by the
  library? (Absent: all in EVALUATION.) The dumps do not record it; it is derived from the trace:
  the components of an un-relinearised BFV product are left in coefficient representation
  (`bfvrns-leveledshe.cpp:206-442`), every other operation here leaves or restores evaluation. -/
  fmt : IO.Ref (Std.HashMap String (Array Bool))
  /-- OpenFHE's root of unity per modulus (`minRoot`). -/
  roots : IO.Ref (Std.HashMap Nat Nat)

namespace BX

def N (b : BX) : Nat := b.x.c.N
def t (b : BX) : Nat := b.x.c.t
def K (b : BX) : Nat := b.x.o.K
def cv (b : BX) : Conv := b.m.cv b.fmaBuild
def plain (b : BX) : Bool := b.m.isNone && b.x.o.mu = .none
/-- The arithmetic of the build. -/
def arith (b : BX) : Spec.Float.Arith := if b.fmaBuild then A64fma else A64
def arithName (b : BX) : String := if b.fmaBuild then "A64fma" else "A64"
def forcedMaxN (b : BX) : Nat := max (16 * b.x.o.litMaxN) b.x.o.forcedMaxN

def ops (l : List Obj) : (String × Json) := ("operands", Json.arr (l.map (Json.str ·.id)).toArray)

end BX

/-! ## Multiplication -/

/-- Which locked definition a multiplication is, with its auxiliary moduli. -/
inductive Plan
  | hps (ps : Array Nat)
  | poverq (ps : Array Nat)
  | leveled (ps : Array Nat) (drop : Nat)
  | behz (bs : Array Nat) (msk mt : Nat)

def Plan.fn : Plan → String
  | .hps _ => "Challenge.BFVMul.Fl.hpsMul"
  | .poverq _ => "Challenge.BFVMul.Fl.poverqMul"
  | .leveled _ _ => "Challenge.BFVMul.Fl.leveledMul"
  | .behz _ _ _ => "Challenge.BFVMul.behzMul"

def Plan.thm : Plan → String
  | .hps _ => "hpsForced_eq"
  | .poverq _ => "poverqForced_eq"
  | .leveled _ _ => "leveledForced_eq"
  | .behz _ _ _ => "behzForced_eq"

def Plan.isFloat : Plan → Bool
  | .behz _ _ _ => false
  | _ => true

def Plan.json : Plan → List (String × Json)
  | .hps ps => [("aux", Json.arr (ps.map natJ))]
  | .poverq ps => [("aux", Json.arr (ps.map natJ))]
  | .leveled ps d => [("aux", Json.arr (ps.map natJ)), ("drop", Json.num d)]
  | .behz bs msk mt => [("aux", Json.arr (bs.map natJ)), ("msk", natJ msk), ("mtilde", natJ mt)]

/-- The definition OpenFHE's `EvalMult`/`EvalSquare` runs at `k` towers
(`bfvrns-leveledshe.cpp:206-442`). -/
def BX.plan (b : BX) (k : Nat) (ld : Option Int) : Except String Plan :=
  let aux := if b.m.auxReversed then b.aux.reverse else b.aux
  if b.mult == "HPS" then
    if k != b.L then .error "HPS below the top level: the library uses its full-chain tables on fewer limbs; not modelled"
    else .ok (.hps aux)
  else if b.mult == "HPSPOVERQ" then .ok (.poverq (aux.extract 0 k))
  else if b.mult == "HPSPOVERQLEVELED" then
    if k < b.L then .ok (.poverq (aux.extract 0 k))
    else match ld with
      | none => .error "HPSPOVERQLEVELED at the top level: levelsDropped is not in the trace"
      | some d =>
        if d ≤ 0 || b.m.mulDropIgnored then .ok (.poverq (aux.extract 0 k))
        else .ok (.leveled aux d.toNat)
  else if b.mult == "BEHZ" then
    if k != b.L then .error "BEHZ below the top level: not modelled"
    else if b.bsk.size < 2 then .error "pin.json: behzBsk"
    else .ok (.behz b.bsk.pop b.bsk.back! b.mt)
  else .error s!"unknown multiplication technique {b.mult}"

/-- The array mirror of the plan. -/
def runFast (cv : Conv) (K t : Nat) (qs : Array Nat) (pl : Plan) (c d : Array RP) : Array RP :=
  match pl with
  | .hps ps => hpsF cv K t qs ps c d
  | .poverq ps => poverqF cv K t qs ps c d
  | .leveled ps drop => leveledF cv K t qs ps drop c d
  | .behz bs msk mt => behzF cv K t qs bs msk mt c d

/-- The locked definition of the plan, literally (`forced = none`) or with its intermediates
forced (`forced = some K`; equal by `hpsForced_eq`, `poverqForced_eq`, `leveledForced_eq`,
`behzForced_eq`). -/
def runDef {N : ℕ} (forced : Option ℕ) (S : Fl.Sums) (t : ℕ) (qs : List ℕ) (pl : Plan)
    (c d : List (IntPoly N)) : List (IntPoly N) :=
  match pl, forced with
  | .hps ps, none => Fl.hpsMul S t qs ps.toList c d
  | .hps ps, some K => hpsForced K S t qs ps.toList c d
  | .poverq ps, none => Fl.poverqMul S t qs ps.toList c d
  | .poverq ps, some K => poverqForced K S t qs ps.toList c d
  | .leveled ps drop, none => Fl.leveledMul S t qs ps.toList drop c d
  | .leveled ps drop, some K => leveledForced K S t qs ps.toList drop c d
  | .behz bs msk mt, none => behzMul t qs bs.toList msk mt c d
  | .behz bs msk mt, some K => behzForced K t qs bs.toList msk mt c d

/-- The limbs of a list of integer polynomials (each forced once). -/
def limbsOfDef {N : ℕ} (K : ℕ) (qs : Array ℕ) (x : List (IntPoly N)) : Array (Array (Array Int)) :=
  x.toArray.map fun p =>
    let pa := toArr K p
    qs.map fun (q : ℕ) => pa.map (· % (q : ℤ))

def countDiff (a b : Array RP) : Nat :=
  (Array.range (min a.size b.size)).foldl (fun acc p =>
    (Array.range (min a[p]!.size b[p]!.size)).foldl (fun acc i =>
      acc + diffCount (a[p]!)[i]! (b[p]!)[i]!) acc) 0

/-- Sample indices `0, step, 2·step, …` (at most `n`). -/
def sampleIdx (N n : Nat) : Array Nat :=
  let step := max 1 (N / n)
  (Array.range (min N n)).map (· * step)

/-- The mirrored primitives against the **locked scalar functions** (`Fl.switch1`, `Fl.scale1`,
`POverQ.approx1`, `BEHZ.smmrq1`, `BEHZ.floor1`, `BEHZ.sk1`, with the sums of `S`) on sampled
coefficients of the limbs `a0` (over `qs`): (values compared, differing). -/
def spotMul (S : Fl.Sums) (cv : Conv) (t : Nat) (qs : Array Nat) (pl : Plan) (a0 : RP) : Nat × Nat := Id.run do
  let N := if h : 0 < a0.size then a0[0].size else 0
  let idx := sampleIdx N 8
  let ql := qs.toList
  let col := fun (x : RP) (c : Nat) => (x.map fun l => ((l[c]! : Nat) : ℤ)).toList
  let mut n := 0
  let mut bad := 0
  match pl with
  | .behz bs msk mt =>
    let bsk := bs.push msk
    let E := smmrqF cv 1 qs bsk mt a0
    let F := floorqF 1 t qs bsk a0 E
    let G := convSKF cv 1 qs bs msk E
    for c in idx do
      for j in [0:bsk.size] do
        n := n + 2
        if BEHZ.smmrq1 ql mt (col a0 c) bsk[j]! != (((E[j]!)[c]! : Nat) : ℤ) then bad := bad + 1
        if BEHZ.floor1 t ql (col a0 c) bsk[j]! (((E[j]!)[c]! : Nat) : ℤ) != (((F[j]!)[c]! : Nat) : ℤ) then
          bad := bad + 1
      for i in [0:qs.size] do
        n := n + 1
        if BEHZ.sk1 bs.toList msk (col (E.extract 0 bs.size) c) (((E[bs.size]!)[c]! : Nat) : ℤ) qs[i]!
            != (((G[i]!)[c]! : Nat) : ℤ) then bad := bad + 1
  | .hps ps | .poverq ps | .leveled ps _ =>
    let E := switchF cv 1 qs ps a0
    let F := scaleF cv 1 t qs ps a0 E
    let W := fastScaleF cv 1 qs ps a0
    for c in idx do
      for j in [0:ps.size] do
        n := n + 3
        if Fl.switch1 S ql (col a0 c) ps[j]! != (((E[j]!)[c]! : Nat) : ℤ) then bad := bad + 1
        if Fl.scale1 S t ql ps.toList (col a0 c) ps[j]! (((E[j]!)[c]! : Nat) : ℤ) != (((F[j]!)[c]! : Nat) : ℤ) then
          bad := bad + 1
        if POverQ.approx1 ql (POverQ.negPDigits ql (prodL ps) (col a0 c)) ps[j]! != (((W[j]!)[c]! : Nat) : ℤ) then
          bad := bad + 1
  return (n, bad)

/-- One `EvalMult(ct, ct)` / `EvalSquare(ct)` (the 3-component product, no relinearisation). -/
def BX.checkMul (b : BX) (a d out : Obj) (ld : Option Int) (via : String) : IO Unit := do
  let x := b.x
  x.explain out.id
  b.fmt.modify (·.insert out.id (Array.replicate out.parts.size true))
  let n ← x.nTensor.get
  x.nTensor.set (n + 1)
  if let some k := x.o.maxTensor then
    if n ≥ k then
      x.emit "algo.mul" out.id "mul" none "staged" [("why", Json.str s!"skipped: --max-tensor {k}")]
      return
  let k := a.towers
  let qs := x.qsArr k
  let ex0 := [BX.ops [a, d], ("via", Json.str via), ("towers", Json.num k),
              ("operandParts", Json.arr #[Json.num a.parts.size, Json.num d.parts.size])] ++
             (match ld with | some v => [("levelsDropped", intJ v)] | none => [])
  if d.towers != k || out.towers != k then
    x.emit "algo.mul" out.id "mul" (some false) "staged" ([("why", Json.str "tower counts differ")] ++ ex0)
    return
  let pl ← match b.plan k ld with
    | .ok p => pure p
    | .error e => x.emit "algo.mul" out.id "mul" none "staged" ([("why", Json.str e)] ++ ex0); return
  let ex := ex0 ++ [("fn", Json.str pl.fn)] ++ pl.json
  let two := a.parts.size == 2 && d.parts.size == 2
  let aN := toN a.parts
  let dN := toN d.parts
  let (c1, c2) := if b.m.rolesSwapped then (dN, aN) else (aN, dN)
  let floatNote := if pl.isFloat then [("float", Json.str (if b.cv.fma then "A64fma" else "A64"))] else []
  let (got, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => runFast b.cv b.K b.t qs pl c1 c2
  let _ ← x.report "algo.mul" "mul" (if two then "staged" else "mirror-only") out (toZ got) ms
    (ex ++ floatNote ++
     [("how", Json.str (if two then "array mirror of the locked definition (FHE.Pin.BFV.Fast)"
        else "the locked definitions cover 2 x 2 components only; the mirror's convolution is not a project definition"))])
  if !b.plain then return
  let outN := toN out.parts
  -- variants (never failures): the other contraction choice, the exact sums
  if pl.isFloat && x.o.variantsMaxN != 0 then
    let vars : List (String × Conv) :=
      [(if b.fmaBuild then "A64 (uncontracted)" else "A64fma (contracted)", { fma := !b.fmaBuild }),
       ("exact (Fl.exactSums)", { exactSw := true, exactSr := true }),
       ("exact overflow sum only", { fma := b.fmaBuild, exactSw := true }),
       ("exact scaling sum only", { fma := b.fmaBuild, exactSr := true })]
    for (name, cvV) in vars do
      let g := runFast cvV b.K b.t qs pl aN dN
      let dOut := countDiff g outN
      x.emit "algo.variant.mul" out.id "mul" none "staged"
        ([("variant", Json.str name), ("matches", boolJ (dOut == 0)),
          ("limbs", Json.num (outN.size * k)), ("coeffs", Json.num (outN.size * k * b.N)),
          ("mismatches", Json.num dOut), ("differsFromCheck", Json.num (countDiff g got)),
          ("why", Json.str "for the record: another arithmetic for the two float sums")] ++ ex)
  -- the locked definition: forced (proved equal) and literal
  if two then
    let S : Fl.Sums := Fl.floatSums b.arith
    if b.N ≤ b.forcedMaxN || b.N ≤ x.o.litMaxN then
      let lift := fun (o : Obj) => o.parts.toList.mapM fun part =>
        (crt "operand" b.N qs part).map fun z => (ofArr (N := b.N) z : IntPoly b.N)
      match lift a, lift d with
      | .ok cI, .ok dI =>
        if b.N ≤ b.forcedMaxN then
          let (g, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => limbsOfDef b.K qs (runDef (some b.K) S b.t qs.toList pl cI dI)
          let _ ← x.report "algo.mul" "mul" "forced" out g ms
            (ex ++ floatNote ++ [("how", Json.str s!"the locked definition with forced intermediates, proved equal ({pl.thm})")])
          x.emit "algo.mul.forced-vs-staged" out.id "mul" (some (g == toZ got)) "forced"
            ([("mismatches", Json.num (countDiff (toN g) got))] ++ ex)
        let nl ← b.nLit.get
        if b.N ≤ x.o.litMaxN && nl < 4 then
          b.nLit.set (nl + 1)
          let (g, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => limbsOfDef b.K qs (runDef none S b.t qs.toList pl cI dI)
          let _ ← x.report "algo.mul" "mul" "literal" out g ms
            (ex ++ floatNote ++ [("how", Json.str "the locked definition, executed as written")])
          x.emit "algo.mul.literal-vs-staged" out.id "mul" (some (g == toZ got)) "literal"
            ([("mismatches", Json.num (countDiff (toN g) got))] ++ ex)
      | .error e, _ | _, .error e =>
        x.emit "algo.mul" out.id "mul" (some false) "forced" ([("why", Json.str e)] ++ ex)
    -- the mirrored primitives against the locked scalar functions, on samples
    let (cnt, bad) := spotMul S b.cv b.t qs pl aN[0]!
    x.emit "algo.mul.spot" out.id "mul" (some (bad == 0)) "staged"
      ([("values", Json.num cnt), ("mismatches", Json.num bad),
        ("why", Json.str "mirrored primitives vs the locked scalar functions (Fl.switch1, Fl.scale1, POverQ.approx1 / BEHZ.smmrq1, floor1, sk1) on sampled coefficients")] ++ ex)

/-! ## Key switching -/

/-- `keySwitchPlain` (centred ModUp, plain centred ModDown) executed literally. -/
def runKSPlain (N K : Nat) (qs special : List Nat) (ℓ : Nat) (sizes : List Nat)
    (d : Array (Array Int)) (keyB keyA : Array (Array Int)) :
    Except String (Array (Array Int) × Array (Array Int)) :=
  if hq : (∀ q ∈ qs, 0 < q) ∧ qs.Pairwise Nat.Coprime then
    if hp : (∀ q ∈ special, 0 < q) ∧ special.Pairwise Nat.Coprime then
      if hℓ : ℓ ≤ qs.length then
        if hs : sizes.sum = ℓ then
          if hN : N = 0 then .error "N = 0" else
            haveI : NeZero N := ⟨hN⟩
            let C : Basis ℓ := Basis.take qs ℓ hℓ hq.1 hq.2
            let Bp : Basis special.length := Basis.ofList special hp.1 hp.2
            let Dg : Digits ℓ := digitsOfSizes sizes ℓ hs
            let kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) N :=
              fun j => ofInt _ (ofArr (N := N) keyB[j.val]!)
            let ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N :=
              fun j => ofInt _ (ofArr (N := N) keyA[j.val]!)
            let a : RNSPoly C N := ofFam C.q d
            let r := keySwitchPlain Dg C Bp a kb ka
            .ok (forceFam K C.q r.1, forceFam K C.q r.2)
        else .error s!"digit sizes {sizes} do not sum to {ℓ}"
      else .error "more towers than the chain"
    else .error "the special primes are not positive and pairwise coprime"
  else .error "the chain is not positive and pairwise coprime"

namespace BX

def zeros (b : BX) (ℓ : Nat) : Array (Array Int) := Array.replicate ℓ (Array.replicate b.N 0)

/-- The HYBRID digit sizes at `ℓ` towers (`keyswitch-hybrid.cpp:340-345`). -/
def sizes (b : BX) (ℓ : Nat) (mu : AMut) : Option (List Nat) :=
  let s := digitSizes b.alpha b.dnum ℓ
  if mu = .digitBoundary then moveBoundary b.dnum s else some s

/-- HYBRID key switch of `d` (ℓ towers): `runKS` of `FHE.Pin.Algo` at the plaintext modulus
`tKS` (BFV: 1, i.e. no `t`-correction). -/
def ksStagedMaxN : Nat := 1024

def addRP (qs : Array Nat) (a c : RP) : RP := (Array.range qs.size).map fun i => addF qs[i]! a[i]! c[i]!

/-- The key digits for the limbs `q_0..q_{ℓ-1}, p_*`, as residues (no CRT lift). -/
def keyLimbs (b : BX) (key : Json) (ℓ ndig : Nat) : IO (Array RP × Array RP) := do
  let L := b.x.c.qs.length
  let k := b.x.c.special.length
  let digits := jArr key "digits"
  if digits.size < ndig then throw (IO.userError s!"the key has {digits.size} digits, {ndig} are needed")
  let pick := fun (nm : String) => do
    let some e := b.x.c.polys[nm]? | throw (IO.userError s!"polys.txt has no entry {nm}")
    if e.moduli.toList != b.x.c.qs ++ b.x.c.special then
      throw (IO.userError s!"{nm}: key limbs are not the chain followed by the special primes")
    pure (((e.limbs.extract 0 ℓ) ++ (e.limbs.extract L (L + k))).map (·.map Int.toNat))
  let mut kb := #[]
  let mut ka := #[]
  for j in [0:ndig] do
    let (some bn, some an) := (jStr? digits[j]! "b", jStr? digits[j]! "a") | throw (IO.userError "key digit names")
    kb := kb.push (← pick bn)
    ka := ka.push (← pick an)
  return (kb, ka)

/-- The array mirror `hybridKSF` for the operations `add` and `rotLast` (v1.3.1 order). -/
def ksFast (b : BX) (sz : List Nat) (key : Json) (ℓ : Nat) (op : KSOp) (d : Array (Array Int)) :
    IO (Option (Array (Array Int) × Array (Array Int))) := do
  let qs := b.x.qsArr ℓ
  let (kb, ka) ← b.keyLimbs key ℓ sz.length
  let (k0, k1) := hybridKSF b.K qs b.x.c.special.toArray sz (d.map (·.map Int.toNat)) kb ka
  let nat := fun (x : Array (Array Int)) => x.map (·.map Int.toNat)
  match op with
  | .add c0 c1 =>
    return some (toZ1 (addRP qs (nat c0) k0), toZ1 (addRP qs (nat c1) k1))
  | .rotLast g c0 =>
    let s0 := addRP qs (nat c0) k0
    return some (toZ1 ((Array.range ℓ).map fun i => autoF g qs[i]! s0[i]!),
                 toZ1 ((Array.range ℓ).map fun i => autoF g qs[i]! k1[i]!))
  | _ => return none

/-- HYBRID key switch of `d` (ℓ towers): `runKS` of `FHE.Pin.Algo` at the plaintext modulus
`tKS` (BFV: 1, i.e. no `t`-correction), the proved staged execution of `keySwitchBGVOpenFHE`
(quadratic products), up to `N = ksStagedMaxN`; above, the array mirror `hybridKSF`
(Kronecker products), which is compared with the staged execution at every `N ≤ ksStagedMaxN`
(`algo.relin.fast-vs-staged`). -/
def ksHybrid (b : BX) (mu : AMut) (literal : Bool) (key : Json) (ℓ : Nat) (op : KSOp)
    (d : Array (Array Int)) (tKS : Nat) (cmpId : String := "") :
    IO (Except String (Array (Array Int) × Array (Array Int))) := do
  let some sz := b.sizes ℓ mu | return .error "no other digit partition at this level"
  let fastOK := mu = .none && !literal && tKS == 1
  if fastOK && b.N > ksStagedMaxN then
    match ← b.ksFast sz key ℓ op d with
    | some r => return .ok r
    | none => pure ()
  let (kb, ka) ← b.x.keyDigits key ℓ sz.length
  let r := runKS b.N b.K tKS b.x.c.qs b.x.c.special ℓ sz mu literal op d kb ka
  if fastOK && cmpId != "" then
    if let .ok (r0, r1) := r then
      if let some (f0, f1) ← b.ksFast sz key ℓ op d then
        b.x.emit "algo.relin.fast-vs-staged" cmpId "keySwitch" (some (f0 == r0 && f1 == r1)) "staged"
          [("why", Json.str "the array mirror hybridKSF against the proved staged keySwitchBGVOpenFHE at t = 1"),
           ("towers", Json.num ℓ)]
  return r

/-- BV key switch of `d` (limbs over `qs`): `(Σ_j digit_j·b_j, Σ_j digit_j·a_j)`
(`keyswitch-bv.cpp`: `CRTDecompose`, then the inner products limb by limb). -/
def ksBV (b : BX) (key : Json) (qs : Array Nat) (d : RP) : IO (RP × RP) := do
  let digs := bvDigits b.m.bvCanon b.m.bvUnbalanced b.digitSize qs d
  let entries := jArr key "digits"
  if entries.size < digs.size then
    throw (IO.userError s!"the key has {entries.size} entries, {digs.size} digits are needed")
  let pick := fun (nm : String) => do
    let some e := b.x.c.polys[nm]? | throw (IO.userError s!"polys.txt has no entry {nm}")
    if e.moduli.extract 0 qs.size != qs then
      throw (IO.userError s!"{nm}: key limbs do not start with the ciphertext's limbs")
    pure ((e.limbs.extract 0 qs.size).map (·.map Int.toNat))
  let mut kb : Array RP := #[]
  let mut ka : Array RP := #[]
  for j in [0:digs.size] do
    let (some bn, some an) := (jStr? entries[j]! "b", jStr? entries[j]! "a")
      | throw (IO.userError "key digit names")
    kb := kb.push (← pick bn)
    ka := ka.push (← pick an)
  let r0 := parMap b.K qs.size fun k => innerNeg qs[k]! (digs.map (·[k]!)) (kb.map (·[k]!))
  let r1 := parMap b.K qs.size fun k => innerNeg qs[k]! (digs.map (·[k]!)) (ka.map (·[k]!))
  return (r0, r1)

def ksBudget (b : BX) (check : String) (out : Obj) (op : String) : IO Bool := b.x.ksBudget check out op

/-- The raw key switch `(KS₀, KS₁)` of `d` over `qs` (HYBRID or BV). -/
def ksRaw (b : BX) (mu : AMut) (key : Json) (qs : Array Nat) (d : RP) : IO (Except String (RP × RP)) := do
  if b.ksT == "BV" then
    return .ok (← b.ksBV key qs d)
  else
    let z := b.zeros qs.size
    match ← b.ksHybrid mu false key qs.size (.add z z) (toZ1 d) (if b.m.ksWithT then b.t else 1) with
    | .ok (r0, r1) => return .ok (r0.map (·.map Int.toNat), r1.map (·.map Int.toNat))
    | .error e => return .error e


/-- Observation (never a failure; nothing is recomputed): the recorded decryptions of the operand
(3 components) and of the result of a relinearisation, and on how many coefficients they
differ. -/
def observeRelin (b : BX) (a out : Obj) (ld : Option Int) (via : String) : IO Unit := do
  let x := b.x
  let raw := fun (id : String) => do
    let o ← x.c.object? id
    let dj ← jObj? o "decrypt"
    let nm ← jStr? dj "raw"
    let e ← x.c.polys[nm]?
    e.limbs[0]?
  match raw a.id, raw out.id with
  | some ra, some ro =>
    let changed := diffCount ra ro
    x.emit "algo.observe.relin" out.id "relin" none "openfhe"
      ([BX.ops [a], ("via", Json.str via), ("towers", Json.num a.towers), ("coeffs", Json.num b.N),
        ("plaintextCoeffsChanged", Json.num changed), ("plaintextPreserved", boolJ (changed == 0)),
        ("why", Json.str (if changed == 0 then "the recorded decryptions of the operand and of the relinearised result agree"
          else "the recorded decryptions of the operand and of the relinearised result differ"))] ++
       (match ld with | some v => [("levelsDropped", intJ v)] | none => []))
    if changed != 0 then
      b.notUnderS.modify (·.insert out.id "the recorded decryptions before and after the relinearisation that produced it differ (algo.observe.relin)")
  | _, _ => pure ()

/-- The BV key entries for the limbs `qs` (all of them). -/
def bvKeys (b : BX) (key : Json) (qs : Array Nat) : IO (Array RP × Array RP) := do
  let nd := if b.digitSize == 0 then qs.size
    else qs.foldl (fun acc q => acc + (bitLen q + b.digitSize - 1) / b.digitSize) 0
  let entries := jArr key "digits"
  if entries.size < nd then throw (IO.userError s!"the key has {entries.size} entries, {nd} are needed")
  let pick := fun (nm : String) => do
    let some e := b.x.c.polys[nm]? | throw (IO.userError s!"polys.txt has no entry {nm}")
    pure ((e.limbs.extract 0 qs.size).map (·.map Int.toNat))
  let mut kb : Array RP := #[]
  let mut ka : Array RP := #[]
  for j in [0:nd] do
    let (some bn, some an) := (jStr? entries[j]! "b", jStr? entries[j]! "a")
      | throw (IO.userError "key entry names")
    kb := kb.push (← pick bn)
    ka := ka.push (← pick an)
  return (kb, ka)

/-- **`algo.relin.leveled` / `algo.rotate.leveled`**: the locked `Challenge.BFVMul.Fl.leveledKS`
(scale the switched component down to `Q_l` with `Fl.scaleDown`, key-switch at `Q_l` with
`core`, `Fl.scaleUp`, add), executed on the CRT lifts of the recorded operand, with the sums of
`Fl.floatSums A64` (the build's arithmetic) and `core` the key switch at `Q_l` from the top-level
keys cut down to `Q_l`: HYBRID `keySwitchBGVOpenFHE` at plaintext modulus 1 (proved staged
execution at `N ≤ ksStagedMaxN`, the array mirror `hybridKSF` above), BV the mirror of
`keyswitch-bv.cpp` (no project definition). `core` is a parameter of the locked definition. -/
def checkLeveledKS (b : BX) (a out : Obj) (key : Json) (drop : Nat) (isKS : Bool)
    (ex : List (String × Json)) : IO Unit := do
  let x := b.x
  let k := a.towers
  let qsA := x.qsArr k
  let qs := qsA.toList
  let l := k - drop
  let ql := qsA.extract 0 l
  let check := if isKS then "algo.rotate.leveled" else "algo.relin.leveled"
  let S : Fl.Sums := if b.cv.exactSr then Fl.exactSums else Fl.floatSums (if b.cv.fma then A64fma else A64)
  let mu := x.o.mu
  let coreArr : RP → RP × RP ← (do
    if b.ksT == "BV" then
      let (kb, ka) ← b.bvKeys key ql
      pure fun d =>
        let ds := bvDigits b.m.bvCanon b.m.bvUnbalanced b.digitSize ql d
        (parMap b.K ql.size fun i => innerNeg ql[i]! (ds.map (·[i]!)) (kb.map (·[i]!)),
         parMap b.K ql.size fun i => innerNeg ql[i]! (ds.map (·[i]!)) (ka.map (·[i]!)))
    else
      let some sz := b.sizes l mu | throw (IO.userError "no partition at this level")
      if b.N > ksStagedMaxN && mu = .none then
        let (kb, ka) ← b.keyLimbs key l sz.length
        pure fun d => hybridKSF b.K ql x.c.special.toArray sz d kb ka
      else
        let (kb, ka) ← x.keyDigits key l sz.length
        let z := b.zeros l
        pure fun d =>
          match runKS b.N b.K 1 x.c.qs x.c.special l sz mu false (.add z z) (toZ1 d) kb ka with
          | .ok (r0, r1) => (r0.map (·.map Int.toNat), r1.map (·.map Int.toNat))
          | .error _ => (#[], #[]))
  -- the CRT lift as an ARRAY: a function returning an `IntPoly` would be re-run by the compiled
  -- code for every coefficient (see `FHE.Pin.mulArr`)
  let liftA := fun (limbs : RP) => (match crt "core" b.N ql (toZ1 limbs) with
    | .ok z => z
    | .error _ => Array.replicate b.N (0 : Int))
  let core : IntPoly b.N → IntPoly b.N × IntPoly b.N := fun d =>
    let dA := toArr b.K d
    let r := coreArr (ql.map fun (q : Nat) => dA.map fun (v : Int) => (v % (q : Int)).toNat)
    let z1 := liftA r.1
    let z2 := liftA r.2
    (ofArr (N := b.N) z1, ofArr (N := b.N) z2)
  let cts ← (a.parts.toList.take (if isKS then 2 else 3)).mapM fun part => liftExcept (crt "operand" b.N qsA part)
  let ct : List (IntPoly b.N) := cts.map fun z => ofArr z
  -- `core` is evaluated ONCE, on `Fl.scaleDown S qs l c_sel` (the locked step 2), and the locked
  -- `Fl.leveledKS` is run with the constant function returning that pair: equal to running it
  -- with `core`, which it applies to exactly that argument (definition of `Fl.leveledKS`). Without
  -- this the compiled closures may re-run the key switch per coefficient.
  let sel := ct.getD (if isKS then 1 else 2) 0
  let (ab, ms0) ← FHE.Pin.Algo.Cx.timedPure fun _ =>
    let r := core (frc b.K (Fl.scaleDown S qs l sel))
    (frc b.K r.1, frc b.K r.2)
  let (got, ms1) ← FHE.Pin.Algo.Cx.timedPure fun _ => limbsOfDef b.K qsA (Fl.leveledKS S qs drop (fun _ => ab) ct)
  let ms := ms0 + ms1
  let _ ← x.report check (if isKS then "rotate" else "relin") "literal:Fl.leveledKS" out got ms
    (ex ++ [("fn", Json.str "Challenge.BFVMul.Fl.leveledKS (locked), sums Fl.floatSums A64"),
            ("core", Json.str (if b.ksT == "BV" then s!"BV key switch at Q_l (mirror, digitSize {b.digitSize})"
              else if b.N > ksStagedMaxN then "keySwitchBGVOpenFHE at t = 1 at Q_l: array mirror hybridKSF"
              else "keySwitchBGVOpenFHE at t = 1 at Q_l: proved staged execution")),
            ("drop", Json.num drop), ("ks", Json.str b.ksT)])

/-- The parameters and key-switching layout of the locked transcriptions: the program's, or for a
refused program the parameters of `pin.json` with the library's layout. -/
def lockedPL (b : BX) : FullParams × Spec.Budget.KSLayout :=
  let c := b.x.c
  let fallbackP : FullParams :=
    { src := { kind := .bfv, N := c.N, qs := c.qs, t := c.t }
      store := { W := c.N, limbs := c.qs.map (⟨·, 0⟩), special := c.special.map (⟨·, 0⟩) }
      secretBound := 1, inputNoise := 0, keyNoise := 0, outputNoise := 0 }
  let fallbackLay := if b.ksT == "BV" then Spec.Budget.uniformLayout 1 false
    else Spec.Budget.uniformLayout b.alpha true
  match FHE.Pin.BFV.decodeProg c with
  | .ok inp =>
    let P := inp.base.P
    (P, (FHE.Check.layoutOf P inp.base.ks).toOption.getD fallbackLay)
  | .error _ => (fallbackP, fallbackLay)

/-- **The locked transcriptions of `RelinearizeCore` and `EvalAutomorphism`**, executed as
written (`N ≤ litMaxN`): `Challenge.RealizeBFV.relinBFV` / `keySwitchBFV` at the operand's level,
or under HPSPOVERQLEVELED at the top level `Fl.leveledKS (Fl.floatSums A64) … drop
(fun c => ksBFV P lay (L − drop) c keys)` (as `Challenge.CertifyBFV.libKS`), and for a rotation
`Challenge.RealizeBFV.rotateBFV` against the `EvalAutomorphism` output. The keys are pin.json's,
CRT-lifted over all their limbs (`libKeys`). -/
def checkLockedKS (b : BX) (a out : Obj) (rotOut : Option Obj) (drop : Nat) (leveledTop isKS : Bool)
    (g : Option Nat) (ex : List (String × Json)) : IO Unit := do
  let x := b.x
  let (P, lay) := b.lockedPL
  if P.src.N != x.c.N || P.src.qs != x.c.qs then return
  if b.ksT == "BV" && b.digitSize > 0 then
    x.emit (if rotOut.isSome then "algo.rotate" else "algo.relin") (rotOut.getD out).id "relin" none "literal:Challenge.RealizeBFV"
      (ex ++ [("why", Json.str s!"BV with digit size {b.digitSize} > 0: not transcribed by Challenge.RealizeBFV.ksBV (digit size 0 only); compared by the mirror only")])
    return
  let N := P.src.N
  let k := a.towers
  let qsA := x.qsArr k
  let keys := match g with
    | some gi => libKeys x.c N "rot" (some gi)
    | none => libKeys x.c N "relin" none
  let cts ← (a.parts.toList.take (if isKS then 2 else 3)).mapM fun part => liftExcept (crt "operand" x.c.N qsA part)
  let ct : List (IntPoly N) := cts.map fun z => ofArr z
  let S : Fl.Sums := Fl.floatSums (if b.fmaBuild then A64fma else A64)
  let (fnName, res) :=
    if leveledTop && drop > 0 then
      ("Challenge.BFVMul.Fl.leveledKS (Fl.floatSums A64) with core Challenge.RealizeBFV.ksBFV at L - drop",
       Fl.leveledKS S (P.src.qs.take k) drop (fun c => Challenge.RealizeBFV.ksBFV P lay (k - drop) c keys) ct)
    else if isKS then ("Challenge.RealizeBFV.keySwitchBFV", Challenge.RealizeBFV.keySwitchBFV P lay k ct keys)
    else ("Challenge.RealizeBFV.relinBFV", Challenge.RealizeBFV.relinBFV P lay k ct keys)
  if rotOut.isNone then
   let (got, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => limbsOfDef b.K qsA res
   let check := if leveledTop && drop > 0 then (if isKS then "algo.rotate.leveled" else "algo.relin.leveled") else "algo.relin"
   let _ ← x.report check "relin" ("literal:" ++ fnName) out got ms
     (ex ++ [("fn", Json.str fnName), ("ksDeclOK", boolJ (Challenge.RealizeBFV.ksDeclOK? P lay))])
  -- the rotation as a whole: `rotateBFV` (key switch, then σ_g) against the EvalAutomorphism output
  if let (some ro, some gi) := (rotOut, g) then
    if !(leveledTop && drop > 0) then
      let (gr, ms2) ← FHE.Pin.Algo.Cx.timedPure fun _ =>
        limbsOfDef b.K qsA (Challenge.RealizeBFV.rotateBFV P lay k gi ct keys)
      let _ ← x.report "algo.rotate" "rotate" "literal:Challenge.RealizeBFV.rotateBFV" ro gr ms2
        (ex ++ [("fn", Json.str "Challenge.RealizeBFV.rotateBFV"), ("g", Json.num gi)])

/-- `LeveledSHEBFVRNS::RelinearizeCore` (`bfvrns-leveledshe.cpp:898-946`): key switch of the last
component (`c₂` of a product, `c₁` of a 2-component ciphertext), under HPSPOVERQLEVELED at the top
level after an internal `ScaleAndRound` to `Q_l` and followed by `ExpandCRTBasisQlHat`. -/
def checkRelinCore (b : BX) (a out : Obj) (ld : Option Int) (rot : Option Nat) (via : String) :
    IO Unit := do
  let x := b.x
  x.explain out.id
  if a.parts.size == 3 then b.observeRelin a out ld via
  if !(← b.ksBudget "algo.relin" out "relin") then return
  let k := a.towers
  let qs := x.qsArr k
  let isKS := a.parts.size == 2
  let sel := if isKS then 1 else 2
  let leveledTop := b.mult == "HPSPOVERQLEVELED" && k == b.L
  let ex := [BX.ops [a], ("operandParts", Json.num a.parts.size), ("via", Json.str via),
             ("towers", Json.num k), ("keySwitchOf", Json.str (if isKS then "c1" else "c2"))] ++
            (match ld with | some v => [("levelsDropped", intJ v)] | none => []) ++
            (match rot with | some g => [("g", Json.num g)] | none => []) ++
            (if a.parts.size > 3 then [("partsDroppedByOpenFHE", natJ (a.parts.size - 3))] else [])
  try
    let key ← (if isKS then
        match rot with
        | some g => match x.findKey "rot" g with
          | some k => pure k
          | none => throw (IO.userError s!"no rotation key for index {g}")
        | none => throw (IO.userError "key switch of a 2-component ciphertext outside EvalAutomorphism: which key?")
      else match x.findKey "relin" 2 with
        | some k => pure k
        | none => throw (IO.userError "no relinearization key"))
    let drop : Nat ← (if leveledTop then
        match ld with
        | some v => pure (if b.m.ksDropIgnored then 0 else v.toNat)
        | none => throw (IO.userError "HPSPOVERQLEVELED at the top level: levelsDropped is not in the trace")
      else pure 0)
    let aN := toN a.parts
    let d0 := aN[sel]!
    let mu := x.o.mu
    let hybridPlain := b.ksT != "BV" && !leveledTop
    let impl := if hybridPlain then (if b.N > ksStagedMaxN then "mirror" else "staged") else "mirror-only"
    let fn := (if b.ksT == "BV" then s!"BV key switch (CRTDecompose, digitSize {b.digitSize}): no project definition"
               else "FHE.KeySwitch.keySwitchBGVOpenFHE at plaintext modulus 1 (canonical ModUp, ModDown without t-correction)") ++
              (if leveledTop then "; inside ScaleAndRound to Q_l / ExpandCRTBasisQlHat (the leveled key switch: no project definition)" else "")
    let (res, ms) ← FHE.Pin.Algo.Cx.timed (do
      if hybridPlain then
        -- `relinOpenFHE … 1`: (c₀ + KS₀, c₁ + KS₁), with c₁ = 0 for a 2-component input
        let c1 := if isKS then b.zeros k else a.parts[1]!
        match ← b.ksHybrid mu false key k (.add a.parts[0]! c1) a.parts[sel]! (if b.m.ksWithT then b.t else 1) out.id with
        | .ok (r0, r1) => pure (Except.ok #[r0, r1])
        | .error e => pure (Except.error e)
      else
        let l := k - drop
        let ql := qs.extract 0 l
        let dS := if leveledTop then
            scaleF b.cv b.K 1 (qs.extract l k) ql (d0.extract l k) (d0.extract 0 l)
          else d0
        match ← b.ksRaw mu key ql dS with
        | .ok (r0, r1) =>
          let (e0, e1) := if leveledTop then (expandQlHatF qs ql r0, expandQlHatF qs ql r1) else (r0, r1)
          let o0 := addRP qs aN[0]! e0
          let o1 := if isKS then e1 else addRP qs aN[1]! e1
          pure (Except.ok #[toZ1 o0, toZ1 o1])
        | .error e => pure (Except.error e))
    -- with an internal drop the CHECK is the locked `Fl.leveledKS`; the mirror is a variant line
    let useLeveled := leveledTop && (ld.getD 0) > 0
    if b.N ≤ x.o.litMaxN && b.plain then
      match ← (b.checkLockedKS a out none drop leveledTop isKS (if isKS then rot else none) ex).toBaseIO with
      | .error e => x.emit "algo.relin" out.id "relin" (some false) "literal" ([("why", Json.str s!"locked transcription: {e}")] ++ ex)
      | .ok _ => pure ()
    if useLeveled then
      try b.checkLeveledKS a out key drop isKS ex
      catch e =>
        x.emit (if isKS then "algo.rotate.leveled" else "algo.relin.leveled") out.id "relin" (some false) "literal:Fl.leveledKS" ([("why", Json.str s!"{e}")] ++ ex)
    match res with
    | .error e => x.emit (if useLeveled then "algo.variant.relin" else "algo.relin") out.id "relin" none impl ([("why", Json.str e)] ++ ex)
    | .ok got =>
      if useLeveled then
        let r := cmpParts b.t qs out.parts got
        x.emit "algo.variant.relin" out.id "relin" none impl
          ([("variant", Json.str "the leveled key switch mirror (ScaleAndRound / key switch / ExpandCRTBasisQlHat on limbs)"),
            ("matches", boolJ r.ok), ("fn", Json.str fn), ("ks", Json.str b.ksT)] ++ r.json ++ ex)
      else
        let _ ← x.report "algo.relin" "relin" impl out got ms (ex ++ [("fn", Json.str fn), ("ks", Json.str b.ksT)])
    if !b.plain then return
    -- for the record: other variants of the HYBRID key switch; the literal definitions at small N
    if hybridPlain then
      let c1 := if isKS then b.zeros k else a.parts[1]!
      let run := fun (name : String) (m : AMut) (lit : Bool) (tKS : Nat) (counts : Bool) => do
        match ← b.ksHybrid m lit key k (.add a.parts[0]! c1) a.parts[sel]! tKS with
        | .ok (r0, r1) =>
          if counts then
            let _ ← x.report "algo.relin" "relin" name out #[r0, r1] 0 (ex ++ [("ks", Json.str b.ksT)])
          else
            let r := cmpParts b.t qs out.parts #[r0, r1]
            x.emit "algo.variant.relin" out.id "relin" none name
              ([("matches", boolJ r.ok), ("why", Json.str "for the record: another variant")] ++ r.json ++ ex)
        | .error e => x.emit "algo.variant.relin" out.id "relin" none name ([("why", Json.str e)] ++ ex)
      if b.N ≤ x.o.litMaxN then
        run "literal" .none true 1 true
      if b.N ≤ x.o.variantsMaxN then
        run "staged:keySwitchBGV at t = 1 (centred ModUp, centred ModDown)" .allCentred false 1 false
        run "staged:keySwitchBGVAddDown at t = 1" .downAdd false 1 false
        run "staged:keySwitchBGVOpenFHE at the plaintext modulus (BGV's t-correction)" .none false b.t false
      if b.N ≤ x.o.litMaxN then
        match b.sizes k .none with
        | some sz =>
          let (kb, ka) ← x.keyDigits key k sz.length
          match runKSPlain b.N b.K x.c.qs x.c.special k sz a.parts[sel]! kb ka with
          | .ok (r0, r1) =>
            let g := #[toZ1 (addRP qs aN[0]! (r0.map (·.map Int.toNat))),
                       toZ1 (addRP qs (toN #[c1])[0]! (r1.map (·.map Int.toNat)))]
            let r := cmpParts b.t qs out.parts g
            x.emit "algo.variant.relin" out.id "relin" none "literal:keySwitchPlain"
              ([("matches", boolJ r.ok), ("why", Json.str "for the record: the centred BFV/CKKS key switch FHE.KeySwitch.keySwitchPlain")] ++ r.json ++ ex)
          | .error e => x.emit "algo.variant.relin" out.id "relin" none "literal:keySwitchPlain" ([("why", Json.str e)] ++ ex)
        | none => pure ()
  catch e =>
    x.emit "algo.relin" out.id "relin" (some false) "glue" ([("why", Json.str s!"{e}")] ++ ex)

/-- `LeveledSHEBase::RelinearizeInPlace` (`base-leveledshe.cpp`): `KeySwitchInPlace` for every
component `j ≥ 2` under the key for `s^j`; **no** internal drop even under HPSPOVERQLEVELED. -/
def checkRelinBase (b : BX) (a out : Obj) (via : String) : IO Unit := do
  let x := b.x
  x.explain out.id
  if a.parts.size == 3 then b.observeRelin a out none via
  if !(← b.ksBudget "algo.relin" out "relin") then return
  let k := a.towers
  let qs := x.qsArr k
  let ex := [BX.ops [a], ("operandParts", Json.num a.parts.size), ("via", Json.str via),
             ("towers", Json.num k), ("ks", Json.str b.ksT)]
  try
    let aN := toN a.parts
    let (res, ms) ← FHE.Pin.Algo.Cx.timed (do
      let mut c0 := aN[0]!
      let mut c1 := aN[1]!
      let mut err : Option String := none
      for j in [2:a.parts.size] do
        let some key := x.findKey "relin" j | throw (IO.userError s!"no relinearization key for s^{j}")
        match ← b.ksRaw x.o.mu key qs aN[j]! with
        | .ok (r0, r1) =>
          c0 := addRP qs c0 r0
          c1 := addRP qs c1 r1
        | .error e => err := some e
      pure (err, #[toZ1 c0, toZ1 c1]))
    let impl := if b.ksT == "BV" then "mirror-only" else if b.N > ksStagedMaxN then "mirror" else "staged"
    match res with
    | (some e, _) => x.emit "algo.relin" out.id "relin" none impl ([("why", Json.str e)] ++ ex)
    | (none, got) =>
      let _ ← x.report "algo.relin" "relin" impl out got ms
        (ex ++ [("fn", Json.str (if b.ksT == "BV" then "BV key switch: no project definition"
          else "FHE.KeySwitch.keySwitchBGVOpenFHE at plaintext modulus 1, + c"))])
  catch e =>
    x.emit "algo.relin" out.id "relin" (some false) "glue" ([("why", Json.str s!"{e}")] ++ ex)

/-- `LeveledSHEBFVRNS::EvalAutomorphism` (`bfvrns-leveledshe.cpp:775-793`): `RelinearizeCore`
with the key for `g` (key switch of `c₁`, `c₀` added), **then** `σ_g` on both components.
`r` is the traced output of the inner `RelinearizeCore`. -/
def checkAutomorph (b : BX) (a r out : Obj) (g : Nat) (via : String) : IO Unit := do
  let x := b.x
  x.explain out.id
  let k := out.towers
  let qs := x.qsArr k
  let ex := [BX.ops [r], ("g", Json.num g), ("via", Json.str via)]
  -- σ_g of the key-switched ciphertext
  let rN := toN r.parts
  let (got, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => rN.map fun part => (Array.range k).map fun i => autoF g qs[i]! part[i]!
  let _ ← x.report "algo.automorph" "automorph" "staged" out (toZ got) ms
    (ex ++ [("fn", Json.str "X^i -> X^(i*g mod 2N) on arrays (mirror of Spec.NPoly.automorph)")])
  if b.plain && b.N ≤ 1024 then
    x.hom "algo.automorph" "automorph" [r] out (fun l => (l.getD 0 []).map (automorph g))
      [("g", Json.num g), ("via", Json.str via), ("fn", Json.str "Spec.NPoly.automorph")]
  -- the whole rotation from the operand: `rotateOpenFHE` at t = 1 (σ_g last)
  let leveledTop := b.mult == "HPSPOVERQLEVELED" && k == b.L
  if b.N ≤ x.o.litMaxN && b.plain && !leveledTop && a.parts.size == 2 && a.towers == k then
    match ← (b.checkLockedKS a r (some out) 0 false true (some g) ex).toBaseIO with
    | .error e => x.emit "algo.rotate" out.id "rotate" (some false) "literal" [("why", Json.str s!"locked transcription: {e}")]
    | .ok _ => pure ()
  if b.ksT == "BV" || leveledTop || a.parts.size != 2 || a.towers != k then return
  let some key := x.findKey "rot" g | return
  let ex := [BX.ops [a], ("g", Json.num g), ("via", Json.str via)]
  let mu := x.o.mu
  let tKS := if b.m.ksWithT then b.t else 1
  let op : KSOp := if mu = .autoFirst then .rotFirst g a.parts[0]!
    else if b.m.autoBeforeModDown then .rot g a.parts[0]! else .rotLast g a.parts[0]!
  try
    let (res, ms) ← FHE.Pin.Algo.Cx.timed (b.ksHybrid mu false key k op a.parts[1]! tKS out.id)
    match res with
    | .ok (r0, r1) =>
      let _ ← x.report "algo.rotate" "rotate" (if b.N > ksStagedMaxN then "mirror" else "staged") out #[r0, r1] ms
        (ex ++ [("fn", Json.str "FHE.Pin.Algo.rotateOpenFHE at plaintext modulus 1: key switch, + c0, then the automorphism (rotStaged_openfhe)")])
    | .error e => x.emit "algo.rotate" out.id "rotate" none "staged" ([("why", Json.str e)] ++ ex)
    if !b.plain then return
    if b.N ≤ x.o.litMaxN then
      match ← b.ksHybrid .none true key k (.rotLast g a.parts[0]!) a.parts[1]! 1 with
      | .ok (r0, r1) => let _ ← x.report "algo.rotate" "rotate" "literal" out #[r0, r1] 0 ex
      | .error _ => pure ()
    if b.N ≤ x.o.variantsMaxN then
      match ← b.ksHybrid .none false key k (.rot g a.parts[0]!) a.parts[1]! 1 with
      | .ok (r0, r1) =>
        let rr := cmpParts b.t qs out.parts #[r0, r1]
        x.emit "algo.variant.rotate" out.id "rotate" none
          "staged:rotateOpenFHE161 at t = 1 (BGV's v1.6.1 order: automorphism over Q*P before ModDown)"
          ([("matches", boolJ rr.ok), ("why", Json.str "for the record: the order BGV uses in v1.6.1")] ++ rr.json ++ ex)
      | .error _ => pure ()
  catch e =>
    x.emit "algo.rotate" out.id "rotate" (some false) "glue" ([("why", Json.str s!"{e}")] ++ ex)

/-! ## Mixed representations

The recorded product of `LeveledSHEBFVRNS::EvalMult(ct, ct)` / `EvalSquare(ct)` is held in
coefficient representation (`bfvrns-leveledshe.cpp:206-442`); the other operations here hold
evaluation representation. `DCRTPoly::operator+=`, `-=`, `*=` (`dcrtpoly-impl.h:409-447`) operate
on the vectors as stored. When the operands of an addition, subtraction or plaintext operation are
held in different representations, the comparison uses the recorded representations: the mirror
below combines the stored vectors entry by entry (the evaluation vector in OpenFHE's NTT order,
`FHE.Pin.BFV.NTT`). The representation of each component is inferred from the trace (it is not
recorded); the trusted ring operation is run as well. -/

def flagsOf (b : BX) (o : Obj) : IO (Array Bool) := do
  match (← b.fmt.get)[o.id]? with
  | some f => pure (if f.size == o.parts.size then f else Array.replicate o.parts.size false)
  | none => pure (Array.replicate o.parts.size false)

def psi (b : BX) (q : Nat) : IO Nat := do
  match (← b.roots.get)[q]? with
  | some r => pure r
  | none =>
    let r := minRoot b.N q
    b.roots.modify (·.insert q r)
    pure r

def mixedWhy : String :=
  "operands held in different representations (coefficient: an un-relinearised product; evaluation: the others); the mirror combines the stored vectors entry by entry"

/-- The trusted ring operation on operands held in different representations: reported as a
variant line (never a failure); the check is the representation-aware mirror. -/
def ringVariant (b : BX) (check op : String) (ops : List Obj) (out : Obj)
    (g : List (List (IntPoly b.N)) → List (IntPoly b.N)) (ex : List (String × Json)) : IO Unit := do
  let x := b.x
  x.explain out.id
  if ops.any (·.towers != out.towers) then return
  let qs := x.qsArr out.towers
  let got := homLimb b.N b.K qs (ops.map (·.parts)) g
  let r := cmpParts b.t qs out.parts got
  x.emit ("algo.variant." ++ (check.drop 5).toString) out.id op none "limb"
    ([("variant", Json.str "the trusted ring operation (Spec.NPoly) on the stored vectors of operands held in different representations"),
      ("matches", boolJ r.ok)] ++ r.json ++ ex)

def taint (b : BX) (id why : String) : IO Unit :=
  b.notUnderS.modify fun m => if m.contains id then m else m.insert id why

/-- `EvalAddCoreInPlace` / `EvalSubCoreInPlace(ct, ct)`: the trusted `padZip` and, when the
representations of the two operands differ in some component, the mirror of what the library
does (`a ± NTT(b)` resp. `a ± NTT⁻¹(b)` as vectors). -/
def checkAddCore (b : BX) (sub : Bool) (a c out : Obj) : IO Unit := do
  let x := b.x
  let fa ← b.flagsOf a
  let fc ← b.flagsOf c
  let n := min a.parts.size c.parts.size
  let mixed := (Array.range n).any fun i => fa[i]! != fc[i]!
  let fo := (Array.range out.parts.size).map fun i => if i < a.parts.size then fa[i]! else fc[i]!
  b.fmt.modify (·.insert out.id fo)
  let check := if sub then "algo.sub" else "algo.add"
  let op := if sub then "sub" else "add"
  let ex := if mixed then [("why", Json.str mixedWhy),
      ("coefficientRepresentation", Json.arr #[Json.arr (fa.map Json.bool), Json.arr (fc.map Json.bool)])] else []
  let g : List (List (IntPoly b.N)) → List (IntPoly b.N) := fun l =>
    if sub then Challenge.Source.padZip (· - ·) (l.getD 0 []) (l.getD 1 [])
    else Challenge.Source.padZip (· + ·) (l.getD 0 []) (l.getD 1 [])
  if mixed then b.ringVariant check op [a, c] out g ex
  else x.hom check op [a, c] out g ex
  if mixed then
    b.taint out.id "the output of an addition that mixed coefficient and evaluation representations"
    if a.towers != out.towers || c.towers != out.towers then return
    let k := out.towers
    let qs := x.qsArr k
    let aN := toN a.parts
    let cN := toN c.parts
    let mut rs := #[]
    for q in qs do rs := rs.push (← b.psi q)
    let got : Array RP := (Array.range out.parts.size).map fun p => (Array.range k).map fun i =>
      let q := qs[i]!
      if p < n then
        let A := (aN[p]!)[i]!
        let B := (cN[p]!)[i]!
        let B' := if fa[p]! == fc[p]! then B else if fa[p]! then nttF rs[i]! q B else inttF rs[i]! q B
        if sub then subF q A B' else addF q A B'
      else if p < a.parts.size then (aN[p]!)[i]!
      else if sub then ((cN[p]!)[i]!).map fun v => (q - v) % q else (cN[p]!)[i]!
    let _ ← x.report check op "mirror-only" out (toZ got) 0
      ([BX.ops [a, c], ("deviation", Json.str "the second operand's components added as stored: its evaluation (NTT) vector to a coefficient vector, or its coefficient vector to an evaluation vector (OpenFHE's NTT order, minimum primitive root)"),
        ("why", Json.str mixedWhy)])

/-- `EvalMultInPlace(ct, pt)`: every component times the stored plaintext; for a component in
coefficient representation the library multiplies its coefficient vector entry by entry with the
plaintext's evaluation vector. -/
def checkMulPlain (b : BX) (a p out : Obj) (via : String) : IO Unit := do
  let x := b.x
  let fa ← b.flagsOf a
  b.fmt.modify (·.insert out.id fa)
  let mixed := fa.any id
  let ex := [("via", Json.str via), ("fn", Json.str "every component times the stored plaintext polynomial (Spec.NPoly *)")] ++
    (if mixed then [("why", Json.str mixedWhy)] else [])
  if b.N > 4096 && !mixed && a.towers == out.towers && p.towers ≥ out.towers then
    -- the trusted quadratic product is too slow here: Kronecker products (`mulNeg`, `#guard`ed
    -- against the schoolbook product), compared with the trusted `*` at every N ≤ 4096
    x.explain out.id
    let qs := x.qsArr out.towers
    let aN := toN a.parts
    let pN := (toN p.parts)[0]!
    let (got, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ =>
      aN.map fun part => (Array.range out.towers).map fun i => mulNeg qs[i]! part[i]! pN[i]!
    let _ ← x.report "algo.mulPlain" "mulPlain" "mirror" out (toZ got) ms (ex ++ [BX.ops [a, p]])
    return
  let g : List (List (IntPoly b.N)) → List (IntPoly b.N) := fun l => match l.getD 1 [] with
      | [c] => (l.getD 0 []).map (c * ·)
      | _ => []
  if mixed then
    b.ringVariant "algo.mulPlain" "mulPlain" [a, p] out g ex
    x.explain out.id
  else x.hom "algo.mulPlain" "mulPlain" [a, p] out g ex
  if mixed then
    b.taint out.id "the output of a plaintext multiplication that mixed coefficient and evaluation representations"
    if a.towers != out.towers || p.towers < out.towers then return
    let k := out.towers
    let qs := x.qsArr k
    let aN := toN a.parts
    let pN := (toN p.parts)[0]!
    let mut rs := #[]
    for q in qs do rs := rs.push (← b.psi q)
    let got : Array RP := (Array.range out.parts.size).map fun j => (Array.range k).map fun i =>
      let q := qs[i]!
      if fa[j]! then
        Array.zipWith (fun u v => u * v % q) (aN[j]!)[i]! (nttF rs[i]! q pN[i]!)
      else mulNeg q (aN[j]!)[i]! pN[i]!
    let _ ← x.report "algo.mulPlain" "mulPlain" "mirror-only" out (toZ got) 0
      ([BX.ops [a, p], ("deviation", Json.str "coefficient vector times the plaintext's evaluation (NTT) vector, entry by entry"),
        ("why", Json.str mixedWhy)])

/-! ## Plaintext operations -/

/-- `t − (Q_k mod t)` (`m_negQModt[level]`, `bfvrns-cryptoparameters.cpp:79-88`: `t.Sub(Q mod t)`,
which is `t`, not `0`, when `t ∣ Q`). -/
def negQModt (b : BX) (k : Nat) : Nat := b.t - prodL (b.x.qsArr k) % b.t

/-- `TimesQovert` of the stored plaintext limbs (over the first `kp` towers), under the mutant's
rounding. `none`: the mutant's rounding needs one integer polynomial but the limbs do not hold a
common value in `[0, t)`. -/
def scaledPlain (b : BX) (mode : QOverT) (p : RP) (kp : Nat) : Option RP :=
  let qs := b.x.qsArr kp
  let Q := prodL qs
  match mode with
  | .ceil => some ((Array.range kp).map fun i => timesQovertF b.t (b.negQModt kp) qs[i]! p[i]!)
  | _ =>
    let p0 := p[0]!
    if (p.all fun l => l == p0) && p0.all (· < b.t) then
      some ((Array.range kp).map fun i => p0.map fun v =>
        (match mode with
          | .round => (2 * Q * v + b.t) / (2 * b.t)
          | .floor => Q * v / b.t
          | _ => Q / b.t * v) % qs[i]!)
    else none

/-- `EvalAddInPlace` / `EvalSubInPlace(Ciphertext, Plaintext)` (`bfvrns-leveledshe.cpp:56-104`):
`c₀ ± TimesQovert(p)`. -/
def checkAddPlain (b : BX) (sub : Bool) (a p out : Obj) (via : String) : IO Unit := do
  let x := b.x
  x.explain out.id
  let check := if sub then "algo.subPlain" else "algo.addPlain"
  let op := if sub then "subPlain" else "addPlain"
  let k := a.towers
  let kp := p.towers
  let qs := x.qsArr k
  let ex := [BX.ops [a, p], ("via", Json.str via), ("towers", Json.num k), ("plaintextTowers", Json.num kp)]
  if kp != k || out.towers != k then
    x.emit check out.id op none "mirror-only" ([("why", Json.str "the plaintext and the ciphertext have different numbers of towers")] ++ ex)
    return
  let aN := toN a.parts
  let pN := (toN p.parts)[0]!
  let common := (pN.all fun l => l == pN[0]!) && pN[0]!.all (· < b.t)
  let fa ← b.flagsOf a
  b.fmt.modify (·.insert out.id fa)
  let mixed := fa[0]!
  let ex := ex ++ [("storedPlaintextInZeroT", boolJ common)] ++ (if mixed then [("why", Json.str mixedWhy)] else [])
  match b.scaledPlain b.m.qovert pN kp with
  | none => x.emit check out.id op none "mirror-only" ([("why", Json.str "the stored plaintext is not one integer polynomial in [0, t)")] ++ ex)
  | some sp =>
    let c0 := (Array.range k).map fun i => if sub then subF qs[i]! (aN[0]!)[i]! sp[i]! else addF qs[i]! (aN[0]!)[i]! sp[i]!
    let got := aN.set! 0 c0
    if mixed then
      let r := cmpParts b.t qs out.parts (toZ got)
      x.emit ("algo.variant." ++ (check.drop 5).toString) out.id op none "mirror-only"
        ([("variant", Json.str "c0 +- TimesQovert(p) on the stored vectors, both read as coefficient vectors"),
          ("matches", boolJ r.ok)] ++ r.json ++ ex)
    else
      let _ ← x.report check op "mirror-only" out (toZ got) 0
        (ex ++ [("fn", Json.str "c0 +- TimesQovert(p), TimesQovert(p) = ceil(Q*p/t) limb by limb: Spec.EncryptBFV.scaleUpCeil per limb")])
    if mixed then
      b.taint out.id "the output of a plaintext addition that mixed coefficient and evaluation representations"
      let mut rs := #[]
      for q in qs do rs := rs.push (← b.psi q)
      let c0 := (Array.range k).map fun i =>
        let e := nttF rs[i]! qs[i]! sp[i]!
        if sub then subF qs[i]! (aN[0]!)[i]! e else addF qs[i]! (aN[0]!)[i]! e
      let _ ← x.report check op "mirror-only:mixed" out (toZ (aN.set! 0 c0)) 0
        (ex ++ [("deviation", Json.str "the evaluation (NTT) vector of TimesQovert(p) added to the coefficient vector of c0, entry by entry")])
      return
    if !b.plain then return
    -- for the record: the project's definitions (round to nearest; floor(Q/t)*p)
    for (name, mode) in [("Challenge.BFVMul.bfvAddPlainRounded / bfvSubPlainRounded (scaleUp: round to nearest)", QOverT.round),
                         ("Challenge.BFV.bfvAddPlain / bfvSubPlain (floor(Q/t)*p)", QOverT.delta),
                         ("floor(Q*p/t)", QOverT.floor)] do
      match b.scaledPlain mode pN kp with
      | some sp' =>
        let c0' := (Array.range k).map fun i => if sub then subF qs[i]! (aN[0]!)[i]! sp'[i]! else addF qs[i]! (aN[0]!)[i]! sp'[i]!
        let r := cmpParts b.t qs out.parts (toZ (aN.set! 0 c0'))
        x.emit "algo.variant.addPlain" out.id op none "mirror-only"
          ([("variant", Json.str name), ("matches", boolJ r.ok)] ++ r.json ++ ex)
      | none => pure ()
    -- the locked definitions themselves, on the CRT lifts
    if common && b.N ≤ 4096 then
      match crt "operand" b.N qs a.parts[0]! with
      | .ok c0Z =>
        let Q := prodL qs
        let pZ : IntPoly b.N := ofArr (pN[0]!.map fun (v : Nat) => (v : Int))
        let c : List (IntPoly b.N) := [ofArr c0Z]
        let g : List (IntPoly b.N) := if sub then bfvSubPlainRounded b.t Q c pZ else bfvAddPlainRounded b.t Q c pZ
        let g0 := (limbsOfDef b.K qs g)[0]!
        let r := cmpParts b.t qs #[out.parts[0]!] #[g0]
        x.emit "algo.variant.addPlain" out.id op none "literal"
          ([("variant", Json.str (if sub then "Challenge.BFVMul.bfvSubPlainRounded" else "Challenge.BFVMul.bfvAddPlainRounded")),
            ("matches", boolJ r.ok)] ++ r.json ++ ex)
      | .error _ => pure ()

/-! ## Encryption -/

/-- `PKEBFVRNS::Encrypt` (`bfvrns-pke.cpp:167-223`). STANDARD: `c₀ = b·u + e₁ + TimesQovert(p)`,
`c₁ = a·u + e₂` over the plaintext's limbs. EXTENDED: the same over `Q·r` with the plaintext
CRT-interpolated and re-reduced, then `ScaleAndRoundPOverQ` (divide by `r`, centred remainder). -/
def checkEncrypt (b : BX) : IO Unit := do
  let x := b.x
  let N := b.N
  let some pub := jObj? x.c.pin "public" | return
  let (some bn, some an) := (jStr? pub "b", jStr? pub "a") | return
  let (some eb, some ea) := (x.c.polys[bn]?, x.c.polys[an]?)
    | x.emit "algo.encrypt" "pk" "encrypt" (some false) "mirror-only" [("why", Json.str "public key missing")]
  for enc in jArr x.c.pin "encryptions" do
    let ctId := (jStr? enc "ct").getD "?"
    try
      let (some ptId, some un, some e1n, some e2n) :=
          (jStr? enc "pt", jStr? enc "u", jStr? enc "e1", jStr? enc "e2")
        | do
          x.emit "algo.encrypt" ctId "encrypt" none "mirror-only"
            [("why", Json.str s!"randomness not captured ({(jStr? enc "randomness").getD "?"})")]
          continue
      let u ← liftExcept (x.c.intPoly un)
      let e1 ← liftExcept (x.c.intPoly e1n)
      let e2 ← liftExcept (x.c.intPoly e2n)
      let pt ← x.obj ptId
      let ct ← x.obj ctId
      x.explain ctId
      let kp := pt.towers
      let pN := (toN pt.parts)[0]!
      let common := (pN.all fun l => l == pN[0]!) && pN[0]!.all (· < b.t)
      let red := fun (z : Array Int) (q : Nat) => z.map fun v => (v % (q : Int)).toNat
      let ex := [BX.ops [pt], ("enc", Json.str b.enc), ("plaintextTowers", Json.num kp),
                 ("storedPlaintextInZeroT", boolJ common), ("encoding", Json.str ((x.c.object? ptId).bind (jStr? · "encoding") |>.getD "?"))]
      if b.enc == "EXTENDED" then
        let r := b.extPrime
        let ms := (x.qsArr b.L).push r
        if eb.moduli != ms || ea.moduli != ms then
          x.emit "algo.encrypt" ctId "encrypt" none "mirror-only"
            ([("why", Json.str s!"EXTENDED: the dumped public key is over {eb.moduli.size} limbs, not over Q and the extra prime; the encryption over Q*r cannot be recomputed")] ++ ex)
          continue
        if kp != b.L then
          x.emit "algo.encrypt" ctId "encrypt" none "mirror-only" ([("why", Json.str "EXTENDED with a lower-level plaintext: not modelled")] ++ ex)
          continue
        -- CRTInterpolate, then the residues modulo every limb of Q*r
        let pZ ← liftExcept (crt ptId N (x.qsArr kp) pt.parts[0]!)
        let negQr := b.t - prodL ms % b.t
        let (got, t0) ← FHE.Pin.Algo.Cx.timedPure fun _ =>
          let big := (Array.range ms.size).map fun i =>
            let q := ms[i]!
            let p := timesQovertF b.t negQr q (pZ.map fun v => (v % (q : Int)).toNat)
            let c0 := addF q (addF q (mulNeg q (eb.limbs[i]!.map Int.toNat) (red u q)) (red e1 q)) p
            let c1 := addF q (mulNeg q (ea.limbs[i]!.map Int.toNat) (red u q)) (red e2 q)
            #[c0, c1]
          (Array.range 2).map fun part =>
            dropLastScaleF false ms (big.map (·[part]!))
        let _ ← x.report "algo.encrypt" "encrypt" "mirror-only" ct (toZ got) t0
          (ex ++ [("fn", Json.str "EXTENDED: (b*u + e1 + TimesQovert_{Q*r}(p), a*u + e2) over Q*r, then ScaleAndRoundPOverQ (division by r, centred remainder): no project definition")])
      else
        if ct.towers != kp then throw (IO.userError "the ciphertext and the plaintext have different numbers of towers")
        let qs := x.qsArr kp
        if eb.moduli.extract 0 kp != qs || ea.moduli.extract 0 kp != qs then
          throw (IO.userError "public key limbs do not start with the ciphertext's limbs")
        let run := fun (mode : QOverT) =>
          (b.scaledPlain mode pN kp).map fun sp =>
            (Array.range 2).map fun part => (Array.range kp).map fun i =>
              let q := qs[i]!
              if part == 0 then
                addF q (addF q (mulNeg q (eb.limbs[i]!.map Int.toNat) (red u q)) (red e1 q)) sp[i]!
              else addF q (mulNeg q (ea.limbs[i]!.map Int.toNat) (red u q)) (red e2 q)
        match run b.m.qovert with
        | none => x.emit "algo.encrypt" ctId "encrypt" none "mirror-only" ([("why", Json.str "the stored plaintext is not one integer polynomial in [0, t)")] ++ ex)
        | some got =>
          let _ ← x.report "algo.encrypt" "encrypt" "staged" ct (toZ got) 0
            (ex ++ [("fn", Json.str "array mirror of Spec.EncryptBFV.encryptBFV (Kronecker products)")])
        -- the trusted definition `Spec.EncryptBFV.encryptBFV t Q_k b a p u e₁ e₂` on each limb
        -- (integer representatives: the key limbs' residues, the common stored plaintext), by its
        -- forced form `encryptBFVF` (Kronecker products; `encryptBFVF_eq`), at every `N`
        if common && b.m.qovert = .ceil then
          let Qk := prodL qs
          let pZ : IntPoly N := ofArr (pN[0]!.map fun (v : Nat) => (v : Int))
          let (g, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ =>
            transpose <| (Array.range kp).map fun i =>
              let q : Nat := qs[i]!
              (encryptBFVF b.t Qk (ofArr (N := N) eb.limbs[i]!) (ofArr ea.limbs[i]!) pZ
                (ofArr u) (ofArr e1) (ofArr e2)).toArray.map fun (c : IntPoly N) =>
                  (toArr x.K c).map fun (v : Int) => v % (q : Int)
          let _ ← x.report "algo.encrypt" "encrypt" "literal:Spec.EncryptBFV.encryptBFV" ct g ms
            (ex ++ [("fn", Json.str "Spec.EncryptBFV.encryptBFV (trusted), per limb")])
        if b.plain then
          for (name, mode) in [("round to nearest (scaleUp)", QOverT.round), ("floor(Q/t)*p", QOverT.delta)] do
            match run mode with
            | some g =>
              let r := cmpParts b.t qs ct.parts (toZ g)
              x.emit "algo.variant.encrypt" ctId "encrypt" none "mirror-only"
                ([("variant", Json.str name), ("matches", boolJ r.ok)] ++ r.json ++ ex)
            | none => pure ()
    catch e =>
      x.emit "algo.encrypt" ctId "encrypt" (some false) "mirror-only" [("why", Json.str s!"{e}")]

/-! ## Compress -/

/-- `LeveledSHEBFVRNS::Compress` (`bfvrns-leveledshe.cpp:948-976`): `DropLastElementAndScale` of
every component, once per dropped limb. -/
def checkCompress (b : BX) (a out : Obj) (via : String) : IO Unit := do
  let x := b.x
  x.explain out.id
  let k := a.towers
  let levels := k - out.towers
  let ex := [BX.ops [a], ("via", Json.str via), ("fromTowers", Json.num k), ("levels", Json.num levels)]
  let (got, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => (toN a.parts).map fun part => Id.run do
    let mut cur := part
    let mut ms := x.qsArr k
    for _ in [0:levels] do
      cur := dropLastScaleF b.m.compressFloor ms cur
      ms := ms.pop
    return cur
  let _ ← x.report "algo.compress" "compress" "staged" out (toZ got) ms
    (ex ++ [("fn", Json.str "DropLastElementAndScale on limbs: (x_i - [x_last]_centred) * q_last^-1 (mirror)")])
  if !b.plain then return
  -- the locked definition on the CRT lift: ⌊c/q⌉ per dropped limb
  let (r, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => a.parts.mapM fun part => do
    let mut cur ← crt "operand" b.N (x.qsArr k) part
    for l in [0:levels] do
      let q := x.c.qs.getD (k - 1 - l) 0
      cur := toArr b.K (Challenge.BFV.bfvModSwitchComp q (ofArr (N := b.N) cur))
    return ((x.qsArr out.towers).map fun (q : Nat) => cur.map (· % (q : Int)))
  match r with
  | .ok g =>
    let _ ← x.report "algo.compress" "compress" "int:bfvModSwitchComp" out g ms
      (ex ++ [("fn", Json.str "Challenge.BFV.bfvModSwitchComp (round to nearest) on the CRT lift in [0, Q)")])
  | .error e => x.emit "algo.compress" out.id "compress" (some false) "int:bfvModSwitchComp" ([("why", Json.str e)] ++ ex)

/-! ## Decryption -/

/-- The limbs of the phase `c₀ + c₁·s + c₂·s² + …` (`DecryptCore`). -/
def phaseLimbs (b : BX) (qs : Array Nat) (parts : Array RP) : RP :=
  parMap b.K qs.size fun i =>
    let q := qs[i]!
    let s := b.s.map fun v => (v % (q : Int)).toNat
    (Array.range parts.size).foldl (fun (acc : Limb) j =>
      let cj := (parts[parts.size - 1 - j]!)[i]!
      if j == 0 then cj else addF q cj (mulNeg q acc s)) #[]

/-- `PKEBFVRNS::Decrypt` of every ciphertext the exporter decrypted, (i) by exact rounding
(`Spec.Scheme.bfvDecrypt`) and (ii) by the library's own procedure. -/
def checkDecrypt (b : BX) : IO Unit := do
  let x := b.x
  let objs : Array String := match jObj? x.c.pin "objects" with
    | some (.obj kvs) => kvs.toArray.map fun (kv : String × Json) => kv.1
    | _ => #[]
  -- deterministic order: by the number in the id
  let num := fun (p : String) => (p.drop 3).toString.toNat!
  let ids := (objs.filter fun (p : String) => p.startsWith "ct_").qsort fun (p q : String) =>
    num p < num q || (num p == num q && p < q)
  for id in ids do
    let some o := x.c.object? id | continue
    let some dj := jObj? o "decrypt" | continue
    let some rawName := jStr? dj "raw" | continue
    try
      let some raw := x.c.polys[rawName]? | throw (IO.userError s!"polys.txt has no entry {rawName}")
      let rawN := raw.limbs[0]!.map Int.toNat
      -- `rawReduced: false` (modulus 0): the library's native values, unreduced (can be `t`)
      let unreduced := raw.moduli[0]! == 0
      let red := fun (v : Nat) => if unreduced then v else v % b.t
      let ct ← x.obj id
      let k := ct.towers
      let qs := x.qsArr k
      let Q := prodL qs
      let (phi, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ => b.phaseLimbs qs (toN ct.parts)
      -- the recorded phase (`DecryptCore`'s output, if the exporter dumped it)
      if let some phName := jStr? dj "phase" then
        if let some ph := x.c.polys[phName]? then
          let pr := ph.limbs.map (·.map Int.toNat)
          let bad := (Array.range (min pr.size phi.size)).foldl (fun acc i => acc + diffCount pr[i]! phi[i]!) 0
          x.emit "algo.decrypt.phase" id "decrypt" (some (bad == 0 && pr.size == phi.size)) "limb"
            [("limbs", Json.num pr.size), ("coeffs", Json.num (pr.size * b.N)), ("mismatches", Json.num bad),
             ("fn", Json.str "c0 + c1*s + c2*s^2 per limb (Kronecker products) against the recorded DecryptCore output")]
      let full := k == b.L
      let proc := if !full then "DropLastElementAndScale to one limb, MultiplyAndRound(t, q) in double, centred switch to t"
        else if b.mult == "BEHZ" then "BEHZ: gamma-corrected integer ScaleAndRound"
        else s!"HPS family: ScaleAndRound to t in double (branch {decBranch b.t qs})"
      let ex := [("towers", Json.num k), ("parts", Json.num ct.parts.size), ("procedure", Json.str proc),
                 ("rawModulus", natJ raw.moduli[0]!)]
      -- (ii) the library's procedure
      let fma := if b.m.flipFma then !b.fmaBuild else b.fmaBuild
      -- the trusted transcription `Spec.DecryptBFV.decrypt1` (the coefficient function of
      -- `Spec.DecryptBFV.bfvDecryptLib`), in the binary64 arithmetic `FHE.Float.RNE.rneD`, on the
      -- residues of the phase (HPS family, full chain)
      if full && b.mult != "BEHZ" && b.plain then
        let ql := qs.toList
        let tab := Spec.DecryptBFV.tables FHE.Float.RNE.rneD.base b.t ql
        let (g, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ =>
          (Array.range b.N).map fun c =>
            Spec.DecryptBFV.decrypt1 FHE.Float.RNE.rneD b.t ql tab (ql.length.fold (fun i _ acc => acc ++ [(phi[i]!)[c]!]) [])
        let gT := g.map red
        let bad := diffCount gT rawN
        x.emit "algo.decrypt" id "decrypt" (some (bad == 0)) "literal:Spec.DecryptBFV.decrypt1"
          ([("limbs", Json.num 1), ("coeffs", Json.num b.N), ("mismatches", Json.num bad), ("ms", Json.num ms),
            ("fn", Json.str "Spec.DecryptBFV.decrypt1 with Spec.DecryptBFV.tables, arithmetic FHE.Float.RNE.rneD (trusted transcription), per coefficient of the phase residues"),
            ("comparedModuloT", Json.bool (!unreduced))] ++ ex)
        if b.N ≤ x.o.litMaxN then
          let cts ← ct.parts.toList.mapM fun part => liftExcept (crt id b.N qs part)
          let ctP : List (Poly ql.prod b.N) := cts.map fun z => ofInt ql.prod (ofArr (N := b.N) z)
          let lit := (toArr b.K (Spec.DecryptBFV.bfvDecryptLib FHE.Float.RNE.rneD b.t ql (ofArr (N := b.N) b.s) ctP)).map red
          x.emit "algo.decrypt" id "decrypt" (some (diffCount lit rawN == 0)) "literal:Spec.DecryptBFV.bfvDecryptLib"
            ([("limbs", Json.num 1), ("coeffs", Json.num b.N), ("mismatches", Json.num (diffCount lit rawN))] ++ ex)
      let lib := if !full then decSmallF fma b.m.decryptExactScale b.m.compressFloor b.t qs phi
        else if b.mult == "BEHZ" then decBehzF b.t b.gamma qs phi
        else decHpsF fma (b.m.exactSr) b.t qs phi
      -- the dump holds residues modulo t; the BEHZ routine itself can return t (unreduced)
      let libT := lib.map red
      let bad := diffCount libT rawN
      let first : Option Nat := (Array.range b.N).find? fun (i : Nat) => libT[i]! != rawN[i]!
      let why ← (do
        match (← b.notUnderS.get)[id]? with
        | some w => pure [("notAnEncryptionUnderS", Json.str w)]
        | none => pure [])
      let ex := ex ++ why
      x.emit "algo.decrypt" id "decrypt" (some (bad == 0)) "mirror-only"
        ([("limbs", Json.num 1), ("coeffs", Json.num b.N), ("mismatches", Json.num bad), ("ms", Json.num ms),
          ("fn", Json.str "PKEBFVRNS::Decrypt's own procedure: no project definition"),
          ("comparedModuloT", Json.bool (!unreduced)), ("mirrorValuesEqualToT", Json.num (lib.filter (· == b.t)).size),
          ("recordedValuesEqualToT", Json.num (rawN.filter (· == b.t)).size)] ++
         (match first with
          | some i => [("first", Json.mkObj [("coeff", Json.num i), ("openfhe", natJ rawN[i]!), ("lean", natJ lib[i]!)])]
          | none => []) ++ ex)
      if !b.plain then continue
      -- (i) exact rounding: ⌊t·Φ/Q⌉ mod t with Φ the phase in [0, Q)
      let phiZ ← liftExcept (crt id b.N qs (toZ1 phi))
      let exact := phiZ.map fun (v : Int) => (((2 * (b.t : Int) * v + (Q : Int)) / (2 * (Q : Int))) % (b.t : Int)).toNat
      let diffs : Array Nat := (Array.range b.N).filter fun (i : Nat) => exact[i]! != rawN[i]! % b.t
      -- the phase of the first few differing coefficients, centred, and its distance to a rounding boundary
      let cen := fun (v : Int) => if 2 * v > (Q : Int) then v - (Q : Int) else v
      -- t·Φ/Q = n + f: the distance of f from the tie 1/2, in millionths
      let tiePpm := fun (v : Int) =>
        let r := (2 * (b.t : Int) * v + (Q : Int)) % (2 * (Q : Int))
        (min r (2 * (Q : Int) - r) * 1000000 / (2 * (Q : Int))).toNat
      let minTie := phiZ.foldl (fun acc v => min acc (tiePpm v)) 1000000
      let detail := (diffs.extract 0 4).map fun (i : Nat) =>
        let v := phiZ[i]!
        Json.mkObj [("coeff", Json.num i), ("openfhe", natJ rawN[i]!), ("exact", natJ exact[i]!),
                    ("centredPhase", intJ (cen v)), ("distanceFromTiePpm", Json.num (tiePpm v)), ("Q", natJ Q)]
      -- a ciphertext that is not an encryption under `s` (its phase under `s` is arbitrary): the
      -- trusted decryption does not apply to it; the differences are still counted
      let invalid := !why.isEmpty
      -- the library rounds in binary64: a differing coefficient whose exact value t·Φ/Q lies within
      -- the proved error δ (`Spec.DecryptBFV.delta`, plus 2⁻⁶⁴) of a rounding tie is allowed by
      -- the trusted `Spec.DecryptBFV.decrypt1` (whose bit-exact comparison is `a.decryptLib`); only a
      -- difference farther from every tie is a failure (the per-coefficient form of `decLibOK?`)
      let dl : ℚ := Spec.DecryptBFV.delta b.t qs.toList + 1 / 2 ^ 64
      let tieDist := fun (v : Int) =>
        let r := (2 * (b.t : Int) * v + (Q : Int)) % (2 * (Q : Int))
        ((min r (2 * (Q : Int) - r) : Int) : ℚ) / (2 * (Q : ℚ))
      let nearTie := diffs.all fun (i : Nat) => tieDist phiZ[i]! ≤ dl
      x.emit "algo.decrypt.exact" id "decrypt"
        (if diffs.isEmpty then some true else if invalid || nearTie then none else some false) "exact"
        ([("limbs", Json.num 1), ("coeffs", Json.num b.N), ("mismatches", Json.num diffs.size),
          ("fn", Json.str "Spec.Scheme.bfvDecrypt: round(t*phase/Q) mod t, exact"),
          ("minDistanceFromTiePpm", Json.num minTie)] ++
         (if diffs.isEmpty then [] else [("differing", Json.arr detail),
            ("why", Json.str ("the recorded decryption differs from the exact rounding on these coefficients" ++
              (if invalid then " (the ciphertext is not an encryption under s: reported, not a failure)"
               else if nearTie then " (each within the proved binary64 error delta of a rounding tie: allowed by Spec.DecryptBFV.decrypt1, reported, not a failure)"
               else "")))]) ++ ex)
      -- the trusted definition itself at small N
      if b.N ≤ x.o.litMaxN then
        let cts ← ct.parts.toList.mapM fun part => liftExcept (crt id b.N qs part)
        let sP : IntPoly b.N := ofArr b.s
        let ctP : List (Poly Q b.N) := cts.map fun z => ofInt Q (ofArr (N := b.N) z)
        let lit := (toArr b.K (Scheme.bfvDecrypt b.t sP ctP)).map fun (z : ZMod b.t) => z.val
        x.emit "algo.decrypt.literal-vs-staged" id "decrypt" (some (lit == exact)) "literal"
          ([("mismatches", Json.num (diffCount lit exact)), ("fn", Json.str "Spec.Scheme.bfvDecrypt")] ++ ex)
      -- for the record: the library's float procedure with exact sums / the other contraction
      if full && b.mult != "BEHZ" then
        for (name, g) in [("exact sum", decHpsF fma true b.t qs phi), ("other contraction", decHpsF (!fma) false b.t qs phi),
                          ("integer part kept out of the double", decHpsF fma false b.t qs phi true)] do
          x.emit "algo.variant.decrypt" id "decrypt" none "mirror-only"
            ([("variant", Json.str name), ("matches", boolJ (g == rawN)), ("coeffs", Json.num b.N),
              ("mismatches", Json.num (diffCount g rawN)), ("mismatchesVsExactRounding", Json.num (diffCount g exact))] ++ ex)
      if !full then
        for (name, g) in [("exact MultiplyAndRound", decSmallF fma true false b.t qs phi),
                          ("other contraction", decSmallF (!fma) false false b.t qs phi)] do
          x.emit "algo.variant.decrypt" id "decrypt" none "mirror-only"
            ([("variant", Json.str name), ("matches", boolJ (g == rawN)), ("coeffs", Json.num b.N),
              ("mismatches", Json.num (diffCount g rawN)), ("mismatchesVsExactRounding", Json.num (diffCount g exact))] ++ ex)
    catch e =>
      x.emit "algo.decrypt" id "decrypt" (some false) "mirror-only" [("why", Json.str s!"{e}")]

end BX

/-! ## The library's execution of the certified program -/

/-- **`algo.runLibrary`**: the locked `Challenge.CertifyBFV.runLibrary` (by the proved-equal
forced execution `runLibL`, `runLibrary_list`) on the recorded inputs and keys of a CERTIFIED
program, every intermediate and output ciphertext with a recorded object compared limb for
limb. -/
def BX.checkRunLibrary (b : BX) : IO Unit := do
  let x := b.x
  let c := x.c
  let emitP := fun (ok : Option Bool) (ex : List (String × Json)) =>
    x.emit "algo.runLibrary" "program" "runLibrary" ok "literal:Challenge.CertifyBFV.runLibrary" ex
  let .ok inp := FHE.Pin.BFV.decodeProg c
    | emitP none [("why", Json.str "no program (extractor refusal or no prog.fhecheck.json)")]
  let P := inp.base.P
  let .ok lay := FHE.Check.layoutOf P inp.base.ks
    | emitP none [("why", Json.str "no key-switching layout")]
  let x0 := FHE.Check.BFV.inputBFV inp lay
  if (Challenge.CertifyBFV.certifyBFV? x0).isNone then
    emitP none [("why", Json.str "the program is not certified (certifyBFV? = none): runLibrary is stated for certified programs")]
    return
  if P.src.N != c.N || P.src.qs != c.qs then
    emitP (some false) [("why", Json.str "the program's parameters are not pin.json's")]
    return
  if c.N > max x.o.libMaxN b.forcedMaxN then
    emitP none [("why", Json.str s!"N = {c.N} > max(--library-max-n {x.o.libMaxN}, forced cap {b.forcedMaxN}): the run uses the forced (proved-equal) multiplications and key switches, bounded like algo.mul's forced tier (--forced-max-n)")]
    return
  let prog := x0.prog
  let progJ := (jObj? c.progJson "program").getD Json.null
  let originOf : Spec.Source.Var → Option String := fun v =>
    (jArr progJ "inputs").findSome? fun d =>
      if jStr? d "name" == some v then (jObj? d "origin").bind (jStr? · "openfhe") else none
  let objOf : Spec.Source.Var → Option String := fun v =>
    if (c.object? v).isSome then some v else
      match v.splitOn "#" with
      | [base, (k : String)] => if k.all Char.isDigit && !k.isEmpty && (c.object? base).isSome then some base else none
      | _ => none
  let mut tab : Std.HashMap Spec.Source.Var (List (Array Int)) := {}
  for d in prog.inputs do
    let objId := if (c.object? d.name).isSome then d.name else (originOf d.name).getD d.name
    let o ← x.obj objId
    let qsO := x.qsArr o.towers
    let comps ← o.parts.toList.mapM fun part => liftExcept (crt objId c.N qsO part)
    tab := tab.insert d.name comps
  let tabF := tab
  let N := x0.P.src.N
  let cts : Spec.Source.Var → List (IntPoly N) := fun v => ((tabF[v]?).getD []).map fun a => ofArr a
  let rk := libKeys c N "relin" none
  let gk : ℕ → List (IntPoly N × IntPoly N) := fun g => libKeys c N "rot" (some g)
  let A := if b.fmaBuild then A64fma else A64
  let base := Trace.initCt x0.P prog cts
  let (tabL, ms) ← FHE.Pin.Algo.Cx.timedPure fun _ =>
    runLibL x0 A b.K rk gk base 0 prog.body (Spec.Source.initEnv x0.P.src prog fun _ => .exact 0) []
  let σ := envOf base tabL
  let mut nVars : Nat := 0
  let mut nCoeffs : Nat := 0
  let mut nBad : Nat := 0
  let mut nInstr : Nat := 0
  for i in prog.body do
    nInstr := nInstr + 1
    let d := Trace.dst i
    let some oid := objOf d | continue
    let some o := c.object? oid | continue
    if jStr? o "kind" != some "ct" then continue
    let some comps := σ d | continue
    let rec_ ← x.obj oid
    let qs := x.qsArr rec_.towers
    let got : Array (Array (Array Int)) := comps.toArray.map fun (p : IntPoly N) =>
      let pa := toArr b.K p
      qs.map fun (q : Nat) => pa.map (· % (q : Int))
    let r := cmpParts b.t qs rec_.parts got
    nVars := nVars + 1
    nCoeffs := nCoeffs + r.coeffs
    if !r.ok then nBad := nBad + 1
    x.emit "algo.runLibrary.var" oid "runLibrary" (some r.ok) "literal:Challenge.CertifyBFV.runLibrary"
      ([("variable", Json.str d), ("instruction", Json.str (Trace.dst i)), ("towers", Json.num rec_.towers),
        ("parts", Json.num rec_.parts.size)] ++ r.json)
  emitP (some (nBad == 0))
    [("instructions", Json.num nInstr), ("ciphertexts", Json.num nVars), ("coeffs", Json.num nCoeffs),
     ("ciphertextsDiffering", Json.num nBad), ("ms", Json.num ms),
     ("float", Json.str (if b.fmaBuild then "A64fma" else "A64")),
     ("fn", Json.str "Challenge.CertifyBFV.runLibrary (locked) by runLibL (runLibrary_list), keys from pin.json evalKeys")]

/-! ## Walking the trace -/

partial def walk (b : BX) (rot : Option Nat) (f : Frame) : IO Unit := do
  let x := b.x
  let fn := f.fn
  let isAuto := fn.startsWith "LeveledSHEBFVRNS::EvalAutomorphism("
  let rot' : Option Nat := if isAuto then (f.int? "index").map (·.toNat) else none
  for k in f.kids do walk b rot' k
  let ins := Frame.cts f.ins
  let outs := f.outs.filter (·.kind == "ct")
  let key := fun (op : String) (as : Array Arg) (o : Arg) =>
    s!"{op}/{String.intercalate "," (as.map (·.id)).toList}/{o.id}"
  let lin := x.want "lin"
  let ld := f.int? "levelsDropped"
  try
    if fn.startsWith "LeveledSHEBase::EvalAddCoreInPlace(Ciphertext,Ciphertext)"
        || fn.startsWith "LeveledSHEBase::EvalSubCoreInPlace(Ciphertext,Ciphertext)" then
      let sub := has fn "EvalSub"
      if lin && ins.size ≥ 2 && outs.size ≥ 1 then if ← x.fresh (key (if sub then "sub" else "add") ins outs[0]!) then
        b.checkAddCore sub (← x.obj ins[0]!.id) (← x.obj ins[1]!.id) (← x.obj outs[0]!.id)
    else if fn.startsWith "LeveledSHEBase::EvalNegateInPlace" then
      if lin && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "neg" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        b.fmt.modify (·.insert o.id (← b.flagsOf a))
        x.hom "algo.negate" "negate" [a] o fun l => (l.getD 0 []).map (- ·)
    else if fn == "LeveledSHEBFVRNS::EvalAddInPlace(Ciphertext,Plaintext)"
        || fn == "LeveledSHEBFVRNS::EvalSubInPlace(Ciphertext,Plaintext)" then
      if lin && ins.size ≥ 2 && outs.size ≥ 1 then if ← x.fresh (key "addPlain" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let p ← x.obj ins[1]!.id
        let o ← x.obj outs[0]!.id
        b.checkAddPlain (has fn "EvalSub") a p o (baseName fn)
    else if fn.startsWith "LeveledSHERNS::EvalMultInPlace(ciphertext, plaintext)"
        || fn.startsWith "LeveledSHERNS::EvalMult(ciphertext, plaintext)" then
      if lin && ins.size ≥ 2 && outs.size ≥ 1 then if ← x.fresh (key "mulPlain" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let p ← x.obj ins[1]!.id
        let o ← x.obj outs[0]!.id
        if !(← x.explained.get).contains o.id then
          b.checkMulPlain a p o (baseName fn)
    else if fn == "LeveledSHEBFVRNS::EvalMultCoreInPlace(Ciphertext,NativeInteger)" then
      if lin && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "mulConst" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        let cst := (f.int? "constant").getD 0
        b.fmt.modify (·.insert o.id (← b.flagsOf a))
        x.hom "algo.mulConst" "mulConst" [a] o (fun l => (l.getD 0 []).map (cst • ·)) [("constant", intJ cst)]
    else if fn == "LeveledSHEBFVRNS::EvalMult(Ciphertext,Ciphertext)" then
      if x.want "tensor" && ins.size ≥ 2 && outs.size ≥ 1 then if ← x.fresh (key "mul" ins outs[0]!) then
        b.checkMul (← x.obj ins[0]!.id) (← x.obj ins[1]!.id) (← x.obj outs[0]!.id) ld "EvalMult(Ciphertext,Ciphertext)"
    else if fn.startsWith "CryptoContext::EvalMultNoRelinNoCheck(" && f.kids.isEmpty then
      -- `CryptoContext::EvalMultNoRelinNoCheck` (`cryptocontext.h:2299`): the bare tensor product of
      -- the stored components (no scaling by t/Q, no base extension): a ring operation per limb
      if x.want "tensor" && ins.size ≥ 2 && outs.size ≥ 1 then if ← x.fresh (key "tensor" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let c ← x.obj ins[1]!.id
        let o ← x.obj outs[0]!.id
        b.taint o.id "the bare tensor product of EvalMultNoRelinNoCheck (not scaled by t/Q): not a BFV ciphertext"
        if a.parts.size == 2 && c.parts.size == 2 then
          x.hom "algo.tensor" "tensor" [a, c] o (fun l => Challenge.Source.tensor (l.getD 0 []) (l.getD 1 []))
            [("via", Json.str "EvalMultNoRelinNoCheck"), ("fn", Json.str "Challenge.Source.tensor")]
        else
          x.hom "algo.tensorN" "tensor" [a, c] o (fun l => tensorGen (l.getD 0 []) (l.getD 1 []))
            [("via", Json.str "EvalMultNoRelinNoCheck"), ("fn", Json.str "FHE.Pin.Algo.tensorGen (convolution; not a project definition)")]
    else if fn == "LeveledSHEBFVRNS::EvalSquare(Ciphertext)" then
      if x.want "tensor" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "square" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        b.checkMul a a (← x.obj outs[0]!.id) ld "EvalSquare(Ciphertext)"
    else if fn == "LeveledSHEBFVRNS::RelinearizeCore(Ciphertext,EvalKey)" then
      if x.want "ks" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "relin" ins outs[0]!) then
        b.checkRelinCore (← x.obj ins[0]!.id) (← x.obj outs[0]!.id) ld rot "RelinearizeCore"
    else if fn.startsWith "LeveledSHEBase::RelinearizeInPlace(" then
      if x.want "ks" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "relin" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        if a.parts.size ≤ 2 then
          x.explain o.id
          let _ ← x.report "algo.relin" "relin" "limb" o a.parts 0
            [BX.ops [a], ("via", Json.str "Relinearize of 2 parts: a copy")]
        else b.checkRelinBase a o "LeveledSHEBase::RelinearizeInPlace"
    else if isAuto then
      if x.want "ks" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "automorph" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        let r ← match f.kids.back? with
          | some k => match (k.outs.filter (·.kind == "ct"))[0]? with
            | some ro => x.obj ro.id
            | none => throw (IO.userError "EvalAutomorphism: no traced RelinearizeCore output")
          | none => throw (IO.userError "EvalAutomorphism: no traced RelinearizeCore")
        b.taint r.id (s!"the output of RelinearizeCore inside EvalAutomorphism (index {rot'.getD 0}), before the automorphism: an encryption under the automorphism of s by the inverse index, not under s")
        b.checkAutomorph a r o (rot'.getD 0) "EvalAutomorphism"
    else if fn == "LeveledSHEBFVRNS::Compress(Ciphertext,size_t)" then
      if x.want "modreduce" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "compress" ins outs[0]!) then
        b.checkCompress (← x.obj ins[0]!.id) (← x.obj outs[0]!.id) "Compress"
    -- an output no rule explained: a copy (same polynomials, new metadata) of the last child's
    -- output or of an input?
    if x.o.only.isNone then
      for o in outs do
        if !(← x.explained.get).contains o.id then
          let cands := (match f.kids.back? with
            | some k => k.outs.filter (·.kind == "ct")
            | none => #[]) ++ ins.filter (·.kind == "ct")
          let oo ← x.obj o.id
          for cnd in cands do
            if cnd.id != o.id && !(← x.explained.get).contains o.id then
              let co ← x.obj cnd.id
              if co.parts == oo.parts then
                b.fmt.modify (·.insert o.id (← b.flagsOf co))
                x.explain o.id
                let _ ← x.report "algo.copy" "copy" "limb" oo co.parts 0
                  [BX.ops [co], ("via", Json.str (baseName fn)),
                   ("why", Json.str "same polynomials; only the metadata (hence the id) changed")]
    -- an output computed from a ciphertext that is not a valid encryption under `s` is not one either
    let bad ← b.notUnderS.get
    match (ins.filter (·.kind == "ct")).find? fun i => bad.contains i.id with
    | some i =>
      for o in outs do
        if o.id != i.id then b.taint o.id s!"computed from {i.id}: {(bad[i.id]?).getD ""}"
    | none => pure ()
  catch e =>
    x.emit "algo.error" ((outs[0]?.map (·.id)).getD "?") fn (some false) "glue"
      [("why", Json.str s!"{e}"), ("line", Json.num f.line)]

/-- Add the scheme fields to a result line. -/
def tag (b : BX) (j : Json) : Json :=
  let add := fun (j : Json) (k : String) (v : Json) =>
    match j.getObjVal? k with
    | .ok _ => j
    | .error _ => j.setObjVal! k v
  let j := add j "scheme" (Json.str "BFV")
  let j := add j "mult" (Json.str b.mult)
  let j := add j "ks" (Json.str b.ksT)
  let j := add j "enc" (Json.str b.enc)
  if b.m.isNone then j else add j "mutate" (Json.str b.m.name)

/-- **Entry point.** Every `algo.*` comparison of one loaded BFV case. Never throws. -/
def runCase (c : Case) (o : FHE.Pin.Algo.Opts := {}) : IO (Array Json) := do
  let out ← IO.mkRef (#[] : Array Json)
  let seen ← IO.mkRef {}
  let explained ← IO.mkRef {}
  let nKS ← IO.mkRef 0
  let nTensor ← IO.mkRef 0
  let x : FHE.Pin.Algo.Cx := { c, o, out, seen, explained, nKS, nTensor }
  let bj := (jObj? c.pin "bfv").getD Json.null
  let fl := (jObj? ((jObj? c.pin "build").getD Json.null) "float").getD Json.null
  let s := match (jStr? c.pin "secret").map c.intPoly with
    | some (.ok s) => s
    | _ => #[]
  let b : BX :=
    { x, mult := (jStr? bj "mult").getD "?", ksT := (jStr? bj "ks").getD "?",
      enc := (jStr? bj "enc").getD "?",
      aux := natArr bj "auxR", bsk := natArr bj "behzBsk", mt := natOf bj "behzMtilde",
      gamma := natOf bj "behzGamma", extPrime := natOf bj "extendedPrime",
      fmaBuild := jBool fl "fmaContraction",
      dnum := (jNat? bj "dnum").getD 0, alpha := (jNat? bj "towersPerDigit").getD 0,
      digitSize := (jNat? bj "digitSizeBV").getD 0,
      m := (AlgoMut.ofString? o.mutName).getD {},
      L := c.qs.length, s, nLit := ← IO.mkRef 0, notUnderS := ← IO.mkRef {},
      fmt := ← IO.mkRef {}, roots := ← IO.mkRef {} }
  try
    x.emit "algo.info" "bfv" "info" none "glue"
      [("why", Json.str "information"), ("float", Json.str b.arithName),
       ("fmaContraction", boolJ b.fmaBuild), ("towers", Json.num b.L),
       ("aux", Json.num b.aux.size), ("digitSizeBV", Json.num b.digitSize)]
    if x.want "encrypt" then b.checkEncrypt
    let tracePath : System.FilePath := (c.dir : System.FilePath) / "trace.jsonl"
    if !(← tracePath.pathExists) then
      x.emit "algo.trace" "trace.jsonl" "load" none "glue" [("why", Json.str "no trace.jsonl")]
    else
      let roots := parseTrace (← IO.FS.readFile tracePath)
      for f in roots do walk b none f
      if o.only.isNone then
        let produced := roots.foldl (fun a f => producedIds f a) #[]
        let ex ← x.explained.get
        let missing := produced.filter fun id => !ex.contains id
        x.emit "algo.coverage" "trace.jsonl" "coverage" (if missing.isEmpty then some true else none) "glue"
          [("produced", Json.num produced.size), ("explained", Json.num (produced.size - missing.size)),
           ("unexplained", Json.arr (missing.map Json.str)),
           ("why", Json.str (if missing.isEmpty then "every ciphertext the trace produces is the output of a compared operation"
              else "ciphertexts produced by operations this module does not compare"))]
    if x.want "decrypt" then b.checkDecrypt
    if x.want "library" && b.plain then
      match ← b.checkRunLibrary.toBaseIO with
      | .error e => x.emit "algo.runLibrary" "program" "runLibrary" (some false) "glue" [("why", Json.str s!"{e}")]
      | .ok _ => pure ()
  catch e =>
    x.emit "algo.error" "case" "case" (some false) "glue" [("why", Json.str s!"{e}")]
  return (← out.get).map (tag b)

end FHE.Pin.BFV.Algo
