import FHE.Pin.AlgoMutants
import FHE.Pin.AlgoOpenFHE
import FHE.Pin.AlgoLocked
import FHE.Pin.Core
import FHE.KeySwitch.Layout
import Challenge.Source

/-!
# FHE.Pin.Algo — the proved reference algorithms against OpenFHE, limb by limb   (UNTRUSTED glue)

For every operation OpenFHE performed in a dumped run (`trace.jsonl`), the **exact exported
inputs** are fed to the corresponding Lean function and the result is compared with OpenFHE's
exported output, RNS limb by RNS limb, coefficient by coefficient (`check` names `algo.*`).

| OpenFHE operation | Lean function |
|---|---|
| `Encrypt` | `Spec.Encrypt.encrypt` on the stored plaintext polynomial |
| `EvalAddCore`, `EvalSubCore` (any numbers of parts), plaintext add/sub | `Challenge.Source.padZip (· + ·)`, `(· - ·)` |
| `EvalNegate`, multiplication by a constant, by a plaintext | `-·`, `c • ·`, `c * ·` of `Spec.NPoly` |
| `EvalMultCore`, `EvalSquareCore` | `Challenge.Source.tensor` (2×2), its convolution generalisation otherwise |
| key switching: `Relinearize`, `EvalMult` with key | `relinOpenFHE` (`FHE.KeySwitch.keySwitchBGVOpenFHE`, then `+`), run staged: `addKS_openfhe` |
| `EvalAutomorphism`, `EvalRotate` (v1.6.1) | `rotateOpenFHE161` (canonical ModUp, inner products with the key for `g` over `Q_ℓ·P`, `+ P·c₀`, `Spec.NPoly.automorph g`, then OpenFHE's BGV ModDown), run staged: `rotStaged161_openfhe` |
| `ModReduce` | `FHE.RNS.Basis.bgvModSwitchPoly` (RNS) and `Challenge.Source.bgvModSwitchComp` (integers) |
| `LevelReduce` | the limbs are dropped |

**Coefficient format.** OpenFHE computes in evaluation (NTT) format; the exporter converted
every polynomial with OpenFHE's own inverse NTT, so all comparisons are in the coefficient domain
and rely on OpenFHE's NTT being the ring isomorphism. The `algo.tensor` comparisons pin exactly
that: the trusted negacyclic `*` of two dumped polynomials equals OpenFHE's pointwise product.

**Ring homomorphic operations** (`+ − · σ`, hence `padZip`, `tensor`, `encrypt`) are run on the
residues of each limb (as integer representatives) and reduced modulo that limb's prime
(`impl = "limb"`); at `N ≤ litMaxN` they are also run on the CRT-lifted integer polynomials
(`impl = "crt"`). Key switching and modulus switching are not limbwise and are run on all limbs.
-/

namespace FHE.Pin.Algo
open Lean Spec Spec.NPoly FHE.RNS FHE.KeySwitch FHE.Pin

/-- Options of the algorithm-level comparison. -/
structure Opts where
  /-- Chunks (tasks) per forced polynomial. -/
  K : Nat := 32
  /-- Largest `N` at which the literal (unstaged) key switch and the CRT-level operations are
  also run. -/
  litMaxN : Nat := 16
  /-- Largest `N` at which the other existing key-switching variants (`keySwitchBGV`,
  `keySwitchBGVAddDown`) are also run, for the record. -/
  variantsMaxN : Nat := 64
  /-- Largest `N` at which the locked `Challenge.CertifyBFV.runLibrary` is executed on a recorded
  BFV program (`algo.runLibrary`, by the proved-equal forced execution `runLibL`), besides the
  forced cap `max (16 · litMaxN) forcedMaxN`, whichever is larger. 64 covers every committed BFV
  fixture. -/
  libMaxN : Nat := 64
  /-- Largest `N` at which the BFV products are also run as the locked definitions with forced
  intermediates (`hpsForced_eq` …), besides the staged mirror: `max (16 · litMaxN) forcedMaxN`
  (default `256`). The forced products are Kronecker products (`FHE.Pin.mulArr`), so real sizes
  are feasible: `--forced-max-n 32768`. -/
  forcedMaxN : Nat := 0
  mu : AMut := .none
  mutName : String := "none"
  /-- Operation groups to run (`encrypt`, `lin`, `tensor`, `ks`, `modreduce`); `none`: all. -/
  only : Option (List String) := none
  /-- At most this many key-switching operations per case. -/
  maxKS : Option Nat := none
  /-- At most this many tensor products per case. -/
  maxTensor : Option Nat := none
  verbose : Bool := false

/-- The comparison options matching the checker's options. -/
def Opts.ofPin (o : FHE.Pin.Opts) : Opts := { K := o.K, litMaxN := o.litMaxN }

/-! ## Trace frames -/

structure Arg where
  name : String
  kind : String
  id : String := ""
  v : Int := 0
  deriving Inhabited

structure Frame where
  fn : String
  ins : Array Arg := #[]
  outs : Array Arg := #[]
  kids : Array Frame := #[]
  line : Nat := 0

instance : Inhabited Frame := ⟨{ fn := "" }⟩

def argOf (j : Json) : Arg :=
  { name := (jStr? j "name").getD "", kind := (jStr? j "kind").getD "",
    id := (jStr? j "id").getD "",
    v := match j.getObjVal? "v" with
      | .ok v => (v.getInt?.toOption).getD 0
      | _ => 0 }

/-- Parse `trace.jsonl` into the forest of call frames. -/
def parseTrace (text : String) : Array Frame := Id.run do
  let mut roots : Array Frame := #[]
  let mut stack : Array Frame := #[]
  let mut ln := 0
  for l in text.splitOn "\n" do
    ln := ln + 1
    if l.isEmpty then continue
    let .ok j := Json.parse l | continue
    match jStr? j "ev" with
    | some "begin" => stack := stack.push { fn := (jStr? j "fn").getD "", line := ln }
    | some "in" =>
      if let some f := stack.back? then stack := stack.pop.push { f with ins := f.ins.push (argOf j) }
    | some "out" =>
      if let some f := stack.back? then stack := stack.pop.push { f with outs := f.outs.push (argOf j) }
    | some "end" =>
      if let some f := stack.back? then
        stack := stack.pop
        match stack.back? with
        | some p => stack := stack.pop.push { p with kids := p.kids.push f }
        | none => roots := roots.push f
    | _ => pure ()
  return roots

def Frame.cts (a : Array Arg) : Array Arg := a.filter fun x => x.kind == "ct" || x.kind == "pt"

def Frame.int? (f : Frame) (name : String) : Option Int :=
  (f.ins.find? fun a => a.kind == "int" && a.name == name).map (·.v)

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The function name of a frame without its argument list. -/
def baseName (fn : String) : String := (fn.splitOn "(").headD fn

/-- Evaluate `f ()` as one sequenced step (so that it can be timed). -/
@[noinline] def forceIO {α : Type} (f : Unit → α) : IO α := pure (f ())

/-! ## Objects and comparison -/

/-- A dumped ciphertext / plaintext: `parts[part][limb][coefficient]`, canonical residues. -/
structure Obj where
  id : String
  kind : String
  towers : Nat
  parts : Array (Array (Array Int))
  deriving Inhabited

def loadObj (c : Case) (id : String) : Except String Obj := do
  let some o := c.object? id | throw s!"pin.json has no object {id}"
  let some towers := jNat? o "towers" | throw s!"object {id}: towers"
  let kind := (jStr? o "kind").getD "?"
  let names : List String :=
    if kind == "pt" then (jStr? o "poly").toList
    else (jArr o "polys").toList.filterMap fun j => j.getStr?.toOption
  if names.isEmpty then throw s!"object {id}: no polys"
  let expect := c.qs.take towers
  let mut parts := #[]
  for nm in names do
    let some e := c.polys[nm]? | throw s!"polys.txt has no entry {nm}"
    if e.moduli.toList != expect then
      throw s!"{nm}: limb moduli {e.moduli.toList} are not the expected {expect}"
    parts := parts.push e.limbs
  return { id, kind, towers, parts }

/-- Result of a limb-by-limb comparison. -/
structure Cmp where
  shapeOK : Bool := true
  limbs : Nat := 0
  coeffs : Nat := 0
  mism : Nat := 0
  /-- first difference: part, limb, coefficient, OpenFHE's value, Lean's value -/
  first : Option (Nat × Nat × Nat × Int × Int) := none
  /-- every difference (centred modulo the limb) is a multiple of `t` -/
  allDivT : Bool := true
  maxAbsDiff : Nat := 0
  deriving Inhabited

def Cmp.ok (r : Cmp) : Bool := r.shapeOK && r.mism == 0

/-- Compare OpenFHE's `exp[part][limb]` with Lean's `got[part][limb]`; `qs` are the limb moduli. -/
def cmpParts (t : Nat) (qs : Array Nat) (exp got : Array (Array (Array Int))) : Cmp := Id.run do
  let mut r : Cmp := {}
  if exp.size != got.size then return { r with shapeOK := false }
  for p in [0:exp.size] do
    let e := exp[p]!
    let g := got[p]!
    if e.size != g.size then return { r with shapeOK := false }
    for i in [0:e.size] do
      let el := e[i]!
      let gl := g[i]!
      if el.size != gl.size then return { r with shapeOK := false }
      r := { r with limbs := r.limbs + 1, coeffs := r.coeffs + el.size }
      if el != gl then
        let q : Int := qs[i]!
        for c in [0:el.size] do
          if el[c]! != gl[c]! then
            let d := (gl[c]! - el[c]!) % q
            let d := if 2 * d > q then d - q else d
            r := { r with mism := r.mism + 1,
                          first := r.first.orElse fun _ => some (p, i, c, el[c]!, gl[c]!),
                          allDivT := r.allDivT && d % (t : Int) == 0,
                          maxAbsDiff := max r.maxAbsDiff d.natAbs }
  return r

def Cmp.json (r : Cmp) : List (String × Json) :=
  [("limbs", Json.num r.limbs), ("coeffs", Json.num r.coeffs), ("mismatches", Json.num r.mism)] ++
  (if r.shapeOK then [] else [("why", Json.str "shapes differ (parts / limbs / length)")]) ++
  (match r.first with
   | some (p, i, c, e, g) =>
     [("first", Json.mkObj [("part", Json.num p), ("limb", Json.num i), ("coeff", Json.num c),
        ("openfhe", intJ e), ("lean", intJ g)]),
      ("allDiffsMultipleOfT", boolJ r.allDivT), ("maxAbsDiffBits", bitsJ r.maxAbsDiff)]
   | none => [])

/-- `a[limb][part] ↦ a[part][limb]`. -/
def transpose (perLimb : Array (Array (Array Int))) : Array (Array (Array Int)) :=
  let nparts := (perLimb.map (·.size)).foldl max 0
  (Array.range nparts).map fun p => perLimb.map fun l => l[p]!

/-! ## Ring-homomorphic operations -/

/-- Run `g` on the residues of every limb (integer representatives), reduce modulo that limb. -/
def homLimb (N K : Nat) (qs : Array Nat) (ops : List (Array (Array (Array Int))))
    (g : List (List (IntPoly N)) → List (IntPoly N)) : Array (Array (Array Int)) :=
  transpose <| (Array.range qs.size).map fun i =>
    let ins : List (List (IntPoly N)) := ops.map fun o => o.toList.map fun part => ofArr (N := N) part[i]!
    (g ins).toArray.map fun p => valsOf (toArr K (ofInt qs[i]! p))

/-- Run `g` on the CRT lifts in `[0, Q)`, reduce modulo every limb. -/
def homCrt (N K : Nat) (qs : Array Nat) (ops : List (Array (Array (Array Int))))
    (g : List (List (IntPoly N)) → List (IntPoly N)) : Except String (Array (Array (Array Int))) := do
  let ins ← ops.mapM fun o => o.toList.mapM fun part =>
    (crt "operand" N (qs.extract 0 part.size) part).map fun z => (ofArr (N := N) z : IntPoly N)
  let outs := (g ins).map fun p => toArr K p
  return outs.toArray.map fun z => qs.map fun q => valsOf (toArr K (ofInt q (ofArr (N := N) z)))

/-- `Challenge.Source.tensor` with the products by Kronecker substitution (`mulArr`); equal to
it on all inputs (`tensorF_eq`). -/
def tensorF {N : Nat} (c d : List (IntPoly N)) : List (IntPoly N) :=
  match c, d with
  | [c₀, c₁], [d₀, d₁] =>
    let p00 := mulArr c₀ d₀
    let p01 := mulArr c₀ d₁
    let p10 := mulArr c₁ d₀
    let p11 := mulArr c₁ d₁
    [ofArr p00, ofArr p01 + ofArr p10, ofArr p11]
  | _, _ => []

theorem tensorF_eq {N : Nat} (c d : List (IntPoly N)) : tensorF c d = Challenge.Source.tensor c d := by
  rcases c with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, c'⟩⟩⟩ <;>
  rcases d with _ | ⟨d₀, _ | ⟨d₁, _ | ⟨d₂, d'⟩⟩⟩ <;>
  first
  | rfl
  | (show _ = [c₀ * d₀, c₀ * d₁ + c₁ * d₀, c₁ * d₁]; simp [tensorF])

/-- Convolution of two component lists: `out_k = Σ_{i+j=k} a_i · b_j` (OpenFHE's `EvalMultCore`
for any numbers of parts; for 2 × 2 it is `Challenge.Source.tensor`), every product by `mulArr`. -/
def tensorGen {N : Nat} (a b : List (IntPoly N)) : List (IntPoly N) :=
  if a.isEmpty || b.isEmpty then [] else
  ((List.range (a.length + b.length - 1)).map fun k =>
    (List.range a.length).foldl (fun (acc : Array ℤ) i =>
      if i ≤ k ∧ k - i < b.length then addArr N acc (mulArr (a.getD i 0) (b.getD (k - i) 0)) else acc)
      (Array.replicate N 0)).map ofArr

/-! ## Context -/

structure Cx where
  c : Case
  o : Opts
  out : IO.Ref (Array Json)
  seen : IO.Ref (Std.HashMap String Unit)
  explained : IO.Ref (Std.HashMap String Unit)
  nKS : IO.Ref Nat
  nTensor : IO.Ref Nat
  /-- The scheme parameters of the case (for the locked transcriptions `Challenge.Realize.*`);
  `none`: not run. -/
  P? : Option FullParams := none
  /-- The layout the extracted program declares (`FHE.Check.layoutOf`), if any. -/
  declLay? : Option Spec.Budget.KSLayout := none

namespace Cx

abbrev N (x : Cx) : Nat := x.c.N
abbrev t (x : Cx) : Nat := x.c.t
def K (x : Cx) : Nat := x.o.K

def want (x : Cx) (g : String) : Bool :=
  match x.o.only with
  | none => true
  | some l => l.contains g

def emit (x : Cx) (check id op : String) (ok : Option Bool) (impl : String)
    (extra : List (String × Json) := []) : IO Unit := do
  let base : List (String × Json) :=
    [("case", Json.str x.c.name), ("check", Json.str check), ("id", Json.str id),
     ("op", Json.str op), ("ok", optBoolJ ok), ("impl", Json.str impl),
     ("N", Json.num x.c.N), ("scaling", Json.str x.c.scaling), ("suite", Json.str x.c.generator)]
  let base := if x.o.mu = .none then base else base ++ [("mutate", Json.str x.o.mutName)]
  x.out.modify (·.push (Json.mkObj (base ++ extra)))

def obj (x : Cx) (id : String) : IO Obj := liftExcept (loadObj x.c id)

def qsArr (x : Cx) (towers : Nat) : Array Nat := (x.c.qs.take towers).toArray

/-- `true` the first time `key` is seen. -/
def fresh (x : Cx) (key : String) : IO Bool := do
  if (← x.seen.get).contains key then return false
  x.seen.modify (·.insert key ())
  return true

def explain (x : Cx) (id : String) : IO Unit := x.explained.modify (·.insert id ())

def timed {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  return (a, t1 - t0)

def timedPure {α : Type} (f : Unit → α) : IO (α × Nat) := timed (forceIO f)

/-- Emit one comparison. -/
def report (x : Cx) (check op impl : String) (out : Obj) (got : Array (Array (Array Int)))
    (ms : Nat) (extra : List (String × Json) := []) : IO Bool := do
  let r := cmpParts x.t (x.qsArr out.towers) out.parts got
  x.emit check out.id op (some r.ok) impl
    ([("towers", Json.num out.towers), ("parts", Json.num out.parts.size)] ++ r.json ++
     [("ms", Json.num ms)] ++ extra)
  return r.ok

/-- A ring-homomorphic operation: per limb, and on CRT lifts at small `N`. -/
def hom (x : Cx) (check op : String) (ops : List Obj) (out : Obj)
    (g : List (List (IntPoly x.N)) → List (IntPoly x.N)) (extra : List (String × Json) := []) :
    IO Unit := do
  x.explain out.id
  let qs := x.qsArr out.towers
  -- a 1-part (plaintext) operand with more towers than the result: OpenFHE's `DCRTPoly +=`/`*=`
  -- reads only the towers of the left operand, i.e. the extra limbs are dropped
  let truncated := ops.any fun o => o.parts.size == 1 && o.towers > out.towers
  let ops := ops.map fun o =>
    if o.parts.size == 1 && o.towers > out.towers then
      { o with towers := out.towers, parts := o.parts.map (·.extract 0 out.towers) }
    else o
  let extra := if truncated then extra ++ [("plaintextLimbsDropped", Json.bool true)] else extra
  if ops.any (·.towers != out.towers) then
    x.emit check out.id op (some false) "limb"
      ([("why", Json.str s!"operands have {ops.map (·.towers)} towers, the result {out.towers}")] ++ extra)
    return
  let ex := [("operands", Json.arr (ops.map (Json.str ·.id)).toArray),
             ("operandParts", Json.arr (ops.map (Json.num ·.parts.size)).toArray)] ++ extra
  let (got, ms) ← timedPure fun _ => homLimb x.N x.K qs (ops.map (·.parts)) g
  let _ ← x.report check op "limb" out got ms ex
  if x.N ≤ x.o.litMaxN && x.o.mu = .none then
    match homCrt x.N x.K qs (ops.map (·.parts)) g with
    | .ok got => let _ ← x.report check op "crt" out got 0 ex
    | .error e => x.emit check out.id op (some false) "crt" [("why", Json.str e)]

end Cx

/-! ## Encryption -/

def checkEncrypt (x : Cx) : IO Unit := do
  let N := x.N
  let t := x.t
  let some pub := jObj? x.c.pin "public" | return
  let (some bn, some an) := (jStr? pub "b", jStr? pub "a") | return
  let (some eb, some ea) := (x.c.polys[bn]?, x.c.polys[an]?)
    | x.emit "algo.encrypt" "pk" "encrypt" (some false) "limb" [("why", Json.str "public key missing")]
  for enc in jArr x.c.pin "encryptions" do
    let ctId := (jStr? enc "ct").getD "?"
    try
      let (some ptId, some un, some e1n, some e2n) :=
          (jStr? enc "pt", jStr? enc "u", jStr? enc "e1", jStr? enc "e2")
        | do
          x.emit "algo.encrypt" ctId "encrypt" none "limb"
            [("why", Json.str s!"randomness not captured ({(jStr? enc "randomness").getD "?"})")]
          continue
      let u ← liftExcept (x.c.intPoly un)
      let e1 ← liftExcept (x.c.intPoly e1n)
      let e2 ← liftExcept (x.c.intPoly e2n)
      let pt ← x.obj ptId
      let ct ← x.obj ctId
      x.explain ctId
      let qs := x.qsArr ct.towers
      if (eb.moduli.extract 0 ct.towers) != qs || (ea.moduli.extract 0 ct.towers) != qs
          || pt.towers < ct.towers then
        throw (IO.userError "public key / plaintext limbs do not start with the ciphertext's limbs")
      -- the stored plaintext polynomial as an integer polynomial: centred CRT lift over the
      -- ciphertext's limbs; the message is its reduction modulo t
      let Qct := qs.foldl (· * ·) 1
      let ptZ ← liftExcept (crt ptId N qs ((pt.parts[0]!).extract 0 ct.towers))
      let ptC : Array Int := toArr x.K (centered (ofInt Qct (ofArr (N := N) ptZ)))
      let m : Array (ZMod t) := toArr x.K (ofInt t (ofArr (N := N) ptC))
      -- stored plaintext = liftMsg m + t·k: `k = 0` for a packed plaintext (stored in [0, t)),
      -- `k ∈ {0, −1}` for a centred one, larger for a plaintext scaled without reduction mod t
      let kk : Array Int := toArr x.K
        (⟨fun i => ((ofArr (N := N) ptC).coeff i - (Encrypt.liftMsg (ofArr (N := N) m)).coeff i) / (t : Int)⟩ : IntPoly N)
      let kMax := normA N kk
      let negs := (kk.filter (· != 0)).size
      let pNorm := normA N ptC
      -- `Spec.Encrypt.encrypt t b a p u e₁ e₂` with `p` the stored plaintext polynomial, limb by limb
      let (got, ms) ← Cx.timedPure fun _ =>
        transpose <| (Array.range ct.towers).map fun i =>
          (encryptMF .none t (ofArr (N := N) eb.limbs[i]!) (ofArr ea.limbs[i]!) (ofArr ptC) (ofArr u)
              (ofArr e1) (ofArr e2)).toArray.map fun p => valsOf (toArr x.K (ofInt qs[i]! p))
      let r := cmpParts t qs ct.parts got
      x.emit "algo.encrypt" ctId "encrypt" (some r.ok) "limb"
        ([("towers", Json.num ct.towers), ("parts", Json.num 2)] ++ r.json ++
         [("ms", Json.num ms), ("storedPlaintextCoeffsOutsideZeroT", Json.num negs),
          ("storedNorm", natJ pNorm), ("storedNormExceedsTMinus1", boolJ (decide (pNorm > t - 1))),
          ("kMax", natJ kMax)])
    catch e =>
      x.emit "algo.encrypt" ctId "encrypt" (some false) "limb" [("why", Json.str s!"{e}")]

/-! ## Modulus switching -/

/-- One RNS modulus switch of one component from the limbs `qs.take (n+1)` (canonical `δ` if
`canon`), by the proved `bgvModSwitchPoly` / `bgvModSwitchCanon`. -/
def modSwitchRNS (N K t : Nat) (qs : List Nat) (canon : Bool) (limbs : Array (Array Int)) :
    Except String (Array (Array Int)) :=
  if hq : (∀ q ∈ qs, 0 < q) ∧ qs.Pairwise Nat.Coprime then
    match hℓ : limbs.size with
    | 0 => .error "no limbs"
    | n + 1 =>
      if h : n + 1 ≤ qs.length then
        let B : Basis (n + 1) := Basis.take qs (n + 1) h hq.1 hq.2
        let a : RNSPoly B N := ofFam B.q limbs
        .ok (forceFam K B.dropLast.q
          (if canon then B.mapCoeff (p := B.dropLast.q) (B.bgvModSwitchCanon t) a
           else B.bgvModSwitchPoly t a))
      else .error "more limbs than the chain"
  else .error "the chain is not positive and pairwise coprime"

/-- `levels` RNS modulus switches of every component. -/
def modReduceRNS (N K t : Nat) (qs : List Nat) (canon : Bool) (levels : Nat)
    (parts : Array (Array (Array Int))) : Except String (Array (Array (Array Int))) :=
  parts.mapM fun limbs => do
    let mut cur := limbs
    for _ in [0:levels] do
      cur ← modSwitchRNS N K t qs canon cur
    return cur

/-- `levels` integer-level modulus switches (`Challenge.Source.bgvModSwitchComp`) of the CRT lift
of every component, reduced modulo the remaining limbs. -/
def modReduceInt (N K t : Nat) (qs : List Nat) (levels : Nat)
    (parts : Array (Array (Array Int))) : Except String (Array (Array (Array Int))) :=
  parts.mapM fun limbs => do
    let ℓ := limbs.size
    let mut cur ← crt "operand" N (qs.take ℓ).toArray limbs
    for r in [0:levels] do
      let q := qs.getD (ℓ - 1 - r) 0
      cur := toArr K (Challenge.Source.bgvModSwitchComp t q (ofArr (N := N) cur))
    return ((qs.take (ℓ - levels)).toArray.map fun q => valsOf (toArr K (ofInt q (ofArr (N := N) cur))))

def checkModReduce (x : Cx) (a out : Obj) (levels : Nat) : IO Unit := do
  x.explain out.id
  let ex := [("operands", Json.arr #[Json.str a.id]), ("levels", Json.num levels),
             ("fromTowers", Json.num a.towers)]
  let canon := x.o.mu = .modReduceCanon
  let (r, ms) ← Cx.timedPure fun _ => modReduceRNS x.N x.K x.t x.c.qs canon levels a.parts
  match r with
  | .ok got =>
    let _ ← x.report "algo.modReduce" "modReduce"
      (if canon then "rns:bgvModSwitchCanon" else "rns:bgvModSwitchPoly") out got ms ex
  | .error e => x.emit "algo.modReduce" out.id "modReduce" (some false) "rns" [("why", Json.str e)]
  if x.o.mu = .none then
    let (r, ms) ← Cx.timedPure fun _ => modReduceInt x.N x.K x.t x.c.qs levels a.parts
    match r with
    | .ok got => let _ ← x.report "algo.modReduce" "modReduce" "int:bgvModSwitchComp" out got ms ex
    | .error e => x.emit "algo.modReduce" out.id "modReduce" (some false) "int" [("why", Json.str e)]
    -- for the record: the canonical-δ variant
    match modReduceRNS x.N x.K x.t x.c.qs true levels a.parts with
    | .ok got =>
      let r := cmpParts x.t (x.qsArr out.towers) out.parts got
      x.emit "algo.variant.modReduce" out.id "modReduce" none "rns:bgvModSwitchCanon"
        ([("matches", boolJ r.ok), ("why", Json.str "for the record: the canonical-δ variant")] ++ r.json ++ ex)
    | .error _ => pure ()

/-! ## Key switching -/

/-- The digit sizes OpenFHE uses with `ℓ` towers (`keyswitch-hybrid.cpp:340-345`): digits of
`alpha` towers, the last one shorter; at most `numPartQ` digits. -/
def digitSizes (alpha numPartQ ℓ : Nat) : List Nat :=
  if alpha == 0 then [] else
  let n := min ((ℓ + alpha - 1) / alpha) numPartQ
  (List.range n).map fun j => if j + 1 == n then ℓ - alpha * j else alpha

/-- What is done with the key-switched pair `(KS₀, KS₁)` of the component `d`. -/
inductive KSOp
  /-- `(c₀ + KS(d)₀, c₁ + KS(d)₁)`: `relinOpenFHE`. -/
  | add (c0 c1 : Array (Array Int))
  /-- OpenFHE v1.6.1: `(ModDown(σ_g(P·c₀ + ⟨ModUp d, kb⟩)), ModDown(σ_g(⟨ModUp d, ka⟩)))`:
  `rotateOpenFHE161`. -/
  | rot (g : Nat) (c0 : Array (Array Int))
  /-- OpenFHE v1.3.1's order `(σ_g(c₀ + KS(d)₀), σ_g(KS(d)₁))`: `rotateOpenFHE` (for the record). -/
  | rotLast (g : Nat) (c0 : Array (Array Int))
  /-- MUTANT: `σ_g` first: `(σ_g(c₀) + KS(σ_g(d))₀, KS(σ_g(d))₁)` with the same key. -/
  | rotFirst (g : Nat) (c0 : Array (Array Int))

/-- One ciphertext-level key-switching operation `op` on the component `d` (limbs over
`qs.take ℓ`) with the key digits `keyB`, `keyA` (CRT-lifted to `[0, Q_ℓ·P)`), by the stages `m`
selects, staged (`addKS`, `rotStaged161`; equal to `relinOpenFHE`, `rotateOpenFHE161` for
`m = none` by `addKS_openfhe`, `rotStaged161_openfhe`). `literal`: call the unstaged definitions themselves and
force only the result. -/
def runKS (N K t : Nat) (qs special : List Nat) (ℓ : Nat) (sizes : List Nat) (m : AMut)
    (literal : Bool) (op : KSOp) (d : Array (Array Int)) (keyB keyA : Array (Array Int)) :
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
            let S : Stages Dg C Bp N := mutStages Dg C Bp m t
            match op with
            | .add c0 c1 =>
              let f0 : RNSPoly C N := ofFam C.q c0
              let f1 : RNSPoly C N := ofFam C.q c1
              if literal then
                let r : RNSPoly C N × RNSPoly C N :=
                  match m with
                  | .none => relinOpenFHE Dg C Bp t f0 f1 a kb ka
                  | _ => addPipe S f0 f1 a kb ka
                .ok (forceFam K C.q r.1, forceFam K C.q r.2)
              else .ok (addKS S K f0 f1 a kb ka)
            | .rot g c0 =>
              -- OpenFHE v1.6.1: σ_g over Q_ℓ·P, before ModDown (`rotateOpenFHE161`)
              let f0 : RNSPoly C N := ofFam C.q c0
              if literal then
                let r : RNSPoly C N × RNSPoly C N :=
                  match m with
                  | .none => rotateOpenFHE161 Dg C Bp t g f0 a kb ka
                  | _ => rotPipe161 S g f0 a kb ka
                .ok (forceFam K C.q r.1, forceFam K C.q r.2)
              else .ok (rotStaged161 S K g f0 a kb ka)
            | .rotLast g c0 =>
              -- OpenFHE v1.3.1's order: ModDown, add c₀, then σ_g (`rotateOpenFHE`)
              let f0 : RNSPoly C N := ofFam C.q c0
              if literal then
                let r : RNSPoly C N × RNSPoly C N :=
                  match m with
                  | .none => rotateOpenFHE Dg C Bp t g f0 a kb ka
                  | _ => rotPipe S g f0 a kb ka
                .ok (forceFam K C.q r.1, forceFam K C.q r.2)
              else .ok (rotStaged S K g f0 a kb ka)
            | .rotFirst g c0 =>
              let s0 := autoFam C.q g (fun i => ofFam (N := N) C.q c0 i)
              let s1 := autoFam C.q g (fun i => a i)
              let o := ksStaged S K (ofFam C.q s1) kb ka
              .ok (forceFam K C.q (fun i => ofFam (N := N) C.q s0 i + ofFam (N := N) C.q o.1 i), o.2)
        else .error s!"digit sizes {sizes} do not sum to {ℓ}"
      else .error "more towers than the chain"
    else .error "the special primes are not positive and pairwise coprime"
  else .error "the chain is not positive and pairwise coprime"

/-! ## The LOCKED transcriptions (`Challenge.Realize`)

`runLocked` evaluates, for the parameters `P` of the case and the layout whose digit sizes are
`sizes` (canonical), either

* `staged = true`: **exactly the left-hand side of `addKS_locked` / `rotStaged161_locked`**
  (`FHE/Pin/AlgoLocked.lean`): `addKS` / `rotStaged161` with the OpenFHE stages on the bases
  `Basis.take P.src.qs ℓ`, `Basis.ofList (P.store.special.map (·.q))`, `digitsOfSizes (sizes ℓ)`,
  operands `C.toRNS c` of the CRT lifts `c` of the operand limbs, keys read through
  `keys.getD j (0, 0)`. The theorems say that this is, limb for limb, the RNS form of the locked
  `Challenge.Realize.relinOpenFHE P lay ℓ [c₀, c₁, c₂] keys` /
  `Challenge.Realize.rotateOpenFHE161 P lay ℓ g [c₀, c₁] keys`, under `SchemeParamsOK P`,
  `SpecialOK P` and `lay.okAt ℓ`, which the caller decides (`schemeParamsOK?`, `specialOK?`, `okAt`);
* `staged = false`: the locked definition itself, applied literally to the CRT lifts (small `N`
  only), each output component forced once and reduced modulo every limb. -/
def runLocked (P : FullParams) (sizes : Nat → List Nat) (K ℓ : Nat) (staged : Bool) (op : KSOp)
    (d : Array (Array Int)) (keyB keyA : Array (Array Int)) :
    Except String (Array (Array Int) × Array (Array Int)) :=
  let lay : Spec.Budget.KSLayout := { sizes, canonical := true }
  let N := P.src.N
  let qsl := (P.src.qs.take ℓ).toArray
  let lift := fun (nm : String) (limbs : Array (Array Int)) =>
    (crt nm N qsl limbs).map fun z => (ofArr (N := N) z : IntPoly N)
  let keys : List (IntPoly N × IntPoly N) := (List.range keyB.size).map fun j =>
    (ofArr (N := N) keyB[j]!, ofArr (N := N) keyA[j]!)
  if hpos : ∀ q ∈ P.src.qs, 0 < q then
  if hcop : P.src.qs.Pairwise Nat.Coprime then
  if hppos : ∀ q ∈ P.store.special.map (·.q), 0 < q then
  if hpcop : (P.store.special.map (·.q)).Pairwise Nat.Coprime then
  if hℓ : ℓ ≤ P.src.qs.length then
  if hs : (lay.sizes ℓ).sum = ℓ then
  if hN : N = 0 then .error "N = 0" else
    haveI : NeZero P.src.N := ⟨hN⟩
    let C : FHE.RNS.Basis ℓ := FHE.RNS.Basis.take P.src.qs ℓ hℓ hpos hcop
    let Bp := FHE.RNS.Basis.ofList (P.store.special.map (·.q)) hppos hpcop
    let Dg := digitsOfSizes (lay.sizes ℓ) ℓ hs
    let kb : Fin Dg.dnum → Poly (C.prod * Bp.prod) P.src.N := fun j => ofInt _ (keys.getD j (0, 0)).1
    let ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) P.src.N := fun j => ofInt _ (keys.getD j (0, 0)).2
    let reduce := fun (L : List (IntPoly N)) =>
      let z0 := toArr K (L.getD 0 0)
      let z1 := toArr K (L.getD 1 0)
      let red := fun (z : Array Int) => qsl.map fun q => valsOf (toArr K (ofInt q (ofArr (N := N) z)))
      (red z0, red z1)
    match op with
    | .add c0 c1 => do
      let l0 ← lift "c0" c0
      let l1 ← lift "c1" c1
      let l2 ← lift "c2" d
      if staged then
        pure (addKS (openfheStages Dg C Bp P.src.t) K (C.toRNS l0) (C.toRNS l1) (C.toRNS l2) kb ka)
      else
        pure (reduce (Challenge.Realize.relinOpenFHE P lay ℓ [l0, l1, l2] keys))
    | .rot g c0 => do
      let l0 ← lift "c0" c0
      let l1 ← lift "c1" d
      if staged then
        pure (rotStaged161 (openfheStages Dg C Bp P.src.t) K g (C.toRNS l0) (C.toRNS l1) kb ka)
      else
        pure (reduce (Challenge.Realize.rotateOpenFHE161 P lay ℓ g [l0, l1] keys))
    | _ => .error "runLocked: only relinearization and the v1.6.1 rotation have a locked transcription"
  else .error s!"digit sizes {lay.sizes ℓ} do not sum to {ℓ}"
  else .error "more towers than the chain"
  else .error "the special primes are not pairwise coprime"
  else .error "a special prime is 0"
  else .error "the chain is not pairwise coprime"
  else .error "a chain modulus is 0"

namespace Cx

/-- The key digits for the limbs `q_0..q_{ℓ-1}, p_*`, CRT-lifted to `[0, Q_ℓ·P)`. -/
def keyDigits (x : Cx) (key : Json) (ℓ ndig : Nat) : IO (Array (Array Int) × Array (Array Int)) := do
  let L := x.c.qs.length
  let k := x.c.special.length
  let digits := jArr key "digits"
  if digits.size < ndig then
    throw (IO.userError s!"the key has {digits.size} digits, {ndig} are needed")
  let moduli := ((x.c.qs.take ℓ) ++ x.c.special).toArray
  let pick := fun (nm : String) => do
    let some e := x.c.polys[nm]? | throw (IO.userError s!"polys.txt has no entry {nm}")
    if e.moduli.toList != x.c.qs ++ x.c.special then
      throw (IO.userError s!"{nm}: key limbs are not the chain followed by the special primes")
    let limbs := (e.limbs.extract 0 ℓ) ++ (e.limbs.extract L (L + k))
    liftExcept (crt nm x.N moduli limbs)
  let mut kb := #[]
  let mut ka := #[]
  for j in [0:ndig] do
    let dj := digits[j]!
    let (some bn, some an) := (jStr? dj "b", jStr? dj "a") | throw (IO.userError "key digit names")
    kb := kb.push (← pick bn)
    ka := ka.push (← pick an)
  return (kb, ka)

def findKey (x : Cx) (kind : String) (idx : Nat) : Option Json :=
  (jArr x.c.pin "evalKeys").find? fun k =>
    jStr? k "kind" == some kind &&
      (if kind == "rot" then jNat? k "index" == some idx else (jNat? k "power").getD 2 == idx)

/-- The digit sizes at `ℓ` towers (after the mutant), and whether they agree with the exporter's
`ksInfo.perLevel`. -/
def sizesAt (x : Cx) (ℓ : Nat) (m : AMut) : IO (Option (List Nat)) := do
  let ks := (jObj? x.c.pin "ksInfo").getD Json.null
  let alpha := (jNat? ks "numPerPartQ").getD ((jNat? x.c.pin "towersPerDigit").getD 0)
  let npq := (jNat? ks "numPartQ").getD ((jNat? x.c.pin "dnum").getD 0)
  let sizes := digitSizes alpha npq ℓ
  if ← x.fresh s!"layout/{ℓ}" then
    let per := (jArr ks "perLevel").find? fun e => jNat? e "towers" == some ℓ
    match per with
    | some e =>
      let dt := (jArr e "digitTowers").toList.filterMap fun j => j.getNat?.toOption
      x.emit "algo.layout" s!"towers={ℓ}" "digits" (some (dt == sizes)) "glue"
        [("lean", Json.arr (sizes.map (Json.num ·)).toArray),
         ("openfhe", Json.arr (dt.map (Json.num ·)).toArray)]
    | none => pure ()
  if m = .digitBoundary then return moveBoundary npq sizes else return some sizes

/-- Hybrid key switch of `d` at `ℓ` towers with `key`; `none` + an emitted line if not possible. -/
def ks (x : Cx) (m : AMut) (literal : Bool) (key : Json) (ℓ : Nat) (op : KSOp)
    (d : Array (Array Int)) :
    IO (Except String (Array (Array Int) × Array (Array Int))) := do
  let some sizes ← x.sizesAt ℓ m | return .error "no other digit partition at this level"
  let (kb, ka) ← x.keyDigits key ℓ sizes.length
  return runKS x.N x.K x.t x.c.qs x.c.special ℓ sizes m literal op d kb ka

/-- The variant name of the v1.3.1 rotation order (run for rotations only). -/
def rotLastName : String := "staged:rotateOpenFHE (v1.3.1 order: ModDown, then σ_g)"

/-- Which variants to run for a key-switching operation: (name, mutant, literal?, counts as the
check?). -/
def ksVariants (x : Cx) : List (String × AMut × Bool × Bool) :=
  if x.o.mu != .none then [(s!"staged:{x.o.mutName}", x.o.mu, false, true)] else
  [("staged:keySwitchBGVOpenFHE", .none, false, true)] ++
  (if x.N ≤ x.o.litMaxN then [("literal:keySwitchBGVOpenFHE", .none, true, true)] else []) ++
  (if x.N ≤ x.o.variantsMaxN then
    [("staged:keySwitchBGV", .allCentred, false, false),
     ("staged:keySwitchBGVAddDown", .downAdd, false, false),
     (rotLastName, .none, false, false)] else [])

def ksBudget (x : Cx) (check : String) (out : Obj) (op : String) : IO Bool := do
  let n ← x.nKS.get
  x.nKS.set (n + 1)
  match x.o.maxKS with
  | some k =>
    if n ≥ k then
      x.emit check out.id op none "staged" [("why", Json.str s!"skipped: --max-ks {k}")]
      return false
    return true
  | none => return true

/-- The lines of the LOCKED transcriptions for one relinearization (`rot = none`) or v1.6.1
rotation (`rot = some g`) on the operand `a` (parts `c₀ c₁ d`): `impl = "staged=locked:…"` (the
left-hand side of `addKS_locked` / `rotStaged161_locked`, at every `N`) and, at `N ≤ litMaxN`,
`impl = "literal:Challenge.Realize.…"` (the locked definition itself). Unmutated runs only. -/
def lockedLines (x : Cx) (check op : String) (a out : Obj) (key : Json) (rot : Option Nat)
    (ex : List (String × Json)) : IO Unit := do
  if x.o.mu != .none then return
  let some P0 := x.P? | return
  -- the locked functions read only `src.N/qs/t` and `store.special`; `inputNoise` (read by
  -- `SchemeParamsOK.msgRange` alone) is raised to `t/2` so that the theorem's hypothesis is about
  -- the key-switching parameters only
  let P : FullParams := { P0 with inputNoise := max P0.inputNoise (P0.src.t / 2) }
  let ks := (jObj? x.c.pin "ksInfo").getD Json.null
  let alpha := (jNat? ks "numPerPartQ").getD ((jNat? x.c.pin "towersPerDigit").getD 0)
  let npq := (jNat? ks "numPartQ").getD ((jNat? x.c.pin "dnum").getD 0)
  let sizes := digitSizes alpha npq
  let ℓ := a.towers
  let lay : Spec.Budget.KSLayout := { sizes, canonical := true }
  let hyps := [("schemeParamsOK?", boolJ (schemeParamsOK? P)), ("specialOK?", boolJ (Spec.Budget.specialOK? P)),
               ("okAt", boolJ (lay.okAt ℓ))]
  let hypsOK := schemeParamsOK? P && Spec.Budget.specialOK? P && lay.okAt ℓ
  let declared := match x.declLay? with
    | some dl => [("declaredLayoutAgrees", boolJ (dl.sizes ℓ == sizes ℓ && dl.canonical))]
    | none => []
  let lockedName := if rot.isSome then "Challenge.Realize.rotateOpenFHE161" else "Challenge.Realize.relinOpenFHE"
  let thm := if rot.isSome then "FHE.Pin.Algo.rotStaged161_locked" else "FHE.Pin.Algo.addKS_locked"
  let ndig := (sizes ℓ).length
  let modes : List Bool := [true] ++ (if x.N ≤ x.o.litMaxN then [false] else [])
  for staged in modes do
    let impl := if staged then s!"staged=locked:{lockedName}" else s!"literal:{lockedName}"
    try
      let (kb, ka) ← x.keyDigits key ℓ ndig
      let opk : KSOp := match rot with
        | some g => .rot g a.parts[0]!
        | none => .add a.parts[0]! a.parts[1]!
      let d := if rot.isSome then a.parts[1]! else a.parts[2]!
      let (res, ms) ← timedPure fun _ => runLocked P sizes x.K ℓ staged opk d kb ka
      match res with
      | .error e => x.emit check out.id op (some false) impl ([("why", Json.str e)] ++ ex)
      | .ok (r0, r1) =>
        let extra := ex ++ declared ++
          (if staged then [("locked", Json.str lockedName), ("theorem", Json.str thm),
              ("theoremHypotheses", Json.mkObj hyps), ("theoremApplies", boolJ hypsOK)]
           else [("locked", Json.str lockedName)])
        let _ ← x.report check op impl out #[r0, r1] ms extra
    catch e =>
      x.emit check out.id op (some false) impl ([("why", Json.str s!"{e}")] ++ ex)

/-- Relinearization: `(c₀ + Σ_{j≥2} KS_j(c_j)₀, c₁ + Σ_{j≥2} KS_j(c_j)₁)`, `KS_j` under the key
for `s^j`. -/
def checkRelin (x : Cx) (a out : Obj) (via : String) (c2only : Bool := false) : IO Unit := do
  x.explain out.id
  if !(← x.ksBudget "algo.relin" out "relin") then return
  let qs := x.qsArr a.towers
  -- `EvalMult`/`EvalSquare` with a key (`base-leveledshe.cpp`) key-switch `cv[2]` only and
  -- `resize(2)`: parts 3, 4, … of a longer product are DROPPED
  let last := if c2only then 3 else a.parts.size
  let ex := [("operands", Json.arr #[Json.str a.id]), ("operandParts", Json.num a.parts.size),
             ("via", Json.str via)] ++
            (if c2only && a.parts.size > 3 then [("partsDroppedByOpenFHE", natJ (a.parts.size - 3))] else [])
  for (name, m, literal, counts) in x.ksVariants.filter (·.1 != rotLastName) do
    try
      let (res, ms) ← timed (do
        let mut c0 := a.parts[0]!
        let mut c1 := a.parts[1]!
        let mut err : Option String := none
        for j in [2:last] do
          let some key := x.findKey "relin" j
            | throw (IO.userError s!"no relinearization key for s^{j}")
          match ← x.ks m literal key a.towers (.add c0 c1) a.parts[j]! with
          | .ok (r0, r1) =>
            c0 := r0
            c1 := r1
          | .error e => err := some e
        pure (err, #[c0, c1]))
      match res with
      | (some e, _) =>
        x.emit (if counts then "algo.relin" else "algo.variant.relin") out.id "relin" none name
          ([("why", Json.str e)] ++ ex)
      | (none, got) =>
        if counts then
          let _ ← x.report "algo.relin" "relin" name out got ms ex
        else
          let r := cmpParts x.t qs out.parts got
          x.emit "algo.variant.relin" out.id "relin" none name
            ([("matches", boolJ r.ok), ("why", Json.str "for the record: another proved variant")] ++
              r.json ++ ex)
    catch e =>
      x.emit "algo.relin" out.id "relin" (some false) name ([("why", Json.str s!"{e}")] ++ ex)
  -- the locked transcription (a 3-component product; for longer ones OpenFHE's EvalMult with a
  -- key also reads c₀ c₁ c₂ only)
  if last == 3 && a.parts.size ≥ 3 then
    if let some key := x.findKey "relin" 2 then
      x.lockedLines "algo.relin" "relin" { a with parts := a.parts.extract 0 3 } out key none ex

/-- Rotation, OpenFHE v1.6.1 (`rotateOpenFHE161`): ModUp of `c₁`, inner products with the key
stored for `g` over `Q_ℓ·P`, `P·c₀` added, `σ_g`, then ModDown. Mutant `autoFirst`: `σ_g` before
the key switch. The v1.3.1 order (`rotateOpenFHE`) is run as a variant, for the record. -/
def checkRotate (x : Cx) (a out : Obj) (g : Nat) (via : String) : IO Unit := do
  x.explain out.id
  if !(← x.ksBudget "algo.rotate" out "rotate") then return
  let qs := x.qsArr a.towers
  let ex := [("operands", Json.arr #[Json.str a.id]), ("g", Json.num g), ("via", Json.str via)]
  if a.parts.size != 2 then
    x.emit "algo.rotate" out.id "rotate" (some false) "staged" ([("why", Json.str "operand does not have 2 parts")] ++ ex)
    return
  let some key := x.findKey "rot" g
    | x.emit "algo.rotate" out.id "rotate" (some false) "staged" ([("why", Json.str s!"no key for index {g}")] ++ ex)
  for (name, m, literal, counts) in x.ksVariants do
    try
      let op : KSOp := if m = .autoFirst then .rotFirst g a.parts[0]!
        else if name == rotLastName || m = .autoLast then .rotLast g a.parts[0]! else .rot g a.parts[0]!
      let (res, ms) ← timed (do
        match ← x.ks m literal key a.towers op a.parts[1]! with
        | .ok (r0, r1) => pure (Except.ok #[r0, r1])
        | .error e => pure (Except.error e))
      match res with
      | .error e =>
        x.emit (if counts then "algo.rotate" else "algo.variant.rotate") out.id "rotate" none name
          ([("why", Json.str e)] ++ ex)
      | .ok got =>
        if counts then
          let _ ← x.report "algo.rotate" "rotate" name out got ms ex
        else
          let r := cmpParts x.t qs out.parts got
          x.emit "algo.variant.rotate" out.id "rotate" none name
            ([("matches", boolJ r.ok), ("why", Json.str "for the record: another proved variant")] ++
              r.json ++ ex)
    catch e =>
      x.emit "algo.rotate" out.id "rotate" (some false) name ([("why", Json.str s!"{e}")] ++ ex)
  x.lockedLines "algo.rotate" "rotate" a out key (some g) ex

end Cx

/-! ## Walking the trace -/

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := b % m
  let mut e := e
  for _ in [0:64] do
    if e == 0 then break
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

/-- The value operands of a wrapper frame after OpenFHE's level/depth adjustment: the outputs of
its last `AdjustFor…` child, else its own ciphertext inputs. -/
def adjusted (f : Frame) : Array Arg :=
  match (f.kids.filter fun k => has k.fn "AdjustFor").back? with
  | some k => let o := Frame.cts k.outs; if o.size ≥ 2 then o else Frame.cts f.ins
  | none => Frame.cts f.ins

partial def walk (x : Cx) (f : Frame) : IO Unit := do
  for k in f.kids do walk x k
  let ins := Frame.cts f.ins
  let outs := f.outs.filter (·.kind == "ct")
  let fn := f.fn
  let key := fun (op : String) (as : Array Arg) (o : Arg) =>
    s!"{op}/{String.intercalate "," (as.map (·.id)).toList}/{o.id}"
  let lin := x.want "lin"
  try
    if fn.startsWith "LeveledSHEBase::EvalAddCoreInPlace(Ciphertext,Ciphertext)"
        || fn.startsWith "LeveledSHEBase::EvalSubCoreInPlace(Ciphertext,Ciphertext)" then
      let sub := has fn "EvalSub"
      if lin && ins.size ≥ 2 && outs.size ≥ 1 then if ← x.fresh (key (if sub then "sub" else "add") ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let b ← x.obj ins[1]!.id
        let o ← x.obj outs[0]!.id
        if sub then
          x.hom "algo.sub" "sub" [a, b] o fun l => Challenge.Source.padZip (· - ·) (l.getD 0 []) (l.getD 1 [])
        else
          x.hom "algo.add" "add" [a, b] o fun l => Challenge.Source.padZip (· + ·) (l.getD 0 []) (l.getD 1 [])
    else if fn.startsWith "LeveledSHEBase::EvalNegateInPlace" then
      if lin && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "neg" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        x.hom "algo.negate" "negate" [a] o fun l => (l.getD 0 []).map (- ·)
    else if fn.startsWith "LeveledSHEBase::EvalMultCore(" then
      if x.want "tensor" && ins.size ≥ 2 && outs.size ≥ 1 then if ← x.fresh (key "tensor" ins outs[0]!) then
        tensor x ins[0]!.id ins[1]!.id outs[0]!.id "EvalMultCore"
    else if fn.startsWith "LeveledSHEBGVRNS::EvalMultCoreInPlace(Ciphertext,NativeInteger)" then
      if lin && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "mulConst" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        let cst := (f.int? "constant").getD 0
        x.hom "algo.mulConst" "mulConst" [a] o (fun l => (l.getD 0 []).map (cst • ·))
          [("constant", intJ cst)]
    else if fn.startsWith "LeveledSHEBGVRNS::ModReduceInternalInPlace" then
      if x.want "modreduce" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "modReduce" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        checkModReduce x a o ((f.int? "levels").getD 1).toNat
    else if fn.startsWith "LeveledSHEBGVRNS::LevelReduceInternalInPlace" then
      if lin && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "levelReduce" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        x.explain o.id
        let levels := ((f.int? "levels").getD 1).toNat
        let got := a.parts.map fun limbs => limbs.extract 0 (a.towers - levels)
        let _ ← x.report "algo.levelReduce" "levelReduce" "limb" o got 0
          [("operands", Json.arr #[Json.str a.id]), ("levels", Json.num levels)]
    else if fn.startsWith "LeveledSHEBase::EvalAutomorphism(" then
      if x.want "ks" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "rotate" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        x.checkRotate a o ((f.int? "i").getD 0).toNat "EvalAutomorphism"
    else if fn.startsWith "CryptoContext::EvalFastRotation(" then
      if x.want "ks" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "rotate" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        let idx := ((f.int? "index").getD 0).toNat
        let m := ((f.int? "m").getD 0).toNat
        if idx == 0 then
          x.explain o.id
          let _ ← x.report "algo.rotate" "rotate" "limb" o a.parts 0
            [("operands", Json.arr #[Json.str a.id]), ("via", Json.str "EvalFastRotation, index 0: a copy")]
        else
          x.checkRotate a o (powMod 5 idx m) "EvalFastRotation"
    else if fn.startsWith "LeveledSHEBase::RelinearizeInPlace(" then
      if x.want "ks" && ins.size ≥ 1 && outs.size ≥ 1 then if ← x.fresh (key "relin" ins outs[0]!) then
        let a ← x.obj ins[0]!.id
        let o ← x.obj outs[0]!.id
        if a.parts.size ≤ 2 then
          x.explain o.id
          let _ ← x.report "algo.relin" "relin" "limb" o a.parts 0
            [("operands", Json.arr #[Json.str a.id]), ("via", Json.str "Relinearize of 2 parts: a copy")]
        else x.checkRelin a o "RelinearizeInPlace"
    else if fn.startsWith "LeveledSHEBase::EvalMult" || fn.startsWith "LeveledSHEBase::EvalSquare"
        || fn.startsWith "CryptoContext::EvalMult" || fn.startsWith "CryptoContext::EvalSquare" then
      -- product (a traced child), then relinearization (untraced KeySwitchInPlace)
      if x.want "ks" && outs.size ≥ 1 then
        match f.kids.back? with
        | some k =>
          let ko := k.outs.filter (·.kind == "ct")
          if ko.size ≥ 1 then if ko[0]!.id != outs[0]!.id then if ← x.fresh (key "relin" ko outs[0]!) then
            let a ← x.obj ko[0]!.id
            let o ← x.obj outs[0]!.id
            if a.parts.size ≥ 3 && o.parts.size == 2 then x.checkRelin a o (baseName fn) true
        | none => pure ()
    else if fn.startsWith "LeveledSHERNS::EvalAdd" || fn.startsWith "LeveledSHERNS::EvalSub" then
      let sub := fn.startsWith "LeveledSHERNS::EvalSub"
      let core := f.kids.any fun k =>
        has k.fn (if sub then "EvalSubCoreInPlace" else "EvalAddCoreInPlace") ||
          k.fn.startsWith (if sub then "LeveledSHERNS::EvalSub" else "LeveledSHERNS::EvalAdd")
      if !core && outs.size ≥ 1 then
        let ops := adjusted f
        morph x f
        if lin && ops.size ≥ 2 then if ← x.fresh (key (if sub then "sub" else "add") ops outs[0]!) then
          let a ← x.obj ops[0]!.id
          let b ← x.obj ops[1]!.id
          let o ← x.obj outs[0]!.id
          let plain := b.parts.size == 1
          let ex := [("via", Json.str (baseName fn))]
          if sub then
            x.hom (if plain then "algo.subPlain" else "algo.sub") "sub" [a, b] o
              (fun l => Challenge.Source.padZip (· - ·) (l.getD 0 []) (l.getD 1 [])) ex
          else
            x.hom (if plain then "algo.addPlain" else "algo.add") "add" [a, b] o
              (fun l => Challenge.Source.padZip (· + ·) (l.getD 0 []) (l.getD 1 [])) ex
    else if fn.startsWith "LeveledSHERNS::EvalMult" then
      let core := f.kids.any fun k => has k.fn "EvalMultCore(" || k.fn.startsWith "LeveledSHERNS::EvalMult"
      if !core && outs.size ≥ 1 then
        let ops := adjusted f
        morph x f
        if ops.size ≥ 2 then if ← x.fresh (key "mul" ops outs[0]!) then
          let b ← x.obj ops[1]!.id
          if b.parts.size == 1 then
            if lin then
              let a ← x.obj ops[0]!.id
              let o ← x.obj outs[0]!.id
              x.hom "algo.mulPlain" "mulPlain" [a, b] o
                (fun l => match l.getD 1 [] with
                  | [c] => ((l.getD 0 []).map fun x => mulArr c x).map ofArr
                  | _ => [])
                [("via", Json.str (baseName fn))]
          else if x.want "tensor" then tensor x ops[0]!.id ops[1]!.id outs[0]!.id (baseName fn)
    else if fn.startsWith "LeveledSHERNS::EvalSquare" then
      if x.want "tensor" && outs.size ≥ 1 && ins.size ≥ 1 then
        let src := match f.kids.back? with
          | some k => ((k.outs.filter (·.kind == "ct"))[0]?).getD ins[0]!
          | none => ins[0]!
        if ← x.fresh (key "tensor" #[src, src] outs[0]!) then
          tensor x src.id src.id outs[0]!.id "EvalSquare"
    -- an output no rule explained: is it a copy (same polynomials, new metadata) of the last
    -- child's output or of an input?
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
                x.explain o.id
                let _ ← x.report "algo.copy" "copy" "limb" oo co.parts 0
                  [("operands", Json.arr #[Json.str co.id]), ("via", Json.str (baseName fn)),
                   ("why", Json.str "same polynomials; only the metadata (hence the id) changed")]
  catch e =>
    x.emit "algo.error" ((outs[0]?.map (·.id)).getD "?") fn (some false) "glue"
      [("why", Json.str s!"{e}"), ("line", Json.num f.line)]
where
  tensor (x : Cx) (aId bId oId via : String) : IO Unit := do
    let a ← x.obj aId
    let b ← x.obj bId
    let o ← x.obj oId
    let n ← x.nTensor.get
    x.nTensor.set (n + 1)
    if let some k := x.o.maxTensor then
      if n ≥ k then
        x.explain o.id
        x.emit "algo.tensor" o.id "tensor" none "limb" [("why", Json.str s!"skipped: --max-tensor {k}")]
        return
    if a.parts.size == 2 && b.parts.size == 2 then
      x.hom "algo.tensor" "tensor" [a, b] o
        (fun l => tensorF (l.getD 0 []) (l.getD 1 []))
        [("via", Json.str via), ("fn", Json.str "Challenge.Source.tensor")]
    else
      x.hom "algo.tensorN" "tensor" [a, b] o
        (fun l => tensorGen (l.getD 0 []) (l.getD 1 []))
        [("via", Json.str via), ("fn", Json.str "FHE.Pin.Algo.tensorGen (convolution; not a project definition)")]
  /-- `MorphPlaintext`: the 1-part value OpenFHE makes from a plaintext has the plaintext's limbs. -/
  morph (x : Cx) (f : Frame) : IO Unit := do
    let ins := Frame.cts f.ins
    if ins.size < 2 || ins[1]!.kind != "pt" then return
    let some k := (f.kids.filter fun k => has k.fn "AdjustFor")[0]? | return
    let kin := Frame.cts k.ins
    if kin.size < 2 || kin[1]!.kind != "ct" then return
    if !(← x.fresh s!"morph/{ins[1]!.id}/{kin[1]!.id}") then return
    let p ← x.obj ins[1]!.id
    let c ← x.obj kin[1]!.id
    x.explain c.id
    let got := p.parts.map fun limbs => limbs.extract 0 c.towers
    let _ ← x.report "algo.morph" "morphPlaintext" "limb" c got 0 [("operands", Json.arr #[Json.str p.id])]

/-- Every ciphertext id the trace produces. -/
partial def producedIds (f : Frame) (acc : Array String) : Array String :=
  let acc := f.kids.foldl (fun a k => producedIds k a) acc
  (f.outs.filter (·.kind == "ct")).foldl (fun a o => if a.contains o.id then a else a.push o.id) acc

/-- **Entry point.** Every `algo.*` comparison of one loaded case. Never throws. -/
def runCase (c : Case) (o : Opts := {}) (P? : Option FullParams := none)
    (declLay? : Option Spec.Budget.KSLayout := none) : IO (Array Json) := do
  let out ← IO.mkRef (#[] : Array Json)
  let x : Cx := { c, o, out, seen := ← IO.mkRef {}, explained := ← IO.mkRef {},
                  nKS := ← IO.mkRef 0, nTensor := ← IO.mkRef 0, P?, declLay? }
  try
    if x.want "encrypt" then checkEncrypt x
    let tracePath : System.FilePath := (c.dir : System.FilePath) / "trace.jsonl"
    if !(← tracePath.pathExists) then
      x.emit "algo.trace" "trace.jsonl" "load" none "glue" [("why", Json.str "no trace.jsonl")]
      return (← out.get)
    let roots := parseTrace (← IO.FS.readFile tracePath)
    for f in roots do walk x f
    -- coverage: ciphertext ids produced by the trace that no comparison explained
    if o.only.isNone then
      let produced := roots.foldl (fun a f => producedIds f a) #[]
      let ex ← x.explained.get
      let missing := produced.filter fun id => !ex.contains id
      x.emit "algo.coverage" "trace.jsonl" "coverage" (if missing.isEmpty then some true else none) "glue"
        [("produced", Json.num produced.size), ("explained", Json.num (produced.size - missing.size)),
         ("unexplained", Json.arr (missing.map Json.str)),
         ("why", Json.str (if missing.isEmpty then "every ciphertext the trace produces is the output of a compared operation"
            else "ciphertexts produced by operations this module does not compare"))]
  catch e =>
    x.emit "algo.error" "case" "case" (some false) "glue" [("why", Json.str s!"{e}")]
  out.get

end FHE.Pin.Algo
