import FHE.Pin.BFV.ChecksProg
import FHE.Pin.BFV.ChecksEnc

/-!
# FHE.Pin.BFV.Run — every BFV check group on one case   (UNTRUSTED glue)

`openfhe_pin` calls `FHE.Pin.BFV.runCase` for a case whose `pin.json` has `"scheme": "BFV"`.
Groups (`--only`): `a` decryption, `b` message semantics, `c` fresh encryption and inputs,
`d` keys, `e` step contracts, `f` bounds and the verdict, `x` refusals
(`harness/openfhe-pin/lean/README.md`, "BFV").
-/

namespace FHE.Pin.BFV
open Lean Spec FHE.Pin

/-- The declarations of the program file that the dump can contradict: technique, auxiliary
basis, special primes. -/
def checkDeclared (b : BX) (inp : FHE.Check.BFV.Input) : IO Unit := do
  let bj := b.bfvJ
  let nat := fun (k : String) => (natList bj k).toOption.getD []
  let auxR := nat "auxR"
  let bsk := nat "behzBsk"
  let (tech, aux, extraOK) : String × List Nat × Bool := match inp.mul with
    | some m =>
      (m.technique.name, m.auxBasis,
        match m.technique with
        | .behz => m.mSk == bsk.getLast? && m.mTilde == jNat? bj "behzMtilde"
        | _ => true)
    | none => ("", [], true)
  let auxExpected := if tech == "BEHZ" then bsk.dropLast else auxR
  let techOK := inp.mul.isNone || tech == b.mult
  let auxOK := inp.mul.isNone || aux == auxExpected
  let specialOK := b.P.store.special.map (·.q) == b.c.special
  let ksDecl := match inp.base.ks.variant with
    | .centred => "centred" | _ => "canonical-modup"
  let ksOK := if b.ks == "BV" then b.c.special.isEmpty && ksDecl == "centred" else !b.c.special.isEmpty
  b.emit "load.declared" "bfv" "declarations" (some (techOK && auxOK && extraOK && specialOK && ksOK)) "glue"
    [("technique", Json.str tech), ("pinTechnique", Json.str b.mult), ("techniqueOK", boolJ techOK),
     ("auxBasisOK", boolJ auxOK), ("auxLimbs", Json.num aux.length), ("behzOK", boolJ extraOK),
     ("specialOK", boolJ specialOK), ("ksVariant", Json.str ksDecl), ("ksOK", boolJ ksOK),
     ("floatTolerant", match inp.mul with | some m => boolJ m.floatTolerant | none => Json.null),
     ("maxInternalDrop", match inp.mul.bind (·.maxInternalDrop) with | some d => Json.num d | none => Json.null),
     ("maxInternalDropKS", match inp.mul.bind (·.maxInternalDropKS) with | some d => Json.num d | none => Json.null),
     ("plainAdd", match inp.plainAdd with | some pa => Json.str pa.method.name | none => Json.null),
     ("what", Json.str "the program file's technique, auxiliary basis, special primes and key-switching variant against pin.json (the library's own accessors)")]

/-- Run every BFV check group on one loaded case; never throws. -/
def runCase (o : Opts) (mu : BMut) (c : Case) (dir : String) : IO (Array Json) := do
  let out ← IO.mkRef (#[] : Array Json)
  let bj := (jObj? c.pin "bfv").getD Json.null
  let mult := (jStr? bj "mult").getD "?"
  let ks := (jStr? bj "ks").getD "?"
  let enc := (jStr? bj "enc").getD "?"
  let loadFail := fun (why : String) => do
    out.modify (·.push (Json.mkObj
      [("case", Json.str c.name), ("check", Json.str "load"), ("id", Json.str dir),
       ("op", Json.str "load"), ("ok", Json.bool false), ("impl", Json.str "glue"),
       ("scheme", Json.str "BFV"), ("mult", Json.str mult), ("ks", Json.str ks), ("N", Json.num c.N),
       ("why", Json.str why)]))
    out.get
  try
    let inp := decodeProg c
    -- the numbers of limbs at which the run encrypts (for the extractor's input-noise formula)
    let encLevels : List Nat := ((jArr c.pin "encryptions").toList.filterMap fun e =>
      ((jStr? e "ct").bind c.object?).bind (jNat? · "towers")).eraseDups
    let encLevels := if encLevels.isEmpty then (List.range c.qs.length).map (· + 1) else encLevels
    let extPrime := (jNat? bj "extendedPrime").getD 0
    let fallbackP : FullParams :=
      { src := { kind := .bfv, N := c.N, qs := c.qs, t := c.t }
        store := { W := c.N, limbs := c.qs.map (⟨·, 0⟩), special := c.special.map (⟨·, 0⟩) }
        secretBound := if jStr? bj "secretKeyDist" == some "GAUSSIAN" then gaussBound else 1
        inputNoise := extractorInputNoise c.N c.t c.qs encLevels (if enc == "EXTENDED" then extPrime else 0)
        keyNoise := gaussBound
        outputNoise := 0 }
    let P := match inp with
      | .ok i => i.base.P
      | .error _ => fallbackP
    let some sName := jStr? c.pin "secret" | return (← loadFail "pin.json: secret")
    let s ← match c.intPoly sName with
      | .ok s => pure s
      | .error e => return (← loadFail e)
    let x : Cx := { c, o := { o with mu := mu.bgv, mutName := mu.name }, P, s, out,
                    keyCache := ← IO.mkRef {}, objCache := ← IO.mkRef {} }
    let b : BX := { x, mu, mult, ks, enc, inp, declared := inp.isOk,
                    stepFail := ← IO.mkRef 0, boundFail := ← IO.mkRef 0, inputFail := ← IO.mkRef 0,
                    objNoise := ← IO.mkRef {} }
    let paramsOK := P.src.N == c.N && P.src.t == c.t && P.src.qs == c.qs && P.src.kind == .bfv
    b.emit "load.params" "params" "load" (some paramsOK) "glue"
      [("progQs", Json.arr (P.src.qs.map natJ).toArray), ("pinQs", Json.arr (c.qs.map natJ).toArray),
       ("inputNoise", natJ P.inputNoise), ("keyNoise", natJ P.keyNoise), ("secretBound", natJ P.secretBound),
       ("declared", boolJ inp.isOk),
       ("inputNoiseIsExtractorFormula", boolJ (P.inputNoise == fallbackP.inputNoise)),
       ("schemeParamsOK", boolJ (schemeParamsOK? P)), ("specialOK", boolJ (Budget.specialOK? P)),
       ("L", Json.num c.qs.length), ("specialPrimes", Json.num c.special.length)]
    if !paramsOK then return (← out.get)
    match inp with
    | .ok i =>
      b.emit "load.prog" "prog.fhecheck.json" "load" (some true) "glue"
      checkDeclared b i
    | .error e =>
      b.emit "load.prog" "prog.fhecheck.json" "load" none "glue"
        [("why", Json.str s!"no program: {e}; the program checks (c.input, b, e, f) are not run")]
      if b.want "x" then checkRefusal b
    if let some bld := jObj? c.pin "build" then
      b.emit "info.build" "build" "info" none "glue" [("why", Json.str "information"), ("build", bld),
        ("bfv", bj), ("notes", Json.arr (jArr c.pin "notes"))]
    if let some rn := jStr? c.pin "secretRns" then
      match c.polys[rn]? with
      | some e =>
        let ok := (List.range e.moduli.size).all fun i =>
          let q : Int := e.moduli[i]!
          e.limbs[i]! == s.map (· % q)
        b.emit "load.secret" rn "load" (some ok) "glue" [("limbs", Json.num e.moduli.size)]
      | none => b.emit "load.secret" rn "load" (some false) "glue" [("why", Json.str "missing")]
    let guard := fun (g : String) (act : IO Unit) => do
      if b.want g then
        try act catch e => b.emit s!"{g}.error" "group" g (some false) "glue" [("why", Json.str s!"{e}")]
    -- the key-switching layout: the program's; for a refused case HYBRID with the dumped digit
    -- size, BV (digit size 0) one limb per digit
    let fallbackLay := if ks == "BV" then Budget.uniformLayout 1 false
      else Budget.uniformLayout ((jNat? bj "towersPerDigit").getD 1) true
    let lay : Budget.KSLayout ← match inp with
      | .ok i =>
        match FHE.Check.layoutOf P i.base.ks with
        | .ok l => pure l
        | .error e =>
          b.emit "load.layout" "layout" "load" (some false) "glue" [("why", Json.str e)]
          pure fallbackLay
      | .error _ => pure fallbackLay
    guard "c" (checkFresh b)
    guard "d" (checkKeys b lay)
    -- the program replay runs before `a.decrypt`, which reads the noise it measures
    match inp with
    | .ok i =>
      if b.want "a" || b.want "b" || b.want "e" || b.want "f" || b.want "c" then
        try checkProg b i lay
        catch e => b.emit "b.error" "program" "program" (some false) "glue" [("why", Json.str s!"{e}")]
    | .error _ => pure ()
    guard "a" (checkDecrypt b)
    guard "a" (checkDecryptLib b)
    guard "c" (checkEncryptBFV b)
    out.get
  catch e => loadFail s!"{e}"

end FHE.Pin.BFV
