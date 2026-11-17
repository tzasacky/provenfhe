import FHE.Pin.BFV.Load
import FHE.Pin.ChecksA

/-!
# FHE.Pin.BFV.Checks — the BFV checks that need no program: decryption (a), fresh encryption (c),
keys (d), refusals (x)   (UNTRUSTED glue around the trusted definitions)

* `a.decrypt`: `Spec.Scheme.bfvDecrypt t s ct` at the object's own modulus against OpenFHE's raw
  `Decrypt` output, all `N` coefficients. Where they differ: for a program variable under `s`
  the line fails if the noise `f.bound` measures (for the message the program computes) satisfies
  `Challenge.BFV.decOK`, and is `null` otherwise (the ciphertext does not encrypt the message).
  Any other object has no intended message (it may be under another key, e.g. the key-switched
  ciphertext inside `EvalAutomorphism` before the permutation, or not an encryption at all): the
  line fails if a differing coefficient is more than 1/4 from a rounding boundary (the error the
  library's own comments allow its floating-point `ScaleAndRound`), and is `null` otherwise.
  `tieDist*`: the distance of `t·Φ/Q` from a rounding boundary; a mismatch at distance `d` shows
  a rounding error of the library of at least `d`.
* `c.fresh`: every recorded encryption satisfies `Spec.Scheme.BFVEncrypts` (the BFV case of
  `Spec.Correct.Encrypts`) for the stored plaintext polynomial reduced mod `t`, at the bound the
  certificate uses; `c.predict`: the measured noise polynomial equals the one predicted from the
  recorded randomness; `c.support`, `c.stored`.
* `d.key`: `Spec.Budget.GadgetKeysOK` at every level (decided by `FHE.Pin.BFV.gadgetKeysCheck`,
  sound); `d.pubkey`.
* `x.refusal`: an extractor refusal must be an expected one whose reason the data shows.
-/

namespace FHE.Pin.BFV
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source FHE.Pin
open Challenge.BFV (decOK)

instance {N : ℕ} (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) :
    Decidable (BFVEncrypts t B s ct m) := by
  unfold BFVEncrypts; infer_instance

instance {N : ℕ} (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) :
    Decidable (BGVEncrypts t B s ct m) := by
  unfold BGVEncrypts; infer_instance

/-! ## a. Decryption -/

def checkDecrypt (b : BX) : IO Unit := do
  let P := b.P
  let N := b.N
  let t := b.t
  for (id, o) in objList b.x do
    if jStr? o "kind" != some "ct" then continue
    let parts := (jNat? o "parts").getD 0
    let some dec := jObj? o "decrypt"
      | do
        if parts ≥ 2 then
          b.emit "a.decrypt" id "decrypt" none "forced"
            [("why", Json.str s!"OpenFHE did not decrypt this ciphertext: {(jStr? o "decryptError").getD "decrypt is null"}"),
             ("parts", Json.num parts)]
        continue
    try
      let ph ← b.x.objPh id
      let towers := ph.level
      let Q := P.src.modulus towers
      let some rawName := jStr? dec "raw" | throw (IO.userError "decrypt.raw missing")
      -- OpenFHE's raw output, reduced modulo t (an unreduced line may hold t itself)
      let (raw, rawT) ← b.rawDec rawName
      let mine := b.mu.decryptOfPhase N b.K t Q ph.Φ
      let agree := valsOf mine == raw
      -- the measured noise: for the message the program computes if the object is a program
      -- variable, else for the message the trusted decryption returns
      let progNoise := (← b.objNoise.get)[id]?
      let noise := progNoise.getD (b.mu.noise N b.K t Q ph.Z mine)
      let dOK := decOK t Q noise
      -- distance of t·Φ/Q from a rounding boundary, in units of 2⁻⁴⁰
      let tie : Nat → Nat := fun j =>
        let u := ((t : Int) * ph.Φ[j]!) % (Q : Int)
        ((2 * u - (Q : Int)).natAbs * 2 ^ 40) / (2 * Q)
      let toF : Nat → Json := fun n => floatJ (Float.ofNat n / Float.ofNat (2 ^ 40))
      let mineV := valsOf mine
      let tieMin := (List.range N).foldl (fun acc j => min acc (tie j)) (2 ^ 40)
      let tieMis := (List.range N).foldl (fun (acc : Option Nat) j =>
        if mineV[j]! == raw[j]! then acc else some (max (acc.getD 0) (tie j))) none
      let common : List (String × Json) :=
        [("towers", Json.num towers), ("parts", Json.num parts), ("mismatches", Json.num (diffCount mineV raw)),
         ("rawEqualsT", Json.num rawT),
         ("noise", natJ noise), ("noiseBits", bitsJ noise), ("decOK", boolJ dOK),
         ("noiseFor", Json.str (if progNoise.isSome then "the message the program computes" else "the trusted decryption itself")),
         ("limitBits", match FHE.Check.BFV.maxNoise t Q with | some m => bitsJ m | none => Json.null),
         ("tieDistMin", toF tieMin),
         ("tieDistMismatchMax", match tieMis with | some d => toF d | none => Json.null)]
      -- the verdict where the two decryptions differ (module docstring)
      let farFromTie := match tieMis with
        | some d => decide (4 * d > 2 ^ 40)
        | none => true
      let differ : Option Bool :=
        if progNoise.isSome then (if dOK then some false else none)
        else (if farFromTie then some false else none)
      let why := if agree then [] else
        [("why", Json.str (
          if progNoise.isSome then
            (if dOK then "Spec.Scheme.bfvDecrypt differs from OpenFHE's Decrypt although the measured noise of the ciphertext (for the message the program computes) satisfies decOK"
             else "the measured noise of this ciphertext violates Challenge.BFV.decOK: it does not encrypt the program's message, and exact rounding and the library's RNS decryption need not agree")
          else if farFromTie then "Spec.Scheme.bfvDecrypt differs from OpenFHE's Decrypt at a coefficient more than 1/4 from a rounding boundary"
          else "not a program variable under s (no intended message): the two decryptions differ only within 1/4 of a rounding boundary, the error the library's ScaleAndRound allows itself"))]
      let verdict : Option Bool := if agree then some true else differ
      b.emit "a.decrypt" id "decrypt" verdict "forced" (common ++ why)
      if b.literal parts then
        let ctQ : List (Poly Q P.src.N) := ph.comps.map fun c => ofInt Q (ofArr c)
        let lit := toArr b.K (bfvDecrypt P.src.t (ofArr b.s) ctQ)
        b.emit "a.decrypt" id "decrypt" (if valsOf lit == raw then some true else differ) "literal"
          ([("towers", Json.num towers), ("parts", Json.num parts)] ++ (if valsOf lit == raw then [] else why))
        b.emit "a.decrypt.literal-vs-forced" id "decrypt" (some (lit == mine)) "literal+forced"
    catch e =>
      b.emit "a.error" id "decrypt" (some false) "forced" [("why", Json.str s!"{e}")]

/-! ## c. Fresh encryption -/

/-- `⌈a / t⌉` of an integer (`t > 0`). -/
def ceilDivInt (a : Int) (t : Nat) : Int := -((-a) / (t : Int))

/-- The exported public-key error `pk.e`, if captured. -/
def pkError (b : BX) : IO (Option (Array Int)) := do
  match (jObj? b.c.pin "public").bind (jStr? · "e") with
  | some en =>
    match b.c.intPoly en with
    | .ok e => pure (some e)
    | .error _ => pure none
  | none => pure none

def checkFresh (b : BX) : IO Unit := do
  let P := b.P
  let N := b.N
  let t := b.t
  b.emit "c.support" "s" "secret" (some (decide (normA N b.s ≤ b.secretDistBound))) "literal"
    [("measured", natJ (normA N b.s)), ("bound", natJ b.secretDistBound), ("secretBound", natJ P.secretBound),
     ("secretKeyDist", Json.str ((jStr? b.bfvJ "secretKeyDist").getD "?"))]
  let ePk ← pkError b
  let prog? : Option Program := match b.inp with
    | .ok inp => some inp.base.prog
    | .error _ => none
  for enc in jArr b.c.pin "encryptions" do
    let ctId := (jStr? enc "ct").getD "?"
    try
      let some ptId := jStr? enc "pt" | throw (IO.userError "encryption without pt")
      let (p, msg, _) ← storedPlain b ptId
      let ph ← b.x.objPh ctId
      let towers := ph.level
      let Q := P.src.modulus towers
      let parts := ph.comps.length
      let extended := jBool enc "extended"
      let encoding := ((b.c.object? ptId).bind (jStr? · "encoding")).getD "?"
      let pN := normA N p
      let inZeroT := (List.range N).all fun i => decide (0 ≤ p[i]! ∧ p[i]! < (t : Int))
      -- the bound the certificate uses for this ciphertext
      let (B0, src) : Nat × String := match prog? with
        | some prog =>
          match prog.inputs.find? (·.name = ctId) with
          | some d => (TraceBFV.inputBound P prog d, "Spec.TraceBFV.inputBound P prog d (the input of the extracted program)")
          | none => (P.inputNoise, "params.inputNoise of the program file (this ciphertext is not an input of the extracted program)")
        | none => (P.inputNoise, "the extractor's documented formula (no program: the extractor refused the case)")
      let B := B0 / b.mu.freshDiv
      let noise := b.mu.noise N b.K t Q ph.Z msg
      let decrypts := b.mu.decryptOfPhase N b.K t Q ph.Φ == msg
      let ok := b.mu.inputOK P b.K B parts ph msg
      let common : List (String × Json) :=
        [("towers", Json.num towers), ("parts", Json.num parts), ("declared", boolJ b.declared),
         ("boundSource", Json.str src), ("extended", boolJ extended), ("decrypts", boolJ decrypts),
         ("randomness", Json.str ((jStr? enc "randomness").getD "?"))]
      b.emit "c.fresh" ctId "encrypt" (some ok) "forced" (measuredBound noise B ++ common)
      if b.literal parts then
        let ctQ : List (Poly Q P.src.N) := ph.comps.map fun c => ofInt Q (ofArr c)
        let lit := decide (BFVEncrypts P.src.t B (ofArr b.s) ctQ (ofArr msg))
        b.emit "c.fresh" ctId "encrypt" (some lit) "literal" common
        b.emit "c.fresh.literal-vs-forced" ctId "encrypt" (some (lit == ok)) "literal+forced"
      -- the encoder's convention
      let storedFields : List (String × Json) :=
        [("ptEncoding", Json.str encoding), ("storedNorm", natJ pN), ("tMinus1", natJ (t - 1)),
         ("storedInZeroT", boolJ inZeroT)]
      if encoding == "packed" || encoding == "coefpacked" then
        -- both BFV encoders store coefficients in [0, t) (Spec.EncryptBFV, "The stored plaintext":
        -- the coefficient-packed encoding stores a negative value v as t − |v| for BFVrns)
        b.emit "c.stored" ctId encoding (some inZeroT) "literal"
          (storedFields ++ [("convention", Json.str s!"{encoding}: every coefficient of the stored polynomial in [0, t) (Spec.EncryptBFV)")])
      else
        b.emit "c.stored" ctId encoding none "literal"
          (storedFields ++ [("why", Json.str s!"encoding {encoding}: no convention claimed")])
      -- the recorded randomness
      let (some un, some e1n, some e2n) := (jStr? enc "u", jStr? enc "e1", jStr? enc "e2")
        | do
          b.emit "c.predict" ctId "encrypt" none "glue"
            [("why", Json.str s!"randomness not captured ({(jStr? enc "randomness").getD "?"})")]
          continue
      let u ← liftExcept (b.c.intPoly un)
      let e1 ← liftExcept (b.c.intPoly e1n)
      let e2 ← liftExcept (b.c.intPoly e2n)
      b.emit "c.support" ctId "randomness"
        (some (decide (normA N u ≤ b.secretDistBound) && decide (normA N e1 ≤ gaussBound) && decide (normA N e2 ≤ gaussBound))) "literal"
        [("u", natJ (normA N u)), ("e1", natJ (normA N e1)), ("e2", natJ (normA N e2)),
         ("boundU", natJ b.secretDistBound), ("boundE", natJ gaussBound)]
      if extended then
        b.emit "c.predict" ctId "encrypt" none "glue"
          [("why", Json.str "EXTENDED encryption: (u, e1, e2) are drawn modulo Q·p and both components are divided by p with rounding; no closed relation is claimed")]
        continue
      let some e := ePk
        | do
          b.emit "c.predict" ctId "encrypt" none "glue" [("why", Json.str "pk.e was not captured")]
          continue
      -- predicted noise: e_pk·u + e1 + e2·s + (⌈Q·p/t⌉ − ⌊Q/t⌋·m), m = p mod t in [0, t)
      let G := toArr b.K (ofArr (N := N) (mulArr (ofArr (N := N) e) (ofArr u)) + ofArr e1 + ofArr (N := N) (mulArr (ofArr (N := N) e2) (ofArr b.s)))
      let dev : Array Int := Array.ofFn (n := N) fun i =>
        let pi := p[i.val]!
        let encd := if b.mu.encFloor then ((Q : Int) * pi) / (t : Int) else ceilDivInt ((Q : Int) * pi) t
        encd - ((Q / t : Nat) : Int) * (((ofArr (N := N) msg).coeff i).val : Int)
      let pred := toArr b.K (ofArr (N := N) G + ofArr dev)
      let meas := b.mu.noisePoly N b.K t Q ph.Z msg
      let fits := decide (2 * normA N pred < Q)
      let devBound := cdiv (Q % t * (t - 1)) t
      let gBound := gaussBound * (1 + 2 * N * P.secretBound)
      b.emit "c.predict" ctId "encrypt" (if meas == pred then some true else if fits then some false else none) "glue"
        ([("towers", Json.num towers), ("mismatches", Json.num (diffCount meas pred)),
          ("measured", natJ (normA N meas)), ("predicted", natJ (normA N pred)),
          ("gaussianPart", natJ (normA N G)), ("gaussianBound", natJ gBound),
          ("encodingDeviation", natJ (normA N dev)), ("encodingDeviationBound", natJ devBound),
          ("QmodT", natJ (Q % t)),
          ("partsWithinBounds", boolJ (decide (normA N G ≤ gBound) && decide (normA N dev ≤ devBound))),
          ("model", Json.str "noise = e_pk·u + e1 + e2·s + (⌈Q·p/t⌉ − ⌊Q/t⌋·p): c0 = b·u + e1 + TimesQovert(p), c1 = a·u + e2")] ++
          (if meas == pred || fits then [] else [("why", Json.str "the predicted noise is not below Q/2")]))
    catch e =>
      b.emit "c.error" ctId "encrypt" (some false) "forced" [("why", Json.str s!"{e}")]

/-! ## d. Keys -/

def checkKeys (b : BX) (lay : Budget.KSLayout) : IO Unit := do
  let P := b.P
  let N := b.N
  let L := P.src.qs.length
  let special := P.store.special.map (·.q)
  let mt := b.x.mt
  let digitSize := (jNat? b.bfvJ "digitSizeBV").getD 0
  -- public key: b + a·s = e over the key's limbs, ‖e‖ ≤ keyNoise
  if let some pub := jObj? b.c.pin "public" then
    try
      let some bn := jStr? pub "b" | throw (IO.userError "public.b")
      let some an := jStr? pub "a" | throw (IO.userError "public.a")
      let (mb, pb) ← liftExcept (b.c.rnsPolyAny bn)
      let (ma, pa) ← liftExcept (b.c.rnsPolyAny an)
      if mb != ma then throw (IO.userError "pk.b and pk.a have different limbs")
      let Qpk := mb.foldl (· * ·) 1
      let e := toArr b.K (centered (ofInt Qpk (ofArr (N := N) (keyLhsZ N b.K mt pb pa b.s))))
      let en := normA N e
      let ePk ← pkError b
      b.emit "d.pubkey" "pk" "publicKey"
        (some (decide (en ≤ P.keyNoise) && (match ePk with | some x => x == e | none => true))) "glue"
        (measuredBound en P.keyNoise ++
          [("pkLimbs", Json.num mb.length), ("pkModuliAreChain", boolJ (mb == P.src.qs)),
           ("equalsExportedE", match ePk with | some x => boolJ (x == e) | none => Json.null),
           ("relation", Json.str "b + a·s ≡ e (mod Q), ‖e‖∞ ≤ keyNoise")])
    catch e =>
      b.emit "d.error" "pk" "publicKey" (some false) "forced" [("why", Json.str s!"{e}")]
  for ek in jArr b.c.pin "evalKeys" do
    let kind := (jStr? ek "kind").getD "?"
    let index := (jNat? ek "index").getD 0
    let kid := if kind == "relin" then "relin" else s!"rot{index}"
    try
      let dj := (jArr ek "digits").toList
      let dnames := dj.filterMap fun d =>
        match jStr? d "b", jStr? d "a" with
        | some bn, some an => some (bn, an)
        | _, _ => none
      let some (b0n, _) := dnames.head? | throw (IO.userError "no digits")
      let keyMod ← liftExcept (b.c.moduliOf b0n)
      -- the key's limbs: the chain, then the special primes; with EXTENDED encryption and BV the
      -- library generates keys over Q·r (r the extra prime of the encryption), one more limb. The
      -- CRT lift over all the key's limbs is reduced modulo Q_ℓ·P, i.e. restricted to those limbs.
      let extPrime := (jNat? b.bfvJ "extendedPrime").getD 0
      let extra := keyMod.drop (L + special.length)
      let limbsOK := keyMod.take (L + special.length) == P.src.qs ++ special &&
        (extra.isEmpty || (extra == [extPrime] && extPrime > 1))
      b.emit "d.limbs" kid kind (some limbsOK) "literal"
        [("keyLimbs", Json.num keyMod.length), ("chainLimbs", Json.num L), ("special", Json.num special.length),
         ("extraLimbs", Json.arr (extra.map natJ).toArray), ("extraIsExtendedPrime", boolJ (extra == [extPrime] && extPrime > 1)),
         ("digits", Json.num dnames.length)]
      if !limbsOK then throw (IO.userError s!"key limb moduli {keyMod} are not chain ++ special (++ the extended prime)")
      let keys ← dnames.toArray.mapM fun (bn, an) => do
        let kb ← liftExcept (b.c.rnsPoly bn keyMod)
        let ka ← liftExcept (b.c.rnsPoly an keyMod)
        pure (kb, ka)
      -- OpenFHE switches with the stored key and then applies X ↦ X^g: σ_g of the stored key is a
      -- key for the target σ_g(s) under s
      let (tgt, keysR) : KeyTarget × Array (Array Int × Array Int) :=
        if kind == "relin" then (.square, keys)
        else (.galois index, keys.map fun (kb, ka) => (autoA N b.K mt index kb, autoA N b.K mt index ka))
      let reading := if kind == "relin" then "secret=s target=square key=as-stored"
        else "secret=s target=galois(i) key=sigma_i(stored)"
      let lhs := keysR.map fun k => keyLhsZ N b.K mt k.1 k.2 b.s
      let tg := targetZ N b.K mt b.s tgt
      if digitSize > 0 then
        -- BV with base-2^w digits: key (i, k) holds 2^(w·k)·target in limb i. `Spec.Budget.KSLayout`
        -- has one gadget factor per group of limbs and cannot express the powers of 2^w.
        let Q := P.src.modulus L
        let mut ok := true
        let mut maxE := 0
        for j in [0:dj.length] do
          let i := (jNat? dj[j]! "limb").getD 0
          let k := (jNat? dj[j]! "power").getD 0
          let hat := (P.src.qs.eraseIdx i).prod
          let qi := P.src.qs.getD i 1
          let c : ZMod Q := ((2 ^ (digitSize * k) * (hat * ((hat : ZMod qi)⁻¹).val) : Nat) : ZMod Q)
          let en := normA N (keyErrA N b.K Q c lhs[j]! tg)
          ok := ok && decide (en ≤ P.keyNoise)
          maxE := max maxE en
        b.emit "d.key" kid kind none "forced"
          (measuredBound maxE P.keyNoise ++
            [("reading", Json.str reading), ("digitSizeBV", Json.num digitSize), ("holds", boolJ ok),
             ("why", Json.str s!"BV key switching with digit size {digitSize}: Spec.Budget.KSLayout/gadgetFactor cannot express the base-2^w digits, so no trusted GadgetKeysOK applies; `holds` is the same error formula with the factor 2^(w·k)·(CRT idempotent of limb i), on the data")])
        continue
      for ℓ in [1:L + 1] do
        let nd := (lay.sizes ℓ).length
        -- the verdict: `FHE.Pin.BFV.gadgetKeysCheck` (sound for `Spec.Budget.GadgetKeysOK`)
        let ok := gadgetKeysCheck P lay ℓ b.K lhs tg
        let mut maxE := 0
        for j in [0:min nd lhs.size] do
          maxE := max maxE (normA N (gadgetErrA P lay ℓ b.K j lhs[j]! tg))
        b.emit "d.key" kid kind (some ok) "forced"
          (measuredBound maxE P.keyNoise ++
            [("reading", Json.str reading), ("level", Json.num ℓ), ("digits", Json.num nd),
             ("storedDigits", Json.num lhs.size), ("sizes", Json.arr ((lay.sizes ℓ).map (Json.num ·)).toArray),
             ("specialPrimes", Json.num special.length)])
        if b.literal 2 then
          let lit := decide (Budget.GadgetKeysOK P lay ℓ tgt (ofArr b.s)
            ((keysR.toList.take nd).map fun k => (ofArr k.1, ofArr k.2)))
          b.emit "d.key" kid kind (some lit) "literal" [("reading", Json.str reading), ("level", Json.num ℓ)]
          b.emit "d.key.literal-vs-forced" kid kind (some (lit == ok)) "literal+forced" [("level", Json.num ℓ)]
    catch e =>
      b.emit "d.error" kid kind (some false) "forced" [("why", Json.str s!"{e}")]

/-! ## x. Refusals -/

/-- The refusals of `harness/frontend/openfhe/extract_bfv.py` this harness expects: a substring
of the message, a class name, whether the dumped data shows the reason, and what that is. -/
def refusalClasses (b : BX) : List (String × String × Bool × String) :=
  let objs := objList b.x
  let L := b.c.qs.length
  let nonPacked := objs.any fun (_, o) =>
    jStr? o "kind" == some "pt" && jStr? o "encoding" != some "packed"
  let parts := fun (k : Nat) => objs.any fun (_, o) =>
    jStr? o "kind" == some "ct" && (jNat? o "parts").getD 0 ≥ k
  let coefCt3 := objs.any fun (_, o) =>
    jStr? o "kind" == some "ct" && (jNat? o "parts").getD 0 ≥ 3 && jStr? o "format" == some "COEFFICIENT"
  let shortPt := objs.any fun (_, o) =>
    jStr? o "kind" == some "pt" && (jNat? o "towers").getD L < L
  let shortCt := objs.any fun (_, o) =>
    jStr? o "kind" == some "ct" && (jNat? o "towers").getD L < L
  let called := fun (needle : String) => b.c.traceFns.any fun fn => (fn.splitOn needle).length > 1
  let noted := fun (needle : String) => (jArr b.c.pin "notes").any fun n =>
    match n.getStr? with
    | .ok s => (s.splitOn needle).length > 1
    | .error _ => false
  let digitSize := (jNat? b.bfvJ "digitSizeBV").getD 0
  let dist := (jStr? b.bfvJ "secretKeyDist").getD ""
  [("is the unrelinearised output of a BFV product", "unrelinearised-product-combined", coefCt3,
     "pin.json has a 3-component ciphertext object with \"format\": \"COEFFICIENT\""),
   ("ENCRYPTION_TECHNIQUE = EXTENDED", "extended-encryption", jStr? b.bfvJ "enc" == some "EXTENDED",
     "pin.json: bfv.enc = \"EXTENDED\""),
   ("only packed plaintexts are mapped", "non-packed-plaintext", nonPacked,
     "pin.json has a plaintext whose encoding is not packed"),
   ("encryption with the PRIVATE key is not mapped", "private-key-encryption",
     called "Encrypt(Plaintext,PrivateKey)" || called "Encrypt(PrivateKey,Plaintext)",
     "the trace calls CryptoContext::Encrypt with a private key"),
   ("plaintexts encoded at fewer limbs are not mapped", "plaintext-fewer-limbs", shortPt,
     "pin.json has a plaintext with fewer limbs than the chain"),
   ("EvalMultNoRelinNoCheck multiplies the components directly", "evalmult-norelin-nocheck",
     called "EvalMultNoRelinNoCheck", "the trace calls EvalMultNoRelinNoCheck"),
   ("-part ciphertext: only 3 parts are mapped", "relinearize-more-than-3-parts", parts 4,
     "pin.json has a ciphertext with 4 or more components"),
   ("-part ciphertext outside", "relinearize-more-than-3-parts", parts 4,
     "pin.json has a ciphertext with 4 or more components"),
   ("BV key switching with digit size", "bv-digit-size", decide (digitSize > 0),
     "pin.json: bfv.digitSizeBV > 0"),
   ("EvalFastRotation / EvalFastRotationExt (hoisted rotation with precomputed digits) is not mapped",
     "fast-rotation-not-mapped", called "EvalFastRotation", "the trace calls EvalFastRotation*"),
   ("EvalInnerProduct calls EvalSum", "evalinnerproduct-not-mapped", called "EvalInnerProduct",
     "the trace calls EvalInnerProduct"),
   ("EvalSum / EvalSumRows / EvalSumCols", "evalsum-not-mapped", called "EvalSum", "the trace calls EvalSum"),
   ("EvalMultMutable / EvalMultMutableInPlace run untraced cores", "evalmultmutable-not-mapped",
     called "EvalMultMutable", "the trace calls EvalMultMutable"),
   ("EvalSquareMutable runs untraced cores", "evalsquaremutable-not-mapped",
     called "EvalSquareMutable", "the trace calls EvalSquareMutable"),
   ("EvalMerge uses EvalSum-style rotations", "evalmerge-not-mapped", called "EvalMerge",
     "the trace calls EvalMerge"),
   ("only UNIFORM_TERNARY and SPARSE_TERNARY secrets are mapped", "gaussian-secret",
     dist != "UNIFORM_TERNARY" && dist != "SPARSE_TERNARY" && dist != "",
     "pin.json: bfv.secretKeyDist is not a ternary distribution"),
   ("EvalMult of operands with different numbers of limbs", "mult-different-limbs", shortCt,
     "pin.json has a ciphertext with fewer limbs than the chain (a compressed operand)"),
   ("EvalAutomorphism of a ", "rotation-of-3-part", parts 3,
     "pin.json has a ciphertext with 3 or more components"),
   ("the rotation key used is not recorded in the trace", "rotation-of-3-part-threw",
     parts 3 && noted "should be relinearized",
     "pin.json has a 3-component ciphertext and a note that OpenFHE's EvalAutomorphism threw on it"),
   ("Compress(Ciphertext,size_t) recorded no output ciphertext", "compress-threw",
     noted "Compress(): BFV Compress is not currently supported",
     "pin.json notes that OpenFHE's Compress threw (BFV Compress is not supported for BEHZ, HPS or EXTENDED encryption)"),
   ("recorded no output ciphertext (the call threw", "operation-threw", noted "EXC ",
     "pin.json notes an exception thrown by the library (EXC …)"),
   ("multiparty / proxy re-encryption / key switching to another key", "key-model",
     called "CryptoContext::Multi" || called "ReKeyGen" || called "ReEncrypt" || called "KeySwitchGen" ||
       called "CryptoContext::KeySwitch" || called "SparseKeyGen",
     "the trace calls a multiparty / re-encryption / key-switching API"),
   ("the trace contains no homomorphic operation", "no-operation",
     !(b.c.traceFns.any fun fn => (fn.splitOn "::Eval").length > 1 || (fn.splitOn "Compress").length > 1 ||
        (fn.splitOn "Relinearize").length > 1),
     "the trace has no Eval*, Relinearize or Compress call")]

/-- When `prog.fhecheck.json` is an extractor refusal `{"format": …, "error": msg}`: the message
must be one of the expected refusals, and the data must show its reason. -/
def checkRefusal (b : BX) : IO Unit := do
  let some msg := jStr? b.c.progJson "error"
    | b.emit "x.refusal" "prog.fhecheck.json" "extract" (some false) "glue"
        [("why", Json.str s!"prog.fhecheck.json is neither a decodable BFV program nor an extractor refusal: {match b.inp with | .error e => e | .ok _ => ""}")]
  match (refusalClasses b).find? fun (sub, _) => (msg.splitOn sub).length > 1 with
  | some (_, cls, confirmed, what) =>
    b.emit "x.refusal" "prog.fhecheck.json" cls (some confirmed) "glue"
      ([("class", Json.str cls), ("message", Json.str msg), ("dataShows", Json.str what)] ++
        (if confirmed then [] else [("why", Json.str s!"the extractor refused with the expected message but the data does not show its reason: {what}")]))
  | none =>
    b.emit "x.refusal" "prog.fhecheck.json" "unclassified" (some false) "glue"
      [("class", Json.str "unclassified"), ("message", Json.str msg),
       ("why", Json.str "the extractor refused this case with a message that is not one of the expected refusals")]

end FHE.Pin.BFV
