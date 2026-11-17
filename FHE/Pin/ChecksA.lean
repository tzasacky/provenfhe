import FHE.Pin.Core

/-!
# FHE.Pin.ChecksA — decryption (a), fresh encryption (c), keys (d), and the data-only checks
(UNTRUSTED glue around the trusted definitions)
-/

namespace FHE.Pin
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source

def objList (x : Cx) : Array (String × Json) :=
  match jObj? x.c.pin "objects" with
  | some (.obj o) => o.toArray
  | _ => #[]

/-! ## a. Decryption -/

def checkA (x : Cx) : IO Unit := do
  let P := x.P
  for (id, o) in objList x do
    if jStr? o "kind" != some "ct" then continue
    let parts := (jNat? o "parts").getD 0
    let some dec := jObj? o "decrypt"
      | do
        if parts ≥ 2 then
          x.emit "a.switched" id "decrypt" none "forced"
            [("why", Json.str s!"OpenFHE did not decrypt this ciphertext: {(jStr? o "decryptError").getD "decrypt is null"}"),
             ("parts", Json.num parts)]
        continue
    try
      let ph ← x.objPh id
      let towers := ph.level
      let qsℓ := P.src.qs.take towers
      let some rawName := jStr? dec "raw" | throw (IO.userError "decrypt.raw missing")
      let raw ← x.rawPoly rawName x.t
      let common : List (String × Json) := [("towers", Json.num towers), ("parts", Json.num parts)]
      -- OpenFHE's Decrypt = bgvDecryptSwitched
      let sw := switchedPhaseA x.N x.K x.mt x.t qsℓ ph.Φ
      let decS := valsOf (decryptOfPhaseA x.N x.K x.t sw)
      x.emit "a.switched" id "decrypt" (some (decS == raw)) "forced"
        (common ++ [("mismatches", Json.num (diffCount decS raw))])
      -- textbook decryption at the ciphertext's level, times decScale
      let normΦ := normA x.N ph.Φ
      let decT := decryptOfPhaseA x.N x.K x.t ph.Φ
      let scaled := valsOf (toArr x.K (x.mt.decScaleM P.src towers • (ofArr decT : Poly P.src.t P.src.N)))
      let okT := scaled == raw
      let pre := Decrypt.decryptOK? P.src towers normΦ
      let Q := P.src.modulus towers
      let dB := Decrypt.decBound P.src towers normΦ
      let cls := if okT then "agree" else if pre then
          "DISAGREE although decryptOK? holds for the measured phase (contradicts Challenge.Decrypt.decrypt_switched)"
        else "switched phase may wrap modulo q0 (decBound of the measured phase is not below q0/2): the two decryptions need not agree"
      x.emit "a.textbook" id "decrypt" (if okT then some true else if pre then some false else none) "forced"
        (common ++ [("measured", natJ normΦ), ("halfQ", natJ (Q / 2)), ("measuredBits", bitsJ normΦ),
          ("halfQBits", bitsJ (Q / 2)), ("decBound", natJ dB), ("q0", natJ (P.src.qs.headD 0)),
          ("class", Json.str cls)] ++ (if okT then [] else [("why", Json.str cls)]))
      -- the switched phase is within decBound of the phase it came from
      let normSw := normA x.N sw
      x.emit "a.decbound" id "decrypt" (some (decide (normSw ≤ dB))) "forced"
        (common ++ [("measured", natJ normSw), ("bound", natJ dB)])
      -- the one-tower polynomial before reduction modulo t
      if let some q0Name := jStr? dec "rawQ0" then
        let q0 := P.src.qs.headD 0
        let rawQ0 ← x.rawPoly q0Name q0
        let mine := valsOf (toArr x.K (ofInt q0 (ofArr (N := x.N) sw)))
        x.emit "a.switchedQ0" id "decrypt" (some (mine == rawQ0)) "forced"
          (common ++ [("mismatches", Json.num (diffCount mine rawQ0))])
      -- literal trusted definitions
      if x.literal parts then
        let ctQ : List (Poly qsℓ.prod P.src.N) := ph.comps.map fun c => ofInt qsℓ.prod (ofArr c)
        let litS := valsOf (toArr x.K (Decrypt.bgvDecryptSwitched P.src.t qsℓ (ofArr x.s) ctQ))
        x.emit "a.switched" id "decrypt" (some (litS == raw)) "literal" common
        x.emit "a.switched.literal-vs-forced" id "decrypt" (some (litS == decS)) "literal+forced" common
        let litT := valsOf (toArr x.K (Decrypt.decScale P.src towers • bgvDecrypt P.src.t (ofArr x.s) ctQ))
        x.emit "a.textbook" id "decrypt"
          (if litT == raw then some true else if pre then some false else none) "literal"
          (common ++ (if litT == raw then [] else [("why", Json.str cls)]))
        x.emit "a.textbook.literal-vs-forced" id "decrypt" (some (litT == scaled)) "literal+forced" common
        let litΦ := toArr x.K (centeredPhase (ofArr x.s) ctQ)
        x.emit "a.phase.literal-vs-forced" id "centeredPhase" (some (litΦ == ph.Φ)) "literal+forced" common
    catch e =>
      x.emit "a.error" id "decrypt" (some false) "forced" [("why", Json.str s!"{e}")]

/-! ## c. Fresh encryption -/

def kappas : List Nat := [1, 2, 4, 8, 16, 32, 64, 128]

/-- `declBp`: the bound declared for the stored plaintext polynomial of a fresh encryption
(`freshEncryption.plaintextBound` of the extracted program, `t − 1` if it declares none); `none`
when the extractor refused the case (then there is no declaration, and the noise bound is
evaluated at the measured norm of each stored polynomial). -/
def checkC (x : Cx) (declBp : Option Nat) : IO Unit := do
  let P := x.P
  let N := x.N
  let t := x.t
  let some pub := jObj? x.c.pin "public" | return
  let pk ← try
      let some bn := jStr? pub "b" | throw (IO.userError "public.b")
      let some an := jStr? pub "a" | throw (IO.userError "public.a")
      let (mb, b0) ← liftExcept (x.c.rnsPolyAny bn)
      let (ma, a0) ← liftExcept (x.c.rnsPolyAny an)
      if mb != ma then throw (IO.userError "pk.b and pk.a have different limbs")
      pure (some (mb, b0, a0))
    catch e =>
      x.emit "c.error" "pk" "publicKey" (some false) "forced" [("why", Json.str s!"{e}")]
      pure none
  let some (pkMod, b0, a0) := pk | return
  -- the key-order mutant swaps the components wherever the public key is used
  let (b, a) := if x.mt = .keyOrder then (a0, b0) else (b0, a0)
  let Qpk := pkMod.foldl (· * ·) 1
  let chainSpecial := P.src.qs ++ P.store.special.map (·.q)
  let pkInfo : List (String × Json) :=
    [("pkLimbs", Json.num pkMod.length), ("pkModuliAreChainThenSpecial", boolJ (pkMod == chainSpecial)),
     ("pkModuliAreChain", boolJ (pkMod == P.src.qs))]
  x.emit "c.support" "s" "secret" (some (decide (normA N x.s ≤ 1))) "literal"
    [("measured", natJ (normA N x.s)), ("bound", natJ 1)]
  let ePk : Option (Array Int) ← match jStr? pub "e" with
    | some en =>
      try pure (some (← liftExcept (x.c.intPoly en)))
      catch e =>
        x.emit "c.error" "pk.e" "publicKey" (some false) "forced" [("why", Json.str s!"{e}")]
        pure none
    | none => pure none
  -- centred (b + a·s) mod Q: divisible by t, quotient small
  let pkLhs := toArr x.K (ofArr (N := N) b + ofArr (mulArr (ofArr (N := N) a) (ofArr x.s)))
  let D := toArr x.K (centered (ofInt Qpk (ofArr (N := N) pkLhs)))
  let dv := dvdA N t D
  let quot := D.map (· / (t : Int))
  let qn := normA N quot
  x.emit "c.pubkey.shape" "pk" "publicKey"
    (some (dv && decide (qn ≤ 39) && (match ePk with | some e => quot == e | none => true))) "literal"
    (pkInfo ++ [("tDivides", boolJ dv), ("measured", natJ qn), ("bound", natJ 39),
      ("equalsExportedE", match ePk with | some e => boolJ (quot == e) | none => Json.null)])
  match ePk with
  | none =>
    x.emit "c.pubkey" "pk" "PublicKeyOK" none "literal" [("why", Json.str "pk.e was not captured")]
  | some e =>
    let lhs := toArr x.K (ofInt Qpk (ofArr (N := N) pkLhs))
    let rhs := toArr x.K (ofInt Qpk ((t : Int) • ofArr (N := N) e))
    x.emit "c.pubkey" "pk" "PublicKeyOK" (some (lhs == rhs)) "forced" pkInfo
    if x.literal 2 then
      let lit := decide (Encrypt.PublicKeyOK t Qpk (ofArr (N := N) x.s) (ofArr e) (ofArr b) (ofArr a))
      x.emit "c.pubkey" "pk" "PublicKeyOK" (some lit) "literal" pkInfo
      x.emit "c.pubkey.literal-vs-forced" "pk" "PublicKeyOK" (some (lit == (lhs == rhs))) "literal+forced"
    x.emit "c.support" "pk.e" "keyError" (some (decide (normA N e ≤ 39))) "literal"
      [("measured", natJ (normA N e)), ("bound", natJ 39)]
  let worst := Encrypt.worstError N 1 39 1 39 39
  let V := Encrypt.varProxy N 1 39 1 39 39
  for enc in jArr x.c.pin "encryptions" do
    let ctId := (jStr? enc "ct").getD "?"
    try
      let some ptId := jStr? enc "pt" | throw (IO.userError "encryption without pt")
      let (un, e1n, e2n) := (jStr? enc "u", jStr? enc "e1", jStr? enc "e2")
      let (some un, some e1n, some e2n) := (un, e1n, e2n)
        | do
          x.emit "c.encrypt" ctId "encrypt" none "literal"
            [("why", Json.str s!"randomness not captured ({(jStr? enc "randomness").getD "?"})")]
          continue
      let u ← liftExcept (x.c.intPoly un)
      let e1 ← liftExcept (x.c.intPoly e1n)
      let e2 ← liftExcept (x.c.intPoly e2n)
      let some pto := x.c.object? ptId | throw (IO.userError s!"no object {ptId}")
      let some ptPoly := jStr? pto "poly" | throw (IO.userError s!"{ptId}: poly")
      let (ptMod, ptx) ← liftExcept (x.c.rnsPolyAny ptPoly)
      -- the stored plaintext polynomial `p`: the integer polynomial OpenFHE adds to the first
      -- component, as the centred representative modulo the plaintext's own modulus (packed
      -- encoding: coefficients in [0, t); CoefPacked: negative coefficients; FLEXIBLEAUTO*:
      -- multiplied by the scaling factor without reduction modulo t)
      let ptC := centredA N x.K .none (ptMod.foldl (· * ·) 1) ptx
      let pN := normA N ptC
      let encoding := (jStr? pto "encoding").getD "?"
      let inZeroT := (List.range N).all fun i => decide (0 ≤ ptC[i]! ∧ ptC[i]! < (t : Int))
      let exceeds := decide (pN > t - 1)
      let (comps, towers) ← x.objComps ctId
      let Qct := P.src.modulus towers
      let common : List (String × Json) :=
        [("towers", Json.num towers), ("randomness", Json.str ((jStr? enc "randomness").getD "?"))]
      -- Spec.Encrypt.encrypt on OpenFHE's key, stored plaintext and randomness
      let enc' : List (Array Int) :=
        (encryptMF x.mt P.src.t (ofArr (N := P.src.N) b0) (ofArr a0) (ofArr ptC) (ofArr u) (ofArr e1) (ofArr e2)).map
          (toArr x.K)
      let encQ := enc'.map fun c => valsOf (toArr x.K (ofInt Qct (ofArr (N := N) c)))
      let mm : Nat := (encQ.zip comps).foldl (fun (acc : Nat) p => acc + diffCount p.1 p.2) 0
      let storedFields : List (String × Json) :=
        [("ptEncoding", Json.str encoding), ("storedNorm", natJ pN), ("tMinus1", natJ (t - 1)),
         ("storedInZeroT", boolJ inZeroT), ("storedCentred", boolJ (decide (pN ≤ t / 2))),
         ("storedExceedsTMinus1", boolJ exceeds), ("storedNormBits", bitsJ pN)]
      x.emit "c.encrypt" ctId "encrypt" (some (encQ == comps)) "forced"
        (common ++ [("mismatches", Json.num mm)] ++ storedFields)
      if x.literal 2 then
        let lit := ((Encrypt.encrypt P.src.t (ofArr (N := P.src.N) b0) (ofArr a0) (ofArr ptC) (ofArr u) (ofArr e1)
          (ofArr e2)).map (toArr x.K)).map fun c => valsOf (toArr x.K (ofInt Qct (ofArr (N := N) c)))
        x.emit "c.encrypt" ctId "encrypt" (some (lit == comps)) "literal" (common ++ storedFields)
        x.emit "c.encrypt.literal-vs-forced" ctId "encrypt" (some (lit == encQ)) "literal+forced" common
      -- the encoder's convention, as `Spec.Encrypt`'s docstring states it
      let fixedScaling := x.c.scaling == "FIXEDMANUAL" || x.c.scaling == "FIXEDAUTO"
      let (conv, convOK) : String × Option Bool :=
        if encoding == "packed" then ("packed: every coefficient in [0, t)", some inZeroT)
        else if encoding == "coefpacked" && fixedScaling then
          ("coefpacked, fixed scaling: centred, norm at most t/2", some (decide (pN ≤ t / 2)))
        else if encoding == "coefpacked" then
          ("coefpacked, flexible scaling: multiplied by the scaling factor without reduction modulo t (no bound claimed)", none)
        else (s!"encoding {encoding}: no convention claimed", none)
      x.emit "c.stored" ctId encoding convOK "literal"
        (common ++ storedFields ++ [("convention", Json.str conv)] ++
          (if convOK.isNone then [("why", Json.str conv)] else []))
      -- the generalisation is exercised: a stored polynomial larger than t − 1 for which the
      -- encryption relation holds
      if exceeds then
        x.emit "c.stored.exceeds" ctId encoding (some (encQ == comps)) "forced"
          (common ++ storedFields ++ [("mismatches", Json.num mm)])
      x.emit "c.support" ctId "randomness"
        (some (decide (normA N u ≤ 1) && decide (normA N e1 ≤ 39) && decide (normA N e2 ≤ 39))) "literal"
        [("u", natJ (normA N u)), ("e1", natJ (normA N e1)), ("e2", natJ (normA N e2))]
      match ePk with
      | none =>
        x.emit "c.phase" ctId "encrypt" none "forced" [("why", Json.str "pk.e was not captured")]
      | some e =>
        let fe := freshErrorA x.K (ofArr (N := N) x.s) (ofArr e) (ofArr u) (ofArr e1) (ofArr e2)
        let rhs := toArr x.K (ofArr (N := N) ptC + (t : Int) • ofArr fe)
        let ph ← x.objPh ctId
        let feN := normA N fe
        let rhsN := normA N rhs
        let fits := decide (2 * rhsN < Qct)
        x.emit "c.phase" ctId "encrypt"
          (if ph.Φ == rhs then some true else if fits then some false else none) "forced"
          (common ++ [("measured", natJ rhsN), ("halfQ", natJ (Qct / 2))] ++
            (if ph.Φ == rhs || fits then [] else
              [("why", Json.str "p + t·freshError is not below Q/2: the phase of a fresh encryption wraps")]))
        let noise := normA N ph.Φ
        -- `freshNoise t Bp worstError` at the DECLARED bound `Bp` of the stored plaintext
        let Bp := declBp.getD pN
        let fn := Encrypt.freshNoise t Bp worst
        x.emit "c.worst" ctId "encrypt"
          (some (decide (pN ≤ Bp) && decide (feN ≤ worst) && decide (noise ≤ fn))) "literal"
          (common ++ [("freshError", natJ feN), ("worstError", natJ worst), ("measured", natJ noise),
            ("bound", natJ fn), ("inputNoise", natJ P.inputNoise),
            ("plaintextBound", natJ Bp), ("plaintextBoundDeclared", boolJ declBp.isSome),
            ("storedNorm", natJ pN), ("storedWithinBound", boolJ (decide (pN ≤ Bp))),
            ("boundIsInputNoise", boolJ (fn == P.inputNoise))] ++
            (if declBp.isSome then [] else [("note", Json.str
              "the extractor refused this case, so no bound is declared: Bp is the measured norm of the stored polynomial")]))
        let eps := kappas.map fun κ => Encrypt.epsFor V (2 * N) κ
        x.emit "c.tail" ctId "encrypt" none "literal"
          (common ++ [("why", Json.str "statistic (aggregated by summarize.py)"),
            ("freshError", natJ feN), ("varProxy", natJ V), ("worstError", natJ worst),
            ("maxU", natJ (normA N u)), ("maxE1", natJ (normA N e1)), ("maxE2", natJ (normA N e2)),
            ("maxEpk", natJ (normA N e)),
            ("kappa", Json.arr (kappas.map (Json.num ·)).toArray),
            ("eps", Json.arr (eps.map natJ).toArray),
            ("exceeds", Json.arr (eps.map fun ε => boolJ (decide (ε ≤ feN))).toArray)])
    catch e =>
      x.emit "c.error" ctId "encrypt" (some false) "forced" [("why", Json.str s!"{e}")]

/-- c.ptbound: the stored plaintext polynomial against the bound declared for it. -/
def checkPt (x : Cx) (declBp : Option Nat) : IO Unit := do
  let N := x.N
  let decls : List (String × Nat) := match x.c.inp with
    | .ok inp => inp.prog.bounds
    | .error _ => []
  for (id, o) in objList x do
    if jStr? o "kind" != some "pt" then continue
    try
      let some nm := jStr? o "poly" | throw (IO.userError "poly")
      let (mods, v) ← liftExcept (x.c.rnsPolyAny nm)
      let Q := mods.foldl (· * ·) 1
      let cen := centredA N x.K .none Q v
      let cn := normA N cen
      let ln := normA N v
      let declared := (decls.find? fun (n, _) => n.startsWith (id ++ "@")).map (·.2)
      let fields : List (String × Json) :=
        [("measured", natJ cn), ("liftNorm", natJ ln), ("declared", boolJ declared.isSome),
         ("towers", Json.num mods.length), ("tMinus1", natJ (x.t - 1)),
         ("exceedsTMinus1", boolJ (decide (cn > x.t - 1)))]
      -- against the DECLARED bound: the one the extracted program declares for this plaintext
      -- input, else (a plaintext that is only encrypted) the declared bound of fresh encryptions
      match declared, declBp with
      | some bound, _ | none, some bound =>
        x.emit "c.ptbound" id ((jStr? o "encoding").getD "pt") (some (decide (cn ≤ bound))) "literal"
          (fields ++ [("bound", natJ bound)])
      | none, none =>
        x.emit "c.ptbound" id ((jStr? o "encoding").getD "pt") none "literal"
          (fields ++ [("why", Json.str "the extractor refused this case: no bound is declared for this plaintext")])
    catch e =>
      x.emit "c.error" id "ptbound" (some false) "forced" [("why", Json.str s!"{e}")]

/-! ## d. Keys -/

/-- A reading of an evaluation key: which secret, which target, and whether an automorphism is
applied to the stored key first. -/
structure Reading where
  name : String
  primary : Bool
  sec : Array Int
  tgt : KeyTarget
  auto : Option Nat

def classify (N t Pm : Nat) (q : Nat) (D tg : Array Int) (c : Nat) : Bool := Id.run do
  -- does (D − c·tg)·t⁻¹ mod q have centred norm ≤ 39 ?
  let ti : Int := invMod (t % q) q
  let qi : Int := q
  let _ := Pm
  for k in [0:N] do
    let r := ((D[k]! - (c : Int) * tg[k]!) % qi * ti) % qi
    let r := if 2 * r > qi then r - qi else r
    if r.natAbs > 39 then return false
  return true

def checkD (x : Cx) (lay : Budget.KSLayout) : IO Unit := do
  let P := x.P
  let N := x.N
  let L := P.src.qs.length
  let Pm := Budget.specialProd P
  let special := P.store.special.map (·.q)
  let ksInfo := jObj? x.c.pin "ksInfo"
  for ek in jArr x.c.pin "evalKeys" do
    let kind := (jStr? ek "kind").getD "?"
    let index := (jNat? ek "index").getD 0
    let kid := if kind == "relin" then (match jNat? ek "power" with | some p => if p == 2 then "relin" else s!"relin^{p}" | none => "relin") else s!"rot{index}"
    try
      let dnames := (jArr ek "digits").toList.filterMap fun d =>
        match jStr? d "b", jStr? d "a" with
        | some b, some a => some (b, a)
        | _, _ => none
      let some (b0n, _) := dnames.head? | throw (IO.userError "no digits")
      let keyMod ← liftExcept (x.c.moduliOf b0n)
      let nq := ((List.range (min keyMod.length L)).takeWhile fun i => keyMod[i]! == P.src.qs[i]!).length
      let rest := keyMod.drop nq
      let limbsOK := keyMod == P.src.qs ++ special
      x.emit "d.limbs" kid kind (some limbsOK) "literal"
        [("keyLimbs", Json.num keyMod.length), ("chainLimbs", Json.num L),
         ("chainPrefixInKey", Json.num nq), ("specialMatches", boolJ (rest == special)),
         ("digits", Json.num dnames.length),
         ("note", Json.str (if limbsOK then "key limbs are exactly q_0..q_{L-1} then the special primes (every limb of the chain, including any extra top limb)"
            else s!"key limb moduli {keyMod} differ from chain {P.src.qs} ++ special {special}"))]
      if rest != special then throw (IO.userError "the key's limbs after the chain prefix are not the special primes")
      let keys ← dnames.toArray.mapM fun (bn, an) => do
        let b ← liftExcept (x.c.rnsPoly bn keyMod)
        let a ← liftExcept (x.c.rnsPoly an keyMod)
        pure (b, a)
      let power := (jNat? ek "power").getD 2
      if kind == "relin" && power != 2 then
        -- a key for s^power (OpenFHE relinearisation of degree > 2): `Spec.Scheme.KeyTarget` has no
        -- such target, so no trusted statement applies; the same error formula is evaluated on the data
        let mut tg := x.s
        for _ in [1:power] do
          tg := mulArrM x.mt (ofArr (N := N) tg) (ofArr x.s)
        for ℓ in [1:min L nq + 1] do
          let nd := (lay.sizes ℓ).length
          let M := P.src.modulus ℓ * Pm
          let dm := Budget.digitModuli P lay ℓ
          let mut ok := decide (nd ≤ keys.size)
          let mut maxE := 0
          for j in [0:min nd keys.size] do
            let (b, a) := keys[j]!
            let c : ZMod M := ((x.mt.gadgetFactorM Pm dm j : Nat) : ZMod M)
            let e := keyErrA N x.K M c (keyLhsZ N x.K x.mt b a x.s) tg
            ok := ok && keyValidOfErr N x.t P.keyNoise e
            maxE := max maxE (normA N e / x.t)
          x.emit "d.key.power" s!"relin^{power}" kind none "forced"
            [("level", Json.num ℓ), ("power", Json.num power), ("holds", boolJ ok), ("measured", natJ maxE),
             ("why", Json.str s!"KeyTarget cannot express s^{power}; `holds` is the KeyValid error formula with target s^{power} evaluated on the data")]
        continue
      let inv := Mutants.invIndex N index
      let readings : List Reading :=
        if kind == "relin" then [⟨"secret=s target=square key=as-stored", true, x.s, .square, none⟩]
        else
          [⟨"secret=s target=galois(i) key=sigma_i(stored)", true, x.s, .galois index, some index⟩,
           ⟨"secret=sigma_{i^-1}(s) target=galois(i) key=as-stored", false, autoA N x.K x.mt inv x.s, .galois index, none⟩,
           ⟨"secret=s target=galois(i) key=as-stored", false, x.s, .galois index, none⟩,
           ⟨"secret=s target=galois(i^-1) key=as-stored", false, x.s, .galois inv, none⟩,
           ⟨"secret=sigma_i(s) target=galois(i^-1) key=as-stored", false, autoA N x.K x.mt index x.s, .galois inv, none⟩,
           ⟨"secret=s target=galois(i^-1) key=sigma_{i^-1}(stored)", false, x.s, .galois inv, some inv⟩]
      -- at large N only the primary reading and the stored-key reading are evaluated
      let readings := if N > 1024 then readings.take 2 else readings
      for r in readings do
        let keysR := match r.auto with
          | none => keys
          | some g => keys.map fun (b, a) => (autoA N x.K x.mt g b, autoA N x.K x.mt g a)
        let keysR := if x.mt = .keyOrder then keysR.map fun (b, a) => (a, b) else keysR
        let lhs := keysR.map fun k => keyLhsZ N x.K x.mt k.1 k.2 r.sec
        let tg := targetZ N x.K x.mt r.sec r.tgt
        let mut allLevels := true
        for ℓ in [1:L + 1] do
          let nd := (lay.sizes ℓ).length
          let M := P.src.modulus ℓ * Pm
          let dm := Budget.digitModuli P lay ℓ
          -- the verdict: `gadgetKeysCheck` (`FHE/Pin/Sound.lean`, proved sound for
          -- `Spec.Budget.GadgetKeysOK`: `gadgetKeysCheck_sound`), for a key that has the limbs of
          -- this level
          let ok := decide (ℓ ≤ nq) && gadgetKeysCheck P lay ℓ x.K x.mt lhs tg
          let mut maxE := 0
          let mut perDigit : Array Json := #[]
          let why := if ℓ ≤ nq then (if nd ≤ lhs.size then "" else s!"the layout has {nd} digits at this level, the key {lhs.size}")
            else s!"the key has no limb for q_{ℓ - 1}"
          -- per-digit detail, for the report only
          if ℓ ≤ nq then
            for j in [0:min nd lhs.size] do
              let c : ZMod M := ((x.mt.gadgetFactorM Pm dm j : Nat) : ZMod M)
              let e := keyErrA N x.K M c lhs[j]! tg
              let v := keyValidOfErr N x.t P.keyNoise e
              let nrm := normA N e
              let dv := dvdA N x.t e
              if v then maxE := max maxE (nrm / x.t)
              perDigit := perDigit.push (Json.mkObj
                [("digit", Json.num j), ("valid", boolJ v), ("tDivides", boolJ dv),
                 ("errOverT", if dv && v then natJ (nrm / x.t) else Json.null), ("errBits", bitsJ nrm)])
          allLevels := allLevels && ok
          let fields : List (String × Json) :=
            [("reading", Json.str r.name), ("level", Json.num ℓ), ("digits", Json.num nd),
             ("holds", boolJ ok), ("measured", natJ maxE), ("bound", natJ (P.keyNoise / x.t)),
             ("keyNoise", natJ P.keyNoise), ("perDigit", Json.arr perDigit)] ++
            (if why.isEmpty then [] else [("why", Json.str why)])
          if r.primary then
            x.emit "d.key" kid kind (some ok) "forced" fields
            if x.literal 2 then
              let lit := decide (Budget.GadgetKeysOK P lay ℓ r.tgt (ofArr r.sec)
                ((keysR.toList.take nd).map fun k => (ofArr k.1, ofArr k.2)))
              x.emit "d.key" kid kind (some lit) "literal" [("reading", Json.str r.name), ("level", Json.num ℓ)]
              x.emit "d.key.literal-vs-forced" kid kind (some (lit == ok)) "literal+forced" [("level", Json.num ℓ)]
          else
            x.emit "d.reading" kid kind none "forced" (fields ++ [("why", Json.str "alternative reading (informational): see holds")])
        x.emit "d.reading.summary" kid kind none "forced"
          [("reading", Json.str r.name), ("primary", boolJ r.primary), ("holdsAtEveryLevel", boolJ allLevels),
           ("why", Json.str "summary of one reading over all levels")]
      -- d.layout: residue by residue, which factor each stored digit key carries on each limb
      let (secL, tgtL) :=
        if kind == "relin" then (x.s, KeyTarget.square) else (autoA N x.K .none inv x.s, KeyTarget.galois index)
      let tgZ := targetZ N x.K .none secL tgtL
      let lhsL := keys.map fun (b, a) => keyLhsZ N x.K .none b a secL
      let fits := fun (j i : Nat) (c : Nat) =>
        let q := keyMod[i]!
        classify N x.t Pm q (lhsL[j]!.map (· % (q : Int))) (tgZ.map (· % (q : Int))) c
      let pattern := String.intercalate " " <| (List.range keys.size).map fun j =>
        s!"d{j}:" ++ String.join ((List.range keyMod.length).map fun i =>
          (if i == nq then "|" else "") ++
          (match fits j i (Pm % keyMod[i]!), fits j i 0 with
           | true, false => "P" | false, true => "0" | false, false => "x"
           | true, true => if Pm % keyMod[i]! == 0 then "0" else "?"))
      for ℓ in [1:L + 1] do
        let nd := (lay.sizes ℓ).length
        let dm := Budget.digitModuli P lay ℓ
        let ofheDigits : Option Nat := do
          let ki ← ksInfo
          let e ← (jArr ki "perLevel").find? fun e => jNat? e "towers" == some ℓ
          jNat? e "numPartitions"
        let limbIdx := (List.range (min ℓ nq)) ++ (List.range special.length).map (nq + ·)
        let mut bad : Array String := #[]
        for j in [0:min nd keys.size] do
          for i in limbIdx do
            let ev := Budget.gadgetFactor Pm dm j % keyMod[i]!
            if !(fits j i ev) then bad := bad.push s!"digit {j} limb {i}"
        let digitsOK := match ofheDigits with | some n => n == nd | none => true
        x.emit "d.layout" kid kind
          (if ℓ ≤ nq && nd ≤ keys.size then some (digitsOK && bad.isEmpty) else some false) "glue"
          [("level", Json.num ℓ), ("leanDigits", Json.num nd), ("leanSizes", Json.arr ((lay.sizes ℓ).map (Json.num ·)).toArray),
           ("openfheDigits", match ofheDigits with | some n => Json.num n | none => Json.null),
           ("factorMismatch", Json.arr (bad.map Json.str)),
           ("pattern", Json.str pattern),
           ("patternLegend", Json.str "per digit, per key limb (| before the special primes): P = factor ≡ P mod q_i, 0 = factor ≡ 0, x = neither, ? = both fit")]
    catch e =>
      x.emit "d.error" kid kind (some false) "forced" [("why", Json.str s!"{e}")]

/-! ## e.modswitch-parts: every traced ModReduce, by number of components -/

def checkModReduce (x : Cx) (lay : Budget.KSLayout) : IO Unit := do
  let P := x.P
  let N := x.N
  let t := x.t
  let E := Budget.certified P lay
  let ref1 := E.modSwitchAt 1
  let ref2 := E.modSwitchAt 2
  let ref3 := E.modSwitchAt 3
  let mut seen : List (String × String) := []
  for mr in x.c.modReduces do
    if seen.contains (mr.src, mr.dst) then continue
    seen := (mr.src, mr.dst) :: seen
    let id := s!"{mr.src}->{mr.dst}"
    try
      let some so := x.c.object? mr.src | throw (IO.userError s!"no object {mr.src}")
      let parts := (jNat? so "parts").getD 0
      let a ← x.objPh mr.src
      let d ← x.objPh mr.dst
      if a.level != d.level + mr.levels then
        throw (IO.userError s!"towers {a.level} -> {d.level} but levels = {mr.levels}")
      -- dropped limbs, last first
      let dropped := ((P.src.qs.take a.level).drop d.level).reverse
      let qprod := dropped.foldl (· * ·) 1
      let δ := toArr x.K (((qprod : Nat) : Int) • ofArr (N := N) d.Φ - ofArr a.Φ)
      let nrm := normA N δ
      let dv := dvdA N t δ
      let bnd := fun (E : Nat) =>
        -- Σ_j (q_1 ⋯ q_j)·E : the composed contract of `levels` single switches
        (List.range dropped.length).foldl (fun acc j => acc + (dropped.take (j + 1)).foldl (· * ·) 1 * E) 0
      -- the parts-dependent budget `Trace.Budget.modSwitchAt` of `Spec.Budget.certified`
      let refFor : Option Nat := if parts = 0 then none else some (x.mt.msBudgetM E parts)
      let fields : List (String × Json) :=
        [("parts", Json.num parts), ("levels", Json.num mr.levels), ("fromTowers", Json.num a.level),
         ("measured", natJ nrm), ("q", natJ qprod), ("measuredOverQ", natJ ((nrm + qprod - 1) / qprod)),
         ("measuredOverQBits", bitsJ ((nrm + qprod - 1) / qprod)),
         ("msBudgetOne", natJ ref1), ("msBudget", natJ ref2), ("msBudget3", natJ ref3),
         ("budget", match refFor with | some E => natJ E | none => Json.null),
         ("tDivides", boolJ dv), ("exceeds2part", boolJ (decide (nrm > bnd ref2))),
         ("exceeds1part", boolJ (decide (nrm > bnd ref1))),
         ("composite", boolJ (mr.levels > 1)), ("traceLine", Json.num mr.line)]
      match refFor with
      | some E =>
        x.emit "e.modswitch-parts" id "ModReduce" (some (dv && decide (nrm ≤ bnd E))) "forced"
          (fields ++ [("bound", natJ (bnd E))])
      | none =>
        x.emit "e.modswitch-parts" id "ModReduce" none "forced"
          (fields ++ [("why", Json.str s!"no reference budget for {parts} components")])
    catch e =>
      x.emit "e.modswitch-parts" id "ModReduce" none "forced" [("why", Json.str s!"{e}")]

/-- b.negate: every traced `EvalNegate`, on the data alone (the extractor refuses these programs). -/
def checkNegate (x : Cx) : IO Unit := do
  let P := x.P
  let N := x.N
  let mut seen : List (String × String) := []
  for ng in x.c.negates do
    if seen.contains (ng.src, ng.dst) then continue
    seen := (ng.src, ng.dst) :: seen
    let id := s!"{ng.src}->{ng.dst}"
    try
      let a ← x.objPh ng.src
      let d ← x.objPh ng.dst
      let Q := P.src.modulus d.level
      -- the mulConst (−1) contract: φ' = (−1) • φ
      let lhs := toArr x.K (ofInt Q (ofArr (N := N) d.Z))
      let rhs := toArr x.K (((-1 : Int) : ZMod Q) • ofInt Q (ofArr (N := N) a.Z))
      let so := (x.c.object? ng.src).getD Json.null
      let do' := (x.c.object? ng.dst).getD Json.null
      let rawRel : Option Bool ← match (jObj? so "decrypt").bind (jStr? · "raw"), (jObj? do' "decrypt").bind (jStr? · "raw") with
        | some ra, some rd => do
          let va ← x.rawPoly ra x.t
          let vd ← x.rawPoly rd x.t
          pure (some (vd == va.map fun v => (-v) % (x.t : Int)))
        | _, _ => pure none
      x.emit "b.negate" id "EvalNegate" (some (lhs == rhs && a.level == d.level && rawRel != some false)) "forced"
        [("phaseIsMinusPhase", boolJ (lhs == rhs)), ("sameTowers", boolJ (a.level == d.level)),
         ("decryptIsMinusDecrypt", match rawRel with | some b => boolJ b | none => Json.null),
         ("sfIn", match jNat? so "sf" with | some n => natJ n | none => Json.null),
         ("sfOut", match jNat? do' "sf" with | some n => natJ n | none => Json.null),
         ("decryptSfIn", match (jObj? so "decrypt").bind (jNat? · "sf") with | some n => natJ n | none => Json.null),
         ("decryptSfOut", match (jObj? do' "decrypt").bind (jNat? · "sf") with | some n => natJ n | none => Json.null)]
    catch e =>
      x.emit "b.negate" id "EvalNegate" none "forced" [("why", Json.str s!"{e}")]

/-! ## x.refusal: an extractor refusal is tested, not excused -/

/-- The refusals of `harness/frontend/openfhe/extract.py` this harness expects: a substring of the
message, a class name, and what the dumped data must show for the refusal to be that one. -/
def refusalClasses (x : Cx) : List (String × String × Bool × String) :=
  let objs := objList x
  let nonPacked := objs.any fun (_, o) =>
    jStr? o "kind" == some "pt" && jStr? o "encoding" != some "packed"
  let parts := fun (k : Nat) => objs.any fun (_, o) =>
    jStr? o "kind" == some "ct" && (jNat? o "parts").getD 0 ≥ k
  let called := fun (needle : String) => x.c.traceFns.any fun fn => (fn.splitOn needle).length > 1
  let noted := fun (needle : String) => (jArr x.c.pin "notes").any fun n =>
    match n.getStr? with
    | .ok s => (s.splitOn needle).length > 1
    | .error _ => false
  [("only packed plaintexts are mapped", "non-packed-plaintext", nonPacked,
     "pin.json has a plaintext whose encoding is not packed"),
   ("relinearizes only the third component of the product", "evalmult-key-on-3-part-operand", parts 3,
     "pin.json has a ciphertext with 3 or more components"),
   ("-part ciphertext: only 3 parts are mapped", "relinearize-more-than-3-parts", parts 4,
     "pin.json has a ciphertext with 4 or more components"),
   ("EvalFastRotation / EvalFastRotationExt (hoisted rotation with precomputed digits) is not mapped",
     "fast-rotation-not-mapped", called "EvalFastRotationPrecompute", "the trace calls EvalFastRotationPrecompute"),
   ("EvalInnerProduct calls EvalSum", "evalinnerproduct-not-mapped", called "EvalInnerProduct",
     "the trace calls EvalInnerProduct"),
   ("EvalSum / EvalSumRows / EvalSumCols", "evalsum-not-mapped", called "EvalSum", "the trace calls EvalSum"),
   ("EvalMultMutable / EvalMultMutableInPlace run untraced cores", "evalmultmutable-not-mapped",
     called "EvalMultMutable", "the trace calls EvalMultMutable"),
   ("Compress is not mapped", "compress-not-mapped", called "Compress", "the trace calls Compress"),
   ("EvalAutomorphism(Ciphertext,usint,std::map<usint,EvalKey>) on a 3-part operand: OpenFHE throws \"Ciphertext should be relinearized before.\"",
     "rotation-of-3-part-threw",
     parts 3 && noted "EvalAutomorphism(): Ciphertext should be relinearized before",
     "pin.json has a 3-component ciphertext and a note that OpenFHE's EvalAutomorphism threw on it (the call threw before it registered its key)")]

/-- When `prog.fhecheck.json` is an extractor refusal `{"format": …, "error": msg}`: the message
must be one of the expected refusals, and the data must show its reason. Anything else is a
failure (an unexplained refusal is not a pass). -/
def checkRefusal (x : Cx) : IO Unit := do
  let some msg := jStr? x.c.progJson "error"
    | x.emit "x.refusal" "prog.fhecheck.json" "extract" (some false) "glue"
        [("why", Json.str "prog.fhecheck.json is neither a decodable program nor an extractor refusal")]
  match (refusalClasses x).find? fun (sub, _) => (msg.splitOn sub).length > 1 with
  | some (_, cls, confirmed, what) =>
    x.emit "x.refusal" "prog.fhecheck.json" cls (some confirmed) "glue"
      ([("class", Json.str cls), ("message", Json.str msg), ("dataShows", Json.str what)] ++
        (if confirmed then [] else [("why", Json.str s!"the extractor refused with the expected message but the data does not show its reason: {what}")]))
  | none =>
    x.emit "x.refusal" "prog.fhecheck.json" "unclassified" (some false) "glue"
      [("class", Json.str "unclassified"), ("message", Json.str msg),
       ("why", Json.str "the extractor refused this case with a message that is not one of the expected refusals")]

end FHE.Pin
