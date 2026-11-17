import FHE.Pin.BFV.Checks
import Spec.EncryptBFV
import Spec.DecryptBFV
import FHE.Float.RNE

/-!
# FHE.Pin.BFV.ChecksEnc — OpenFHE's BFV encryption and floating-point decryption against the
trusted transcriptions `Spec.EncryptBFV` and `Spec.DecryptBFV`   (UNTRUSTED glue)

* `c.encryptBFV`: `Spec.EncryptBFV.encryptBFV t Q_k b a p u e₁ e₂` on the recorded key, stored
  plaintext and randomness, modulo the plaintext's own modulus `Q_k`, = OpenFHE's ciphertext
  (forced: `encryptBFVF`, equal to the trusted definition by `encryptBFVF_eq`; literal at small
  `N`); every stored coefficient in `[0, t)`. `c.pubkeyBFV`: `Spec.Encrypt.PublicKeyOK 1 Q s e b a`.
* `c.timesQovert`: the residues of `Spec.EncryptBFV.scaleUpCeil t Q_k p` = the recorded
  `TimesQovert` of the library, limb by limb.
* `a.decryptLib.tables`: `Spec.DecryptBFV.tables` under round-to-nearest-even binary64
  (`FHE.Float.RNE.rneA`) = the library's tables (`decryptTables`; doubles compared as exact
  rationals decoded from their bit patterns).
* `a.decryptLib.phase`: the recorded `decrypt.phase` = the residues of the trusted phase.
* `a.decryptLib`: `Spec.DecryptBFV.decrypt1 FHE.Float.RNE.rneD t qs (tables …)` on the residues of
  the phase, coefficient by coefficient, = OpenFHE's UNREDUCED raw `Decrypt` output; every value
  at most `t`; and, wherever `Spec.DecryptBFV.decLibOK? t qs B` holds at the measured noise `B`,
  the value mod `t` = the textbook `bfvDecrypt` (`Challenge.BFVDecrypt.bfvDecryptLib_eq` says it
  must). Literal `bfvDecryptLib` at small `N`.
-/

namespace FHE.Pin.BFV
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source FHE.Pin

/-! ## Encryption -/

/-- `Spec.EncryptBFV.encryptBFV` with the products as arrays (`FHE.Pin.mulArr`, Kronecker). -/
def encryptBFVF {N : ℕ} (t Q : ℕ) (b a p u e₁ e₂ : IntPoly N) : List (IntPoly N) :=
  [ofArr (mulArr b u) + e₁ + EncryptBFV.scaleUpCeil t Q p, ofArr (mulArr a u) + e₂]

/-- **`Spec.EncryptBFV.encryptBFV`.** -/
theorem encryptBFVF_eq {N : ℕ} (t Q : ℕ) (b a p u e₁ e₂ : IntPoly N) :
    encryptBFVF t Q b a p u e₁ e₂ = EncryptBFV.encryptBFV t Q b a p u e₁ e₂ := by
  simp only [encryptBFVF, EncryptBFV.encryptBFV, Encrypt.encrypt, ofArr_mulArr, Nat.cast_one, List.cons.injEq, and_true]
  constructor <;> ext i <;> simp

/-- Forced `b + a·s` reduced mod `Q` and `e` reduced mod `Q`: their equality is
`Spec.Encrypt.PublicKeyOK 1 Q s e b a` (`pubKeyF_iff`). -/
def pubKeyLhsF {N : ℕ} (K Q : ℕ) (s b a : Array ℤ) : Array (ZMod Q) :=
  toArr K (ofInt Q (ofArr (N := N) b + ofArr (mulArr (ofArr (N := N) a) (ofArr s))))

def pubKeyRhsF {N : ℕ} (K Q : ℕ) (e : Array ℤ) : Array (ZMod Q) :=
  toArr K (ofInt Q (((1 : ℕ) : ℤ) • ofArr (N := N) e))

theorem pubKeyF_iff {N : ℕ} (K Q : ℕ) (s e b a : Array ℤ) :
    (pubKeyLhsF (N := N) K Q s b a == pubKeyRhsF (N := N) K Q e) = true ↔
      Encrypt.PublicKeyOK 1 Q (ofArr (N := N) s) (ofArr e) (ofArr b) (ofArr a) := by
  constructor
  · intro h
    have := toArr_inj (eq_of_beq h)
    simpa [Encrypt.PublicKeyOK, ofArr_mulArr] using this
  · intro h
    simp only [Encrypt.PublicKeyOK] at h
    simp [pubKeyLhsF, pubKeyRhsF, ofArr_mulArr, h]

instance {N : ℕ} (t Q : ℕ) (s e b a : IntPoly N) : Decidable (Encrypt.PublicKeyOK t Q s e b a) := by
  unfold Encrypt.PublicKeyOK; infer_instance

def checkEncryptBFV (b : BX) : IO Unit := do
  let P := b.P
  let N := b.N
  let t := b.t
  let K := b.K
  -- public key and its error
  let some pub := jObj? b.c.pin "public" | return
  let pk : Option (List Nat × Array Int × Array Int) ← try
      let some bn := jStr? pub "b" | throw (IO.userError "public.b")
      let some an := jStr? pub "a" | throw (IO.userError "public.a")
      let (mb, pb) ← liftExcept (b.c.rnsPolyAny bn)
      let (ma, pa) ← liftExcept (b.c.rnsPolyAny an)
      if mb != ma then throw (IO.userError "pk.b and pk.a have different limbs")
      pure (some (mb, pb, pa))
    catch e =>
      b.emit "c.error" "pk" "publicKey" (some false) "forced" [("why", Json.str s!"{e}")]
      pure none
  let some (pkMod, pb, pa) := pk | return
  let Qpk := pkMod.foldl (· * ·) 1
  let ePk ← pkError b
  match ePk with
  | none => b.emit "c.pubkeyBFV" "pk" "PublicKeyOK" none "forced" [("why", Json.str "pk.e was not captured")]
  | some e =>
    let ok := pubKeyLhsF (N := N) K Qpk b.s pb pa == pubKeyRhsF (N := N) K Qpk e
    b.emit "c.pubkeyBFV" "pk" "PublicKeyOK" (some ok) "forced"
      [("what", Json.str "Spec.Encrypt.PublicKeyOK 1 Q s e b a (b + a·s ≡ e mod Q, noise scale 1)"),
       ("pkLimbs", Json.num pkMod.length)]
    if b.literal 2 then
      let lit := decide (Encrypt.PublicKeyOK 1 Qpk (ofArr (N := N) b.s) (ofArr e) (ofArr pb) (ofArr pa))
      b.emit "c.pubkeyBFV" "pk" "PublicKeyOK" (some lit) "literal"
      b.emit "c.pubkeyBFV.literal-vs-forced" "pk" "PublicKeyOK" (some (lit == ok)) "literal+forced"
  for enc in jArr b.c.pin "encryptions" do
    let ctId := (jStr? enc "ct").getD "?"
    if jBool enc "extended" then
      b.emit "c.encryptBFV" ctId "encrypt" none "forced"
        [("why", Json.str "EXTENDED encryption: Spec.EncryptBFV describes STANDARD encryption only")]
      continue
    try
      let some ptId := jStr? enc "pt" | throw (IO.userError "encryption without pt")
      let some pto := b.c.object? ptId | throw (IO.userError s!"no object {ptId}")
      let some ptPoly := jStr? pto "poly" | throw (IO.userError s!"{ptId}: poly")
      -- the stored plaintext: the canonical CRT lift over its own limbs (every limb holds the same
      -- integer in [0, t) when the encoder's convention holds)
      let (ptMod, p) ← liftExcept (b.c.rnsPolyAny ptPoly)
      let Qk := ptMod.foldl (· * ·) 1
      let inT := p.all fun x => decide (0 ≤ x ∧ x < (t : Int))
      let (comps, towers) ← b.x.objComps ctId
      let common : List (String × Json) :=
        [("towers", Json.num towers), ("ptLimbs", Json.num ptMod.length),
         ("storedInZeroT", boolJ inT), ("randomness", Json.str ((jStr? enc "randomness").getD "?"))]
      -- c.timesQovert: the residues of scaleUpCeil t Q_k p = the library's TimesQovert
      let sc := toArr K (EncryptBFV.scaleUpCeil t Qk (ofArr (N := N) p))
      match jStr? enc "timesQovert" with
      | some tn =>
        match b.c.polys[tn]? with
        | some te =>
          let limbsOK := te.moduli.toList == ptMod
          let mut mism : Nat := 0
          for i in [0:te.moduli.size] do
            let q : Int := te.moduli[i]!
            for j in [0:N] do
              if sc[j]! % q != (te.limbs[i]!)[j]! then mism := mism + 1
          b.emit "c.timesQovert" ctId "TimesQovert" (some (limbsOK && mism == 0 && inT)) "forced"
            (common ++ [("mismatches", Json.num mism), ("limbsOK", boolJ limbsOK),
              ("what", Json.str "residues of Spec.EncryptBFV.scaleUpCeil t Q_k p = the library's TimesQovert of the stored plaintext")])
        | none => b.emit "c.timesQovert" ctId "TimesQovert" (some false) "forced" [("why", Json.str s!"polys.txt has no {tn}")]
      | none => b.emit "c.timesQovert" ctId "TimesQovert" none "forced" [("why", Json.str "no timesQovert recorded")]
      -- c.encryptBFV
      let (some un, some e1n, some e2n) := (jStr? enc "u", jStr? enc "e1", jStr? enc "e2")
        | do
          b.emit "c.encryptBFV" ctId "encrypt" none "forced"
            (common ++ [("why", Json.str s!"randomness not captured ({(jStr? enc "randomness").getD "?"})")])
          continue
      let u ← liftExcept (b.c.intPoly un)
      let e1 ← liftExcept (b.c.intPoly e1n)
      let e2 ← liftExcept (b.c.intPoly e2n)
      let f := (encryptBFVF t Qk (ofArr (N := N) pb) (ofArr pa) (ofArr p) (ofArr u) (ofArr e1) (ofArr e2)).map
        fun c => valsOf (toArr K (ofInt Qk (toArr K c |> ofArr (N := N))))
      let recQ := comps.map fun c => valsOf (toArr K (ofInt Qk (ofArr (N := N) c)))
      let encOK := f == recQ && towers == ptMod.length
      let mm : Nat := (f.zip recQ).foldl (fun acc pr => acc + diffCount pr.1 pr.2) 0
      b.emit "c.encryptBFV" ctId "encrypt" (some (encOK && inT)) "forced"
        (common ++ [("mismatches", Json.num mm), ("relationHolds", boolJ encOK),
          ("what", Json.str "Spec.EncryptBFV.encryptBFV t Q_k b a p u e1 e2 mod Q_k = the recorded ciphertext, and every stored coefficient in [0, t)")])
      if b.literal 2 then
        let lit := (EncryptBFV.encryptBFV t Qk (ofArr (N := N) pb) (ofArr pa) (ofArr p) (ofArr u) (ofArr e1)
          (ofArr e2)).map fun c => valsOf (toArr K (ofInt Qk c))
        b.emit "c.encryptBFV" ctId "encrypt" (some (lit == recQ && towers == ptMod.length && inT)) "literal" common
        b.emit "c.encryptBFV.literal-vs-forced" ctId "encrypt" (some (lit == f)) "literal+forced"
    catch e =>
      b.emit "c.error" ctId "encryptBFV" (some false) "forced" [("why", Json.str s!"{e}")]

/-! ## Decryption -/

/-- The exact value of an IEEE-754 binary64 bit pattern (16 hex digits, big-endian); `none` for
infinities and NaNs. -/
def ofHexDouble (s : String) : Option ℚ := do
  guard (s.length == 16)
  let bits : Nat ← s.toList.foldlM (fun (acc : Nat) c =>
    let d := if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none
    d.map fun d => acc * 16 + d) 0
  let sign : ℚ := if bits / 2 ^ 63 % 2 == 1 then -1 else 1
  let ex : Nat := bits / 2 ^ 52 % 2 ^ 11
  let man : Nat := bits % 2 ^ 52
  guard (ex != 2047)
  let v : ℚ := if ex == 0 then (man : ℚ) / 2 ^ 1074
    else ((2 ^ 52 + man : ℕ) : ℚ) * (2 : ℚ) ^ ((ex : ℤ) - 1075)
  pure (sign * v)

def natsOf (j : Json) (k : String) : List Nat := (natList j k).toOption.getD []

def checkDecryptLib (b : BX) : IO Unit := do
  let N := b.N
  let t := b.t
  let some dt := jObj? b.c.pin "decryptTables" | return
  let qs := natsOf dt "qs"
  let tabT := Spec.DecryptBFV.tables FHE.Float.RNE.rneA t qs
  let fracs := fun (k : String) => (jArr dt k).toList.map fun j => (j.getStr?.toOption).bind ofHexDouble
  let intLo := natsOf dt "intLo"
  let intHi := natsOf dt "intHi"
  let fracLo := fracs "fracLo"
  let fracHi := fracs "fracHi"
  let split := Spec.DecryptBFV.pathSplit qs
  let tabOK :=
    jNat? dt "t" == some t && qs == b.c.qs &&
    intLo == tabT.map (·.intLo) && fracLo == tabT.map (some ·.fracLo) &&
    (if split then intHi == tabT.map (·.intHi) && fracHi == tabT.map (some ·.fracHi) else intHi.isEmpty && fracHi.isEmpty)
  b.emit "a.decryptLib.tables" "decryptTables" "tables" (some tabOK) "literal"
    [("limbs", Json.num qs.length), ("split", boolJ split), ("pathReduce", boolJ (Spec.DecryptBFV.pathReduce t qs)),
     ("tPow2", boolJ (Spec.DecryptBFV.isPow2 t)),
     ("decParamsOK", boolJ (Spec.DecryptBFV.decParamsOK? t qs)),
     ("what", Json.str "Spec.DecryptBFV.tables FHE.Float.RNE.rneA t qs = the library's tables (doubles as exact rationals)")]
  -- the decryption uses the TRUSTED tables, whatever the comparison above says
  let Q := qs.foldl (· * ·) 1
  for (id, o) in objList b.x do
    if jStr? o "kind" != some "ct" then continue
    let some dec := jObj? o "decrypt" | continue
    if jStr? dec "branch" != some "hps-float" then continue
    try
      let ph ← b.x.objPh id
      if ph.level != qs.length then throw (IO.userError "branch hps-float on a ciphertext without all limbs")
      let some rawName := jStr? dec "raw" | throw (IO.userError "decrypt.raw missing")
      let some re := b.c.polys[rawName]? | throw (IO.userError s!"no {rawName}")
      let raw := re.limbs[0]!
      let rawLimbOK := re.moduli == #[t] || re.moduli == #[0]
      -- the residues of the trusted phase, against the recorded decrypt.phase
      let Z := ph.Z
      let resid : Array (List Nat) := Array.ofFn (n := N) fun j =>
        qs.map fun q => (Z[j.val]! % (q : Int)).toNat
      let phaseOK ← match jStr? dec "phase" with
        | some pn =>
          match b.c.polys[pn]? with
          | some pe =>
            let ok := pe.moduli.toList == qs && (List.range qs.length).all fun i =>
              (List.range N).all fun j => (pe.limbs[i]!)[j]! == ((resid[j]!)[i]! : Int)
            b.emit "a.decryptLib.phase" id "phase" (some ok) "forced"
              [("what", Json.str "the recorded decrypt.phase (c0 + c1·s + … as the library computes it) = the residues of the trusted phase")]
            pure ok
          | none => pure false
        | none => pure true
      let _ := phaseOK
      let out : Array Nat := resid.map fun xs => Spec.DecryptBFV.decrypt1 FHE.Float.RNE.rneD t qs tabT xs
      let agree := (List.range N).all fun j => ((out[j]! : Nat) : Int) == raw[j]!
      let mism : Nat := (List.range N).foldl (fun n j => if ((out[j]! : Nat) : Int) == raw[j]! then n else n + 1) 0
      let leT := out.all (· ≤ t)
      let eqT : Nat := out.foldl (fun n v => if v == t then n + 1 else n) 0
      -- against the textbook decryption, where decLibOK? holds at the measured noise
      let progNoise := (← b.objNoise.get)[id]?
      let textbook := decryptBFVOfPhaseA N b.K t Q ph.Φ
      let noise := progNoise.getD (noiseA N b.K t Q ph.Z textbook)
      let libOK := Spec.DecryptBFV.decLibOK? t qs noise
      let tbAgree := (List.range N).all fun j => ((out[j]! % t : Nat) : Int) == ((textbook[j]!).val : Int)
      let tbMism : Nat := (List.range N).foldl (fun n j =>
        if ((out[j]! % t : Nat) : Int) == ((textbook[j]!).val : Int) then n else n + 1) 0
      b.emit "a.decryptLib" id "decrypt1" (some (agree && rawLimbOK && leT)) "forced"
        [("mismatches", Json.num mism), ("outputEqualsT", Json.num eqT), ("atMostT", boolJ leT),
         ("what", Json.str "Spec.DecryptBFV.decrypt1 FHE.Float.RNE.rneD t qs (tables) on the residues of the trusted phase = OpenFHE's unreduced Decrypt output")]
      b.emit "a.decryptLib.textbook" id "decrypt1" (if tbAgree then some true else if libOK then some false else none) "forced"
        ([("mismatches", Json.num tbMism), ("decLibOK", boolJ libOK), ("noise", natJ noise), ("noiseBits", bitsJ noise),
          ("noiseFor", Json.str (if progNoise.isSome then "the message the program computes" else "the textbook decryption itself")),
          ("what", Json.str "decrypt1 mod t = Spec.Scheme.bfvDecrypt wherever Spec.DecryptBFV.decLibOK? t qs B holds at the measured noise B")] ++
          (if tbAgree then [] else [("why", Json.str (if libOK then
            "decLibOK? holds at the measured noise but the library's decryption differs from the textbook one"
            else "decLibOK? does not hold at the measured noise: no claim"))]))
      if b.literal ph.comps.length then
        let ctQ : List (Poly qs.prod N) := ph.comps.map fun c => ofInt qs.prod (ofArr c)
        let lit := toArr b.K (Spec.DecryptBFV.bfvDecryptLib FHE.Float.RNE.rneD t qs (ofArr (N := N) b.s) ctQ)
        b.emit "a.decryptLib" id "bfvDecryptLib" (some ((List.range N).all fun j => ((lit[j]! : Nat) : Int) == raw[j]!)) "literal"
        b.emit "a.decryptLib.literal-vs-forced" id "bfvDecryptLib" (some (lit == out)) "literal+forced"
    catch e =>
      b.emit "a.error" id "decryptLib" (some false) "forced" [("why", Json.str s!"{e}")]

end FHE.Pin.BFV
