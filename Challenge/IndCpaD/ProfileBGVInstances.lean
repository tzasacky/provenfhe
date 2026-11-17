import Challenge.IndCpaD.ProfileBGV
import Challenge.Source
import Challenge.BFV

/-!
# Challenge.IndCpaD.ProfileBGVInstances — an encryption, an evaluator and a nonempty class for the library-free BGV theorem   (LOCKED statements; proofs in `Validation/IndCpaD/ProfileBGVInstances.lean`)

`Challenge.IndCpaD.ProfileBGV` states the reduction for an abstract BGV scheme with an abstract
encryption and an abstract evaluator. There is no composed BGV library evaluator in this
development; this file supplies instances of the hypotheses so that the statement is not
vacuous.

* **The evaluator** `exactEval D`: the textbook execution of the circuit's program on the input
  ciphertexts with the exact operations of `Challenge.Trace` (componentwise addition and
  subtraction with zero padding, the tensor product for `mul` and `square`, multiplication by an
  integer, `σ_g` of every component, plaintext operations on the first component or every
  component, keeping the components for `copy`/`toEval`/`toCoeff`/`dropLimbs`). It does no key
  switching and no modulus switching: on a `relin`, `keySwitch` or `modSwitch` it stops and
  returns `[]`. It reads neither the public key nor anything secret.
* `exactClass D prof`: the circuits of the profile class `admBGV D prof` whose body has none of
  `relin`, `keySwitch`, `modSwitch` (`exactOnly`).
* `exactEval_meets`: **the exact evaluator meets hypothesis (ii) on that class, at every
  profile** (its steps add no error, so they meet every budget); `correct_exactEval`: hence the
  scheme is perfectly correct there, and `bgv_prob_eq`, `bgv_prob_le` apply.
* **The encryption** `bgvData P Bk Bu B1 B2`: BGV public-key encryption `Spec.Encrypt.encrypt`
  of the stored representative `liftMsg m` at the top level, under a public key `(b, a)` with
  `b + a·s = t·e` and randomness `(u, e₁, e₂)` within the sampler bounds; `eps` is
  `freshNoise t (t − 1) (worstError …)`. Its public key carries no key-switching keys (the
  evaluator above needs none). `encOK_bgvData`: it meets hypothesis (i) when
  `2·eps < Q_top` (a closed check). The circuits of `bgvData` are triples
  (program, fresh names, plaintext constants).
* **A realistic instance**: `bgvSeal`, the parameters of `Challenge.BFV.sealBFV` (`N = 2¹³`, four
  43–44-bit primes, `t = 65537`, ternary secret) read as BGV, with error bounds 41 in the
  public key and the encryption and a ternary `u` (as `Challenge.IndCpaD.sealSetting`). `correct_exactEval_bgvSeal`:
  perfect correctness on `exactClass` at the constant profile `Spec.Budget.certified` (no
  hypothesis left); the `#guard`s show a product of two fresh encryptions plus a plaintext and
  a scaling in the class, and a circuit outside it.
-/

namespace Challenge.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.Encrypt Challenge.Source

/-- Whether an instruction is one of the exact operations of `exactStep`. -/
def exactInstr : Instr → Bool
  | .relin .. | .keySwitch .. | .modSwitch .. => false
  | _ => true

/-- The body has no key switch and no modulus switch. -/
def exactOnly (body : List Instr) : Bool := body.all exactInstr

/-- One exact step on a ciphertext environment (module docstring). -/
def exactStep (P : FullParams) (σ : Trace.CtEnv P) : Instr → Option (Trace.CtEnv P)
  | .add d a b => (σ a).bind fun ca => (σ b).map fun cb => σ.set d (padZip (· + ·) ca cb)
  | .sub d a b => (σ a).bind fun ca => (σ b).map fun cb => σ.set d (padZip (· - ·) ca cb)
  | .mul d a b => (σ a).bind fun ca => (σ b).map fun cb => σ.set d (tensorParts ca cb)
  | .square d a => (σ a).map fun ca => σ.set d (tensorParts ca ca)
  | .mulConst d a c => (σ a).map fun ca => σ.set d (ca.map (c • ·))
  | .copy d a => (σ a).map fun ca => σ.set d ca
  | .toEval d a => (σ a).map fun ca => σ.set d ca
  | .toCoeff d a => (σ a).map fun ca => σ.set d ca
  | .dropLimbs d a _ => (σ a).map fun ca => σ.set d ca
  | .automorph d a g => (σ a).map fun ca => σ.set d (ca.map (automorph g))
  | .addPlain d a p => (σ a).bind fun ca => (σ p).map fun cp => σ.set d (padZip (· + ·) ca cp)
  | .subPlain d a p => (σ a).bind fun ca => (σ p).map fun cp => σ.set d (padZip (· - ·) ca cp)
  | .mulPlain d a p => (σ a).bind fun ca => (σ p).map fun cp => σ.set d (ca.map (cp.headD 0 * ·))
  | .relin .. | .keySwitch .. | .modSwitch .. => none

/-- **The exact evaluator** (module docstring): the program's body by `exactStep` from the input
ciphertexts, the outputs in order with their message-independent levels. -/
def exactEval (D : AbsScheme) (C : D.Circ) (cs : List (ℕ × List (IntPoly D.P.src.N))) :
    List (ℕ × List (IntPoly D.P.src.N)) :=
  (((D.prog C).body.foldlM (exactStep D.Pe) (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD []

/-- The profile class restricted to bodies without key or modulus switching. -/
def exactClass (D : AbsScheme) (prof : D.Circ → Trace.Budget) (C : D.Circ) : Bool :=
  admBGV D prof C && exactOnly (D.prog C).body

/-- **The exact evaluator meets the BGV contracts at every profile** on `exactClass`. -/
theorem exactEval_meets (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget) :
    EvalMeetsBGV D prof (exactClass D prof) (fun _ C cs => exactEval D C cs) := sorry

/-- **Perfect correctness with the exact evaluator.** -/
theorem correct_exactEval (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget) :
    Correct (schemeBGV D (fun _ C cs => exactEval D C cs) (exactClass D prof)) := sorry

/-- **BGV public-key encryption at the top level as abstract data** (module docstring). -/
def bgvData (P : FullParams) (Bk Bu B1 B2 : ℕ) : AbsScheme where
  P := P
  eps := freshNoise P.src.t (P.src.t - 1) (worstError P.src.N P.secretBound Bk Bu B1 B2)
  lvl := P.src.qs.length
  PK := IntPoly P.src.N × IntPoly P.src.N
  SK := IntPoly P.src.N × IntPoly P.src.N
  ER := IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N
  Circ := Program × List Var × (Var → Poly P.src.t P.src.N)
  sec := Prod.fst
  enc := fun pk m r => (P.src.qs.length, encrypt P.src.t pk.1 pk.2 (liftMsg m) r.1 r.2.1 r.2.2)
  KeysOK := fun pk sk => SecretOK P.secretBound sk.1 ∧ normInf sk.2 ≤ Bk ∧
    PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) sk.1 sk.2 pk.1 pk.2
  GoodE := fun _ _ r => normInf r.1 ≤ Bu ∧ normInf r.2.1 ≤ B1 ∧ normInf r.2.2 ≤ B2
  prog := fun C => C.1
  fresh := fun C => C.2.1
  pt := fun C => C.2.2

/-- **The BGV encryption meets the encryption hypothesis** when the fresh noise does not wrap at
the top level. -/
theorem encOK_bgvData (P : FullParams) (Bk Bu B1 B2 : ℕ) (ht : 2 ≤ P.src.t)
    (hQ : 2 * (bgvData P Bk Bu B1 B2).eps < P.src.modulus P.src.qs.length) :
    (bgvData P Bk Bu B1 B2).EncOKBGV := sorry

/-- `sealBFV`'s parameters (`N = 2¹³`, four 43–44-bit primes, `t = 65537`, ternary secret) as
BGV. -/
def bgvSeal : FullParams :=
  { Challenge.BFV.sealBFV with src := { Challenge.BFV.sealBFV.src with kind := .bgv } }

/-- The data at `bgvSeal` with error bounds 41 (public key, `e₁`, `e₂`) and a ternary `u`. -/
def bgvSealData : AbsScheme := bgvData bgvSeal 41 1 41 41

/-- The constant profile of the computed BGV budget at `bgvSeal`, one limb per digit. -/
def bgvSealProfile (_ : bgvSealData.Circ) : Trace.Budget :=
  Spec.Budget.certified bgvSeal (Spec.Budget.uniformLayout 1)

/-- **The instance at `bgvSeal`**, every hypothesis discharged (the encryption check by the
kernel). -/
theorem correct_exactEval_bgvSeal :
    Correct (schemeBGV bgvSealData (fun _ C cs => exactEval bgvSealData C cs)
      (exactClass bgvSealData bgvSealProfile)) := sorry

/-- A product of two fresh encryptions, a plaintext addition and a scaling by 3. -/
def bgvSealCirc : bgvSealData.Circ :=
  ({ inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩, ⟨"p", 1, 4, 1, 1⟩],
     body := [.mul "c" "a" "b", .addPlain "d" "c" "p", .mulConst "o" "d" 3],
     outputs := ["o"] }, ["a", "b"], fun _ => 0)

-- In the class (the product leaves three components; textbook decryption reads them all).
#guard exactClass bgvSealData bgvSealProfile bgvSealCirc
-- In the profile class, outside the exact evaluator's class: a relinearization.
#guard admBGV bgvSealData bgvSealProfile
  ({ bgvSealCirc.1 with body := bgvSealCirc.1.body ++ [.relin "o" "o"] }, ["a", "b"], fun _ => 0)
#guard !exactClass bgvSealData bgvSealProfile
  ({ bgvSealCirc.1 with body := bgvSealCirc.1.body ++ [.relin "o" "o"] }, ["a", "b"], fun _ => 0)
-- Outside the profile class: three successive products of fresh encryptions (the noise of the
-- worst case outgrows `Q/2`).
#guard !admBGV bgvSealData bgvSealProfile
  ({ inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩],
     body := [.mul "c" "a" "b", .mul "c" "c" "a", .mul "c" "c" "b"], outputs := ["c"] },
    ["a", "b"], fun _ => 0)

end Challenge.IndCpaDProfile
