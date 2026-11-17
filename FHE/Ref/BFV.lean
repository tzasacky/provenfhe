import FHE.Ref.BGV
import Challenge.IndCpaD.LMBFV

/-!
# FHE.Ref.BFV — the executable reference BFV: evaluator, key generation, encryption, PROVED equal
to the locked definitions   (UNTRUSTED glue; the theorems are kernel-checked)

* `bfvStepA` is `Challenge.IndCpaDLM.bfvStep` on arrays (textbook products `bfvMul` by the
  Kronecker product, plaintext operations, rounding modulus switch, BFV relinearization and key
  switching `relinBFV`, `keySwitchBFV` with the keys of the operand's level); `bfvEvalA` is
  `interpEval` of it: **`bfvEvalA_eq`**.
* `bfvKeyGenA` is `Challenge.IndCpaDLM.bfvKeyGen` (**`bfvKeyGenA_eq`**); `encBFVA` is
  `Spec.EncryptBFV.encryptBFV` and the encryption of `bfvKSData` (**`encBFVA_eq`**).
* Decryption and `sem` are in `FHE.Ref.Run` (`decBFVA_eq`, `semA_eq`).
-/

namespace FHE.Ref
open Spec Spec.NPoly Spec.Scheme FHE.Pin Spec.Source Spec.IndCpaDProfile Spec.Budget
  Challenge.IndCpaDLM Challenge.BFV Challenge.RealizeBFV

/-! ## The textbook operations -/

/-- `⌊t·a/Q⌉` coefficientwise (`Challenge.BFV.scaleRound`). -/
def scaleRoundA (N t Q : ℕ) (a : Array ℤ) : Array ℤ := mapA N (fun z : ℤ => roundDiv (t * z) Q) a

/-- The centred representative modulo `Q` (`centered (ofInt Q ·)`). -/
def centA (N Q : ℕ) (a : Array ℤ) : Array ℤ := mapA N (fun z : ℤ => ((z : ZMod Q)).valMinAbs) a

/-- `Challenge.BFV.bfvMul` on arrays. -/
def bfvMulA (N t Q : ℕ) (c d : List (Array ℤ)) : List (Array ℤ) :=
  (tensorA N (c.map (centA N Q)) (d.map (centA N Q))).map (scaleRoundA N t Q)

theorem bfvMul_def {N : ℕ} (t Q : ℕ) (c d : List (IntPoly N)) :
    bfvMul t Q c d = (Challenge.Source.tensor (c.map fun x => centered (ofInt Q x))
      (d.map fun x => centered (ofInt Q x))).map (scaleRound t Q) := rfl

theorem wC_bfvMulA {N : ℕ} (t Q : ℕ) (c d : List (Array ℤ)) :
    wC N (bfvMulA N t Q c d) = bfvMul t Q (wC N c) (wC N d) := by
  have hc : ∀ x : Array ℤ, (ofArr (centA N Q x) : IntPoly N) = centered (ofInt Q (ofArr x)) := by
    intro x; rw [centA, ofArr_mapA]; rfl
  have hs : ∀ x : Array ℤ, (ofArr (scaleRoundA N t Q x) : IntPoly N) = scaleRound t Q (ofArr x) := by
    intro x; rw [scaleRoundA, ofArr_mapA]; rfl
  rw [bfvMul_def, bfvMulA, wC_map _ _ hs, wC_tensorA, wC_map _ (fun x => centered (ofInt Q x)) hc,
    wC_map _ (fun x => centered (ofInt Q x)) hc]

/-- `⌊c/q⌉` coefficientwise (`Challenge.BFV.bfvModSwitchComp`). -/
def bfvMsA (N q : ℕ) (c : Array ℤ) : Array ℤ := mapA N (fun z : ℤ => roundDiv z q) c

theorem ofArr_bfvMsA {N : ℕ} (q : ℕ) (c : Array ℤ) :
    (ofArr (bfvMsA N q c) : IntPoly N) = bfvModSwitchComp q (ofArr c) := by
  rw [bfvMsA, ofArr_mapA]; rfl

/-- `Challenge.BFV.bfvAddPlain` / `bfvSubPlain` on arrays: `c₀ ± ⌊Q/t⌋·p`. -/
def bfvPlainA (N : ℕ) (f : Array ℤ → Array ℤ → Array ℤ) (t Q : ℕ) (c : List (Array ℤ))
    (p : Array ℤ) : List (Array ℤ) :=
  padZipA N f c [smulA N ((Q / t : ℕ) : ℤ) p]

theorem wC_bfvAddPlainA {N : ℕ} (t Q : ℕ) (c : List (Array ℤ)) (p : Array ℤ) :
    wC N (bfvPlainA N (addA N) t Q c p) = bfvAddPlain t Q (wC N c) (ofArr p) := by
  rw [bfvPlainA, wC_padZipA _ (· + ·) (fun a b => ofArr_addA a b)]
  show _ = Challenge.Source.padZip (· + ·) (wC N c) [((Q / t : ℕ) : ℤ) • ofArr p]
  simp [wC]

theorem wC_bfvSubPlainA {N : ℕ} (t Q : ℕ) (c : List (Array ℤ)) (p : Array ℤ) :
    wC N (bfvPlainA N (subA N) t Q c p) = bfvSubPlain t Q (wC N c) (ofArr p) := by
  rw [bfvPlainA, wC_padZipA _ (· - ·) (fun a b => ofArr_subA a b)]
  show _ = Challenge.Source.padZip (· - ·) (wC N c) [((Q / t : ℕ) : ℤ) • ofArr p]
  simp [wC]

/-! ## One step -/

/-- **`Challenge.IndCpaDLM.bfvStep` on arrays.** -/
def bfvStepA (P : FullParams) (lay : KSLayout) (rk : ℕ → List (Array ℤ × Array ℤ))
    (gk : ℕ → ℕ → List (Array ℤ × Array ℤ)) (ρ : Env P.src) (σ : CtEnvA) : Instr → Option CtEnvA
  | .add d a b => (getA σ a).bind fun ca => (getA σ b).map fun cb => setA σ d (padZipA P.src.N (addA P.src.N) ca cb)
  | .sub d a b => (getA σ a).bind fun ca => (getA σ b).map fun cb => setA σ d (padZipA P.src.N (subA P.src.N) ca cb)
  | .mul d a b => (ρ a).bind fun x => (getA σ a).bind fun ca => (getA σ b).map fun cb =>
      setA σ d (bfvMulA P.src.N P.src.t (P.src.modulus x.level) ca cb)
  | .square d a => (ρ a).bind fun x => (getA σ a).map fun ca =>
      setA σ d (bfvMulA P.src.N P.src.t (P.src.modulus x.level) ca ca)
  | .mulConst d a c => (getA σ a).map fun ca => setA σ d (ca.map (smulA P.src.N c))
  | .copy d a => (getA σ a).map fun ca => setA σ d ca
  | .toEval d a => (getA σ a).map fun ca => setA σ d ca
  | .toCoeff d a => (getA σ a).map fun ca => setA σ d ca
  | .dropLimbs d a _ => (getA σ a).map fun ca => setA σ d ca
  | .automorph d a g => (getA σ a).map fun ca => setA σ d (ca.map (autoA P.src.N g))
  | .addPlain d a p => (ρ a).bind fun x => (getA σ a).bind fun ca => (getA σ p).map fun cp =>
      setA σ d (bfvPlainA P.src.N (addA P.src.N) P.src.t (P.src.modulus x.level) ca
        (cp.headD (zeroA P.src.N)))
  | .subPlain d a p => (ρ a).bind fun x => (getA σ a).bind fun ca => (getA σ p).map fun cp =>
      setA σ d (bfvPlainA P.src.N (subA P.src.N) P.src.t (P.src.modulus x.level) ca
        (cp.headD (zeroA P.src.N)))
  | .mulPlain d a p => (getA σ a).bind fun ca => (getA σ p).map fun cp =>
      setA σ d (ca.map (mulA P.src.N (cp.headD (zeroA P.src.N))))
  | .relin d a => (ρ a).bind fun x => (getA σ a).map fun ca =>
      setA σ d (relinBFVA P lay x.level ca (rk x.level))
  | .keySwitch d a => (ρ a).bind fun x => (getA σ a).map fun ca =>
      setA σ d (keySwitchBFVA P lay x.level ca (gk x.key x.level))
  | .modSwitch d a => (ρ a).bind fun x => (getA σ a).map fun ca =>
      setA σ d (ca.map (bfvMsA P.src.N P.src.qs[x.level - 1]!))

/-- **One step of the array evaluator is `bfvStep`.** -/
theorem bfvStepA_spec (P : FullParams) (lay : KSLayout) (rk : ℕ → List (Array ℤ × Array ℤ))
    (gk : ℕ → ℕ → List (Array ℤ × Array ℤ)) (ρ : Env P.src) (σ : CtEnvA) (i : Instr) :
    (bfvStepA P lay rk gk ρ σ i).map (wE (P := P)) =
      bfvStep P lay (fun ℓ => wK P.src.N (rk ℓ)) (fun g ℓ => wK P.src.N (gk g ℓ)) ρ (wE σ) i := by
  cases i with
  | add d a b => exact shapeB (P := P) σ d a b _ _ (wC_padZipA _ _ fun x y => ofArr_addA x y)
  | sub d a b => exact shapeB (P := P) σ d a b _ _ (wC_padZipA _ _ fun x y => ofArr_subA x y)
  | mul d a b =>
    show ((ρ a).bind fun x => (getA σ a).bind fun ca => (getA σ b).map fun cb =>
        setA σ d (bfvMulA P.src.N P.src.t (P.src.modulus x.level) ca cb)).map wE =
      (ρ a).bind fun x => ((wE σ) a).bind fun ca => ((wE σ) b).map fun cb =>
        (wE (P := P) σ).set d (bfvMul P.src.t (P.src.modulus x.level) ca cb)
    cases ρ a with
    | none => rfl
    | some x => exact shapeB (P := P) σ d a b _ _ (wC_bfvMulA _ _)
  | square d a =>
    show ((ρ a).bind fun x => (getA σ a).map fun ca =>
        setA σ d (bfvMulA P.src.N P.src.t (P.src.modulus x.level) ca ca)).map wE =
      (ρ a).bind fun x => ((wE σ) a).map fun ca =>
        (wE (P := P) σ).set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeM (P := P) σ d a (fun ca => bfvMulA P.src.N P.src.t (P.src.modulus x.level) ca ca)
        (fun ca => bfvMul P.src.t (P.src.modulus x.level) ca ca) fun ca => wC_bfvMulA _ _ ca ca
  | mulConst d a c =>
    exact shapeM (P := P) σ d a _ (fun ca => ca.map (bfvMulConst c))
      (wC_map _ _ fun x => by rw [ofArr_smulA]; rfl)
  | copy d a => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | toEval d a => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | toCoeff d a => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | dropLimbs d a n => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | automorph d a g =>
    exact shapeM (P := P) σ d a _ (fun ca => ca.map (automorph g)) (wC_map _ _ fun x => ofArr_autoA g x)
  | addPlain d a p =>
    show ((ρ a).bind fun x => (getA σ a).bind fun ca => (getA σ p).map fun cp =>
        setA σ d (bfvPlainA P.src.N (addA P.src.N) P.src.t (P.src.modulus x.level) ca
          (cp.headD (zeroA P.src.N)))).map wE =
      (ρ a).bind fun x => ((wE σ) a).bind fun ca => ((wE σ) p).map fun cp =>
        (wE (P := P) σ).set d (bfvAddPlain P.src.t (P.src.modulus x.level) ca (cp.headD 0))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeB (P := P) σ d a p _ _ fun ca cp => by rw [wC_headD]; exact wC_bfvAddPlainA _ _ _ _
  | subPlain d a p =>
    show ((ρ a).bind fun x => (getA σ a).bind fun ca => (getA σ p).map fun cp =>
        setA σ d (bfvPlainA P.src.N (subA P.src.N) P.src.t (P.src.modulus x.level) ca
          (cp.headD (zeroA P.src.N)))).map wE =
      (ρ a).bind fun x => ((wE σ) a).bind fun ca => ((wE σ) p).map fun cp =>
        (wE (P := P) σ).set d (bfvSubPlain P.src.t (P.src.modulus x.level) ca (cp.headD 0))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeB (P := P) σ d a p _ _ fun ca cp => by rw [wC_headD]; exact wC_bfvSubPlainA _ _ _ _
  | mulPlain d a p =>
    exact shapeB (P := P) σ d a p _ (fun ca cp => ca.map (cp.headD 0 * ·)) fun ca cp => by
      rw [wC_headD]; exact wC_map _ _ (fun x => ofArr_mulA _ x) ca
  | relin d a =>
    show ((ρ a).bind fun x => (getA σ a).map fun ca => setA σ d (relinBFVA P lay x.level ca (rk x.level))).map wE =
      (ρ a).bind fun x => ((wE σ) a).map fun ca =>
        (wE (P := P) σ).set d (relinBFV P lay x.level ca (wK P.src.N (rk x.level)))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeM (P := P) σ d a (fun ca => relinBFVA P lay x.level ca (rk x.level))
        (fun ca => relinBFV P lay x.level ca (wK P.src.N (rk x.level)))
        fun ca => wC_relinBFVA P lay x.level ca (rk x.level)
  | keySwitch d a =>
    show ((ρ a).bind fun x => (getA σ a).map fun ca =>
        setA σ d (keySwitchBFVA P lay x.level ca (gk x.key x.level))).map wE =
      (ρ a).bind fun x => ((wE σ) a).map fun ca =>
        (wE (P := P) σ).set d (keySwitchBFV P lay x.level ca (wK P.src.N (gk x.key x.level)))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeM (P := P) σ d a (fun ca => keySwitchBFVA P lay x.level ca (gk x.key x.level))
        (fun ca => keySwitchBFV P lay x.level ca (wK P.src.N (gk x.key x.level)))
        fun ca => wC_keySwitchBFVA P lay x.level ca (gk x.key x.level)
  | modSwitch d a =>
    show ((ρ a).bind fun x => (getA σ a).map fun ca =>
        setA σ d (ca.map (bfvMsA P.src.N P.src.qs[x.level - 1]!))).map wE =
      (ρ a).bind fun x => ((wE σ) a).map fun ca =>
        (wE (P := P) σ).set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeM (P := P) σ d a (fun ca => ca.map (bfvMsA P.src.N P.src.qs[x.level - 1]!))
        (fun ca => ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))
        (wC_map _ _ fun y => ofArr_bfvMsA _ y)

/-! ## The evaluator -/

/-- **The executable reference BFV evaluator**: `interpEval` of `bfvStep`, on arrays. -/
def bfvEvalA (D : AbsScheme) (lay : KSLayout) (rk : ℕ → List (Array ℤ × Array ℤ))
    (gk : ℕ → ℕ → List (Array ℤ × Array ℤ)) (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    List (ℕ × List (Array ℤ)) :=
  evalA D (bfvStepA D.Pe lay rk gk) C cs

theorem irun_nil (D : AbsScheme) (stepF : StepFn D) (pk : D.PK) (ρ : Env D.P.src)
    (σ : Trace.CtEnv D.Pe) : irun D stepF pk [] ρ σ = some σ := rfl

theorem irun_cons (D : AbsScheme) (stepF : StepFn D) (pk : D.PK) (i : Instr) (is : List Instr)
    (ρ : Env D.P.src) (σ : Trace.CtEnv D.Pe) :
    irun D stepF pk (i :: is) ρ σ = (step D.P.src ρ i).bind fun ρ' =>
      (stepF pk ρ σ i).bind fun σ' => irun D stepF pk is ρ' σ' := rfl

/-- **The executable reference BFV evaluator is `interpEval` of `bfvStepFn`**, for every abstract
scheme, layout, public key whose evaluation keys are the arrays `rk`, `gk`, circuit and input
ciphertexts. -/
theorem bfvEvalA_eq (D : AbsScheme) (lay : KSLayout)
    (rkF : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gkF : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) (pk : D.PK)
    (rk : ℕ → List (Array ℤ × Array ℤ)) (gk : ℕ → ℕ → List (Array ℤ × Array ℤ))
    (hrk : rkF pk = fun ℓ => wK D.P.src.N (rk ℓ)) (hgk : gkF pk = fun g ℓ => wK D.P.src.N (gk g ℓ))
    (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    wIn D.P.src.N (bfvEvalA D lay rk gk C cs) =
      interpEval D (bfvStepFn D lay rkF gkF) pk C (wIn D.P.src.N cs) := by
  have hst : ∀ ρ σ i, (bfvStepA D.Pe lay rk gk ρ σ i).map (wE (P := D.Pe)) =
      bfvStepFn D lay rkF gkF pk ρ (wE σ) i := by
    intro ρ σ i
    show _ = bfvStep D.Pe lay (rkF pk) (gkF pk) ρ (wE σ) i
    rw [hrk, hgk]
    exact bfvStepA_spec D.Pe lay rk gk ρ σ i
  exact evalA_spec D (bfvStepA D.Pe lay rk gk) (bfvStepFn D lay rkF gkF pk) hst
    (irun D (bfvStepFn D lay rkF gkF) pk) (irun_nil D _ pk) (irun_cons D _ pk) C cs

/-! ## Key generation and encryption -/

/-- `Challenge.IndCpaDLM.bfvGadgetGen` on arrays; `T` is `tgtA N s tgt`, computed once. -/
def bfvGadgetGenA (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (T s : Array ℤ) (as es : List (Array ℤ)) :
    List (Array ℤ × Array ℤ) :=
  (List.range (lay.sizes ℓ).length).map fun j =>
    (addA P.src.N (subA P.src.N (es.getD j (zeroA P.src.N)) (mulA P.src.N (as.getD j (zeroA P.src.N)) s))
      (smulA P.src.N ((gadgetFactor (specialProd P) (digitModuli P lay ℓ) j : ℕ) : ℤ) T),
     as.getD j (zeroA P.src.N))

theorem bfvGadgetGen_def (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (tgt : KeyTarget)
    (s : IntPoly P.src.N) (as es : List (IntPoly P.src.N)) :
    bfvGadgetGen P lay ℓ tgt s as es = (List.range (lay.sizes ℓ).length).map fun j =>
      (es.getD j 0 - as.getD j 0 * s +
          ((gadgetFactor (specialProd P) (digitModuli P lay ℓ) j : ℕ) : ℤ) • tgt.eval s,
        as.getD j 0) := rfl

theorem bfvGadgetGenA_eq (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (tgt : KeyTarget) (s : Array ℤ)
    (as es : List (Array ℤ)) :
    wK P.src.N (bfvGadgetGenA P lay ℓ (tgtA P.src.N s tgt) s as es) =
      bfvGadgetGen P lay ℓ tgt (ofArr s) (as.map ofArr) (es.map ofArr) := by
  rw [bfvGadgetGen_def, bfvGadgetGenA, wK, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, map_getD, ofArr_addA, ofArr_subA, ofArr_smulA, ofArr_mulA, ofArr_tgtA]

/-- The BFV public key on arrays. -/
abbrev BFVPKA : Type :=
  Array ℤ × Array ℤ × (ℕ → List (Array ℤ × Array ℤ)) × (ℕ → ℕ → List (Array ℤ × Array ℤ))

/-- The BFV public key it stands for. -/
def wPKB (N : ℕ) (pk : BFVPKA) : BFVPK N :=
  (ofArr pk.1, ofArr pk.2.1, fun ℓ => wK N (pk.2.2.1 ℓ), fun g ℓ => wK N (pk.2.2.2 g ℓ))

/-- **`Challenge.IndCpaDLM.bfvKeyGen` on arrays.** -/
def bfvKeyGenA (P : FullParams) (lay : KSLayout) (s e a : Array ℤ) (ra re : ℕ → List (Array ℤ))
    (ga ge : ℕ → ℕ → List (Array ℤ)) : BFVPKA :=
  let s2 := tgtA P.src.N s .square
  (subA P.src.N e (mulA P.src.N a s), a,
    fun ℓ => bfvGadgetGenA P lay ℓ s2 s (ra ℓ) (re ℓ),
    fun g ℓ => bfvGadgetGenA P lay ℓ (tgtA P.src.N s (.galois g)) s (ga g ℓ) (ge g ℓ))

/-- **The executable BFV key generation is `bfvKeyGen`**, for all secrets, errors and uniform
parts. -/
theorem bfvKeyGenA_eq (P : FullParams) (lay : KSLayout) (s e a : Array ℤ) (ra re : ℕ → List (Array ℤ))
    (ga ge : ℕ → ℕ → List (Array ℤ)) :
    wPKB P.src.N (bfvKeyGenA P lay s e a ra re ga ge) =
      bfvKeyGen P lay (ofArr s) (ofArr e) (ofArr a) (fun ℓ => (ra ℓ).map ofArr)
        (fun ℓ => (re ℓ).map ofArr) (fun g ℓ => (ga g ℓ).map ofArr) (fun g ℓ => (ge g ℓ).map ofArr) := by
  show (_, _, _, _) = (ofArr e - ofArr a * ofArr s, ofArr a,
    fun ℓ => bfvGadgetGen P lay ℓ .square (ofArr s) ((ra ℓ).map ofArr) ((re ℓ).map ofArr),
    fun g ℓ => bfvGadgetGen P lay ℓ (.galois g) (ofArr s) ((ga g ℓ).map ofArr) ((ge g ℓ).map ofArr))
  simp only [bfvKeyGenA, ofArr_subA, ofArr_mulA, bfvGadgetGenA_eq]

/-- `Spec.EncryptBFV.scaleUpCeil` on arrays: `⌈Q·p/t⌉`. -/
def scaleUpCeilA (N t Q : ℕ) (p : Array ℤ) : Array ℤ :=
  mapA N (fun z : ℤ => ((Q : ℤ) * z + (-((Q : ℤ) * z)) % (t : ℤ)) / (t : ℤ)) p

/-- `Spec.EncryptBFV.encryptBFV` on arrays. -/
def encBFVA (N t Q : ℕ) (b a p u e₁ e₂ : Array ℤ) : List (Array ℤ) :=
  encA N 1 b a (scaleUpCeilA N t Q p) u e₁ e₂

theorem encBFVA_spec (N t Q : ℕ) (b a p u e₁ e₂ : Array ℤ) :
    wC N (encBFVA N t Q b a p u e₁ e₂) =
      EncryptBFV.encryptBFV t Q (ofArr b) (ofArr a) (ofArr p) (ofArr u) (ofArr e₁) (ofArr e₂) := by
  rw [encBFVA, encA_eq]
  have h : (ofArr (scaleUpCeilA N t Q p) : IntPoly N) = EncryptBFV.scaleUpCeil t Q (ofArr p) := by
    rw [scaleUpCeilA, ofArr_mapA]; rfl
  rw [h]; rfl

/-- **The executable BFV encryption is the encryption of `bfvKSData`.** -/
theorem encBFVA_eq (P : FullParams) (lay : KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ)
    (pk : BFVPKA) (m : Poly P.src.t P.src.N) (u e₁ e₂ : Array ℤ) :
    (bfvKSData P lay rots Bk Bu B1 B2).enc (wPKB P.src.N pk) m (ofArr u, ofArr e₁, ofArr e₂) =
      (P.src.qs.length, wC P.src.N (encBFVA P.src.N P.src.t (P.src.modulus P.src.qs.length)
        pk.1 pk.2.1 (force P.src.N (Encrypt.liftMsg m)) u e₁ e₂)) := by
  rw [encBFVA_spec, ofArr_force]
  rfl

end FHE.Ref
