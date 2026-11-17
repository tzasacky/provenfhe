import FHE.Ref.KeySwitch
import FHE.Ref.Run
import Challenge.IndCpaD.ProfileBGVKS

/-!
# FHE.Ref.BGV — the executable reference BGV: evaluator, key generation, encryption, PROVED equal
to the locked definitions   (UNTRUSTED glue; the theorems are kernel-checked)

* `ksEvalA` is `Challenge.IndCpaDProfile.ksEval` (exact operations, hybrid relinearization and
  key switching with the top-level keys, t-corrected modulus switch) on arrays:
  **`ksEvalA_eq`**: `wIn N (ksEvalA D lay rk gk C cs) = ksEval D lay (wK N rk) (fun g => wK N (gk g)) C (wIn N cs)`
  for every abstract scheme `D`, layout, keys, circuit and input ciphertexts.
* `keyGenA` is `Challenge.IndCpaDProfile.keyGen` (**`keyGenA_eq`**), with the gadget keys of
  `gadgetGen` (**`gadgetGenA_eq`**); `encA` is `Spec.Encrypt.encrypt` (**`encA_eq`**), and
  **`encBGVA_eq`** is the encryption of `bgvKSData`.
* Decryption and `sem` are in `FHE.Ref.Run` (`decBGVA_eq`, `semA_eq`).
-/

namespace FHE.Ref
open Spec Spec.NPoly Spec.Scheme FHE.Pin Spec.Source Spec.IndCpaDProfile Spec.Budget
  Challenge.Realize Challenge.IndCpaDProfile

/-! ## One step -/

/-- The t-corrected modulus switch of one component (`Challenge.Source.bgvModSwitchComp`). -/
def msA (N t q : ℕ) (c : Array ℤ) : Array ℤ :=
  mapA N (fun z : ℤ =>
    let r : ZMod q := ((-z : ℤ) : ZMod q) * (t : ZMod q)⁻¹
    (z + (t : ℤ) * r.valMinAbs) / q) c

theorem ofArr_msA {N : ℕ} (t q : ℕ) (c : Array ℤ) :
    (ofArr (msA N t q c) : IntPoly N) = Challenge.Source.bgvModSwitchComp t q (ofArr c) := by
  rw [msA, ofArr_mapA]; rfl

/-- `Challenge.IndCpaDProfile.ksStep` on arrays (with `exactStep` for the exact operations). -/
def ksStepA (P : FullParams) (lay : KSLayout) (rk : List (Array ℤ × Array ℤ))
    (gk : ℕ → List (Array ℤ × Array ℤ)) (ρ : Env P.src) (σ : CtEnvA) : Instr → Option CtEnvA
  | .add d a b => (getA σ a).bind fun ca => (getA σ b).map fun cb => setA σ d (padZipA P.src.N (addA P.src.N) ca cb)
  | .sub d a b => (getA σ a).bind fun ca => (getA σ b).map fun cb => setA σ d (padZipA P.src.N (subA P.src.N) ca cb)
  | .mul d a b => (getA σ a).bind fun ca => (getA σ b).map fun cb => setA σ d (tensorPartsA P.src.N ca cb)
  | .square d a => (getA σ a).map fun ca => setA σ d (tensorPartsA P.src.N ca ca)
  | .mulConst d a c => (getA σ a).map fun ca => setA σ d (ca.map (smulA P.src.N c))
  | .copy d a => (getA σ a).map fun ca => setA σ d ca
  | .toEval d a => (getA σ a).map fun ca => setA σ d ca
  | .toCoeff d a => (getA σ a).map fun ca => setA σ d ca
  | .dropLimbs d a _ => (getA σ a).map fun ca => setA σ d ca
  | .automorph d a g => (getA σ a).map fun ca => setA σ d (ca.map (autoA P.src.N g))
  | .addPlain d a p => (getA σ a).bind fun ca => (getA σ p).map fun cp => setA σ d (padZipA P.src.N (addA P.src.N) ca cp)
  | .subPlain d a p => (getA σ a).bind fun ca => (getA σ p).map fun cp => setA σ d (padZipA P.src.N (subA P.src.N) ca cp)
  | .mulPlain d a p => (getA σ a).bind fun ca => (getA σ p).map fun cp =>
      setA σ d (ca.map (mulA P.src.N (cp.headD (zeroA P.src.N))))
  | .relin d a => (ρ a).bind fun x => (getA σ a).map fun ca => setA σ d (relinA P lay x.level ca rk)
  | .keySwitch d a => (ρ a).bind fun x => (getA σ a).map fun ca =>
      setA σ d (keySwitchA P lay x.level ca (gk x.key))
  | .modSwitch d a => (ρ a).bind fun x => (getA σ a).map fun ca =>
      setA σ d (ca.map (msA P.src.N P.src.t P.src.qs[x.level - 1]!))

section
variable {N : ℕ}
theorem wC_map (f : Array ℤ → Array ℤ) (F : IntPoly N → IntPoly N)
    (h : ∀ a, (ofArr (f a) : IntPoly N) = F (ofArr a)) (ca : List (Array ℤ)) :
    wC N (ca.map f) = (wC N ca).map F := by
  simp [wC, h]
end

/-- **One step of the array evaluator is `ksStep`.** -/
theorem ksStepA_spec (P : FullParams) (lay : KSLayout) (rk : List (Array ℤ × Array ℤ))
    (gk : ℕ → List (Array ℤ × Array ℤ)) (ρ : Env P.src) (σ : CtEnvA) (i : Instr) :
    (ksStepA P lay rk gk ρ σ i).map (wE (P := P)) =
      ksStep P lay (wK P.src.N rk) (fun g => wK P.src.N (gk g)) ρ (wE σ) i := by
  cases i with
  | add d a b => exact shapeB (P := P) σ d a b _ _ (wC_padZipA _ _ fun x y => ofArr_addA x y)
  | sub d a b => exact shapeB (P := P) σ d a b _ _ (wC_padZipA _ _ fun x y => ofArr_subA x y)
  | mul d a b => exact shapeB (P := P) σ d a b _ _ wC_tensorPartsA
  | square d a => exact shapeM (P := P) σ d a _ (fun ca => Challenge.Source.tensorParts ca ca) (fun ca => wC_tensorPartsA ca ca)
  | mulConst d a c => exact shapeM (P := P) σ d a _ (fun ca => ca.map (c • ·)) (wC_map _ _ fun x => ofArr_smulA c x)
  | copy d a => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | toEval d a => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | toCoeff d a => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | dropLimbs d a n => exact shapeM (P := P) σ d a _ (fun ca => ca) fun _ => rfl
  | automorph d a g => exact shapeM (P := P) σ d a _ (fun ca => ca.map (automorph g)) (wC_map _ _ fun x => ofArr_autoA g x)
  | addPlain d a p => exact shapeB (P := P) σ d a p _ _ (wC_padZipA _ _ fun x y => ofArr_addA x y)
  | subPlain d a p => exact shapeB (P := P) σ d a p _ _ (wC_padZipA _ _ fun x y => ofArr_subA x y)
  | mulPlain d a p =>
    exact shapeB (P := P) σ d a p _ (fun ca cp => ca.map (cp.headD 0 * ·)) fun ca cp => by
      rw [wC_headD]; exact wC_map _ _ (fun x => ofArr_mulA _ x) ca
  | relin d a =>
    show ((ρ a).bind fun x => (getA σ a).map fun ca => setA σ d (relinA P lay x.level ca rk)).map wE =
      (ρ a).bind fun x => ((wE σ) a).map fun ca =>
        (wE (P := P) σ).set d (relinOpenFHE P lay x.level ca (wK P.src.N rk))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeM (P := P) σ d a (fun ca => relinA P lay x.level ca rk)
        (fun ca => relinOpenFHE P lay x.level ca (wK P.src.N rk)) fun ca => wC_relinA P lay x.level ca rk
  | keySwitch d a =>
    show ((ρ a).bind fun x => (getA σ a).map fun ca => setA σ d (keySwitchA P lay x.level ca (gk x.key))).map wE =
      (ρ a).bind fun x => ((wE σ) a).map fun ca =>
        (wE (P := P) σ).set d (keySwitchOpenFHE P lay x.level ca (wK P.src.N (gk x.key)))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeM (P := P) σ d a (fun ca => keySwitchA P lay x.level ca (gk x.key))
        (fun ca => keySwitchOpenFHE P lay x.level ca (wK P.src.N (gk x.key)))
        fun ca => wC_keySwitchA P lay x.level ca (gk x.key)
  | modSwitch d a =>
    show ((ρ a).bind fun x => (getA σ a).map fun ca =>
        setA σ d (ca.map (msA P.src.N P.src.t P.src.qs[x.level - 1]!))).map wE =
      (ρ a).bind fun x => ((wE σ) a).map fun ca =>
        (wE (P := P) σ).set d (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!))
    cases ρ a with
    | none => rfl
    | some x =>
      exact shapeM (P := P) σ d a (fun ca => ca.map (msA P.src.N P.src.t P.src.qs[x.level - 1]!))
        (fun ca => ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!))
        (wC_map _ _ fun y => ofArr_msA _ _ y)

/-! ## The evaluator -/

/-- **The executable reference BGV evaluator**: `ksEval` on arrays. -/
def ksEvalA (D : AbsScheme) (lay : KSLayout) (rk : List (Array ℤ × Array ℤ))
    (gk : ℕ → List (Array ℤ × Array ℤ)) (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    List (ℕ × List (Array ℤ)) :=
  evalA D (ksStepA D.Pe lay rk gk) C cs

theorem ksRun_nil (P : FullParams) (lay : KSLayout) (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N)) (ρ : Env P.src) (σ : Trace.CtEnv P) :
    ksRun P lay rk gk [] ρ σ = some σ := rfl

theorem ksRun_cons (P : FullParams) (lay : KSLayout) (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N)) (i : Instr) (is : List Instr)
    (ρ : Env P.src) (σ : Trace.CtEnv P) :
    ksRun P lay rk gk (i :: is) ρ σ = (step P.src ρ i).bind fun ρ' =>
      (ksStep P lay rk gk ρ σ i).bind fun σ' => ksRun P lay rk gk is ρ' σ' := rfl

/-- **The executable reference evaluator is `ksEval`**, for every abstract scheme, layout,
relinearization keys, rotation keys, circuit and input ciphertexts (all arrays). -/
theorem ksEvalA_eq (D : AbsScheme) (lay : KSLayout) (rk : List (Array ℤ × Array ℤ))
    (gk : ℕ → List (Array ℤ × Array ℤ)) (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    wIn D.P.src.N (ksEvalA D lay rk gk C cs) =
      ksEval D lay (wK D.P.src.N rk) (fun g => wK D.P.src.N (gk g)) C (wIn D.P.src.N cs) :=
  evalA_spec D (ksStepA D.Pe lay rk gk)
    (fun ρ σ i => ksStep D.Pe lay (wK D.P.src.N rk) (fun g => wK D.P.src.N (gk g)) ρ σ i)
    (fun ρ σ i => ksStepA_spec D.Pe lay rk gk ρ σ i)
    (ksRun D.Pe lay (wK D.P.src.N rk) (fun g => wK D.P.src.N (gk g)))
    (ksRun_nil D.Pe _ _ _) (ksRun_cons D.Pe _ _ _) C cs

/-! ## Key generation and encryption -/

/-- `KeyTarget.eval` on arrays: `s·s` or `σ_g(s)`. -/
def tgtA (N : ℕ) (s : Array ℤ) : KeyTarget → Array ℤ
  | .square => mulA N s s
  | .galois g => autoA N g s

theorem ofArr_tgtA {N : ℕ} (s : Array ℤ) (tgt : KeyTarget) :
    (ofArr (tgtA N s tgt) : IntPoly N) = tgt.eval (ofArr s) := by
  cases tgt <;> simp [tgtA, KeyTarget.eval]

/-- `Challenge.IndCpaDProfile.gadgetGen` on arrays; `T` is `tgtA N s tgt`, computed once. -/
def gadgetGenA (P : FullParams) (lay : KSLayout) (T s : Array ℤ) (as es : List (Array ℤ)) :
    List (Array ℤ × Array ℤ) :=
  (List.range (lay.sizes P.src.qs.length).length).map fun j =>
    (addA P.src.N (subA P.src.N (smulA P.src.N (P.src.t : ℤ) (es.getD j (zeroA P.src.N)))
        (mulA P.src.N (as.getD j (zeroA P.src.N)) s))
      (smulA P.src.N ((gadgetFactor (specialProd P) (digitModuli P lay P.src.qs.length) j : ℕ) : ℤ) T),
     as.getD j (zeroA P.src.N))

theorem gadgetGen_def (P : FullParams) (lay : KSLayout) (tgt : KeyTarget) (s : IntPoly P.src.N)
    (as es : List (IntPoly P.src.N)) :
    gadgetGen P lay tgt s as es = (List.range (lay.sizes P.src.qs.length).length).map fun j =>
      ((P.src.t : ℤ) • es.getD j 0 - as.getD j 0 * s +
          ((gadgetFactor (specialProd P) (digitModuli P lay P.src.qs.length) j : ℕ) : ℤ) •
            tgt.eval s,
        as.getD j 0) := rfl

theorem gadgetGenA_eq (P : FullParams) (lay : KSLayout) (tgt : KeyTarget) (s : Array ℤ)
    (as es : List (Array ℤ)) :
    wK P.src.N (gadgetGenA P lay (tgtA P.src.N s tgt) s as es) =
      gadgetGen P lay tgt (ofArr s) (as.map ofArr) (es.map ofArr) := by
  rw [gadgetGen_def, gadgetGenA, wK, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, map_getD, ofArr_addA, ofArr_subA, ofArr_smulA, ofArr_mulA, ofArr_tgtA]

/-- The public key on arrays. -/
abbrev KSPKA : Type :=
  Array ℤ × Array ℤ × List (Array ℤ × Array ℤ) × (ℕ → List (Array ℤ × Array ℤ))

/-- The public key it stands for. -/
def wPK (N : ℕ) (pk : KSPKA) : KSPK N :=
  (ofArr pk.1, ofArr pk.2.1, wK N pk.2.2.1, fun g => wK N (pk.2.2.2 g))

/-- **`Challenge.IndCpaDProfile.keyGen` on arrays.** -/
def keyGenA (P : FullParams) (lay : KSLayout) (s e a : Array ℤ) (ra re : List (Array ℤ))
    (ga ge : ℕ → List (Array ℤ)) : KSPKA :=
  (subA P.src.N (smulA P.src.N (P.src.t : ℤ) e) (mulA P.src.N a s), a,
    gadgetGenA P lay (tgtA P.src.N s .square) s ra re,
    fun g => gadgetGenA P lay (tgtA P.src.N s (.galois g)) s (ga g) (ge g))

/-- **The executable key generation is `keyGen`**, for all secrets, errors and uniform parts. -/
theorem keyGenA_eq (P : FullParams) (lay : KSLayout) (s e a : Array ℤ) (ra re : List (Array ℤ))
    (ga ge : ℕ → List (Array ℤ)) :
    wPK P.src.N (keyGenA P lay s e a ra re ga ge) =
      keyGen P lay (ofArr s) (ofArr e) (ofArr a) (ra.map ofArr) (re.map ofArr)
        (fun g => (ga g).map ofArr) (fun g => (ge g).map ofArr) := by
  show (_, _, _, _) = ((P.src.t : ℤ) • ofArr e - ofArr a * ofArr s, ofArr a,
    gadgetGen P lay .square (ofArr s) (ra.map ofArr) (re.map ofArr),
    fun g => gadgetGen P lay (.galois g) (ofArr s) ((ga g).map ofArr) ((ge g).map ofArr))
  simp only [keyGenA, ofArr_subA, ofArr_smulA, ofArr_mulA, gadgetGenA_eq]

/-- `Spec.Encrypt.encrypt` on arrays: `(b·u + t·e₁ + p, a·u + t·e₂)`. -/
def encA (N t : ℕ) (b a p u e₁ e₂ : Array ℤ) : List (Array ℤ) :=
  [addA N (addA N (mulA N b u) (smulA N (t : ℤ) e₁)) p, addA N (mulA N a u) (smulA N (t : ℤ) e₂)]

theorem encA_eq (N t : ℕ) (b a p u e₁ e₂ : Array ℤ) :
    wC N (encA N t b a p u e₁ e₂) =
      Encrypt.encrypt t (ofArr b) (ofArr a) (ofArr p) (ofArr u) (ofArr e₁) (ofArr e₂) := by
  simp [encA, wC, Encrypt.encrypt]

/-- **The executable encryption is the encryption of `bgvKSData`** (`liftMsg m` at the top level). -/
theorem encBGVA_eq (P : FullParams) (lay : KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ)
    (pk : KSPKA) (m : Poly P.src.t P.src.N) (u e₁ e₂ : Array ℤ) :
    (bgvKSData P lay rots Bk Bu B1 B2).enc (wPK P.src.N pk) m (ofArr u, ofArr e₁, ofArr e₂) =
      (P.src.qs.length, wC P.src.N
        (encA P.src.N P.src.t pk.1 pk.2.1 (force P.src.N (Encrypt.liftMsg m)) u e₁ e₂)) := by
  rw [encA_eq, ofArr_force]
  rfl

end FHE.Ref
