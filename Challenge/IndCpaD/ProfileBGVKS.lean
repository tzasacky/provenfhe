import Challenge.IndCpaD.ProfileBGVInstances
import Challenge.Realize.OpenFHE
import Spec.Certify

/-!
# Challenge.IndCpaD.ProfileBGVKS — a BGV evaluator WITH key switching and modulus switching for the library-free reduction   (LOCKED statements; proofs in `Validation/IndCpaD/ProfileBGVKS.lean`)

`Challenge.IndCpaD.ProfileBGV` states the reduction for an abstract BGV scheme and an abstract
evaluator; `Challenge.IndCpaD.ProfileBGVInstances` discharges the evaluator hypothesis only for
circuits without key or modulus switching. This file gives an evaluator that performs all three
and a public key that carries the evaluation keys.

* **The evaluator** `ksEval D lay rk gk`: the program's body executed instruction by
  instruction. The exact operations are those of `exactStep`; a `relin` is hybrid
  relinearization on the digits of `lay` with the relinearization keys `rk`
  (`Challenge.Realize.OpenFHE.relinOpenFHE`), a `keySwitch` is hybrid key switching with the
  keys `gk g` for the operand's Galois element `g` (`keySwitchOpenFHE`), both at the level of the
  operand and with ONE key set generated at the top level (the algorithm reads its first
  digits); a `modSwitch` is the centred t-corrected switch of every component by the last prime
  of the operand's level (`Challenge.Source.bgvModSwitchComp`). Levels and Galois elements are
  read from the replay of `Source.step` on zero messages (public). The key-switching algorithm is
  the transcription of OpenFHE's (canonical digit representatives); it is a textbook hybrid key
  switch and nothing in the statements depends on that library.
* **The class** `ksClass D lay rots prof`: the profile class `admBGV D prof`, plus the side
  conditions of the key-switching realizability pins (`ksSide`: usable special primes, a layout
  that restricts from the top level to every level, keys small enough to restrict, canonical
  digits) and, at every instruction of the zero-message replay (`ksNeed`), that the profile
  covers the step: `ksBoundAt` at the operand's level for `relin`/`keySwitch`, the operand's
  Galois element in `rots` for `keySwitch`, `msBudgetAt` for the operand's number of components
  for `modSwitch`.
* `ksEval_meets`: **for every abstract BGV data whose keys provide, for good keys, a secret
  within `secretBound` and top-level gadget keys for `s²` and for `σ_g(s)`, `g ∈ rots`, the
  evaluator meets hypothesis (ii) of `Challenge.IndCpaD.ProfileBGV` on `ksClass`**;
  `correct_ksEval`: hence perfect correctness, and `bgv_prob_eq`, `bgv_prob_le` apply. The
  reduction is then to IND-CPA of the scheme with the relinearization and rotation keys in the
  public key (a circular-security assumption included), which is not proved.
* **Keys and key generation** (`bgvKSData`, `keyGen`): public key `(b, a, rk, gk)` with
  `b = t·e − a·s`, and gadget key `j` for the target `T(s)` equal to
  `(t·eⱼ − aⱼ·s + gⱼ·T(s), aⱼ)`, `gⱼ` the gadget factor of `Spec.Budget.gadgetReq` at the top
  level. `keyGen_keysOK`: for EVERY secret within the bound, every public-key error within `Bk`,
  every `a`, `aⱼ`, and every key error `eⱼ` with `t·‖eⱼ‖∞ ≤ keyNoise` and
  `2·t·‖eⱼ‖∞ < Q_L·P`, the generated keys are good (rotation keys follow the convention of
  `Challenge.Budget`: gadget keys under `s` for the target `σ_g(s)`; not the stored-key convention
  of `rotateOpenFHE161`, keys under `s'` with `σ_g(s') = s`, so this is not OpenFHE's rotation).
  Key generation, with noisy keys, meets
  `KeysOK`. `keyGen_noisy_bgvKSSeal`: at `bgvKSSeal` with every key error the all-ones polynomial
  (non-zero), for every secret, public-key error and uniform part.
* **The instance** `bgvKSSeal`: `bgvSeal` (`N = 2¹³`, four 43–44-bit primes, one special prime,
  `t = 65537`) with key noise `21·t` (key errors in `[−21, 21]`, multiplied by `t`), encryption
  error bounds 21 and a ternary `u`, rotation keys for `g = 5`, one limb per digit with canonical
  representatives, profile `Spec.Budget.certified`. `correct_ksEval_bgvKSSeal`: perfect
  correctness, every hypothesis discharged. `ksClass_bgvKSSeal`: a circuit with a product, a
  relinearization, a rotation by 5 (automorphism and key switch), a modulus switch and a
  plaintext addition is in the class, **kernel-checked**.
-/

namespace Challenge.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.Encrypt Spec.Budget
  Challenge.Source Challenge.Realize

/-! ## The evaluator -/

/-- What instruction `i` asks of the profile `E`, in front of the zero-message environment `ρ`
(module docstring). -/
def ksNeedAt (P : FullParams) (lay : KSLayout) (rots : List ℕ) (E : Trace.Budget)
    (ρ : Env P.src) : Instr → Bool
  | .relin _ a => (ρ a).elim true fun x => decide (ksBoundAt P lay x.level ≤ E.keySwitch)
  | .keySwitch _ a => (ρ a).elim true fun x =>
      decide (ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)
  | .modSwitch _ a => (ρ a).elim true fun x =>
      decide (msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
  | _ => true

/-- `ksNeedAt` along the zero-message replay of a body. -/
def ksNeed (P : FullParams) (lay : KSLayout) (rots : List ℕ) (E : Trace.Budget) :
    List Instr → Env P.src → Bool
  | [], _ => true
  | i :: is, ρ => ksNeedAt P lay rots E ρ i && (step P.src ρ i).elim true (ksNeed P lay rots E is)

/-- The parameter-level side conditions of the key-switching realizability pins. -/
def ksSide (P : FullParams) (lay : KSLayout) : Bool :=
  specialOK? P && Spec.Certify.layoutOK? P lay && Spec.Certify.keysRestrict? P && lay.canonical

/-- One step of the evaluator: the exact steps, hybrid relinearization and key switching at the
operand's level with the top-level keys, and the centred t-corrected modulus switch. -/
def ksStep (P : FullParams) (lay : KSLayout) (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N)) (ρ : Env P.src) (σ : Trace.CtEnv P) :
    Instr → Option (Trace.CtEnv P)
  | .relin d a => (ρ a).bind fun x => (σ a).map fun ca => σ.set d (relinOpenFHE P lay x.level ca rk)
  | .keySwitch d a => (ρ a).bind fun x => (σ a).map fun ca =>
      σ.set d (keySwitchOpenFHE P lay x.level ca (gk x.key))
  | .modSwitch d a => (ρ a).bind fun x => (σ a).map fun ca =>
      σ.set d (ca.map (bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!))
  | i => exactStep P σ i

/-- The evaluator's run over a body, alongside the zero-message replay. -/
def ksRun (P : FullParams) (lay : KSLayout) (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N)) :
    List Instr → Env P.src → Trace.CtEnv P → Option (Trace.CtEnv P)
  | [], _, σ => some σ
  | i :: is, ρ, σ => (step P.src ρ i).bind fun ρ' =>
      (ksStep P lay rk gk ρ σ i).bind fun σ' => ksRun P lay rk gk is ρ' σ'

/-- **The evaluator with key switching** (module docstring): a function of the evaluation keys,
the circuit and the input ciphertexts. -/
def ksEval (D : AbsScheme) (lay : KSLayout) (rk : List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) (C : D.Circ)
    (cs : List (ℕ × List (IntPoly D.P.src.N))) : List (ℕ × List (IntPoly D.P.src.N)) :=
  ((ksRun D.Pe lay rk gk (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD []

/-- **The class of the evaluator** (module docstring). -/
def ksClass (D : AbsScheme) (lay : KSLayout) (rots : List ℕ) (prof : D.Circ → Trace.Budget)
    (C : D.Circ) : Bool :=
  admBGV D prof C && ksSide D.Pe lay &&
    ksNeed D.Pe lay rots (prof C) (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)

/-- **The evaluator with key switching meets the BGV contracts on its class**, for every
abstract BGV data whose good keys give a secret within the bound and top-level gadget keys. -/
theorem ksEval_meets (D : AbsScheme) (henc : D.EncOKBGV) (lay : KSLayout) (rots : List ℕ)
    (prof : D.Circ → Trace.Budget)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      GadgetKeysOK D.P lay D.P.src.qs.length .square (D.sec sk) (rk pk) ∧
      ∀ g ∈ rots, GadgetKeysOK D.P lay D.P.src.qs.length (.galois g) (D.sec sk) (gk pk g)) :
    EvalMeetsBGV D prof (ksClass D lay rots prof)
      (fun pk C cs => ksEval D lay (rk pk) (gk pk) C cs) := sorry

/-- **Perfect correctness with the evaluator with key switching.** -/
theorem correct_ksEval (D : AbsScheme) (henc : D.EncOKBGV) (lay : KSLayout) (rots : List ℕ)
    (prof : D.Circ → Trace.Budget)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      GadgetKeysOK D.P lay D.P.src.qs.length .square (D.sec sk) (rk pk) ∧
      ∀ g ∈ rots, GadgetKeysOK D.P lay D.P.src.qs.length (.galois g) (D.sec sk) (gk pk g)) :
    Correct (schemeBGV D (fun pk C cs => ksEval D lay (rk pk) (gk pk) C cs)
      (ksClass D lay rots prof)) := sorry

/-! ## Keys, key generation, encryption -/

/-- The public key: `(b, a)`, the relinearization keys, the rotation keys per Galois element. -/
abbrev KSPK (N : ℕ) : Type :=
  IntPoly N × IntPoly N × List (IntPoly N × IntPoly N) × (ℕ → List (IntPoly N × IntPoly N))

/-- **BGV public-key encryption with evaluation keys in the public key, as abstract data.**
Encryption as `bgvData` (`Spec.Encrypt.encrypt` of `liftMsg m` at the top level); the secret
state is `(s, e)`; good keys: the secret within `secretBound`, the public-key error within `Bk`,
`(b, a)` a public key for them, and top-level gadget keys for `s²` and for every `σ_g(s)`,
`g ∈ rots`. -/
def bgvKSData (P : FullParams) (lay : KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ) : AbsScheme where
  P := P
  eps := freshNoise P.src.t (P.src.t - 1) (worstError P.src.N P.secretBound Bk Bu B1 B2)
  lvl := P.src.qs.length
  PK := KSPK P.src.N
  SK := IntPoly P.src.N × IntPoly P.src.N
  ER := IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N
  Circ := Program × List Var × (Var → Poly P.src.t P.src.N)
  sec := Prod.fst
  enc := fun pk m r =>
    (P.src.qs.length, encrypt P.src.t pk.1 pk.2.1 (liftMsg m) r.1 r.2.1 r.2.2)
  KeysOK := fun pk sk => SecretOK P.secretBound sk.1 ∧ normInf sk.2 ≤ Bk ∧
    PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) sk.1 sk.2 pk.1 pk.2.1 ∧
    GadgetKeysOK P lay P.src.qs.length .square sk.1 pk.2.2.1 ∧
    ∀ g ∈ rots, GadgetKeysOK P lay P.src.qs.length (.galois g) sk.1 (pk.2.2.2 g)
  GoodE := fun _ _ r => normInf r.1 ≤ Bu ∧ normInf r.2.1 ≤ B1 ∧ normInf r.2.2 ≤ B2
  prog := fun C => C.1
  fresh := fun C => C.2.1
  pt := fun C => C.2.2

/-- Top-level gadget keys for the target `tgt` generated from the uniform parts `as` and the
errors `es` (module docstring): key `j` is `(t·eⱼ − aⱼ·s + gⱼ·T(s), aⱼ)`. -/
def gadgetGen (P : FullParams) (lay : KSLayout) (tgt : KeyTarget) (s : IntPoly P.src.N)
    (as es : List (IntPoly P.src.N)) : List (IntPoly P.src.N × IntPoly P.src.N) :=
  (List.range (lay.sizes P.src.qs.length).length).map fun j =>
    ((P.src.t : ℤ) • es.getD j 0 - as.getD j 0 * s +
        ((gadgetFactor (specialProd P) (digitModuli P lay P.src.qs.length) j : ℕ) : ℤ) •
          tgt.eval s,
      as.getD j 0)

/-- **Key generation** (module docstring): the public key from the secret `s`, the public-key
error `e`, the uniform parts and the key errors. -/
def keyGen (P : FullParams) (lay : KSLayout) (s e a : IntPoly P.src.N)
    (ra re : List (IntPoly P.src.N)) (ga ge : ℕ → List (IntPoly P.src.N)) : KSPK P.src.N :=
  ((P.src.t : ℤ) • e - a * s, a, gadgetGen P lay .square s ra re,
    fun g => gadgetGen P lay (.galois g) s (ga g) (ge g))

/-- **Key generation with noisy keys meets `KeysOK`** (module docstring). -/
theorem keyGen_keysOK (P : FullParams) (lay : KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ)
    (s e a : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (he : normInf e ≤ Bk) (ra re : List (IntPoly P.src.N)) (ga ge : ℕ → List (IntPoly P.src.N))
    (hre : ∀ j, P.src.t * normInf (re.getD j 0) ≤ P.keyNoise ∧
      2 * (P.src.t * normInf (re.getD j 0)) < P.src.modulus P.src.qs.length * specialProd P)
    (hge : ∀ g ∈ rots, ∀ j, P.src.t * normInf ((ge g).getD j 0) ≤ P.keyNoise ∧
      2 * (P.src.t * normInf ((ge g).getD j 0)) < P.src.modulus P.src.qs.length * specialProd P) :
    (bgvKSData P lay rots Bk Bu B1 B2).KeysOK (keyGen P lay s e a ra re ga ge) (s, e) := sorry

/-- **The encryption meets the encryption hypothesis** when the fresh noise does not wrap at the
top level. -/
theorem encOK_bgvKSData (P : FullParams) (lay : KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ)
    (ht : 2 ≤ P.src.t)
    (hQ : 2 * (bgvKSData P lay rots Bk Bu B1 B2).eps < P.src.modulus P.src.qs.length) :
    (bgvKSData P lay rots Bk Bu B1 B2).EncOKBGV := sorry

/-! ## The instance at `N = 2¹³` -/

/-- `bgvSeal` with key noise `21·t` (key errors in `[−21, 21]`, multiplied by `t`). -/
def bgvKSSeal : FullParams := { bgvSeal with keyNoise := 21 * 65537 }

/-- One limb per digit, canonical representatives. -/
def bgvKSLayout : KSLayout := uniformLayout 1 true

/-- The data at `bgvKSSeal`: error bounds 21, ternary `u`, rotation keys for `g = 5`. -/
def bgvKSSealData : AbsScheme := bgvKSData bgvKSSeal bgvKSLayout [5] 21 1 21 21

/-- The constant profile `Spec.Budget.certified` at `bgvKSSeal`. -/
def bgvKSSealProfile (_ : bgvKSSealData.Circ) : Trace.Budget :=
  certified bgvKSSeal bgvKSLayout

/-- **The instance at `bgvKSSeal`**, every hypothesis discharged. -/
theorem correct_ksEval_bgvKSSeal :
    Correct (schemeBGV bgvKSSealData
      (fun pk C cs => ksEval bgvKSSealData bgvKSLayout pk.2.2.1 pk.2.2.2 C cs)
      (ksClass bgvKSSealData bgvKSLayout [5] bgvKSSealProfile)) := sorry

/-- The all-ones polynomial (a non-zero key error). -/
def onesPoly (N : ℕ) : IntPoly N := ⟨fun _ => 1⟩

/-- **Noisy keys exist at `bgvKSSeal`**: for every secret within the bound, every public-key
error within 21 and all uniform parts, key generation with every key error equal to the
all-ones polynomial (non-zero) gives good keys. -/
theorem keyGen_noisy_bgvKSSeal (s e a : IntPoly bgvKSSeal.src.N)
    (hs : SecretOK bgvKSSeal.secretBound s) (he : normInf e ≤ 21)
    (ra : List (IntPoly bgvKSSeal.src.N)) (ga : ℕ → List (IntPoly bgvKSSeal.src.N)) :
    bgvKSSealData.KeysOK
      (keyGen bgvKSSeal bgvKSLayout s e a ra (List.replicate 4 (onesPoly _))
        ga (fun _ => List.replicate 4 (onesPoly _))) (s, e) := sorry

/-- A product of two fresh encryptions, its relinearization, a rotation by 5 (automorphism and
key switch), a modulus switch and a plaintext addition at the level below. -/
def bgvKSSealCirc : bgvKSSealData.Circ :=
  ({ inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩, ⟨"p", 1, 3, 1, 1⟩],
     body := [.mul "c" "a" "b", .relin "c" "c", .automorph "r" "c" 5, .keySwitch "k" "r",
       .modSwitch "m" "k", .addPlain "o" "m" "p"],
     outputs := ["o"] }, ["a", "b"], fun _ => 0)

/-- **A circuit with relinearization, rotation and modulus switching is in the evaluator's class
at `N = 2¹³`**, kernel-checked; so is the circuit of `ProfileBGVInstances` in the exact class. -/
theorem ksClass_bgvKSSeal :
    ksClass bgvKSSealData bgvKSLayout [5] bgvKSSealProfile bgvKSSealCirc = true ∧
      exactClass bgvSealData bgvSealProfile bgvSealCirc = true := sorry

-- Outside the class: the same circuit with rotation keys for `g = 3` only.
#guard !ksClass bgvKSSealData bgvKSLayout [3] bgvKSSealProfile bgvKSSealCirc

end Challenge.IndCpaDProfile
