import Challenge.IndCpaD.LM
import Challenge.IndCpaD.ProfileInstances
import Challenge.BFV.Domain
import Challenge.Realize.OpenFHEBFV

/-!
# Challenge.IndCpaD.LMBFV — a BFV evaluator for the game with evaluation on earlier results   (LOCKED statements; proofs in `Validation/IndCpaD/LMBFV.lean`)

`Challenge.IndCpaD.LM` proves the Li–Micciancio-style reduction for every local interpreter that
is perfectly correct in the fresh-only game. This file gives a BFV one.

* **The step function** `bfvStep P lay rk gk`: the textbook BFV operations of `Challenge.BFV`
  (componentwise addition and subtraction with zero padding, the textbook Fan–Vercauteren product
  `bfvMul` for `mul` and `square`, `⌊Q/t⌋·p` added or subtracted for plaintext addition, the
  plaintext product, integer and automorphism maps, the rounding modulus switch
  `bfvModSwitchComp`), and hybrid relinearization and key switching `relinBFV`, `keySwitchBFV`
  (`Challenge.Realize.OpenFHEBFV`, the transcription of OpenFHE's BFV key switch, proved to meet
  the contract in `Challenge.RealizeBFV`) at the operand's level with the keys `rk ℓ`, `gk g ℓ`
  the public key carries for that level. Levels, Galois elements and numbers of components come
  from the zero-message replay (public); the step fails when an operand is missing. It is a
  local interpreter (`bfvStep_interpOK`), so `interpEval` of it is an evaluator.
* **The class** `bfvClass D lay rots E`: the BFV profile class at the constant profile `E`, the
  side conditions of the key-switching pins (`bfvSide`), and at every replayed instruction
  (`bfvNeed`): two-component operands and the textbook multiplication budget for `mul`/`square`,
  `ksBoundAt` at the operand's level for `relin`/`keySwitch` (and the Galois element in `rots`),
  a two-component operand and `msBudget` for `modSwitch`.
* `bfvEval_meets`, `correct_bfvEval`: for every abstract BFV data whose good keys give a secret
  within the bound and, at every level, gadget keys for `s²` and for `σ_g(s)`, `g ∈ rots`, the
  evaluator meets hypothesis (ii) of `Challenge.IndCpaD.Profile` and the scheme is perfectly
  correct in the fresh-only game.
* **Keys and encryption** (`bfvKSData`, `bfvKeyGen`, `bfvKeyGen_keysOK`): BFV public-key
  encryption `Spec.EncryptBFV.encryptBFV` of `liftMsg m` at the top level, public key
  `(b, a, rk, gk)` with `b = e − a·s` and, per level, gadget keys `(eⱼ − aⱼ·s + gⱼ·T(s), aⱼ)`
  (BFV key errors are not multiples of `t`): good for every secret within the bound and every key
  error with `‖eⱼ‖∞ ≤ keyNoise` and `2‖eⱼ‖∞ < Q_ℓ·P`.
* **The instance at `sealBFV`** (`N = 2¹³`, four 43–44-bit primes, one special prime,
  `t = 65537`, key noise 21): `correct_lm_bfvSeal`, `probLM_eq_bfvSeal`, `advLM_le_bfvSeal`
  (the game of `Spec.IndCpaDLM` with this evaluator and the class applied to the inlined
  programs), `bfvKeyGen_noisy_bfvSeal` (noisy keys), and `lm_two_stage_bfv_kernel`: stage 1
  multiplies two fresh entries and relinearizes; stage 2, on its output, rotates by 5 and
  switches the modulus; both accepted, kernel-checked.

**The library transcription `runLibrary`** (and `textEval`, built on it) is not covered: its step
`libStep` reads the circuit's own input record (the declared drops `x.drops` at the instruction's
position `n`, for the leveled technique), which a step function of `interpEval` cannot see and
which changes under inlining; it reads operands with `getD []` and never fails, which breaks the
locality clause of `InterpOK`; and `runLibraryAux` continues past a step `Source.step` rejects.
The evaluator here uses the same textbook product and the same transcribed key switch as
`textEval`, as a guarded local step function.
-/

namespace Challenge.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM Spec.Encrypt
  Spec.EncryptBFV Challenge.IndCpaDProfile Challenge.Source Challenge.BFV Challenge.RealizeBFV
  MeasureTheory

/-! ## The evaluator -/

/-- **The BFV step function** (module docstring). -/
def bfvStep (P : FullParams) (lay : Budget.KSLayout)
    (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N)) (ρ : Env P.src)
    (σ : Trace.CtEnv P) : Instr → Option (Trace.CtEnv P)
  | .add d a b => (σ a).bind fun ca => (σ b).map fun cb => σ.set d (padZip (· + ·) ca cb)
  | .sub d a b => (σ a).bind fun ca => (σ b).map fun cb => σ.set d (padZip (· - ·) ca cb)
  | .mul d a b => (ρ a).bind fun x => (σ a).bind fun ca => (σ b).map fun cb =>
      σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca cb)
  | .square d a => (ρ a).bind fun x => (σ a).map fun ca =>
      σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)
  | .mulConst d a c => (σ a).map fun ca => σ.set d (ca.map (bfvMulConst c))
  | .copy d a => (σ a).map fun ca => σ.set d ca
  | .toEval d a => (σ a).map fun ca => σ.set d ca
  | .toCoeff d a => (σ a).map fun ca => σ.set d ca
  | .dropLimbs d a _ => (σ a).map fun ca => σ.set d ca
  | .automorph d a g => (σ a).map fun ca => σ.set d (ca.map (automorph g))
  | .addPlain d a p => (ρ a).bind fun x => (σ a).bind fun ca => (σ p).map fun cp =>
      σ.set d (bfvAddPlain P.src.t (P.src.modulus x.level) ca (cp.headD 0))
  | .subPlain d a p => (ρ a).bind fun x => (σ a).bind fun ca => (σ p).map fun cp =>
      σ.set d (bfvSubPlain P.src.t (P.src.modulus x.level) ca (cp.headD 0))
  | .mulPlain d a p => (σ a).bind fun ca => (σ p).map fun cp => σ.set d (ca.map (cp.headD 0 * ·))
  | .relin d a => (ρ a).bind fun x => (σ a).map fun ca =>
      σ.set d (relinBFV P lay x.level ca (rk x.level))
  | .keySwitch d a => (ρ a).bind fun x => (σ a).map fun ca =>
      σ.set d (keySwitchBFV P lay x.level ca (gk x.key x.level))
  | .modSwitch d a => (ρ a).bind fun x => (σ a).map fun ca =>
      σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))

variable (D : AbsScheme) in
/-- The step function with the evaluation keys of the public key. -/
def bfvStepFn (lay : Budget.KSLayout) (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) : StepFn D :=
  fun pk ρ σ i => bfvStep D.Pe lay (rk pk) (gk pk) ρ σ i

/-- What instruction `i` asks of the budget `E` in front of the replay environment `ρ`. -/
def bfvNeedAt (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)
    (ρ : Env P.src) : Instr → Bool
  | .mul _ a b => (ρ a).elim true fun x => (ρ b).elim true fun y =>
      decide (BudgetBFV.mulLift P ≤ E.mulLift) && decide (BudgetBFV.mulRound P ≤ E.mulRound) &&
        decide (x.parts = 2) && decide (y.parts = 2)
  | .square _ a => (ρ a).elim true fun x =>
      decide (BudgetBFV.mulLift P ≤ E.mulLift) && decide (BudgetBFV.mulRound P ≤ E.mulRound) &&
        decide (x.parts = 2)
  | .relin _ a => (ρ a).elim true fun x => decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch)
  | .keySwitch _ a => (ρ a).elim true fun x =>
      decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)
  | .modSwitch _ a => (ρ a).elim true fun x =>
      decide (BudgetBFV.msBudget P ≤ E.modSwitch) && decide (x.parts = 2)
  | _ => true

/-- `bfvNeedAt` along the zero-message replay. -/
def bfvNeed (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget) :
    List Instr → Env P.src → Bool
  | [], _ => true
  | i :: is, ρ => bfvNeedAt P lay rots E ρ i && (step P.src ρ i).elim true (bfvNeed P lay rots E is)

/-- The parameter-level side conditions of the BFV key-switching pins. -/
def bfvSide (P : FullParams) (lay : Budget.KSLayout) : Bool :=
  Budget.specialOK? P && ksDeclOK? P lay &&
    (List.range P.src.qs.length).all fun j => lay.okAt (j + 1)

/-- **The class of the BFV evaluator** at the constant profile `E` (module docstring). -/
def bfvClass (D : AbsScheme) (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)
    (C : D.Circ) : Bool :=
  admBFV D (fun _ _ => E) C && bfvSide D.Pe lay &&
    bfvNeed D.Pe lay rots E (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)

/-- **The BFV step function is a local interpreter.** -/
theorem bfvStep_interpOK (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    InterpOK D (bfvStepFn D lay rk gk) := sorry

/-- **The BFV evaluator meets the contracts on its class**, for every abstract BFV data whose good
keys give a secret within the bound and gadget keys at every level. -/
theorem bfvEval_meets (D : AbsScheme) (henc : D.EncOKBFV) (lay : Budget.KSLayout)
    (rots : List ℕ) (E : TraceBFV.Budget)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ D.P.src.qs.length →
        Budget.GadgetKeysOK D.P lay ℓ .square (D.sec sk) (rk pk ℓ) ∧
        ∀ g ∈ rots, Budget.GadgetKeysOK D.P lay ℓ (.galois g) (D.sec sk) (gk pk g ℓ)) :
    EvalMeetsBFV D (fun _ _ => E) (bfvClass D lay rots E)
      (interpEval D (bfvStepFn D lay rk gk)) := sorry

/-- **Perfect correctness of the BFV evaluator in the fresh-only game.** -/
theorem correct_bfvEval (D : AbsScheme) (henc : D.EncOKBFV) (lay : Budget.KSLayout)
    (rots : List ℕ) (E : TraceBFV.Budget)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hkeys : ∀ pk sk, D.KeysOK pk sk → SecretOK D.P.secretBound (D.sec sk) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ D.P.src.qs.length →
        Budget.GadgetKeysOK D.P lay ℓ .square (D.sec sk) (rk pk ℓ) ∧
        ∀ g ∈ rots, Budget.GadgetKeysOK D.P lay ℓ (.galois g) (D.sec sk) (gk pk g ℓ)) :
    Correct (freshScheme D (bfvClass D lay rots E) (interpEval D (bfvStepFn D lay rk gk))
      D.decBFV) := sorry

/-! ## Keys, key generation, encryption -/

/-- The BFV public key: `(b, a)`, relinearization keys per level, rotation keys per Galois
element and level. -/
abbrev BFVPK (N : ℕ) : Type :=
  IntPoly N × IntPoly N × (ℕ → List (IntPoly N × IntPoly N)) ×
    (ℕ → ℕ → List (IntPoly N × IntPoly N))

/-- **BFV public-key encryption with evaluation keys, as abstract data** (module docstring). -/
def bfvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ) (Bk Bu B1 B2 : ℕ) :
    AbsScheme where
  P := P
  eps := freshNoiseBFV P.src.t (P.src.modulus P.src.qs.length)
    (worstError P.src.N P.secretBound Bk Bu B1 B2)
  lvl := P.src.qs.length
  PK := BFVPK P.src.N
  SK := IntPoly P.src.N × IntPoly P.src.N
  ER := IntPoly P.src.N × IntPoly P.src.N × IntPoly P.src.N
  Circ := Program × List Var × (Var → Poly P.src.t P.src.N)
  sec := Prod.fst
  enc := fun pk m r => (P.src.qs.length,
    encryptBFV P.src.t (P.src.modulus P.src.qs.length) pk.1 pk.2.1 (liftMsg m) r.1 r.2.1 r.2.2)
  KeysOK := fun pk sk => SecretOK P.secretBound sk.1 ∧ normInf sk.2 ≤ Bk ∧
    PublicKeyOK 1 (P.src.modulus P.src.qs.length) sk.1 sk.2 pk.1 pk.2.1 ∧
    ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
      Budget.GadgetKeysOK P lay ℓ .square sk.1 (pk.2.2.1 ℓ) ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay ℓ (.galois g) sk.1 (pk.2.2.2 g ℓ)
  GoodE := fun _ _ r => normInf r.1 ≤ Bu ∧ normInf r.2.1 ≤ B1 ∧ normInf r.2.2 ≤ B2
  prog := fun C => C.1
  fresh := fun C => C.2.1
  pt := fun C => C.2.2

/-- Gadget keys at level `ℓ` for the target `tgt`: key `j` is `(eⱼ − aⱼ·s + gⱼ·T(s), aⱼ)`. -/
def bfvGadgetGen (P : FullParams) (lay : Budget.KSLayout) (ℓ : ℕ) (tgt : KeyTarget)
    (s : IntPoly P.src.N) (as es : List (IntPoly P.src.N)) :
    List (IntPoly P.src.N × IntPoly P.src.N) :=
  (List.range (lay.sizes ℓ).length).map fun j =>
    (es.getD j 0 - as.getD j 0 * s +
        ((Budget.gadgetFactor (Budget.specialProd P) (Budget.digitModuli P lay ℓ) j : ℕ) : ℤ) •
          tgt.eval s,
      as.getD j 0)

/-- **BFV key generation** from the secret, the public-key error, the uniform parts and the key
errors (per level, and per Galois element and level). -/
def bfvKeyGen (P : FullParams) (lay : Budget.KSLayout) (s e a : IntPoly P.src.N)
    (ra re : ℕ → List (IntPoly P.src.N)) (ga ge : ℕ → ℕ → List (IntPoly P.src.N)) :
    BFVPK P.src.N :=
  (e - a * s, a, fun ℓ => bfvGadgetGen P lay ℓ .square s (ra ℓ) (re ℓ),
    fun g ℓ => bfvGadgetGen P lay ℓ (.galois g) s (ga g ℓ) (ge g ℓ))

/-- **BFV key generation with noisy keys meets `KeysOK`.** -/
theorem bfvKeyGen_keysOK (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (hk : P.src.kind = .bfv) (s e a : IntPoly P.src.N)
    (hs : SecretOK P.secretBound s) (he : normInf e ≤ Bk) (ra re : ℕ → List (IntPoly P.src.N))
    (ga ge : ℕ → ℕ → List (IntPoly P.src.N))
    (hre : ∀ ℓ j, normInf ((re ℓ).getD j 0) ≤ P.keyNoise ∧
      2 * normInf ((re ℓ).getD j 0) < P.src.modulus ℓ * Budget.specialProd P)
    (hge : ∀ g ∈ rots, ∀ ℓ j, normInf ((ge g ℓ).getD j 0) ≤ P.keyNoise ∧
      2 * normInf ((ge g ℓ).getD j 0) < P.src.modulus ℓ * Budget.specialProd P) :
    (bfvKSData P lay rots Bk Bu B1 B2).KeysOK (bfvKeyGen P lay s e a ra re ga ge) (s, e) := sorry

/-- **The BFV encryption meets the encryption hypothesis** when a fresh encryption decrypts at the
top level (a closed check). -/
theorem encOK_bfvKSData (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ)
    (Bk Bu B1 B2 : ℕ) (ht : 2 ≤ P.src.t)
    (hdec : decOK P.src.t (P.src.modulus P.src.qs.length) (bfvKSData P lay rots Bk Bu B1 B2).eps
      = true) :
    (bfvKSData P lay rots Bk Bu B1 B2).EncOKBFV := sorry

/-! ## The instance at `sealBFV` -/

/-- One limb per digit, canonical representatives (what `ksDeclOK?` asks with a special prime). -/
def bfvSealLayout : Budget.KSLayout := Budget.uniformLayout 1 true

/-- The data at `sealBFV`: error bounds 21, ternary `u`, rotation keys for `g = 5`. -/
def bfvSealData : AbsScheme := bfvKSData sealBFV bfvSealLayout [5] 21 1 21 21

/-- The constant profile `Spec.BudgetBFV.certified` at `sealBFV`. -/
def bfvSealBudget : TraceBFV.Budget := BudgetBFV.certified sealBFV bfvSealLayout

/-- The circuit builder, class and evaluator at `sealBFV`. -/
def mkBFVSeal (p : Program) (f : List Var) (c : Var → M bfvSealData) : bfvSealData.Circ :=
  (p, f, c)
def admBFVSeal : bfvSealData.Circ → Bool := bfvClass bfvSealData bfvSealLayout [5] bfvSealBudget
def evBFVSeal : bfvSealData.PK → bfvSealData.Circ → List (CT bfvSealData) →
    List (CT bfvSealData) :=
  interpEval bfvSealData (bfvStepFn bfvSealData bfvSealLayout (fun pk => pk.2.2.1)
    (fun pk => pk.2.2.2))

/-- **Fresh-only correctness at `sealBFV`**, every hypothesis discharged. -/
theorem correct_lm_bfvSeal :
    Correct (freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV) := sorry

/-- **The reduction at `sealBFV` with evaluation on earlier results.** -/
theorem probLM_eq_bfvSeal [DecidableEq (M bfvSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → bfvSealData.PK) (sk : Ω → bfvSealData.SK) (tape : Ω → ℕ → bfvSealData.ER)
    (coins : Ω → Coins) (A : Coins → bfvSealData.PK → LAdv bfvSealData Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, bfvSealData.KeysOK (pk ω) (sk ω) ∧
      ∀ i, bfvSealData.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty bfvSealData) = true} =
      μ {ω | gameCPA (S := freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV) b
        (pk ω) (tape ω) (reductionLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV A
          (coins ω) (pk ω)) 0 = true} := sorry

/-- **The advantage bound at `sealBFV`, evaluation on earlier results.** -/
theorem advLM_le_bfvSeal [DecidableEq (M bfvSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → bfvSealData.PK) (sk : Ω → bfvSealData.SK) (tape : Ω → ℕ → bfvSealData.ER)
    (coins : Ω → Coins) (A : Coins → bfvSealData.PK → LAdv bfvSealData Bool) (q : ℕ)
    (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV true (pk ω) (sk ω)
          (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty bfvSealData) = true}).toReal -
        (μ {ω | gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV false (pk ω) (sk ω)
          (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty bfvSealData) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV)
          true (pk ω) (tape ω) (reductionLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV A
            (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV)
          false (pk ω) (tape ω) (reductionLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV A
            (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (bfvSealData.KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, bfvSealData.GoodE (pk ω) (sk ω) (tape ω i))}).toReal := sorry

/-- The all-ones key error at every level. -/
def onesErr (N : ℕ) : ℕ → List (IntPoly N) := fun _ => List.replicate 4 ⟨fun _ => 1⟩

/-- **Noisy keys exist at `sealBFV`**: key generation with every key error the all-ones
polynomial (non-zero) gives good keys, for every secret, public-key error and uniform part. -/
theorem bfvKeyGen_noisy_bfvSeal (s e a : IntPoly sealBFV.src.N)
    (hs : SecretOK sealBFV.secretBound s) (he : normInf e ≤ 21)
    (ra : ℕ → List (IntPoly sealBFV.src.N)) (ga : ℕ → ℕ → List (IntPoly sealBFV.src.N)) :
    bfvSealData.KeysOK (bfvKeyGen sealBFV bfvSealLayout s e a ra (onesErr _) ga
      (fun _ => onesErr _)) (s, e) := sorry

/-- A fresh-entry declaration at `sealBFV` (level 4). -/
def bfvSealDecl (x : Var) : Decl := { name := x, parts := 2, level := 4, scale := 0, key := 1 }

/-- Stage 1: the product of the fresh entries `a`, `b`, relinearized, as `c`. -/
def bfvStage1 : QCirc bfvSealData :=
  ({ inputs := [bfvSealDecl "a", bfvSealDecl "b"], body := [.mul "c" "a" "b", .relin "c" "c"],
     outputs := ["c"] }, ["a", "b"], fun _ => 0)

/-- Stage 2, on the output `c` of stage 1: a rotation by 5 and a modulus switch. -/
def bfvStage2 : QCirc bfvSealData :=
  ({ inputs := [bfvSealDecl "c"], body := [.automorph "r" "c" 5, .keySwitch "k" "r",
       .modSwitch "m" "k"], outputs := ["m"] }, ["c"], fun _ => 0)

/-- The global program after the encryptions named `a` and `b`. -/
def bfvG0 : Global bfvSealData := ((Global.empty bfvSealData).link "a").link "b"

/-- **The two BFV stages are accepted by the oracle, kernel-checked**, and a fresh encryption
decrypts at the top level. -/
theorem lm_two_stage_bfv_kernel :
    decOK sealBFV.src.t (sealBFV.src.modulus sealBFV.src.qs.length) bfvSealData.eps = true ∧
    admLM mkBFVSeal admBFVSeal bfvG0 bfvStage1 [("a", true), ("b", true)] = true ∧
      admLM mkBFVSeal admBFVSeal (bfvG0.extend bfvStage1) bfvStage2 [("c", true)] = true := sorry

end Challenge.IndCpaDLM
