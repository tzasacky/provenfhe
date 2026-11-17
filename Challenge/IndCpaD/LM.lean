import Spec.IndCpaDLM
import Challenge.IndCpaD.ProfileBGVKS
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Challenge.IndCpaD.LM — IND-CPA-D with evaluation on earlier results reduces to IND-CPA   (LOCKED statements; proofs in `Validation/IndCpaD/LM.lean`)

The game is `Spec.IndCpaDLM.gameLM` (Li–Micciancio's evaluation oracle on any table entry; its
docstring compares it with their definition). The statements here hold for every abstract scheme
whose evaluator is a **local interpreter** of the program body and that is perfectly correct on
its class in the fresh-only sense:

* `irun`, `interpEval`: the interpreter given by a step function `stepF` (from the public key, the
  zero-message replay environment, the ciphertext environment and the instruction), run over the
  body alongside `Source.step` on zero messages; outputs as in `Challenge.IndCpaD.Profile`.
* `InterpOK stepF`: the step function writes only the destination, its result depends only on
  the variables the step reads (an extension of both environments gives the same written
  ciphertext), and it does not get stuck where the program is well formed (when the zero-message
  step succeeds and every variable of the replay has a ciphertext). These are what makes
  "evaluating a query on earlier outputs" the same as "running the inlined program on the fresh
  encryptions": an interpreter evaluating `C` on the outputs of `G` computes, on `C`'s variables,
  exactly what it computes on `G.body ++ C.body` from the fresh inputs.
* `gameLM_eq_gameCPA`, `probLM_eq`, `probLM_le`, `advLM_le`: under `InterpOK` and
  `Correct (freshScheme D adm (interpEval D stepF) dec)` (perfect correctness of the same scheme
  in the fresh-only game, which `Challenge.IndCpaD.ProfileBGV` and its instances provide), the
  game with evaluation on earlier results and the IND-CPA game played by the reduction return the
  same bit on every good tape, have equal winning probabilities, differ by at most the bad event,
  and the advantages differ by at most `2·Pr[bad]`. No compositionality is assumed of the
  evaluator beyond `InterpOK`; no per-level input bound is needed: admissibility is the class
  applied to the inlined program over the fresh entries.

**Instance with key switching** (`ksStepFn`, `ksStep_interpOK`, `interpEval_ks`,
`correct_lm_bgvKSSeal`, `probLM_eq_bgvKSSeal`, `advLM_le_bgvKSSeal`): the BGV evaluator of
`Challenge.IndCpaD.ProfileBGVKS` (exact operations, hybrid relinearization and key switching
with the evaluation keys of the public key, t-corrected modulus switching) is a local interpreter,
equal to `ksEval`; at `bgvKSSeal` (`N = 2¹³`) the reduction holds with the class `ksClass`
applied to the inlined programs. `lm_two_stage_kernel`: a two-stage example is accepted by the
oracle, kernel-checked: stage 1 multiplies two fresh entries and relinearizes; stage 2, on the
OUTPUT of stage 1, rotates it by 5 (automorphism and key switch) and switches the modulus.

**What is not here.** A BFV instance exists (`Challenge.IndCpaD.LMBFV`: textbook multiplication,
transcribed hybrid key switching, rounding modulus switch). On a query on fresh entries the oracle
accepts exactly what the fresh-only class accepts, for the certificate classes at a constant
budget (`Challenge.IndCpaD.LMAgree`); declared input bounds are kept on inlining
(`Challenge.IndCpaD.LMBounds`); the fresh-only game embeds in this one for regular adversaries
(`Challenge.IndCpaD.LMEmbed`). What is still not here is OpenFHE's full BFV library
transcription, the translation of irregular fresh-only adversaries, and the translation from
index-based adversaries with local names. The BFV library evaluators (`runLibrary`, and
the textbook evaluator built on it) are not of the form `interpEval`: `libStep` reads the
circuit's own input record (its declared drops `x.drops`, at the instruction's position `n`, for
the leveled technique), which a `StepFn` cannot see and which changes under inlining; it reads
operands with `getD []` and never fails, which breaks the locality clause of `InterpOK` when an
operand is missing; and `runLibraryAux` continues past a step `Source.step` rejects. With no
declared drops the position plays no role, so an instance through a guarded step function looks
plausible; it is not done. The reduction is to IND-CPA of
the scheme with the evaluation keys in the public key, which is not proved.
-/

namespace Challenge.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM MeasureTheory

variable (D : AbsScheme)

/-- A step function of an interpreter. -/
abbrev StepFn : Type :=
  D.PK → Env D.P.src → Trace.CtEnv D.Pe → Instr → Option (Trace.CtEnv D.Pe)

/-- The interpreter's run over a body, alongside the zero-message replay. -/
def irun (stepF : StepFn D) (pk : D.PK) :
    List Instr → Env D.P.src → Trace.CtEnv D.Pe → Option (Trace.CtEnv D.Pe)
  | [], _, σ => some σ
  | i :: is, ρ, σ => (step D.P.src ρ i).bind fun ρ' =>
      (stepF pk ρ σ i).bind fun σ' => irun stepF pk is ρ' σ'

/-- **The interpreter as an evaluator** (as `Challenge.IndCpaDProfile.ksEval`). -/
def interpEval (stepF : StepFn D) (pk : D.PK) (C : D.Circ) (cs : List (CT D)) : List (CT D) :=
  ((irun D stepF pk (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
    fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD []

/-- **A local interpreter** (module docstring). -/
def InterpOK (stepF : StepFn D) : Prop :=
  (∀ pk ρ ρ₂ σ σ₂ i σ', (∀ x v, ρ x = some v → ρ₂ x = some v) →
    (∀ x c, σ x = some c → σ₂ x = some c) → stepF pk ρ σ i = some σ' →
      ∃ ct, σ' = σ.set (Trace.dst i) ct ∧ stepF pk ρ₂ σ₂ i = some (σ₂.set (Trace.dst i) ct)) ∧
  (∀ pk ρ σ i ρ', step D.P.src ρ i = some ρ' → (∀ x, (ρ x).isSome → (σ x).isSome) →
    (stepF pk ρ σ i).isSome)

variable {D}

/-- **Perfect simulation, evaluation on earlier results.** -/
theorem gameLM_eq_gameCPA (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec)) (b : Bool)
    (pk : D.PK) (sk : D.SK) (tape : ℕ → D.ER) (hk : D.KeysOK pk sk) (A : LAdv D Bool)
    (ht : TapeOKLM pk sk tape A 0) :
    gameLM mk adm (interpEval D stepF) dec b pk sk tape A 0 [] (Global.empty D) =
      gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b pk tape
        (reduceLM mk adm (interpEval D stepF) dec pk A [] (Global.empty D)) 0 := sorry

/-- **Equal winning probabilities, evaluation on earlier results.** -/
theorem probLM_eq (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mk adm (interpEval D stepF) dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
        0 [] (Global.empty D) = true} =
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b (pk ω) (tape ω)
        (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true} := sorry

/-- **The bad-event version, evaluation on earlier results.** -/
theorem probLM_le (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    μ {ω | gameLM mk adm (interpEval D stepF) dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
        0 [] (Global.empty D) = true} ≤
        μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameLM mk adm (interpEval D stepF) dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
          0 [] (Global.empty D) = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} := sorry

/-- **The advantage bound, evaluation on earlier results**, under a finite measure. -/
theorem advLM_le (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mk adm (interpEval D stepF) dec true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal -
        (μ {ω | gameLM mk adm (interpEval D stepF) dec false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) true (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) false (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))}).toReal :=
  sorry

/-! ## The BGV evaluator with key switching -/

variable (D) in
/-- The step function of `Challenge.IndCpaDProfile.ksEval`, with the evaluation keys `rk pk`,
`gk pk` of the public key. -/
def ksStepFn (lay : Budget.KSLayout) (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) : StepFn D :=
  fun pk ρ σ i => Challenge.IndCpaDProfile.ksStep D.Pe lay (rk pk) (gk pk) ρ σ i

/-- **The evaluator with key switching is a local interpreter.** -/
theorem ksStep_interpOK (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    InterpOK D (ksStepFn D lay rk gk) := sorry

/-- **The interpreter is `ksEval`.** -/
theorem interpEval_ks (D : AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) :
    interpEval D (ksStepFn D lay rk gk) =
      fun pk C cs => Challenge.IndCpaDProfile.ksEval D lay (rk pk) (gk pk) C cs := sorry

open Challenge.IndCpaDProfile

/-- The circuit builder of `bgvKSSealData` (its circuits are triples). -/
def mkSeal (p : Program) (f : List Var) (c : Var → M bgvKSSealData) : bgvKSSealData.Circ :=
  (p, f, c)

/-- The class at `bgvKSSeal`, applied by the oracle to the inlined programs. -/
def admSeal : bgvKSSealData.Circ → Bool := ksClass bgvKSSealData bgvKSLayout [5] bgvKSSealProfile

/-- The evaluator at `bgvKSSeal`. -/
def evSeal : bgvKSSealData.PK → bgvKSSealData.Circ → List (CT bgvKSSealData) →
    List (CT bgvKSSealData) :=
  interpEval bgvKSSealData (ksStepFn bgvKSSealData bgvKSLayout (fun pk => pk.2.2.1)
    (fun pk => pk.2.2.2))

/-- **Fresh-only correctness at `bgvKSSeal`**, in the form the game needs. -/
theorem correct_lm_bgvKSSeal :
    Correct (freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) := sorry

/-- **The reduction at `bgvKSSeal` with evaluation on earlier results and key switching.** -/
theorem probLM_eq_bgvKSSeal [DecidableEq (M bgvKSSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → bgvKSSealData.PK) (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, bgvKSSealData.KeysOK (pk ω) (sk ω) ∧
      ∀ i, bgvKSSealData.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true} =
      μ {ω | gameCPA (S := freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) b
        (pk ω) (tape ω) (reductionLM mkSeal admSeal evSeal bgvKSSealData.decBGV A (coins ω) (pk ω))
          0 = true} := sorry

/-- **The advantage bound at `bgvKSSeal`, evaluation on earlier results.** -/
theorem advLM_le_bgvKSSeal [DecidableEq (M bgvKSSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → bgvKSSealData.PK) (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool) (q : ℕ)
    (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true}).toReal -
        (μ {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) true
          (pk ω) (tape ω) (reductionLM mkSeal admSeal evSeal bgvKSSealData.decBGV A (coins ω)
            (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) false
          (pk ω) (tape ω) (reductionLM mkSeal admSeal evSeal bgvKSSealData.decBGV A (coins ω)
            (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (bgvKSSealData.KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, bgvKSSealData.GoodE (pk ω) (sk ω) (tape ω i))}).toReal := sorry

/-! ## A two-stage example -/

/-- A fresh-entry declaration at `bgvKSSeal` (level 4). -/
def sealDecl (x : Var) : Decl := { name := x, parts := 2, level := 4, scale := 0, key := 1 }

/-- Stage 1: the product of the fresh entries `a`, `b`, relinearized, as `c`. -/
def lmStage1 : QCirc bgvKSSealData :=
  ({ inputs := [sealDecl "a", sealDecl "b"], body := [.mul "c" "a" "b", .relin "c" "c"],
     outputs := ["c"] }, ["a", "b"], fun _ => 0)

/-- Stage 2, on the OUTPUT `c` of stage 1: a rotation by 5 (automorphism and key switch) and a
modulus switch. -/
def lmStage2 : QCirc bgvKSSealData :=
  ({ inputs := [sealDecl "c"], body := [.automorph "r" "c" 5, .keySwitch "k" "r",
       .modSwitch "m" "k"], outputs := ["m"] }, ["c"], fun _ => 0)

/-- The global program after the encryptions named `a` and `b`. -/
def lmG0 : Global bgvKSSealData := ((Global.empty bgvKSSealData).link "a").link "b"

/-- **The two stages are accepted by the oracle, kernel-checked**: stage 1 on the fresh entries
`a`, `b`; stage 2 on the entry `c` that stage 1 produced. The inlined program of stage 2 (product,
relinearization, rotation, modulus switch, over `a` and `b`) is in `ksClass`. -/
theorem lm_two_stage_kernel :
    admLM mkSeal admSeal lmG0 lmStage1 [("a", true), ("b", true)] = true ∧
      admLM mkSeal admSeal (lmG0.extend lmStage1) lmStage2 [("c", true)] = true := sorry

/-- **Rejections, kernel-checked**: stage 2 declaring its entry input at a level other than the
one stage 1 left it at; stage 2 writing a name the global program already uses; an entry that is
not linked. -/
theorem lm_reject_kernel :
    admLM mkSeal admSeal (lmG0.extend lmStage1)
      ({ lmStage2.1 with inputs := [{ sealDecl "c" with level := 3 }] }, ["c"], fun _ => 0)
      [("c", true)] = false ∧
    admLM mkSeal admSeal (lmG0.extend lmStage1)
      ({ lmStage2.1 with body := lmStage2.1.body ++ [.copy "a" "m"] }, ["c"], fun _ => 0)
      [("c", true)] = false ∧
    admLM mkSeal admSeal (lmG0.extend lmStage1) lmStage2 [("c", false)] = false := sorry

end Challenge.IndCpaDLM
