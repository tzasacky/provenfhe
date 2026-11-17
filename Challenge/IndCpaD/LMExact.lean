import Challenge.IndCpaD.LM

/-!
# Challenge.IndCpaD.LMExact — the exact-operation BGV evaluator in the game with evaluation on earlier results   (LOCKED statements; proofs in `Validation/IndCpaD/LMExact.lean`)

The exact-operation evaluator of `Challenge.IndCpaD.ProfileBGVInstances` (no key switching, no
modulus switching), recast as the local step function `exactStepFn` (it ignores the replay
environment and the public key; on a key switch or modulus switch, which `exactClass` excludes,
it copies the operand, so that it never gets stuck). `exactStep_interpOK`: it is a local interpreter.
`correct_lm_exact`: for every abstract BGV data meeting the encryption hypothesis and every
profile, its interpreter is perfectly correct in the fresh-only game on `exactClass` (there it
computes what `exactEval` computes, and `correct_exactEval` applies), so
`Challenge.IndCpaD.LM` applies. `probLM_eq_bgvSealExact`: the reduction at `bgvSeal`.
-/

namespace Challenge.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile MeasureTheory

/-- `exactStep`, total on well-formed steps: on a key switch or a modulus switch (which never
occur in `exactClass`) it copies the operand, so that the interpreter does not get stuck. -/
def exactStep' (P : FullParams) (σ : Trace.CtEnv P) : Instr → Option (Trace.CtEnv P)
  | .relin d a => (σ a).map fun ca => σ.set d ca
  | .keySwitch d a => (σ a).map fun ca => σ.set d ca
  | .modSwitch d a => (σ a).map fun ca => σ.set d ca
  | i => exactStep P σ i

variable (D : AbsScheme) in
/-- The exact-operation step function. -/
def exactStepFn : StepFn D := fun _ _ σ i => exactStep' D.Pe σ i

/-- **The exact-operation evaluator is a local interpreter.** -/
theorem exactStep_interpOK (D : AbsScheme) : InterpOK D (exactStepFn D) := sorry

/-- **Its interpreter is perfectly correct in the fresh-only game on `exactClass`.** -/
theorem correct_lm_exact (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget) :
    Correct (freshScheme D (exactClass D prof) (interpEval D (exactStepFn D)) D.decBGV) := sorry

/-- The circuit builder at `bgvSeal`. -/
def mkSealExact (p : Program) (f : List Var) (c : Var → M bgvSealData) : bgvSealData.Circ :=
  (p, f, c)

/-- **The reduction at `bgvSeal` with the exact-operation evaluator, evaluation on earlier
results.** -/
theorem probLM_eq_bgvSealExact [DecidableEq (M bgvSealData)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → bgvSealData.PK) (sk : Ω → bgvSealData.SK) (tape : Ω → ℕ → bgvSealData.ER)
    (coins : Ω → Coins) (A : Coins → bgvSealData.PK → LAdv bgvSealData Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, bgvSealData.KeysOK (pk ω) (sk ω) ∧
      ∀ i, bgvSealData.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mkSealExact (exactClass bgvSealData bgvSealProfile)
        (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV b (pk ω) (sk ω)
        (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty bgvSealData) = true} =
      μ {ω | gameCPA (S := freshScheme bgvSealData (exactClass bgvSealData bgvSealProfile)
          (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV) b
        (pk ω) (tape ω) (reductionLM mkSealExact (exactClass bgvSealData bgvSealProfile)
          (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV A (coins ω)
            (pk ω)) 0 = true} := sorry

-- The fresh-only special case at `bgvKSSeal` (compiled, not a theorem): two queries on the fresh
-- entries `a`, `b` only, each two products deep, are each accepted alone, and the second is
-- accepted after the first (on the inlined program of both). That this holds in general is not
-- proved.
#guard admLM mkSeal admSeal lmG0
    ({ inputs := [sealDecl "a", sealDecl "b"],
       body := [.mul "c" "a" "b", .relin "c" "c", .mul "c2" "c" "a", .relin "c2" "c2"],
       outputs := ["c2"] }, ["a", "b"], fun _ => 0) [("a", true), ("b", true)] &&
  admLM mkSeal admSeal (lmG0.extend
    ({ inputs := [sealDecl "a", sealDecl "b"],
       body := [.mul "c" "a" "b", .relin "c" "c", .mul "c2" "c" "a", .relin "c2" "c2"],
       outputs := ["c2"] }, ["a", "b"], fun _ => 0))
    ({ inputs := [sealDecl "a", sealDecl "b"],
       body := [.mul "d" "a" "b", .relin "d" "d", .mul "d2" "d" "b", .relin "d2" "d2"],
       outputs := ["d2"] }, ["a", "b"], fun _ => 0) [("a", true), ("b", true)]

end Challenge.IndCpaDLM
