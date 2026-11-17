import Challenge.Sanity.Coverage
import Validation.Profile.Tool
import Validation.Budget.RunExists
import Validation.BFV.PerInstr

/-!
# Validation.Sanity.Coverage — proofs of the pins of `Challenge.Sanity.Coverage`

Along the zero-message replay that the accepted analysis runs, every operand of a key switch is
defined and at a level of the chain (`Levels`), so the check at every level gives the check at
the operand's level; the other instructions are checked identically.
-/

namespace Validation.Sanity
open Spec Source Challenge.Profile Challenge.CertifyBFV Challenge.BFV
open Validation.Budget.RunAux (Levels levels_step)

/-- The per-instruction check of `coversBFV?`. -/
def covAt (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (Ek : TraceBFV.Budget) :
    Option Instr → Bool
  | some (.mul ..) | some (.square ..) =>
    decide (BudgetBFV.mulLiftApprox P U ≤ Ek.mulLift) &&
      decide (BudgetBFV.mulRoundApprox P r ≤ Ek.mulRound)
  | some (.relin ..) | some (.keySwitch ..) => ksCoversBFV P lay Ek.keySwitch
  | some (.modSwitch ..) => decide (BudgetBFV.msBudget P ≤ Ek.modSwitch)
  | _ => true

theorem coversBFV?_eq' (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) :
    coversBFV? P lay U r body E =
      (schemeParamsOK? P && Budget.specialOK? P &&
        (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
        (List.range body.length).all fun k => covAt P lay U r (E k) body[k]?) := by
  rfl

theorem ksCovers_at {P : FullParams} {lay : Budget.KSLayout} {b : ℕ}
    (h : ksCoversBFV P lay b = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ P.src.qs.length) :
    BudgetBFV.ksBoundAt P lay ℓ ≤ b := by
  have h' : ((List.range P.src.qs.length).all fun j =>
      decide (BudgetBFV.ksBoundAt P lay (j + 1) ≤ b)) = true := h
  have := List.all_eq_true.mp h' (ℓ - 1) (List.mem_range.mpr (by omega))
  rw [Nat.sub_add_cancel h1] at this
  exact of_decide_eq_true this

theorem levelOf_some {Pr : Params} {ρ : Env Pr} {a : Var} {x : Val Pr} (hx : ρ a = some x) :
    levelOf ρ a = x.level := by
  show ((ρ a).map (·.level)).getD 0 = x.level
  rw [hx]; rfl

theorem needAt_of_cov {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {Ek : TraceBFV.Budget}
    {ρ ρ' : Env P.src} {i : Instr} (hcov : covAt P lay U r Ek (some i) = true)
    (hlv : Levels P ρ) (hstep : step P.src ρ i = some ρ') : needAt P lay U r Ek ρ i = true := by
  cases i
  case relin d a | keySwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    show decide (BudgetBFV.ksBoundAt P lay (levelOf ρ a) ≤ Ek.keySwitch) = true
    rw [levelOf_some hx]
    exact decide_eq_true (ksCovers_at hcov x.level (hlv a x hx).1 (hlv a x hx).2)
  all_goals exact hcov

theorem need_of_run {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {E : ℕ → TraceBFV.Budget} :
    ∀ (is : List Instr) (n : ℕ) (ρ : Env P.src) (β : Var → Option TraceBFV.Bnd)
      (res : Env P.src × (Var → Option TraceBFV.Bnd)),
      (∀ j, j < is.length → covAt P lay U r (E (n + j)) is[j]? = true) → Levels P ρ →
      refRunBFVAt P E n is ρ β = some res → needAux P lay U r E n is ρ = true
  | [], _, _, _, _, _, _, _ => rfl
  | i :: is, n, ρ, β, res, hcov, hlv, h => by
    obtain ⟨ρ', v, b, hstep, -, -, -, hrest, -⟩ := Validation.BFV.PerInstrAux.refRunAt_cons_some P h
    rw [Validation.Profile.needAux_cons, hstep]
    have h0 := hcov 0 (by simp)
    rw [Nat.add_zero] at h0
    refine (Bool.and_eq_true _ _).mpr ⟨needAt_of_cov h0 hlv hstep, ?_⟩
    exact need_of_run is (n + 1) ρ' _ res
      (fun j hj => by
        have := hcov (j + 1) (by simpa using hj)
        rwa [show n + (j + 1) = n + 1 + j by omega] at this)
      (levels_step hlv hstep) hrest

theorem coversBFV?_coversBFVAt? (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs))
    (hc : coversBFV? P lay U r prog.body E = true) :
    coversBFVAt? P lay U r prog E = true := by
  obtain ⟨-, hk, -, -, hB, -⟩ := Validation.Profile.certifyBFVProfile?_some h
  obtain ⟨-, hd, ρz, β, hrun, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hB
  rw [coversBFV?_eq'] at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have hlv : Levels P (initEnv P.src prog fun _ => .exact 0) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd', rfl⟩ := hv
    have hok := List.all_eq_true.mp hd d (List.mem_of_find?_eq_some hd')
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩
  have hn := need_of_run (lay := lay) (U := U) (r := r) prog.body 0 _ _ _
    (fun j hj => by rw [Nat.zero_add]; exact h4 j hj) hlv hrun
  rw [Validation.Profile.coversBFVAt?_eq]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨⟨⟨⟨h1, hk⟩, h2⟩, h3⟩, hn⟩

example := (@coversBFV?_coversBFVAt? : type_of% @Challenge.Sanity.coversBFV?_coversBFVAt?)

end Validation.Sanity
