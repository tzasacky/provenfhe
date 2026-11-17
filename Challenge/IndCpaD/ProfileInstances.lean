import Challenge.IndCpaD.Profile
import Challenge.IndCpaD.Textbook

/-!
# Challenge.IndCpaD.ProfileInstances — the OpenFHE-shaped and textbook BFV theorems as instances of the library-free one   (LOCKED statements; proofs in `Validation/IndCpaD/ProfileInstances.lean`)

`Challenge.IndCpaD.Profile` states the IND-CPA-D reduction for an abstract BFV scheme on a
profile class (`correct_bfv`, `bfv_prob_eq`, `bfv_prob_le`). This file instantiates it.

* `dataOf St`: the setting `St` of `Spec.IndCpaDBFV` as abstract data: OpenFHE's `STANDARD`
  encryption at the top level (`Spec.IndCpaDBFV.enc`), its keys and randomness predicates, its
  circuits, and the fresh noise bound `eps = freshNoiseBFV t Q_top (worstError …)`.
  `profOf St C`: the per-instruction budget that `certifyBFVFresh?` computes for `C` (the
  tool's budget for the declared technique; the zero profile when it rejects). It is a function
  of the circuit and the public setting only.
* `admissible_profile`: **the tool's class is inside the profile class** (tool acceptance implies
  profile acceptance at the computed budget, `Challenge.Profile.certifyBFV?_profile`, at the
  same input noise).
* `encOK_dataOf`: the modelled encryption meets hypothesis (i) when `freshDecOK St`.
* `evalMeets_dataOf`: **every evaluator that meets the contracts at the tool's budget**
  (`Challenge.IndCpaD.EvalMeets`) meets hypothesis (ii) at `profOf`. Hence the library
  transcription (`libEval_meets`, under `Spec.Float.Conforms`) and the textbook-multiplication
  evaluator (`textEval_meets`) are instances.
* `correct_via_profile`, `bfv_prob_eq_via_profile`, `bfv_prob_le_via_profile`: the statements of
  `Challenge.IndCpaD.correct`, `bfv_prob_eq`, `bfv_prob_le`, recovered from the library-free
  theorem; `correct_textEval_via_profile`: `Challenge.IndCpaD.correct_textEval` likewise.
* Non-vacuity of the library-free class: `admBFV_tiny` (kernel-checked, at `tinySetting`) and
  compiled `#guard`s at `sealSetting` (`N = 2¹³`, four 43–44-bit limbs, `t = 65537`), both with the
  tool's profile and with a profile given directly (the textbook budget, no technique).
-/

namespace Challenge.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDBFV Spec.EncryptBFV
  Spec.Encrypt Spec.CertifyBFV Challenge.BFVEncrypt Challenge.IndCpaD MeasureTheory

/-- **The setting `St` as abstract data** (module docstring). -/
def dataOf (St : Setting) : AbsScheme where
  P := St.base.P
  eps := freshNoiseBFV St.base.P.src.t (Qtop St)
    (worstError St.base.P.src.N St.base.P.secretBound St.Bk St.Bu St.B1 St.B2)
  lvl := top St
  PK := PK (St := St)
  SK := SK (St := St)
  ER := ER (St := St)
  Circ := Circ St
  sec := SK.s
  enc := enc
  KeysOK := KeysOK
  GoodE := GoodE
  prog := Circ.prog
  fresh := Circ.fresh
  pt := Circ.pt

/-- **The tool's profile**: the per-instruction budget of the fresh certificate of the circuit,
or the zero profile when the tool rejects it. -/
def profOf (St : Setting) (C : Circ St) : ℕ → TraceBFV.Budget :=
  match certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with
  | some fc => fc.cert.budget
  | none => fun _ => ⟨0, 0, 0, 0, 0⟩

/-- **The tool's class is inside the profile class.** -/
theorem admissible_profile (St : Setting) (C : Circ St) (h : admissible C = true) :
    admBFV (dataOf St) (profOf St) C = true := sorry

/-- **The modelled encryption meets the encryption hypothesis** when a fresh encryption decrypts
in the setting. -/
theorem encOK_dataOf (St : Setting) (hSt : freshDecOK St = true) : (dataOf St).EncOKBFV := sorry

/-- **An evaluator that meets the contracts at the tool's budget meets them at the tool's
profile.** -/
theorem evalMeets_dataOf (St : Setting)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev) : EvalMeetsBFV (dataOf St) (profOf St) admissible ev := sorry

/-- **`Challenge.IndCpaD.correct`, from the library-free theorem.** -/
theorem correct_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A) : Correct (scheme St) := sorry

/-- **`Challenge.IndCpaD.correct_textEval`, from the library-free theorem.** -/
theorem correct_textEval_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hnl : ∀ Ps, St.base.mul ≠ some (.leveled Ps)) : Correct (schemeWith St (textEval St)) :=
  sorry

/-- **`Challenge.IndCpaD.bfv_prob_eq`, from the library-free theorem.** -/
theorem bfv_prob_eq_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Adv (scheme St) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω) ∧ ∀ i, GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | gameCPA (S := scheme St) b (pk ω) (tape ω)
        (reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} := sorry

/-- **`Challenge.IndCpaD.bfv_prob_le`, from the library-free theorem.** -/
theorem bfv_prob_le_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Adv (scheme St) Bool) (b : Bool) (q : ℕ)
    (hq : ∀ r p, Bounded (A r p) q) :
    μ {ω | gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | gameCPA (S := scheme St) b (pk ω) (tape ω)
          (reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := scheme St) b (pk ω) (tape ω)
          (reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} := sorry

/-! ## Non-vacuity of the library-free class -/

/-- **The profile class is not empty at `tinySetting`, and its encryption hypothesis holds**
(kernel-checked through `admissible_tiny`). -/
theorem admBFV_tiny : admBFV (dataOf tinySetting) (profOf tinySetting) tinyCirc = true ∧
    (dataOf tinySetting).EncOKBFV := sorry

/-- The textbook budget of `sealSetting` with one limb per digit, as a profile given directly: no
technique, no tool. -/
def sealTextbookProfile (_ : Circ sealSetting) : ℕ → TraceBFV.Budget :=
  fun _ => BudgetBFV.certified sealSetting.base.P (Budget.uniformLayout 1)


-- At `sealSetting` (`N = 2¹³`, `t = 65537`, four limbs, HPS declared): `sealCirc` (a product, a
-- relinearization, a rotation by 5 and a plaintext addition) is in the profile class at the
-- tool's profile and at the directly given textbook profile, and a fresh encryption decrypts.
#guard freshDecOK sealSetting && admBFV (dataOf sealSetting) (profOf sealSetting) sealCirc
#guard admBFV (dataOf sealSetting) sealTextbookProfile sealCirc
-- Outside the class: a fresh input declared below the encryption level; and the same circuit
-- followed by four more products and relinearizations (the profile certificate rejects it).
#guard !admBFV (dataOf sealSetting) sealTextbookProfile
  ⟨{ sealCirc.prog with inputs := [⟨"a", 2, 3, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩, ⟨"p", 1, 4, 1, 1⟩] },
    [], ["a", "b"], fun _ => 0⟩
#guard !admBFV (dataOf sealSetting) sealTextbookProfile
  ⟨{ sealCirc.prog with
      body := sealCirc.prog.body ++ [.mul "q" "o" "o", .relin "q" "q", .mul "q" "q" "q",
        .relin "q" "q", .mul "q" "q" "q", .relin "q" "q", .mul "q" "q" "q", .relin "q" "q"],
      outputs := ["q"] }, [], ["a", "b"], fun _ => 0⟩
-- THE ZERO PROFILE accepts `sealCirc` too: acceptance of a profile says nothing about whether an
-- evaluator stays within it. In the theorems that is hypothesis (ii), `EvalMeetsBFV`, proved for
-- an evaluator only through a realizability argument (`evalMeets_dataOf` with `libEval_meets`
-- or `textEval_meets`, at the tool's profile).
#guard admBFV (dataOf sealSetting) (fun _ _ => ⟨0, 0, 0, 0, 0⟩) sealCirc

end Challenge.IndCpaDProfile
