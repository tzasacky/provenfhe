import Spec.IndCpaDProfile
import Challenge.Profile.Defs
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Challenge.IndCpaD.ProfileBGV — IND-CPA-D reduces to IND-CPA for an abstract BGV scheme on a profile class   (LOCKED statements; proofs in `Validation/IndCpaD/ProfileBGV.lean`)

The BGV counterpart of `Challenge.IndCpaD.Profile`; no library, technique or particular
encryption algorithm in the statements. The BGV scheme `schemeBGV D ev adm` has:

* **encryption**: the abstract `D.enc`; **decryption**: textbook BGV decryption
  `[[⟨c, (1, s, …)⟩]_Q]_t` at the ciphertext's level with the secret `D.sec sk`
  (`AbsScheme.decBGV`). Not the switched decryption of a library and not a decryption reduced
  further: what a correct output decrypts to;
* **what a circuit computes**: `Source.eval` of its program (`AbsScheme.sem`). For BGV the
  modulus switch multiplies the message by `q⁻¹ mod t` (`Source.step`), so `sem` includes those
  factors: it is exactly what textbook decryption of a correct output returns, and it is a
  public function of the messages, which is all the simulator needs;
* **the evaluator**: ANY function `ev` of the public key, the circuit and the input ciphertexts;
* **the class**: any public decidable `adm` inside the **profile class** `admBGV D prof`: the
  circuits that `Challenge.Profile.certifyProfile?` accepts (not switched) at the parameters with
  input noise `D.eps` and the budget `prof C`, whose inputs have the shape `inputsFit`, and whose
  plaintext operands (stored as `liftMsg`, centred phase of norm up to `t − 1`) are within
  `D.eps` (`Spec.Correct.InputsOK` asks every input, plaintexts included, to be within the input
  noise).

The hypotheses of the reduction (`correct_bgv`, `bgv_prob_eq`, `bgv_prob_le`):
* (i) `D.EncOKBGV`: for good keys and randomness a fresh ciphertext is at level `D.lvl`, has
  two components and encrypts its message under `D.sec sk` with noise (centred phase, message
  included) at most `D.eps`; this includes that it decrypts;
* (ii) `EvalMeetsBGV D prof adm ev`: for good keys, every circuit of the class and good fresh
  encryptions of the right number, the evaluator's outputs are those, at their message-independent
  levels, of SOME run (`Spec.Trace.Run`) in which every instruction meets its BGV contract within
  `prof C`, under the secret `D.sec sk`;
* (iii) `adm C = true → admBGV D prof C = true`.

**What is still assumed** is what `Challenge.IndCpaD.Profile` lists: IND-CPA of the abstract
scheme with the evaluation keys public, good keys and randomness (almost surely, or the bad
event), no running-time model, evaluation on fresh entries only, textbook decryption. An
evaluator that meets (ii) is in `Challenge.IndCpaD.ProfileBGVInstances` (the exact-operation
evaluator on circuits without key switching or modulus switching); no library's BGV evaluator
is proved to meet it.
-/

namespace Challenge.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile MeasureTheory
open Challenge.Profile (certifyProfile?)

variable (D : AbsScheme)

/-- **The BGV profile class** (module docstring). -/
def admBGV (prof : D.Circ → Trace.Budget) (C : D.Circ) : Bool :=
  (certifyProfile? D.Pe (prof C) (D.prog C) false).isSome && D.inputsFit C &&
    (D.prog C).inputs.all fun d => decide (d.name ∈ D.fresh C) || decide (D.P.src.t - 1 ≤ D.eps)

/-- **The abstract BGV scheme** with the evaluator `ev` and the class `adm`. -/
abbrev schemeBGV
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (adm : D.Circ → Bool) : HEScheme where
  PK := D.PK
  SK := D.SK
  CT := ℕ × List (IntPoly D.P.src.N)
  M := Poly D.P.src.t D.P.src.N
  ER := D.ER
  Circ := D.Circ
  enc := D.enc
  eval := fun pk C cs => if cs.length = (D.fresh C).length then ev pk C cs else []
  dec := D.decBGV
  sem := D.sem
  admissible := adm
  KeysOK := D.KeysOK
  GoodE := D.GoodE

/-- **The evaluator meets the BGV contracts within the profile** (module docstring, (ii)). -/
def EvalMeetsBGV (prof : D.Circ → Trace.Budget) (adm : D.Circ → Bool)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N))) : Prop :=
  ∀ pk sk, D.KeysOK pk sk → ∀ C, adm C = true →
    ∀ ins : List (Poly D.P.src.t D.P.src.N × D.ER), (∀ p ∈ ins, D.GoodE pk sk p.2) →
      ins.length = (D.fresh C).length →
      ∃ σ, Trace.Run D.Pe (prof C) (D.sec sk) (D.prog C).body
          (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x))
          (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2))) σ ∧
        ev pk C (ins.map fun p => D.enc pk p.1 p.2) =
          (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])

/-- **Perfect correctness of the abstract BGV scheme on a profile class**: the hypotheses (i),
(ii), (iii) of the module docstring. -/
theorem correct_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBGV D prof adm ev) : Correct (schemeBGV D ev adm) := sorry

/-- **IND-CPA-D reduces to IND-CPA, BGV, no library**: equal winning probabilities. -/
theorem bgv_prob_eq (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBGV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Adv (schemeBGV D ev adm) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameD (S := schemeBGV D ev adm) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} =
      μ {ω | gameCPA (S := schemeBGV D ev adm) b (pk ω) (tape ω)
        (reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true} := sorry

/-- **The bad-event version, BGV, no library.** -/
theorem bgv_prob_le (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBGV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Adv (schemeBGV D ev adm) Bool) (b : Bool) (q : ℕ)
    (hq : ∀ r p, Bounded (A r p) q) :
    μ {ω | gameD (S := schemeBGV D ev adm) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} ≤
        μ {ω | gameCPA (S := schemeBGV D ev adm) b (pk ω) (tape ω)
          (reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := schemeBGV D ev adm) b (pk ω) (tape ω)
          (reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameD (S := schemeBGV D ev adm) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
          = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} := sorry

end Challenge.IndCpaDProfile
