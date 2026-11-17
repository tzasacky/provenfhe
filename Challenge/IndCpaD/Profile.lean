import Spec.IndCpaDProfile
import Challenge.Profile.Defs
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Challenge.IndCpaD.Profile — IND-CPA-D reduces to IND-CPA for an abstract BFV scheme on a profile class   (LOCKED statements; proofs in `Validation/IndCpaD/Profile.lean`)

The games and the reduction are those of `Spec.IndCpaD`; the abstract scheme data is
`Spec.IndCpaDProfile.AbsScheme`. Nothing in these statements names a library, a key-switching
technique, a multiplication algorithm, a floating-point model or a particular encryption
algorithm. The BFV scheme `schemeBFV D ev adm` has:

* **encryption**: the abstract `D.enc`; **decryption**: textbook BFV decryption at the
  ciphertext's level with the secret `D.sec sk` (`AbsScheme.decBFV`); **what a circuit
  computes**: `Source.eval` of its program (`AbsScheme.sem`);
* **the evaluator**: ANY function `ev` of the public key, the circuit and the input ciphertexts
  (the game returns `[]` when their number is not the circuit's number of fresh inputs);
* **the class**: any public decidable `adm` inside the **profile class** `admBFV D prof`:
  the circuits `C` that `Challenge.Profile.certifyBFVProfile?` accepts at the parameters with
  input noise `D.eps` and at the per-instruction profile `prof C`, and whose inputs have the
  shape `AbsScheme.inputsFit`. `prof` is part of the public scheme data: a function of the
  circuit, which is public. No uniformity condition on how the profile is chosen per circuit is
  needed: the reduction only runs the evaluator, and the evaluator hypothesis below is per
  circuit, at that circuit's profile.

The hypotheses of the reduction (`correct_bfv`, `bfv_prob_eq`, `bfv_prob_le`):
* (i) `D.EncOKBFV`: for good keys and randomness a fresh ciphertext is at level `D.lvl`, has
  two components and encrypts its message under `D.sec sk` with noise at most `D.eps`
  (`BFVEncrypts`). This includes that it decrypts: no separate "fresh ciphertexts decrypt"
  hypothesis is needed. (That the parameters are BFV is not a hypothesis: the profile
  certificate checks it, and fresh correctness does not need it.)
* (ii) `EvalMeetsBFV D prof adm ev`: for good keys, every circuit of the class and good fresh
  encryptions of the right number, the evaluator's outputs are those, at their message-independent
  levels, of SOME run (`Spec.TraceBFV.RunAt`) in which instruction `k` meets its contract within
  `prof C k`, under the secret `D.sec sk`;
* (iii) `adm C = true → admBFV D prof C = true`.

**What is still assumed, and not proved anywhere.** That the abstract scheme is IND-CPA with the
evaluation keys in the public key (the assumption the reduction reduces to; it includes a
circular-security assumption for the key-switching keys); that the keys and the encryption
randomness are good (almost surely in `bfv_prob_eq`; the explicit bad event of `bfv_prob_le`);
no running-time model; evaluation on fresh entries only; the decryption oracle returns textbook
decryption (`Spec.IndCpaD`'s docstring lists the rest). That a given evaluator meets (ii) is a
proof about that evaluator (`Challenge.IndCpaD.ProfileInstances`: OpenFHE's transcription under
`Spec.Float.Conforms`, and the textbook-multiplication evaluator).
-/

namespace Challenge.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile MeasureTheory
open Challenge.Profile (certifyBFVProfile?)

variable (D : AbsScheme)

/-- **The BFV profile class**: the profile certificate accepts the circuit's program at input
noise `D.eps` and the profile `prof C`, and the inputs have the shape `inputsFit`. -/
def admBFV (prof : D.Circ → ℕ → TraceBFV.Budget) (C : D.Circ) : Bool :=
  (certifyBFVProfile? D.Pe (prof C) (D.prog C)).isSome && D.inputsFit C

/-- **The abstract BFV scheme** with the evaluator `ev` and the class `adm`. -/
abbrev schemeBFV
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
  dec := D.decBFV
  sem := D.sem
  admissible := adm
  KeysOK := D.KeysOK
  GoodE := D.GoodE

/-- **The evaluator meets the contracts within the profile** (module docstring, (ii)). -/
def EvalMeetsBFV (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N))) : Prop :=
  ∀ pk sk, D.KeysOK pk sk → ∀ C, adm C = true →
    ∀ ins : List (Poly D.P.src.t D.P.src.N × D.ER), (∀ p ∈ ins, D.GoodE pk sk p.2) →
      ins.length = (D.fresh C).length →
      ∃ σ, TraceBFV.RunAt D.Pe (prof C) (D.sec sk) 0 (D.prog C).body
          (initEnv D.P.src (D.prog C) fun x => .exact (D.msg C (ins.map Prod.fst) x))
          (Trace.initCt D.Pe (D.prog C) (D.cts C (ins.map fun p => D.enc pk p.1 p.2))) σ ∧
        ev pk C (ins.map fun p => D.enc pk p.1 p.2) =
          (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])

/-- **Perfect correctness of the abstract BFV scheme on a profile class**: the hypotheses (i),
(ii), (iii) of the module docstring. -/
theorem correct_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBFV D prof adm ev) : Correct (schemeBFV D ev adm) := sorry

/-- **IND-CPA-D reduces to IND-CPA, BFV, no library**: equal winning probabilities for each bit
under any measure on the joint randomness for which the keys and every encryption are good
almost surely. -/
theorem bfv_prob_eq (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBFV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Adv (schemeBFV D ev adm) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameD (S := schemeBFV D ev adm) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} =
      μ {ω | gameCPA (S := schemeBFV D ev adm) b (pk ω) (tape ω)
        (reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true} := sorry

/-- **The bad-event version, BFV, no library**, for an adversary making at most `q` encryption
queries: the two winning probabilities differ by at most the probability that the keys or one
of the first `q` encryptions are not good. -/
theorem bfv_prob_le (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBFV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Adv (schemeBFV D ev adm) Bool) (b : Bool) (q : ℕ)
    (hq : ∀ r p, Bounded (A r p) q) :
    μ {ω | gameD (S := schemeBFV D ev adm) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} ≤
        μ {ω | gameCPA (S := schemeBFV D ev adm) b (pk ω) (tape ω)
          (reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := schemeBFV D ev adm) b (pk ω) (tape ω)
          (reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameD (S := schemeBFV D ev adm) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
          = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} := sorry

end Challenge.IndCpaDProfile
