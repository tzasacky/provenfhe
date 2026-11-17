import Challenge.IndCpaD

/-!
# Challenge.IndCpaD.Generic — the IND-CPA-D reduction for every evaluator that meets the contracts   (LOCKED statements; proofs in `Validation/IndCpaD/Generic.lean`)

`Challenge.IndCpaD.correct` is about one evaluator, the library transcription `runLibrary`. Its
proof uses that evaluator in one place only: the outputs of `runLibrary` are the end of a run
(`Spec.TraceBFV.RunAt`) within the certificate's per-instruction budget. This file separates the
two parts.

* `schemeWith St ev`: the scheme of `St` with the evaluator replaced by an arbitrary public
  deterministic function `ev` of the public key, the circuit and the input ciphertexts (the
  length test of `Challenge.IndCpaD.eval` is kept). Encryption, decryption, messages, what a
  circuit computes, the declared class and the key and randomness predicates are those of
  `scheme St`.
* `EvalMeets St ev`: for good keys, every circuit of the class and good fresh encryptions of the
  right number, the outputs of `ev` are the outputs, read at their levels, of SOME run in which
  instruction `k` meets its contract (`Spec.TraceBFV.StepOK`) within `fc.cert.budget k`, the
  budget of the circuit's certificate.
* `correct_of_meets`: `freshDecOK St` and `EvalMeets St ev` give `Correct (schemeWith St ev)`.
  No floating-point hypothesis: the binary64 model enters only through `libEval_meets`.
* `meets_prob_eq`, `meets_prob_le`: the statements of `Challenge.IndCpaD.prob_eq` and `prob_le`
  for `schemeWith St ev`, for every such `ev`.
* `libEval_meets`: under `Spec.Float.Conforms St.A` the library transcription meets the
  contracts; `schemeWith_libEval`: `schemeWith St (libEval St)` is `scheme St` by definition;
  `correct_libEval`: `Challenge.IndCpaD.correct` recovered as a corollary.

**What is still instance-specific.** The class is still defined through `certifyBFVFresh?` and
hence through the setting's declared technique, layout, plaintext-addition method and the
budget table of `Challenge.CertifyBFV.Defs`: `EvalMeets` asks an evaluator to stay within THAT
budget, which was computed for the declared technique. Encryption is still the modelled
encryption `Spec.IndCpaDBFV.enc` (OpenFHE's `STANDARD` public-key encryption of `liftMsg m` at the
top level) and decryption the textbook one. The evaluator must be a function of public data
only (it is a parameter of `schemeWith`, applied to `pk`, `C` and the ciphertexts); running time
is not modelled, and nothing here says that any evaluator other than those for which
`EvalMeets` is proved satisfies it.
-/

namespace Challenge.IndCpaD
open Spec NPoly Scheme Source Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
  Challenge.CertifyBFV Challenge.BFVEncrypt Spec.IndCpaDBFV MeasureTheory
open Spec.IndCpaD (Correct Adv Bounded gameD gameCPA reduction)

variable {St : Setting}

variable (St) in
/-- **The scheme of `St` with the evaluator `ev`.** Everything but the evaluator is `scheme St`;
the evaluator returns `[]` when the number of ciphertexts is not the circuit's number of fresh
inputs, as `Challenge.IndCpaD.eval` does. -/
abbrev schemeWith
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St))) :
    Spec.IndCpaD.HEScheme :=
  { scheme St with eval := fun pk C cs => if cs.length = C.fresh.length then ev pk C cs else [] }

variable (St) in
/-- **The evaluator meets the contracts within the certified budget.** For good keys, every
circuit of the class (with its fresh certificate `fc`) and good fresh encryptions of the right
number, the evaluator's outputs are those of some run, at the analysed parameters (the
setting's with the input noise of the fresh certificate), in which
instruction `k` meets its contract within `fc.cert.budget k`, each output read with the level of
the zero-message replay (`Circ.outLevel`). -/
def EvalMeets
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St))) : Prop :=
  ∀ pk sk, KeysOK pk sk → ∀ (C : Circ St), admissible C = true → ∀ fc,
    certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc →
    C.extraOK = true →
    ∀ ins : List (Poly St.base.P.src.t St.base.P.src.N × ER (St := St)),
      (∀ p ∈ ins, GoodE pk sk p.2) → ins.length = C.fresh.length →
      ∃ σ, TraceBFV.RunAt ({ St.base.P with inputNoise := fc.params.inputNoise } : FullParams) fc.cert.budget sk.s 0 C.prog.body
          (initEnv St.base.P.src C.prog fun x => .exact (C.msg (ins.map Prod.fst) x))
          (Trace.initCt ({ St.base.P with inputNoise := fc.params.inputNoise } : FullParams) C.prog
            (C.cts (ins.map fun p => enc pk p.1 p.2))) σ ∧
        ev pk C (ins.map fun p => enc pk p.1 p.2) =
          C.prog.outputs.map fun o => (C.outLevel o, (σ o).getD [])

variable (St) in
/-- The library transcription as an evaluator (without the length test, which `schemeWith`
adds). -/
def libEval (pk : PK (St := St)) (C : Circ St) (cs : List (CT (St := St))) :
    List (CT (St := St)) :=
  C.prog.outputs.map fun o =>
    (C.outLevel o, (runLibrary C.input St.A pk.rk pk.gk (C.cts cs) o).getD [])

/-- **Perfect correctness for every evaluator that meets the contracts.** -/
theorem correct_of_meets (St : Setting) (hSt : freshDecOK St = true)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev) : Correct (schemeWith St ev) := sorry

/-- **Equal winning probabilities for every evaluator that meets the contracts**, under any
measure on the joint randomness for which the keys and every encryption are good almost
surely. -/
theorem meets_prob_eq (St : Setting) (hSt : freshDecOK St = true)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Adv (schemeWith St ev) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω) ∧ ∀ i, GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameD (S := schemeWith St ev) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} =
      μ {ω | gameCPA (S := schemeWith St ev) b (pk ω) (tape ω)
        (reduction (S := schemeWith St ev) A (coins ω) (pk ω)) 0 = true} := sorry

/-- **The bad-event version for every evaluator that meets the contracts**, for an adversary
making at most `q` encryption queries. -/
theorem meets_prob_le (St : Setting) (hSt : freshDecOK St = true)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Adv (schemeWith St ev) Bool) (b : Bool)
    (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    μ {ω | gameD (S := schemeWith St ev) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} ≤
        μ {ω | gameCPA (S := schemeWith St ev) b (pk ω) (tape ω)
          (reduction (S := schemeWith St ev) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := schemeWith St ev) b (pk ω) (tape ω)
          (reduction (S := schemeWith St ev) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameD (S := schemeWith St ev) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
          = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} := sorry

/-- **The library transcription is one evaluator that meets the contracts**, when the setting's
binary64 arithmetic conforms to the standard model. -/
theorem libEval_meets (St : Setting) (hA : Spec.Float.Conforms St.A) :
    EvalMeets St (libEval St) := sorry

/-- `schemeWith St (libEval St)` is `scheme St`, by definition. -/
theorem schemeWith_libEval (St : Setting) : schemeWith St (libEval St) = scheme St := sorry

/-- **`Challenge.IndCpaD.correct`, as a corollary**: `correct_of_meets` at `libEval_meets`. -/
theorem correct_libEval (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A) : Correct (schemeWith St (libEval St)) := sorry

end Challenge.IndCpaD
