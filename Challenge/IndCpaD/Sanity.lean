import Spec.IndCpaDSanity
import Spec.IndCpaDLM
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Challenge.IndCpaD.Sanity — what the games and the reductions do, stated   (LOCKED statements; proofs in `Validation/IndCpaD/Sanity.lean`)

Statements a reader comparing `Spec.IndCpaD` and `Spec.IndCpaDLM` with the literature expects to
hold. None is used by the headline theorems; each says that a definition means what its
docstring says.

1. **The reductions make exactly the adversary's encryption queries, at most `q`**
   (`reduce_cpaBounded`, `reduction_cpaBounded`, `reduceLM_cpaBounded`): an IND-CPA-D adversary
   with at most `q` encryption queries on every path gives an IND-CPA adversary with at most `q`
   left-or-right queries on every path (`Spec.IndCpaD.CpaBounded`). Evaluation and decryption
   queries cost no query of the IND-CPA game.
2. **The games read only the first `q` entries of the tape** (`gameD_tape_local`,
   `gameCPA_tape_local`, `gameLM_tape_local`): for a bounded adversary the bit the game returns
   is the same on two tapes that agree below `q`. This is why the bad event of `prob_le` is about
   the first `q` encryptions only.
3. **The games are symmetric in the two messages** (`gameD_swap`, `gameCPA_swap`,
   `reduce_swap`): exchanging the two messages of every encryption query of the adversary is the
   same as flipping the challenge bit, and the reduction commutes with the exchange. So the
   decryption condition, the message tracking of the evaluation oracle and the simulation treat
   the left and right sides alike.
4. **The games can be lost** (`idScheme`, `idScheme_correct`, `idCpaAdv_wins`, `idAdv_wins`,
   `idAdv_reduction_wins`): for the scheme whose encryption is the identity (perfectly correct
   on every circuit), the IND-CPA adversary that submits `(false, true)` and returns the
   ciphertext outputs the challenge bit, and so do the analogous IND-CPA-D adversary and the
   reduction built from it: the definitions are not vacuously secure, and the reduction does not
   lose an adversary that wins.
5. **Evaluation correctness cannot be dropped** (`leakScheme`, `leakScheme_fresh`,
   `leakScheme_not_correct`, `leakAdv_wins`, `leakAdv_reduction_loses`, `leakAdv_advantage`): a scheme in which every
   fresh encryption decrypts to its message, but whose evaluator returns its input where `sem`
   says the constant `false`. An IND-CPA-D adversary encrypts `(false, true)`, evaluates, and
   decrypts the derived entry (whose two tracked messages are equal, so the oracle answers): it
   outputs the challenge bit, while the reduction from it (which answers from the table) always
   outputs `false`. So `Challenge.IndCpaD.gameD_eq_gameCPA` is false without `Correct.eval`, every
   key and tape being good, and so is the advantage bound: the IND-CPA-D advantage of the
   adversary is 1 and the IND-CPA advantage of the reduction from it is 0. (The encryption of
   this toy is the identity, so it is not IND-CPA either: the point is the failure of the
   simulation, not an insecure-but-IND-CPA scheme, which a model without running time cannot
   exhibit for public-key encryption.)
6. **Discrete samplers give measurable events** (`gameD_measurableSet`,
   `gameCPA_reduction_measurableSet`, `bad_measurableSet`): if the keys, the coins and the
   first `q` encryption samples are functions of one measurable map into a countable space with
   measurable singletons (a discrete sampler; the sample space itself may be anything, for
   instance an infinite sequence of samples) and the adversary makes at most `q` encryption
   queries, the events of `Challenge.IndCpaD.prob_le` are measurable sets, so the measures in the
   statements are probabilities, not outer measures. No countability of the key or randomness
   types is assumed (`Challenge.IndCpaD.SanityInstances` applies them to an instance).
7. **Every global program the game with evaluation on earlier results reaches is in `Reach`**
   (`reach_link`, `reach_evalLM`): naming a fresh entry and every accepted evaluation query keep
   the global program reachable, so the agreement statements of `Challenge.IndCpaD.LMAgree`
   (stated for reachable global programs) apply to every state the game visits.
8. **Correctness is necessary for the perfect simulation, and exactly so** (`correct_of_sim`,
   `sim_iff`): if the
   IND-CPA-D game and the IND-CPA game of the reduction return the same bit for every adversary
   on every good tape (the conclusion of `Challenge.IndCpaD.gameD_eq_gameCPA`), then every good
   fresh encryption decrypts to its message, and on every circuit of the class and good fresh
   encryptions, every output the evaluator returns at a position where `sem` has an output
   decrypts to that output. Conversely (`sim_iff`), these two conditions give the perfect
   simulation. So the perfect simulation for every adversary is EQUIVALENT to `Correct` with the
   equality of the decrypted output list and `sem` weakened to agreement at every position both
   lists have: `Correct` is the weakest hypothesis for `gameD_eq_gameCPA` up to the lengths of
   the two lists, and a difference in those lengths alone never breaks the simulation.
9. **Symmetry for the game with evaluation on earlier results, and equal pairs give nothing**
   (`gameLM_swap`, `gameD_pairs_equal`, `gameLM_pairs_equal`): the exchange of 3 for `gameLM`;
   and an adversary whose every encryption query has equal messages (equivalently, which is its
   own exchange) wins with the same probability for both bits, in both games: the bit reaches the
   adversary only through encryption queries with different messages.
10. **Measurability for the game with evaluation on earlier results** (`gameLM_measurableSet`,
    `gameCPA_reductionLM_measurableSet`): under the hypotheses of 6, the event of the game and the
    IND-CPA event of its reduction (the two sides of `Challenge.IndCpaDLM.advLM_le`) are measurable.
-/

namespace Challenge.IndCpaDSanity
open Spec Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM MeasureTheory

/-! ## 1. Query counts of the reductions -/

/-- **The reduction makes at most the adversary's number of encryption queries**, from any
table. -/
theorem reduce_cpaBounded (S : HEScheme) [DecidableEq S.M] (pk : S.PK) (A : Adv S Bool)
    (T : List (Entry S)) (q : ℕ) (hq : Bounded A q) : CpaBounded (reduce pk A T) q := sorry

/-- **The IND-CPA adversary built by the reduction makes at most `q` queries** when the
IND-CPA-D adversary makes at most `q` encryption queries, for every coin value and public key. -/
theorem reduction_cpaBounded (S : HEScheme) [DecidableEq S.M] {Coins : Type}
    (A : Coins → S.PK → Adv S Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) (r : Coins)
    (pk : S.PK) : CpaBounded (reduction A r pk) q := sorry

/-- **The same for the game with evaluation on earlier results.** -/
theorem reduceLM_cpaBounded (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (pk : D.PK) (A : LAdv D Bool)
    (T : List (LEntry D)) (G : Global D) (q : ℕ) (hq : BoundedLM A q) :
    CpaBounded (S := freshScheme D adm ev dec) (reduceLM mk adm ev dec pk A T G) q := sorry

/-! ## 2. The games read the first `q` tape entries only -/

/-- **IND-CPA-D: only the first `q` encryptions' randomness matters** for an adversary with at
most `q` encryption queries. -/
theorem gameD_tape_local (S : HEScheme) [DecidableEq S.M] (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape tape' : ℕ → S.ER) (A : Adv S Bool) (q : ℕ) (hq : Bounded A q)
    (h : ∀ i < q, tape i = tape' i) :
    gameD b pk sk tape A 0 [] = gameD b pk sk tape' A 0 [] := sorry

/-- **IND-CPA: only the first `q` encryptions' randomness matters** for an adversary with at
most `q` queries. -/
theorem gameCPA_tape_local (S : HEScheme) (b : Bool) (pk : S.PK) (tape tape' : ℕ → S.ER)
    (B : CpaAdv S Bool) (q : ℕ) (hq : CpaBounded B q) (h : ∀ i < q, tape i = tape' i) :
    gameCPA b pk tape B 0 = gameCPA b pk tape' B 0 := sorry

/-- **Evaluation on earlier results: only the first `q` encryptions' randomness matters.** -/
theorem gameLM_tape_local (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (b : Bool) (pk : D.PK) (sk : D.SK)
    (tape tape' : ℕ → D.ER) (A : LAdv D Bool) (q : ℕ) (hq : BoundedLM A q)
    (h : ∀ i < q, tape i = tape' i) :
    gameLM mk adm ev dec b pk sk tape A 0 [] (Global.empty D) =
      gameLM mk adm ev dec b pk sk tape' A 0 [] (Global.empty D) := sorry

/-! ## 3. Symmetry in the two messages -/

/-- **IND-CPA-D: exchanging the messages of every encryption query flips the bit.** -/
theorem gameD_swap (S : HEScheme) [DecidableEq S.M] (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape : ℕ → S.ER) (A : Adv S Bool) :
    gameD b pk sk tape A.swap 0 [] = gameD (!b) pk sk tape A 0 [] := sorry

/-- **IND-CPA: exchanging the messages of every query flips the bit.** -/
theorem gameCPA_swap (S : HEScheme) (b : Bool) (pk : S.PK) (tape : ℕ → S.ER)
    (B : CpaAdv S Bool) : gameCPA b pk tape B.swap 0 = gameCPA (!b) pk tape B 0 := sorry

/-- **The reduction commutes with the exchange.** -/
theorem reduce_swap (S : HEScheme) [DecidableEq S.M] (pk : S.PK) (A : Adv S Bool) :
    reduce pk A.swap [] = (reduce pk A []).swap := sorry

/-! ## 4. The games can be lost -/

/-- The scheme whose encryption is the identity on bits: one circuit, which returns its inputs;
every key and every randomness is good. -/
abbrev idScheme : HEScheme where
  PK := Unit
  SK := Unit
  CT := Bool
  M := Bool
  ER := Unit
  Circ := Unit
  enc := fun _ m _ => m
  eval := fun _ _ cs => cs
  dec := fun _ c => c
  sem := fun _ ms => ms
  admissible := fun _ => true
  KeysOK := fun _ _ => True
  GoodE := fun _ _ _ => True

/-- `idScheme` is perfectly correct on its class. -/
theorem idScheme_correct : Correct idScheme := sorry

/-- The IND-CPA adversary: submit `(false, true)`, return the ciphertext. -/
def idCpaAdv : CpaAdv idScheme Bool := .lr false true fun c => .ret c

/-- **The IND-CPA game can be lost**: against `idScheme` the adversary returns the bit. -/
theorem idCpaAdv_wins (b : Bool) (pk : Unit) (tape : ℕ → Unit) :
    gameCPA b pk tape idCpaAdv 0 = b := sorry

/-- The IND-CPA-D adversary: encrypt `(false, true)`, return the ciphertext. -/
def idAdv : Adv idScheme Bool := .enc false true fun c => .ret c

/-- **The IND-CPA-D game can be lost**, and **the reduction from the winning adversary wins**:
the bound of the reduction is attained (advantage 1 on both sides). -/
theorem idAdv_wins (b : Bool) (pk sk : Unit) (tape : ℕ → Unit) :
    gameD b pk sk tape idAdv 0 [] = b ∧
      gameCPA b pk tape (reduction (fun (_ : Unit) _ => idAdv) () pk) 0 = b := sorry

/-! ## 5. Evaluation correctness cannot be dropped -/

/-- A scheme with correct fresh encryptions whose evaluator returns its input ciphertexts while
`sem` says the constant `false`. -/
abbrev leakScheme : HEScheme where
  PK := Unit
  SK := Unit
  CT := Bool
  M := Bool
  ER := Unit
  Circ := Unit
  enc := fun _ m _ => m
  eval := fun _ _ cs => cs
  dec := fun _ c => c
  sem := fun _ _ => [false]
  admissible := fun _ => true
  KeysOK := fun _ _ => True
  GoodE := fun _ _ _ => True

/-- Every fresh encryption of `leakScheme` decrypts to its message (`Correct.fresh`). -/
theorem leakScheme_fresh : ∀ pk sk, leakScheme.KeysOK pk sk → ∀ m er, leakScheme.GoodE pk sk er →
    leakScheme.dec sk (leakScheme.enc pk m er) = m := sorry

/-- `leakScheme` is not perfectly correct on its class. -/
theorem leakScheme_not_correct : ¬ Correct leakScheme := sorry

/-- The IND-CPA-D adversary: encrypt `(false, true)` and ignore the ciphertext; evaluate the
circuit on entry 0; decrypt entry 1 (both tracked messages are `false`); return the answer. -/
def leakAdv : Adv leakScheme Bool :=
  .enc false true fun _ => .eval () [0] fun _ => .dec 1 fun r => .ret (r == some true)

/-- **The adversary wins the IND-CPA-D game** of `leakScheme`, on every key and tape (all good). -/
theorem leakAdv_wins (b : Bool) (pk sk : Unit) (tape : ℕ → Unit) :
    TapeOK pk sk tape leakAdv 0 ∧ gameD b pk sk tape leakAdv 0 [] = b := sorry

/-- **The reduction from it always returns `false`**: the perfect simulation fails for
`b = true` although the keys and every encryption are good. -/
theorem leakAdv_reduction_loses (b : Bool) (pk : Unit) (tape : ℕ → Unit) :
    gameCPA b pk tape (reduction (fun (_ : Unit) _ => leakAdv) () pk) 0 = false := sorry

/-- **The advantage bound fails without `Correct`**: under any probability measure (all keys and
encryptions good, so the bad event is empty), the IND-CPA-D advantage of `leakAdv` is 1 and the
IND-CPA advantage of the reduction from it is 0. -/
theorem leakAdv_advantage {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    |(μ {ω : Ω | gameD true () () (fun _ => ()) leakAdv 0 [] = true}).toReal -
        (μ {ω : Ω | gameD false () () (fun _ => ()) leakAdv 0 [] = true}).toReal| = 1 ∧
      |(μ {ω : Ω | gameCPA true () (fun _ => ())
            (reduction (fun (_ : Unit) _ => leakAdv) () ()) 0 = true}).toReal -
        (μ {ω : Ω | gameCPA false () (fun _ => ())
            (reduction (fun (_ : Unit) _ => leakAdv) () ()) 0 = true}).toReal| = 0 := sorry

/-! ## 6. Measurability for discrete samplers -/

/-- **The IND-CPA-D event is measurable for a discrete sampler**: the keys, the coins and the
first `q` encryption samples are functions of one measurable map `f` into a countable space with
measurable singletons, and the adversary makes at most `q` encryption queries. Nothing is assumed
of the key, randomness or coin types. -/
theorem gameD_measurableSet (S : HEScheme) [DecidableEq S.M] {Ω X Coins : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (pk' : X → S.PK) (sk' : X → S.SK) (tape' : X → ℕ → S.ER) (coins' : X → Coins)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hsk : ∀ ω, sk ω = sk' (f ω))
    (hcoins : ∀ ω, coins ω = coins' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i)
    (A : Coins → S.PK → Adv S Bool) (b : Bool) (hq : ∀ r p, Bounded (A r p) q) :
    MeasurableSet {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} := sorry

/-- **The IND-CPA event of the reduction is measurable for a discrete sampler**, under the same
hypotheses. -/
theorem gameCPA_reduction_measurableSet (S : HEScheme) [DecidableEq S.M] {Ω X Coins : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → S.PK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (pk' : X → S.PK) (tape' : X → ℕ → S.ER) (coins' : X → Coins)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hcoins : ∀ ω, coins ω = coins' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i)
    (A : Coins → S.PK → Adv S Bool) (b : Bool) (hq : ∀ r p, Bounded (A r p) q) :
    MeasurableSet {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} :=
  sorry

/-- **The bad event is measurable for a discrete sampler.** -/
theorem bad_measurableSet (S : HEScheme) {Ω X : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER)
    (pk' : X → S.PK) (sk' : X → S.SK) (tape' : X → ℕ → S.ER)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hsk : ∀ ω, sk ω = sk' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i) :
    MeasurableSet {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))} :=
  sorry

/-! ## 7. The game with evaluation on earlier results stays in `Reach` -/

/-- **Naming a fresh entry keeps the global program reachable.** -/
theorem reach_link (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (G : Global D) (x : Var) (hG : Reach mk adm G) :
    Reach mk adm (G.link x) := sorry

/-- **An accepted evaluation query keeps the global program reachable.** -/
theorem reach_evalLM (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D)) (pk : D.PK)
    (T : List (LEntry D)) (G : Global D) (C : QCirc D) (idx : List ℕ)
    (outs : List (CT D)) (new : List (LEntry D)) (G' : Global D) (hG : Reach mk adm G)
    (h : evalLM mk adm ev pk T G C idx = some (outs, new, G')) : Reach mk adm G' := sorry

/-! ## 8. Correctness is necessary -/

/-- **Perfect simulation for every adversary forces correctness** (module docstring, 8). -/
theorem correct_of_sim (S : HEScheme) [DecidableEq S.M] [Nonempty S.ER]
    (hsim : ∀ (b : Bool) (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) (A : Adv S Bool),
      S.KeysOK pk sk → TapeOK pk sk tape A 0 →
        gameD b pk sk tape A 0 [] = gameCPA b pk tape (reduce pk A []) 0) :
    (∀ pk sk, S.KeysOK pk sk → ∀ m er, S.GoodE pk sk er → S.dec sk (S.enc pk m er) = m) ∧
    (∀ pk sk, S.KeysOK pk sk → ∀ C, S.admissible C = true →
      ∀ ins : List (S.M × S.ER), (∀ p ∈ ins, S.GoodE pk sk p.2) →
        ∀ (j : ℕ) (o : S.CT) (s : S.M),
          (S.eval pk C (ins.map fun p => S.enc pk p.1 p.2))[j]? = some o →
          (S.sem C (ins.map Prod.fst))[j]? = some s → S.dec sk o = s) := sorry

/-- **The perfect simulation for every adversary is equivalent to correctness at every position**
(module docstring, 8). -/
theorem sim_iff (S : HEScheme) [DecidableEq S.M] [Nonempty S.ER] :
    (∀ (b : Bool) (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) (A : Adv S Bool),
      S.KeysOK pk sk → TapeOK pk sk tape A 0 →
        gameD b pk sk tape A 0 [] = gameCPA b pk tape (reduce pk A []) 0) ↔
    ((∀ pk sk, S.KeysOK pk sk → ∀ m er, S.GoodE pk sk er → S.dec sk (S.enc pk m er) = m) ∧
    (∀ pk sk, S.KeysOK pk sk → ∀ C, S.admissible C = true →
      ∀ ins : List (S.M × S.ER), (∀ p ∈ ins, S.GoodE pk sk p.2) →
        ∀ (j : ℕ) (o : S.CT) (s : S.M),
          (S.eval pk C (ins.map fun p => S.enc pk p.1 p.2))[j]? = some o →
          (S.sem C (ins.map Prod.fst))[j]? = some s → S.dec sk o = s)) := sorry

/-! ## 9. Symmetry for `gameLM`; equal pairs -/

/-- **Evaluation on earlier results: exchanging the messages of every encryption query flips
the bit.** -/
theorem gameLM_swap (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (b : Bool) (pk : D.PK) (sk : D.SK)
    (tape : ℕ → D.ER) (A : LAdv D Bool) :
    gameLM mk adm ev dec b pk sk tape A.swap 0 [] (Global.empty D) =
      gameLM mk adm ev dec (!b) pk sk tape A 0 [] (Global.empty D) := sorry

/-- **An adversary with equal messages in every encryption query has no advantage**: the
fresh-only game returns the same bit for both challenge bits. -/
theorem gameD_pairs_equal (S : HEScheme) [DecidableEq S.M] (pk : S.PK) (sk : S.SK)
    (tape : ℕ → S.ER) (A : Adv S Bool) (hA : A.swap = A) :
    gameD true pk sk tape A 0 [] = gameD false pk sk tape A 0 [] := sorry

/-- **The same for the game with evaluation on earlier results.** -/
theorem gameLM_pairs_equal (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (pk : D.PK) (sk : D.SK)
    (tape : ℕ → D.ER) (A : LAdv D Bool) (hA : A.swap = A) :
    gameLM mk adm ev dec true pk sk tape A 0 [] (Global.empty D) =
      gameLM mk adm ev dec false pk sk tape A 0 [] (Global.empty D) := sorry

/-! ## 10. Measurability, evaluation on earlier results -/

/-- **The event of the game with evaluation on earlier results is measurable for a discrete
sampler** (hypotheses as `gameD_measurableSet`). -/
theorem gameLM_measurableSet (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] {Ω X Coins : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (pk' : X → D.PK) (sk' : X → D.SK) (tape' : X → ℕ → D.ER) (coins' : X → Coins)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hsk : ∀ ω, sk ω = sk' (f ω))
    (hcoins : ∀ ω, coins ω = coins' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool) (hq : ∀ r p, BoundedLM (A r p) q) :
    MeasurableSet {ω | gameLM mk adm ev dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
      (Global.empty D) = true} := sorry

/-- **The IND-CPA event of the reduction from the game with evaluation on earlier results is
measurable for a discrete sampler** (hypotheses as `gameCPA_reduction_measurableSet`). -/
theorem gameCPA_reductionLM_measurableSet (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] {Ω X Coins : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → D.PK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (pk' : X → D.PK) (tape' : X → ℕ → D.ER) (coins' : X → Coins)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hcoins : ∀ ω, coins ω = coins' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool) (hq : ∀ r p, BoundedLM (A r p) q) :
    MeasurableSet {ω | gameCPA (S := freshScheme D adm ev dec) b (pk ω) (tape ω)
      (reductionLM mk adm ev dec A (coins ω) (pk ω)) 0 = true} := sorry

end Challenge.IndCpaDSanity
