import Challenge.IndCpaD.Sanity
import Validation.IndCpaD.Abstract

/-!
# Validation.IndCpaD.Sanity — proofs of `Challenge.IndCpaD.Sanity`

Inductions on the adversary trees (`Bounded`, `CpaBounded`, `BoundedLM`, or the tree itself) with
the table and counter generalised; the measurability statements factor the events through the
finitely many samples a bounded adversary reads (`gameD_tape_local`). The toy schemes are closed
computations (`rfl` after a case split on the bit).
-/

namespace Validation.IndCpaDSanity
open Spec Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM MeasureTheory
open Challenge.IndCpaDSanity

/-! ## 1. Query counts -/

theorem reduce_cpaBounded_aux {S : HEScheme} [DecidableEq S.M] (pk : S.PK) :
    ∀ {A : Adv S Bool} {q : ℕ}, Bounded A q → ∀ T, CpaBounded (reduce pk A T) q := by
  intro A q hq
  induction hq with
  | ret a q => intro T; exact CpaBounded.ret a q
  | enc m0 m1 k q _ ih => intro T; exact CpaBounded.lr _ _ _ _ fun c => ih c _
  | eval C idx k q _ ih =>
    intro T
    simp only [reduce]
    split
    · exact ih _ _
    · exact ih _ _
  | dec j k q _ ih => intro T; exact ih _ _

theorem reduce_cpaBounded (S : HEScheme) [DecidableEq S.M] (pk : S.PK) (A : Adv S Bool)
    (T : List (Entry S)) (q : ℕ) (hq : Bounded A q) : CpaBounded (reduce pk A T) q :=
  reduce_cpaBounded_aux pk hq T

theorem reduction_cpaBounded (S : HEScheme) [DecidableEq S.M] {Coins : Type}
    (A : Coins → S.PK → Adv S Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) (r : Coins)
    (pk : S.PK) : CpaBounded (reduction A r pk) q :=
  reduce_cpaBounded_aux pk (hq r pk) []

theorem reduceLM_cpaBounded_aux (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (pk : D.PK) :
    ∀ {A : LAdv D Bool} {q : ℕ}, BoundedLM A q → ∀ T G,
      CpaBounded (S := freshScheme D adm ev dec) (reduceLM mk adm ev dec pk A T G) q := by
  intro A q hq
  induction hq with
  | ret a q => intro T G; exact CpaBounded.ret a q
  | enc m0 m1 x k q _ ih => intro T G; exact CpaBounded.lr _ _ _ _ fun c => ih c _ _
  | eval C idx k q _ ih =>
    intro T G
    simp only [reduceLM]
    split
    · exact ih _ _ _
    · exact ih _ _ _
  | dec j k q _ ih => intro T G; exact ih _ _ _

theorem reduceLM_cpaBounded (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (pk : D.PK) (A : LAdv D Bool)
    (T : List (LEntry D)) (G : Global D) (q : ℕ) (hq : BoundedLM A q) :
    CpaBounded (S := freshScheme D adm ev dec) (reduceLM mk adm ev dec pk A T G) q :=
  reduceLM_cpaBounded_aux D mk adm ev dec pk hq T G

/-! ## 2. Tape locality -/

theorem gameD_local {S : HEScheme} [DecidableEq S.M] (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape tape' : ℕ → S.ER) :
    ∀ {A : Adv S Bool} {q : ℕ}, Bounded A q → ∀ n T,
      (∀ i, n ≤ i → i < n + q → tape i = tape' i) →
      gameD b pk sk tape A n T = gameD b pk sk tape' A n T := by
  intro A q hq
  induction hq with
  | ret a q => intro n T _; rfl
  | enc m0 m1 k q _ ih =>
    intro n T h
    simp only [gameD]
    rw [h n le_rfl (by omega)]
    exact ih _ _ _ fun i h1 h2 => h i (by omega) (by omega)
  | eval C idx k q _ ih =>
    intro n T h
    simp only [gameD]
    split
    · exact ih _ _ _ h
    · exact ih _ _ _ h
  | dec j k q _ ih =>
    intro n T h
    simp only [gameD]
    exact ih _ _ _ h

theorem gameD_tape_local (S : HEScheme) [DecidableEq S.M] (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape tape' : ℕ → S.ER) (A : Adv S Bool) (q : ℕ) (hq : Bounded A q)
    (h : ∀ i < q, tape i = tape' i) :
    gameD b pk sk tape A 0 [] = gameD b pk sk tape' A 0 [] :=
  gameD_local b pk sk tape tape' hq 0 [] fun i _ h2 => h i (by omega)

theorem gameCPA_local {S : HEScheme} (b : Bool) (pk : S.PK) (tape tape' : ℕ → S.ER) :
    ∀ {B : CpaAdv S Bool} {q : ℕ}, CpaBounded B q → ∀ n,
      (∀ i, n ≤ i → i < n + q → tape i = tape' i) →
      gameCPA b pk tape B n = gameCPA b pk tape' B n := by
  intro B q hq
  induction hq with
  | ret a q => intro n _; rfl
  | lr m0 m1 k q _ ih =>
    intro n h
    simp only [gameCPA]
    rw [h n le_rfl (by omega)]
    exact ih _ _ fun i h1 h2 => h i (by omega) (by omega)

theorem gameCPA_tape_local (S : HEScheme) (b : Bool) (pk : S.PK) (tape tape' : ℕ → S.ER)
    (B : CpaAdv S Bool) (q : ℕ) (hq : CpaBounded B q) (h : ∀ i < q, tape i = tape' i) :
    gameCPA b pk tape B 0 = gameCPA b pk tape' B 0 :=
  gameCPA_local b pk tape tape' hq 0 fun i _ h2 => h i (by omega)

theorem gameLM_local (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (b : Bool) (pk : D.PK) (sk : D.SK)
    (tape tape' : ℕ → D.ER) :
    ∀ {A : LAdv D Bool} {q : ℕ}, BoundedLM A q → ∀ n T G,
      (∀ i, n ≤ i → i < n + q → tape i = tape' i) →
      gameLM mk adm ev dec b pk sk tape A n T G = gameLM mk adm ev dec b pk sk tape' A n T G := by
  intro A q hq
  induction hq with
  | ret a q => intro n T G _; rfl
  | enc m0 m1 x k q _ ih =>
    intro n T G h
    simp only [gameLM]
    rw [h n le_rfl (by omega)]
    exact ih _ _ _ _ fun i h1 h2 => h i (by omega) (by omega)
  | eval C idx k q _ ih =>
    intro n T G h
    simp only [gameLM]
    split
    · exact ih _ _ _ _ h
    · exact ih _ _ _ _ h
  | dec j k q _ ih =>
    intro n T G h
    simp only [gameLM]
    exact ih _ _ _ _ h

theorem gameLM_tape_local (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (b : Bool) (pk : D.PK) (sk : D.SK)
    (tape tape' : ℕ → D.ER) (A : LAdv D Bool) (q : ℕ) (hq : BoundedLM A q)
    (h : ∀ i < q, tape i = tape' i) :
    gameLM mk adm ev dec b pk sk tape A 0 [] (Global.empty D) =
      gameLM mk adm ev dec b pk sk tape' A 0 [] (Global.empty D) :=
  gameLM_local D mk adm ev dec b pk sk tape tape' hq 0 [] _ fun i _ h2 => h i (by omega)

/-! ## 3. Symmetry -/

theorem pick_swap {β : Type} (b : Bool) (x y : β) : pick b y x = pick (!b) x y := by
  cases b <;> rfl

theorem freshAt_swap {S : HEScheme} (T : List (Entry S)) (j : ℕ) :
    freshAt (T.map Entry.swap) j = (freshAt T j).map Entry.swap := by
  unfold freshAt
  rw [List.getElem?_map]
  cases T[j]? with
  | none => rfl
  | some e =>
    show (if e.fresh then some e.swap else none) = Option.map Entry.swap (if e.fresh then some e else none)
    cases e.fresh <;> rfl

theorem mapM_swap {S : HEScheme} (T : List (Entry S)) :
    ∀ idx : List ℕ, idx.mapM (freshAt (T.map Entry.swap)) =
      (idx.mapM (freshAt T)).map (List.map Entry.swap)
  | [] => rfl
  | j :: idx => by
    simp only [List.mapM_cons, freshAt_swap, mapM_swap T idx]
    cases freshAt T j <;> cases idx.mapM (freshAt T) <;> rfl

theorem zip_swap {S : HEScheme} :
    ∀ (outs : List S.CT) (s0 s1 : List S.M),
      ((outs.zip (s1.zip s0)).map fun p => (⟨p.2.1, p.2.2, p.1, false⟩ : Entry S)) =
        ((outs.zip (s0.zip s1)).map fun p => (⟨p.2.1, p.2.2, p.1, false⟩ : Entry S)).map
          Entry.swap
  | [], _, _ => rfl
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, [] => by simp
  | o :: os, x :: xs, y :: ys => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [zip_swap os xs ys]
    rfl

theorem evalStep_swap {S : HEScheme} (pk : S.PK) (T : List (Entry S)) (C : S.Circ)
    (idx : List ℕ) :
    evalStep pk (T.map Entry.swap) C idx =
      (evalStep pk T C idx).map fun p => (p.1, p.2.map Entry.swap) := by
  unfold evalStep
  cases S.admissible C with
  | false => rfl
  | true =>
    simp only [ite_true, mapM_swap]
    cases idx.mapM (freshAt T) with
    | none => rfl
    | some es =>
      simp only [Option.map_some, List.map_map]
      have h1 : (Entry.c ∘ Entry.swap : Entry S → S.CT) = Entry.c := rfl
      have h2 : (Entry.m0 ∘ Entry.swap : Entry S → S.M) = Entry.m1 := rfl
      have h3 : (Entry.m1 ∘ Entry.swap : Entry S → S.M) = Entry.m0 := rfl
      rw [h1, h2, h3, zip_swap]
      simp only [List.map_map]

theorem decAns_swap {S : HEScheme} [DecidableEq S.M] (sk : S.SK) (T : List (Entry S)) (j : ℕ) :
    decAns sk (T.map Entry.swap) j = decAns sk T j := by
  unfold decAns
  rw [List.getElem?_map]
  cases T[j]? with
  | none => rfl
  | some e =>
    show (if e.m1 = e.m0 then some (S.dec sk e.c) else none) =
      (if e.m0 = e.m1 then some (S.dec sk e.c) else none)
    by_cases h : e.m0 = e.m1
    · simp [h]
    · simp [h, Ne.symm h]

theorem simAns_swap {S : HEScheme} [DecidableEq S.M] (T : List (Entry S)) (j : ℕ) :
    simAns (T.map Entry.swap) j = simAns T j := by
  unfold simAns
  rw [List.getElem?_map]
  cases T[j]? with
  | none => rfl
  | some e =>
    show (if e.m1 = e.m0 then some e.m1 else none) = (if e.m0 = e.m1 then some e.m0 else none)
    by_cases h : e.m0 = e.m1
    · simp [h]
    · simp [h, Ne.symm h]

theorem gameD_swap_aux {S : HEScheme} [DecidableEq S.M] (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape : ℕ → S.ER) (A : Adv S Bool) : ∀ n T,
    gameD b pk sk tape A.swap n (T.map Entry.swap) = gameD (!b) pk sk tape A n T := by
  induction A with
  | ret a => intro n T; rfl
  | enc m0 m1 k ih =>
    intro n T
    simp only [Adv.swap, gameD]
    rw [pick_swap]
    have := ih (S.enc pk (pick (!b) m0 m1) (tape n)) (n + 1)
      (T ++ [⟨m0, m1, S.enc pk (pick (!b) m0 m1) (tape n), true⟩])
    rw [List.map_append] at this
    exact this
  | eval C idx k ih =>
    intro n T
    simp only [Adv.swap, gameD, evalStep_swap]
    cases evalStep pk T C idx with
    | none => exact ih none n T
    | some p =>
      have := ih (some p.1) n (T ++ p.2)
      rw [List.map_append] at this
      exact this
  | dec j k ih =>
    intro n T
    simp only [Adv.swap, gameD, decAns_swap]
    exact ih _ n T

theorem gameD_swap (S : HEScheme) [DecidableEq S.M] (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape : ℕ → S.ER) (A : Adv S Bool) :
    gameD b pk sk tape A.swap 0 [] = gameD (!b) pk sk tape A 0 [] :=
  gameD_swap_aux b pk sk tape A 0 []

theorem gameCPA_swap_aux {S : HEScheme} (b : Bool) (pk : S.PK) (tape : ℕ → S.ER)
    (B : CpaAdv S Bool) : ∀ n, gameCPA b pk tape B.swap n = gameCPA (!b) pk tape B n := by
  induction B with
  | ret a => intro n; rfl
  | lr m0 m1 k ih =>
    intro n
    simp only [CpaAdv.swap, gameCPA]
    rw [pick_swap]
    exact ih _ _

theorem gameCPA_swap (S : HEScheme) (b : Bool) (pk : S.PK) (tape : ℕ → S.ER)
    (B : CpaAdv S Bool) : gameCPA b pk tape B.swap 0 = gameCPA (!b) pk tape B 0 :=
  gameCPA_swap_aux b pk tape B 0

theorem reduce_swap_aux {S : HEScheme} [DecidableEq S.M] (pk : S.PK) (A : Adv S Bool) :
    ∀ T, reduce pk A.swap (T.map Entry.swap) = (reduce pk A T).swap := by
  induction A with
  | ret a => intro T; rfl
  | enc m0 m1 k ih =>
    intro T
    simp only [Adv.swap, reduce, CpaAdv.swap]
    congr 1
    funext c
    have := ih c (T ++ [⟨m0, m1, c, true⟩])
    rw [List.map_append] at this
    exact this
  | eval C idx k ih =>
    intro T
    simp only [Adv.swap, reduce, evalStep_swap]
    cases evalStep pk T C idx with
    | none => exact ih none T
    | some p =>
      have := ih (some p.1) (T ++ p.2)
      rw [List.map_append] at this
      exact this
  | dec j k ih =>
    intro T
    simp only [Adv.swap, reduce, simAns_swap]
    exact ih _ T

theorem reduce_swap (S : HEScheme) [DecidableEq S.M] (pk : S.PK) (A : Adv S Bool) :
    reduce pk A.swap [] = (reduce pk A []).swap :=
  reduce_swap_aux pk A []

/-! ## 4–5. Toy schemes -/

theorem idScheme_correct : Correct idScheme := by
  refine ⟨fun _ _ _ _ _ _ => rfl, ?_⟩
  intro pk sk _ C _ ins _
  show List.map (fun c : Bool => c) (List.map (fun p : Bool × Unit => p.1) ins) =
    List.map Prod.fst ins
  simp

theorem idCpaAdv_wins (b : Bool) (pk : Unit) (tape : ℕ → Unit) :
    gameCPA b pk tape idCpaAdv 0 = b := by
  cases b <;> rfl

theorem idAdv_wins (b : Bool) (pk sk : Unit) (tape : ℕ → Unit) :
    gameD b pk sk tape idAdv 0 [] = b ∧
      gameCPA b pk tape (reduction (fun (_ : Unit) _ => idAdv) () pk) 0 = b := by
  cases b <;> exact ⟨rfl, rfl⟩

theorem leakScheme_fresh : ∀ pk sk, leakScheme.KeysOK pk sk → ∀ m er, leakScheme.GoodE pk sk er →
    leakScheme.dec sk (leakScheme.enc pk m er) = m :=
  fun _ _ _ _ _ _ => rfl

theorem leakScheme_not_correct : ¬ Correct leakScheme := by
  intro h
  have h1 := h.eval () () trivial () rfl [(true, ())] (fun _ _ => trivial)
  have h2 : ([true] : List Bool) = [false] := h1
  cases h2

theorem leakAdv_wins (b : Bool) (pk sk : Unit) (tape : ℕ → Unit) :
    TapeOK pk sk tape leakAdv 0 ∧ gameD b pk sk tape leakAdv 0 [] = b := by
  refine ⟨⟨trivial, fun _ _ _ => trivial⟩, ?_⟩
  cases b <;> rfl

theorem leakAdv_reduction_loses (b : Bool) (pk : Unit) (tape : ℕ → Unit) :
    gameCPA b pk tape (reduction (fun (_ : Unit) _ => leakAdv) () pk) 0 = false := by
  cases b <;> rfl

theorem leakAdv_advantage {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    |(μ {ω : Ω | gameD true () () (fun _ => ()) leakAdv 0 [] = true}).toReal -
        (μ {ω : Ω | gameD false () () (fun _ => ()) leakAdv 0 [] = true}).toReal| = 1 ∧
      |(μ {ω : Ω | gameCPA true () (fun _ => ())
            (reduction (fun (_ : Unit) _ => leakAdv) () ()) 0 = true}).toReal -
        (μ {ω : Ω | gameCPA false () (fun _ => ())
            (reduction (fun (_ : Unit) _ => leakAdv) () ()) 0 = true}).toReal| = 0 := by
  have h1 : {ω : Ω | gameD true () () (fun _ => ()) leakAdv 0 [] = true} = Set.univ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact (leakAdv_wins true () () _).2
  have h2 : {ω : Ω | gameD false () () (fun _ => ()) leakAdv 0 [] = true} = ∅ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [(leakAdv_wins false () () _).2]; decide
  have h3 : ∀ b, {ω : Ω | gameCPA b () (fun _ => ())
      (reduction (fun (_ : Unit) _ => leakAdv) () ()) 0 = true} = ∅ := by
    intro b
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [leakAdv_reduction_loses b () _]; decide
  rw [h1, h2, h3, h3]
  simp

/-! ## 6. Measurability -/

theorem countable_measurableSet {α : Type} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (s : Set α) : MeasurableSet s :=
  (Set.to_countable s).measurableSet

theorem gameD_measurableSet (S : HEScheme) [DecidableEq S.M] {Ω X Coins : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (pk' : X → S.PK) (sk' : X → S.SK) (tape' : X → ℕ → S.ER) (coins' : X → Coins)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hsk : ∀ ω, sk ω = sk' (f ω))
    (hcoins : ∀ ω, coins ω = coins' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i)
    (A : Coins → S.PK → Adv S Bool) (b : Bool) (hq : ∀ r p, Bounded (A r p) q) :
    MeasurableSet {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} := by
  have hset : {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
      f ⁻¹' {x | gameD b (pk' x) (sk' x) (tape' x) (A (coins' x) (pk' x)) 0 [] = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hpk, hsk, hcoins]
    rw [gameD_tape_local S b _ _ (tape ω) (tape' (f ω)) _ q (hq _ _) (htape ω)]
  rw [hset]
  exact hf (countable_measurableSet _)

theorem gameCPA_reduction_measurableSet (S : HEScheme) [DecidableEq S.M] {Ω X Coins : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → S.PK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (pk' : X → S.PK) (tape' : X → ℕ → S.ER) (coins' : X → Coins)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hcoins : ∀ ω, coins ω = coins' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i)
    (A : Coins → S.PK → Adv S Bool) (b : Bool) (hq : ∀ r p, Bounded (A r p) q) :
    MeasurableSet {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} := by
  have hset : {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} =
      f ⁻¹' {x | gameCPA b (pk' x) (tape' x) (reduction A (coins' x) (pk' x)) 0 = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hpk, hcoins]
    rw [gameCPA_tape_local S b _ (tape ω) (tape' (f ω)) _ q
      (reduction_cpaBounded S A q hq _ _) (htape ω)]
  rw [hset]
  exact hf (countable_measurableSet _)

theorem bad_measurableSet (S : HEScheme) {Ω X : Type}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (f : Ω → X) (hf : Measurable f)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER)
    (pk' : X → S.PK) (sk' : X → S.SK) (tape' : X → ℕ → S.ER)
    (hpk : ∀ ω, pk ω = pk' (f ω)) (hsk : ∀ ω, sk ω = sk' (f ω)) (q : ℕ)
    (htape : ∀ ω, ∀ i < q, tape ω i = tape' (f ω) i) :
    MeasurableSet {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))} := by
  have hset : {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))} =
      f ⁻¹' {x | ¬ (S.KeysOK (pk' x) (sk' x) ∧ ∀ i < q, S.GoodE (pk' x) (sk' x) (tape' x i))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hpk, hsk]
    constructor
    · intro h h'
      exact h ⟨h'.1, fun i hi => by rw [htape ω i hi]; exact h'.2 i hi⟩
    · intro h h'
      exact h ⟨h'.1, fun i hi => by rw [← htape ω i hi]; exact h'.2 i hi⟩
  rw [hset]
  exact hf (countable_measurableSet _)

/-! ## 7. `Reach` -/

theorem reach_link (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (G : Global D) (x : Var) (hG : Reach mk adm G) :
    Reach mk adm (G.link x) :=
  Reach.link G x hG

theorem reach_evalLM (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D)) (pk : D.PK)
    (T : List (LEntry D)) (G : Global D) (C : QCirc D) (idx : List ℕ)
    (outs : List (CT D)) (new : List (LEntry D)) (G' : Global D) (hG : Reach mk adm G)
    (h : evalLM mk adm ev pk T G C idx = some (outs, new, G')) : Reach mk adm G' := by
  unfold evalLM at h
  split at h
  · rename_i es _
    split at h
    · rename_i hadm
      cases h
      exact Reach.extend G C _ hG hadm
    · cases h
  · cases h


/-! ## 8. Correctness is necessary -/

section Nec
variable {S : HEScheme}

/-- Encrypt the messages of `ins` in order, each as the pair `(m, m)`. -/
def encAll : List (S.M × S.ER) → (List S.CT → Adv S Bool) → Adv S Bool
  | [], k => k []
  | p :: ps, k => .enc p.1 p.1 fun c => encAll ps fun cs => k (c :: cs)

/-- The fresh ciphertexts of `ins`. -/
def encsOf (pk : S.PK) (ins : List (S.M × S.ER)) : List S.CT := ins.map fun p => S.enc pk p.1 p.2

/-- The table entries of `ins`. -/
def entriesOf (pk : S.PK) (ins : List (S.M × S.ER)) : List (Entry S) :=
  ins.map fun p => ⟨p.1, p.1, S.enc pk p.1 p.2, true⟩

theorem pick_same {β : Type} (b : Bool) (x : β) : pick b x x = x := by cases b <;> rfl

theorem tape_shift {E : Type} {tape : ℕ → E} {n : ℕ} {p : S.M × E} {ps : List (S.M × E)}
    (h : ∀ i (hi : i < (p :: ps).length), tape (n + i) = ((p :: ps)[i]'hi).2) :
    tape n = p.2 ∧ ∀ i (hi : i < ps.length), tape (n + 1 + i) = (ps[i]'hi).2 := by
  refine ⟨h 0 (by simp), fun i hi => ?_⟩
  have := h (i + 1) (by simp; omega)
  rw [show n + 1 + i = n + (i + 1) by omega]
  simpa using this

theorem gameD_encAll [DecidableEq S.M] (b : Bool) (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) :
    ∀ (ins : List (S.M × S.ER)) (k : List S.CT → Adv S Bool) (n : ℕ) (T : List (Entry S)),
      (∀ i (hi : i < ins.length), tape (n + i) = (ins[i]'hi).2) →
      gameD b pk sk tape (encAll ins k) n T =
        gameD b pk sk tape (k (encsOf pk ins)) (n + ins.length) (T ++ entriesOf pk ins)
  | [], k, n, T, _ => by simp [encAll, encsOf, entriesOf]
  | p :: ps, k, n, T, h => by
    obtain ⟨h0, hs⟩ := tape_shift h
    simp only [encAll, gameD]
    rw [pick_same, h0, gameD_encAll b pk sk tape ps _ (n + 1) _ hs]
    simp only [encsOf, entriesOf, List.map_cons, List.length_cons, List.append_assoc,
      List.singleton_append]
    rw [show n + 1 + ps.length = n + (ps.length + 1) by omega]

theorem cpa_encAll [DecidableEq S.M] (b : Bool) (pk : S.PK) (tape : ℕ → S.ER) :
    ∀ (ins : List (S.M × S.ER)) (k : List S.CT → Adv S Bool) (n : ℕ) (T : List (Entry S)),
      (∀ i (hi : i < ins.length), tape (n + i) = (ins[i]'hi).2) →
      gameCPA b pk tape (reduce pk (encAll ins k) T) n =
        gameCPA b pk tape (reduce pk (k (encsOf pk ins)) (T ++ entriesOf pk ins)) (n + ins.length)
  | [], k, n, T, _ => by simp [encAll, encsOf, entriesOf]
  | p :: ps, k, n, T, h => by
    obtain ⟨h0, hs⟩ := tape_shift h
    simp only [encAll, reduce, gameCPA]
    rw [pick_same, h0, cpa_encAll b pk tape ps _ (n + 1) _ hs]
    simp only [encsOf, entriesOf, List.map_cons, List.length_cons, List.append_assoc,
      List.singleton_append]
    rw [show n + 1 + ps.length = n + (ps.length + 1) by omega]

theorem tapeOK_encAll (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) :
    ∀ (ins : List (S.M × S.ER)) (k : List S.CT → Adv S Bool) (n : ℕ),
      (∀ i (hi : i < ins.length), S.GoodE pk sk (tape (n + i))) →
      (∀ cs m, TapeOK pk sk tape (k cs) m) → TapeOK pk sk tape (encAll ins k) n
  | [], k, n, _, hk => hk [] n
  | p :: ps, k, n, h, hk => by
    refine ⟨by simpa using h 0 (by simp), fun c => tapeOK_encAll pk sk tape ps _ (n + 1) ?_
      (fun cs m => hk _ m)⟩
    intro i hi
    have := h (i + 1) (by simp; omega)
    rwa [show n + (i + 1) = n + 1 + i by omega] at this

theorem mapM_fresh : ∀ (T pre : List (Entry S)), (∀ e ∈ T, e.fresh = true) →
    (List.range' pre.length T.length).mapM (freshAt (pre ++ T)) = some T
  | [], _, _ => rfl
  | e :: T, pre, h => by
    have h1 : freshAt (pre ++ e :: T) pre.length = some e := by
      unfold freshAt
      simp [h e (by simp)]
    have h2 := mapM_fresh T (pre ++ [e]) (fun e' he' => h e' (by simp [he']))
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] at h2
    simp only [List.length_cons, List.range'_succ, List.mapM_cons, h1, h2]
    rfl

theorem new_get (outs : List S.CT) (ss : List S.M) (j : ℕ) (o : S.CT) (s : S.M)
    (ho : outs[j]? = some o) (hs : ss[j]? = some s) :
    ((outs.zip (ss.zip ss)).map fun p => (⟨p.2.1, p.2.2, p.1, false⟩ : Entry S))[j]? =
      some ⟨s, s, o, false⟩ := by
  rw [List.getElem?_map]
  have : (outs.zip (ss.zip ss))[j]? = some (o, (s, s)) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨ho, by rw [List.getElem?_zip_eq_some]; exact ⟨hs, hs⟩⟩
  rw [this]
  rfl

end Nec

theorem correct_of_sim (S : HEScheme) [DecidableEq S.M] [Nonempty S.ER]
    (hsim : ∀ (b : Bool) (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) (A : Adv S Bool),
      S.KeysOK pk sk → TapeOK pk sk tape A 0 →
        gameD b pk sk tape A 0 [] = gameCPA b pk tape (reduce pk A []) 0) :
    (∀ pk sk, S.KeysOK pk sk → ∀ m er, S.GoodE pk sk er → S.dec sk (S.enc pk m er) = m) ∧
    (∀ pk sk, S.KeysOK pk sk → ∀ C, S.admissible C = true →
      ∀ ins : List (S.M × S.ER), (∀ p ∈ ins, S.GoodE pk sk p.2) →
        ∀ (j : ℕ) (o : S.CT) (s : S.M),
          (S.eval pk C (ins.map fun p => S.enc pk p.1 p.2))[j]? = some o →
          (S.sem C (ins.map Prod.fst))[j]? = some s → S.dec sk o = s) := by
  obtain ⟨er0⟩ := ‹Nonempty S.ER›
  constructor
  · intro pk sk hk m er hg
    have h := hsim false pk sk (fun _ => er)
      (.enc m m fun _ => .dec 0 fun r => .ret (decide (r = some m))) hk ⟨hg, fun _ _ => trivial⟩
    simpa [gameD, gameCPA, reduce, decAns, simAns, pick] using h
  · intro pk sk hk C hadm ins hg j o s ho hs
    let n := ins.length
    let A : Adv S Bool := encAll ins fun _ =>
      .eval C (List.range' 0 n) fun _ => .dec (n + j) fun r => .ret (decide (r = some s))
    let tape : ℕ → S.ER := fun i => (ins[i]?.map Prod.snd).getD er0
    have htape : ∀ i (hi : i < ins.length), tape (0 + i) = (ins[i]'hi).2 := by
      intro i hi
      simp [tape, hi]
    have hT : TapeOK pk sk tape A 0 :=
      tapeOK_encAll pk sk tape ins _ 0
        (fun i hi => by rw [htape i hi]; exact hg _ (List.getElem_mem hi))
        (fun _ _ => fun _ => fun _ => trivial)
    have h := hsim false pk sk tape A hk hT
    simp only [A] at h
    rw [gameD_encAll false pk sk tape ins _ 0 [] htape,
      cpa_encAll false pk tape ins _ 0 [] htape] at h
    have hlen : (entriesOf pk ins).length = n := by simp [entriesOf, n]
    have hm : (List.range' 0 n).mapM (freshAt ([] ++ entriesOf pk ins)) =
        some (entriesOf pk ins) := by
      have := mapM_fresh (entriesOf pk ins) [] (by
        intro e he
        simp only [entriesOf, List.mem_map] at he
        obtain ⟨p, _, rfl⟩ := he
        rfl)
      rw [hlen] at this
      exact this
    have hc : (entriesOf pk ins).map (·.c) = ins.map fun p => S.enc pk p.1 p.2 := by
      simp [entriesOf]
    have hm0 : (entriesOf pk ins).map (·.m0) = ins.map Prod.fst := by simp [entriesOf]
    have hm1 : (entriesOf pk ins).map (·.m1) = ins.map Prod.fst := by simp [entriesOf]
    have hev : evalStep pk ([] ++ entriesOf pk ins) C (List.range' 0 n) =
        some (S.eval pk C (ins.map fun p => S.enc pk p.1 p.2),
          ((S.eval pk C (ins.map fun p => S.enc pk p.1 p.2)).zip
            ((S.sem C (ins.map Prod.fst)).zip (S.sem C (ins.map Prod.fst)))).map
              fun p => (⟨p.2.1, p.2.2, p.1, false⟩ : Entry S)) := by
      unfold evalStep
      rw [hadm, hm]
      simp only [ite_true, hc, hm0, hm1]
    have hget : ([] ++ entriesOf pk ins ++
        ((S.eval pk C (ins.map fun p => S.enc pk p.1 p.2)).zip
            ((S.sem C (ins.map Prod.fst)).zip (S.sem C (ins.map Prod.fst)))).map
              fun p => (⟨p.2.1, p.2.2, p.1, false⟩ : Entry S))[n + j]? = some ⟨s, s, o, false⟩ := by
      rw [List.getElem?_append_right (by simp [hlen])]
      simp only [List.nil_append, hlen, Nat.add_sub_cancel_left]
      exact new_get _ _ j o s ho hs
    simp only [gameD, reduce, gameCPA, hev, Nat.zero_add] at h
    unfold decAns simAns at h
    rw [hget] at h
    simpa using h

/-! ## 8b. Sufficiency of positionwise correctness -/

section Suff
variable {S : HEScheme}

/-- Positionwise correctness (the right-hand side of `sim_iff`). -/
def PosCorrect (S : HEScheme) : Prop :=
  (∀ pk sk, S.KeysOK pk sk → ∀ m er, S.GoodE pk sk er → S.dec sk (S.enc pk m er) = m) ∧
  (∀ pk sk, S.KeysOK pk sk → ∀ C, S.admissible C = true →
    ∀ ins : List (S.M × S.ER), (∀ p ∈ ins, S.GoodE pk sk p.2) →
      ∀ (j : ℕ) (o : S.CT) (s : S.M),
        (S.eval pk C (ins.map fun p => S.enc pk p.1 p.2))[j]? = some o →
        (S.sem C (ins.map Prod.fst))[j]? = some s → S.dec sk o = s)

theorem mem_zip_index {α β : Type} {xs : List α} {ys : List β} {p : α × β}
    (h : p ∈ xs.zip ys) : ∃ j : ℕ, xs[j]? = some p.1 ∧ ys[j]? = some p.2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  exact ⟨j, List.getElem?_zip_eq_some.mp hj⟩

theorem evalStep_inv_pos (hC : PosCorrect S) {b : Bool} {pk : S.PK} {sk : S.SK}
    (hk : S.KeysOK pk sk) {T : List (Entry S)} (hT : Validation.IndCpaD.Inv b pk sk T)
    {C : S.Circ} {idx : List ℕ} {outs : List S.CT} {new : List (Entry S)}
    (h : evalStep pk T C idx = some (outs, new)) :
    Validation.IndCpaD.Inv b pk sk (T ++ new) := by
  unfold evalStep at h
  split at h
  · rename_i hadm
    split at h
    · rename_i es hes
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hout, hnew⟩ := h
      have hfr : ∀ e ∈ es, e ∈ T ∧ e.fresh = true := fun e he => by
        obtain ⟨j, hj⟩ := Validation.IndCpaD.mapM_mem hes e he
        exact Validation.IndCpaD.freshAt_mem hj
      obtain ⟨ins, hg, hcs, hms⟩ := Validation.IndCpaD.choose_ins b pk sk es fun e he =>
        (hT e (hfr e he).1).1 (hfr e he).2
      have hdec := hC.2 pk sk hk C hadm ins hg
      rw [hcs, hms, Validation.IndCpaD.sem_pick] at hdec
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hT e he
      · rw [← hnew] at he
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
        refine ⟨fun h => absurd h (by simp), ?_⟩
        obtain ⟨h0, h1⟩ := Validation.IndCpaD.zip3_proj _ _ _ p hp
        cases b
        · obtain ⟨j, hj1, hj2⟩ := mem_zip_index h0
          exact hdec j _ _ hj1 hj2
        · obtain ⟨j, hj1, hj2⟩ := mem_zip_index h1
          exact hdec j _ _ hj1 hj2
    · cases h
  · cases h

theorem sim_pos [DecidableEq S.M] (hC : PosCorrect S) (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape : ℕ → S.ER) (hk : S.KeysOK pk sk) :
    ∀ (A : Adv S Bool) (n : ℕ) (T : List (Entry S)), Validation.IndCpaD.Inv b pk sk T →
      TapeOK pk sk tape A n → gameD b pk sk tape A n T = gameCPA b pk tape (reduce pk A T) n
  | .ret a, n, T, _, _ => rfl
  | .enc m0 m1 k, n, T, hT, ht => by
    simp only [gameD, reduce, gameCPA]
    refine sim_pos hC b pk sk tape hk (k _) (n + 1) _ ?_ (ht.2 _)
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hT e he
    · simp only [List.mem_singleton] at he
      subst he
      exact ⟨fun _ => ⟨tape n, ht.1, rfl⟩, hC.1 pk sk hk _ _ ht.1⟩
  | .eval C idx k, n, T, hT, ht => by
    simp only [gameD, reduce]
    cases h : evalStep pk T C idx with
    | none => exact sim_pos hC b pk sk tape hk (k none) n T hT (ht _)
    | some r =>
      obtain ⟨outs, new⟩ := r
      exact sim_pos hC b pk sk tape hk (k (some outs)) n _ (evalStep_inv_pos hC hk hT h) (ht _)
  | .dec j k, n, T, hT, ht => by
    simp only [gameD, reduce]
    rw [Validation.IndCpaD.decAns_eq hT j]
    exact sim_pos hC b pk sk tape hk (k _) n T hT (ht _)

end Suff

theorem sim_iff (S : HEScheme) [DecidableEq S.M] [Nonempty S.ER] :
    (∀ (b : Bool) (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) (A : Adv S Bool),
      S.KeysOK pk sk → TapeOK pk sk tape A 0 →
        gameD b pk sk tape A 0 [] = gameCPA b pk tape (reduce pk A []) 0) ↔
    ((∀ pk sk, S.KeysOK pk sk → ∀ m er, S.GoodE pk sk er → S.dec sk (S.enc pk m er) = m) ∧
    (∀ pk sk, S.KeysOK pk sk → ∀ C, S.admissible C = true →
      ∀ ins : List (S.M × S.ER), (∀ p ∈ ins, S.GoodE pk sk p.2) →
        ∀ (j : ℕ) (o : S.CT) (s : S.M),
          (S.eval pk C (ins.map fun p => S.enc pk p.1 p.2))[j]? = some o →
          (S.sem C (ins.map Prod.fst))[j]? = some s → S.dec sk o = s)) := by
  constructor
  · exact correct_of_sim S
  · intro hC b pk sk tape A hk ht
    exact sim_pos hC b pk sk tape hk A 0 [] (by intro e he; simp at he) ht

/-! ## 9. Symmetry for `gameLM`; equal pairs -/

section LMSwap
variable {D : AbsScheme}

theorem mapM_map_opt {α β γ : Type} (g : α → Option β) (h : β → γ) :
    ∀ l : List α, (l.mapM fun a => (g a).map h) = (l.mapM g).map (List.map h)
  | [] => rfl
  | a :: l => by
    simp only [List.mapM_cons, mapM_map_opt g h l]
    cases g a <;> cases l.mapM g <;> rfl

theorem mapM_get_swap (T : List (LEntry D)) (idx : List ℕ) :
    (idx.mapM fun j => (T.map LEntry.swap)[j]?) =
      (idx.mapM fun j => T[j]?).map (List.map LEntry.swap) := by
  simp only [List.getElem?_map]
  exact mapM_map_opt (fun j => T[j]?) LEntry.swap idx

theorem zip_swapLM :
    ∀ (outs : List (CT D)) (os : List Var) (s0 s1 : List (M D)),
      ((outs.zip (os.zip (s1.zip s0))).map
          fun p => (⟨p.2.2.1, p.2.2.2, p.1, p.2.1, true⟩ : LEntry D)) =
        ((outs.zip (os.zip (s0.zip s1))).map
          fun p => (⟨p.2.2.1, p.2.2.2, p.1, p.2.1, true⟩ : LEntry D)).map LEntry.swap
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => by simp
  | _ :: _, _ :: _, [], _ => by simp
  | _ :: _, _ :: _, _ :: _, [] => by simp
  | o :: os', x :: xs, y :: ys, z :: zs => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [zip_swapLM os' xs ys zs]
    rfl

theorem evalLM_swap (mk : Program → List Var → (Var → M D) → D.Circ) (adm : D.Circ → Bool)
    (ev : D.PK → D.Circ → List (CT D) → List (CT D)) (pk : D.PK) (T : List (LEntry D))
    (G : Global D) (C : QCirc D) (idx : List ℕ) :
    evalLM mk adm ev pk (T.map LEntry.swap) G C idx =
      (evalLM mk adm ev pk T G C idx).map fun p => (p.1, p.2.1.map LEntry.swap, p.2.2) := by
  unfold evalLM
  rw [mapM_get_swap]
  cases idx.mapM (fun j => T[j]?) with
  | none => rfl
  | some es =>
    simp only [Option.map_some, List.map_map]
    have h0 : ((fun e : LEntry D => (e.name, e.linked)) ∘ LEntry.swap) =
        fun e : LEntry D => (e.name, e.linked) := rfl
    have h1 : (LEntry.c ∘ LEntry.swap : LEntry D → CT D) = LEntry.c := rfl
    have h2 : (LEntry.m0 ∘ LEntry.swap : LEntry D → M D) = LEntry.m1 := rfl
    have h3 : (LEntry.m1 ∘ LEntry.swap : LEntry D → M D) = LEntry.m0 := rfl
    rw [h0, h1, h2, h3]
    split
    · rw [zip_swapLM]
      rfl
    · rfl

theorem decAnsLM_swap [DecidableEq (M D)] (dec : D.SK → CT D → M D) (sk : D.SK)
    (T : List (LEntry D)) (j : ℕ) :
    decAnsLM dec sk (T.map LEntry.swap) j = decAnsLM dec sk T j := by
  unfold decAnsLM
  rw [List.getElem?_map]
  cases T[j]? with
  | none => rfl
  | some e =>
    show (if e.m1 = e.m0 then some (dec sk e.c) else none) =
      (if e.m0 = e.m1 then some (dec sk e.c) else none)
    by_cases h : e.m0 = e.m1
    · simp [h]
    · simp [h, Ne.symm h]

theorem gameLM_swap_aux (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (b : Bool) (pk : D.PK) (sk : D.SK)
    (tape : ℕ → D.ER) (A : LAdv D Bool) : ∀ n T G,
    gameLM mk adm ev dec b pk sk tape A.swap n (T.map LEntry.swap) G =
      gameLM mk adm ev dec (!b) pk sk tape A n T G := by
  induction A with
  | ret a => intro n T G; rfl
  | enc m0 m1 x k ih =>
    intro n T G
    simp only [LAdv.swap, gameLM]
    rw [pick_swap]
    have := ih (D.enc pk (pick (!b) m0 m1) (tape n)) (n + 1)
      (T ++ [⟨m0, m1, D.enc pk (pick (!b) m0 m1) (tape n), x, decide (x ∉ G.names)⟩]) (G.link x)
    rw [List.map_append] at this
    exact this
  | eval C idx k ih =>
    intro n T G
    simp only [LAdv.swap, gameLM, evalLM_swap]
    cases evalLM mk adm ev pk T G C idx with
    | none => exact ih none n T G
    | some p =>
      have := ih (some p.1) n (T ++ p.2.1) p.2.2
      rw [List.map_append] at this
      exact this
  | dec j k ih =>
    intro n T G
    simp only [LAdv.swap, gameLM, decAnsLM_swap]
    exact ih _ n T G

end LMSwap

theorem gameLM_swap (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (b : Bool) (pk : D.PK) (sk : D.SK)
    (tape : ℕ → D.ER) (A : LAdv D Bool) :
    gameLM mk adm ev dec b pk sk tape A.swap 0 [] (Global.empty D) =
      gameLM mk adm ev dec (!b) pk sk tape A 0 [] (Global.empty D) :=
  gameLM_swap_aux mk adm ev dec b pk sk tape A 0 [] _

theorem gameD_pairs_equal (S : HEScheme) [DecidableEq S.M] (pk : S.PK) (sk : S.SK)
    (tape : ℕ → S.ER) (A : Adv S Bool) (hA : A.swap = A) :
    gameD true pk sk tape A 0 [] = gameD false pk sk tape A 0 [] := by
  calc gameD true pk sk tape A 0 [] = gameD true pk sk tape A.swap 0 [] := by rw [hA]
    _ = gameD false pk sk tape A 0 [] := gameD_swap S true pk sk tape A

theorem gameLM_pairs_equal (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] (pk : D.PK) (sk : D.SK)
    (tape : ℕ → D.ER) (A : LAdv D Bool) (hA : A.swap = A) :
    gameLM mk adm ev dec true pk sk tape A 0 [] (Global.empty D) =
      gameLM mk adm ev dec false pk sk tape A 0 [] (Global.empty D) := by
  calc gameLM mk adm ev dec true pk sk tape A 0 [] (Global.empty D)
      = gameLM mk adm ev dec true pk sk tape A.swap 0 [] (Global.empty D) := by rw [hA]
    _ = gameLM mk adm ev dec false pk sk tape A 0 [] (Global.empty D) :=
      gameLM_swap D mk adm ev dec true pk sk tape A

/-! ## 10. Measurability, evaluation on earlier results -/

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
      (Global.empty D) = true} := by
  have hset : {ω | gameLM mk adm ev dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
      (Global.empty D) = true} =
      f ⁻¹' {x | gameLM mk adm ev dec b (pk' x) (sk' x) (tape' x) (A (coins' x) (pk' x)) 0 []
        (Global.empty D) = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hpk, hsk, hcoins]
    rw [gameLM_tape_local D mk adm ev dec b _ _ (tape ω) (tape' (f ω)) _ q (hq _ _) (htape ω)]
  rw [hset]
  exact hf (countable_measurableSet _)

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
      (reductionLM mk adm ev dec A (coins ω) (pk ω)) 0 = true} := by
  have hset : {ω | gameCPA (S := freshScheme D adm ev dec) b (pk ω) (tape ω)
      (reductionLM mk adm ev dec A (coins ω) (pk ω)) 0 = true} =
      f ⁻¹' {x | gameCPA (S := freshScheme D adm ev dec) b (pk' x) (tape' x)
        (reductionLM mk adm ev dec A (coins' x) (pk' x)) 0 = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hpk, hcoins]
    rw [gameCPA_tape_local (freshScheme D adm ev dec) b _ (tape ω) (tape' (f ω))
      (reductionLM mk adm ev dec A _ _) q
      (reduceLM_cpaBounded D mk adm ev dec _ _ [] (Global.empty D) q (hq _ _)) (htape ω)]
  rw [hset]
  exact hf (countable_measurableSet _)

/-! Twins. -/

example := (@reduce_cpaBounded : type_of% @Challenge.IndCpaDSanity.reduce_cpaBounded)
example := (@reduction_cpaBounded : type_of% @Challenge.IndCpaDSanity.reduction_cpaBounded)
example := (@reduceLM_cpaBounded : type_of% @Challenge.IndCpaDSanity.reduceLM_cpaBounded)
example := (@gameD_tape_local : type_of% @Challenge.IndCpaDSanity.gameD_tape_local)
example := (@gameCPA_tape_local : type_of% @Challenge.IndCpaDSanity.gameCPA_tape_local)
example := (@gameLM_tape_local : type_of% @Challenge.IndCpaDSanity.gameLM_tape_local)
example := (@gameD_swap : type_of% @Challenge.IndCpaDSanity.gameD_swap)
example := (@gameCPA_swap : type_of% @Challenge.IndCpaDSanity.gameCPA_swap)
example := (@reduce_swap : type_of% @Challenge.IndCpaDSanity.reduce_swap)
example := (@idScheme_correct : type_of% @Challenge.IndCpaDSanity.idScheme_correct)
example := (@idCpaAdv_wins : type_of% @Challenge.IndCpaDSanity.idCpaAdv_wins)
example := (@idAdv_wins : type_of% @Challenge.IndCpaDSanity.idAdv_wins)
example := (@leakScheme_fresh : type_of% @Challenge.IndCpaDSanity.leakScheme_fresh)
example := (@leakScheme_not_correct : type_of% @Challenge.IndCpaDSanity.leakScheme_not_correct)
example := (@leakAdv_wins : type_of% @Challenge.IndCpaDSanity.leakAdv_wins)
example := (@leakAdv_reduction_loses : type_of% @Challenge.IndCpaDSanity.leakAdv_reduction_loses)
example := (@leakAdv_advantage : type_of% @Challenge.IndCpaDSanity.leakAdv_advantage)
example := (@gameD_measurableSet : type_of% @Challenge.IndCpaDSanity.gameD_measurableSet)
example := (@gameCPA_reduction_measurableSet :
  type_of% @Challenge.IndCpaDSanity.gameCPA_reduction_measurableSet)
example := (@bad_measurableSet : type_of% @Challenge.IndCpaDSanity.bad_measurableSet)
example := (@reach_link : type_of% @Challenge.IndCpaDSanity.reach_link)
example := (@reach_evalLM : type_of% @Challenge.IndCpaDSanity.reach_evalLM)
example := (@correct_of_sim : type_of% @Challenge.IndCpaDSanity.correct_of_sim)
example := (@sim_iff : type_of% @Challenge.IndCpaDSanity.sim_iff)
example := (@gameLM_swap : type_of% @Challenge.IndCpaDSanity.gameLM_swap)
example := (@gameD_pairs_equal : type_of% @Challenge.IndCpaDSanity.gameD_pairs_equal)
example := (@gameLM_pairs_equal : type_of% @Challenge.IndCpaDSanity.gameLM_pairs_equal)
example := (@gameLM_measurableSet : type_of% @Challenge.IndCpaDSanity.gameLM_measurableSet)
example := (@gameCPA_reductionLM_measurableSet :
  type_of% @Challenge.IndCpaDSanity.gameCPA_reductionLM_measurableSet)

end Validation.IndCpaDSanity
