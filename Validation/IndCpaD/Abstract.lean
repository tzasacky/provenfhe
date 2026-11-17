import Spec.IndCpaD
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Validation.IndCpaD.Abstract — the perfect simulation and the probability statements

The invariant `Inv`: in the real game every entry of the table decrypts to its selected message,
and every fresh entry is a good encryption of it. Encryption keeps it (`Correct.fresh`),
evaluation keeps it (`Correct.eval` on the randomness behind the fresh entries), and under it the
real decryption oracle answers as the simulated one (`decAns_eq`).
-/

namespace Validation.IndCpaD
open Spec.IndCpaD MeasureTheory

variable {S : HEScheme}

/-- What the table satisfies in the real game: fresh entries are good encryptions of the
selected message, and every entry decrypts to the selected message. -/
def Inv (b : Bool) (pk : S.PK) (sk : S.SK) (T : List (Entry S)) : Prop :=
  ∀ e ∈ T, (e.fresh = true → ∃ er, S.GoodE pk sk er ∧ e.c = S.enc pk (pick b e.m0 e.m1) er) ∧
    S.dec sk e.c = pick b e.m0 e.m1

theorem freshAt_mem {T : List (Entry S)} {j : ℕ} {e : Entry S} (h : freshAt T j = some e) :
    e ∈ T ∧ e.fresh = true := by
  unfold freshAt at h
  split at h
  · rename_i e' he'
    split at h
    · cases h; exact ⟨List.mem_of_getElem? he', by assumption⟩
    · cases h
  · cases h

theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ y ∈ ys, ∃ x, f x = some y := by
  intro xs
  induction xs with
  | nil => intro ys h y hy; simp at h; subst h; simp at hy
  | cons x xs ih =>
    intro ys h y hy
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    cases hfx : f x with
    | none => simp [hfx] at h
    | some y0 =>
      cases hr : xs.mapM f with
      | none => simp [hfx, hr] at h
      | some ys' =>
        simp [hfx, hr] at h
        subst h
        rcases List.mem_cons.mp hy with h1 | h1
        · exact ⟨x, h1 ▸ hfx⟩
        · exact ih hr y h1

/-- Choose the randomness behind a list of good fresh entries. -/
theorem choose_ins (b : Bool) (pk : S.PK) (sk : S.SK) :
    ∀ es : List (Entry S),
      (∀ e ∈ es, ∃ er, S.GoodE pk sk er ∧ e.c = S.enc pk (pick b e.m0 e.m1) er) →
      ∃ ins : List (S.M × S.ER), (∀ p ∈ ins, S.GoodE pk sk p.2) ∧
        ins.map (fun p => S.enc pk p.1 p.2) = es.map (·.c) ∧
        ins.map Prod.fst = es.map fun e => pick b e.m0 e.m1
  | [], _ => ⟨[], by simp, by simp, by simp⟩
  | e :: es, h => by
    obtain ⟨er, hg, hc⟩ := h e (by simp)
    obtain ⟨ins, h1, h2, h3⟩ := choose_ins b pk sk es fun e' he' => h e' (by simp [he'])
    refine ⟨(pick b e.m0 e.m1, er) :: ins, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp; exact hg
      · exact h1 p hp
    · simp [h2, hc]
    · simp [h3]

theorem zip_map_eq {α β : Type} (f : α → β) :
    ∀ (xs : List α) (ys : List β), xs.map f = ys → ∀ p ∈ xs.zip ys, f p.1 = p.2
  | [], _, _, p, hp => by simp at hp
  | x :: xs, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, h, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp (by simpa using hp) with hp | hp
    · subst hp; exact h.1
    · exact zip_map_eq f xs ys h.2 p hp

theorem zip3_proj {α β γ : Type} :
    ∀ (xs : List α) (ys : List β) (zs : List γ) (p : α × β × γ), p ∈ xs.zip (ys.zip zs) →
      (p.1, p.2.1) ∈ xs.zip ys ∧ (p.1, p.2.2) ∈ xs.zip zs
  | [], _, _, _, hp => by simp at hp
  | _ :: _, [], _, _, hp => by simp at hp
  | _ :: _, _ :: _, [], _, hp => by simp at hp
  | x :: xs, y :: ys, z :: zs, p, hp => by
    rcases List.mem_cons.mp (by simpa using hp) with hp | hp
    · subst hp; simp
    · obtain ⟨h1, h2⟩ := zip3_proj xs ys zs p hp
      rw [List.zip_cons_cons, List.zip_cons_cons]
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem sem_pick (C : S.Circ) (b : Bool) (es : List (Entry S)) :
    S.sem C (es.map fun e => pick b e.m0 e.m1) =
      pick b (S.sem C (es.map (·.m0))) (S.sem C (es.map (·.m1))) := by
  cases b <;> rfl

/-- The evaluation oracle keeps the invariant. -/
theorem evalStep_inv (hC : Correct S) {b : Bool} {pk : S.PK} {sk : S.SK}
    (hk : S.KeysOK pk sk) {T : List (Entry S)} (hT : Inv b pk sk T) {C : S.Circ}
    {idx : List ℕ} {outs : List S.CT} {new : List (Entry S)}
    (h : evalStep pk T C idx = some (outs, new)) : Inv b pk sk (T ++ new) := by
  unfold evalStep at h
  split at h
  · rename_i hadm
    split at h
    · rename_i es hes
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hout, hnew⟩ := h
      have hfr : ∀ e ∈ es, e ∈ T ∧ e.fresh = true := fun e he => by
        obtain ⟨j, hj⟩ := mapM_mem hes e he
        exact freshAt_mem hj
      obtain ⟨ins, hg, hcs, hms⟩ := choose_ins b pk sk es fun e he =>
        (hT e (hfr e he).1).1 (hfr e he).2
      have hdec := hC.eval pk sk hk C hadm ins hg
      rw [hcs, hms, sem_pick] at hdec
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hT e he
      · rw [← hnew] at he
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
        refine ⟨fun h => absurd h (by simp), ?_⟩
        obtain ⟨h0, h1⟩ := zip3_proj _ _ _ p hp
        cases b
        · exact zip_map_eq _ _ _ hdec _ h0
        · exact zip_map_eq _ _ _ hdec _ h1
    · cases h
  · cases h

variable [DecidableEq S.M]

theorem decAns_eq {b : Bool} {pk : S.PK} {sk : S.SK} {T : List (Entry S)}
    (hT : Inv b pk sk T) (j : ℕ) : decAns sk T j = simAns T j := by
  unfold decAns simAns
  split
  · rename_i e he
    split
    · rename_i heq
      have := (hT e (List.mem_of_getElem? he)).2
      rw [this, heq]; cases b <;> rfl
    · rfl
  · rfl

/-- **Perfect simulation.** On every tape on which the keys are good and every encryption the
run performs is good, the IND-CPA-D game and the IND-CPA game played by the reduction return
the same bit. -/
theorem sim (hC : Correct S) (b : Bool) (pk : S.PK) (sk : S.SK)
    (tape : ℕ → S.ER) (hk : S.KeysOK pk sk) :
    ∀ (A : Adv S Bool) (n : ℕ) (T : List (Entry S)), Inv b pk sk T → TapeOK pk sk tape A n →
      gameD b pk sk tape A n T = gameCPA b pk tape (reduce pk A T) n
  | .ret a, n, T, _, _ => rfl
  | .enc m0 m1 k, n, T, hT, ht => by
    simp only [gameD, reduce, gameCPA]
    refine sim hC b pk sk tape hk (k _) (n + 1) _ ?_ (ht.2 _)
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hT e he
    · simp only [List.mem_singleton] at he
      subst he
      exact ⟨fun _ => ⟨tape n, ht.1, rfl⟩, hC.fresh pk sk hk _ _ ht.1⟩
  | .eval C idx k, n, T, hT, ht => by
    simp only [gameD, reduce]
    cases h : evalStep pk T C idx with
    | none => exact sim hC b pk sk tape hk (k none) n T hT (ht _)
    | some r =>
      obtain ⟨outs, new⟩ := r
      exact sim hC b pk sk tape hk (k (some outs)) n _
        (evalStep_inv hC hk hT h) (ht _)
  | .dec j k, n, T, hT, ht => by
    simp only [gameD, reduce]
    rw [decAns_eq hT j]
    exact sim hC b pk sk tape hk (k _) n T hT (ht _)

omit [DecidableEq S.M] in
/-- A bounded adversary needs good randomness only for the encryptions it can make. -/
theorem tapeOK_of_bounded {pk : S.PK} {sk : S.SK} {tape : ℕ → S.ER} :
    ∀ {A : Adv S Bool} {q : ℕ}, Bounded A q → ∀ n, (∀ i, n ≤ i → i < n + q →
      S.GoodE pk sk (tape i)) → TapeOK pk sk tape A n := by
  intro A q hb
  induction hb with
  | ret a q => intro n _; trivial
  | enc m0 m1 k q _ ih =>
    intro n hg
    exact ⟨hg n le_rfl (by omega), fun c => ih c (n + 1) fun i h1 h2 => hg i (by omega) (by omega)⟩
  | eval C idx k q _ ih => intro n hg r; exact ih r n hg
  | dec j k q _ ih => intro n hg r; exact ih r n hg


/-! ## The locked statements -/

theorem gameD_eq_gameCPA (S : HEScheme) [DecidableEq S.M] (hC : Correct S) (b : Bool)
    (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) (hk : S.KeysOK pk sk) (A : Adv S Bool)
    (ht : TapeOK pk sk tape A 0) :
    gameD b pk sk tape A 0 [] = gameCPA b pk tape (reduce pk A []) 0 :=
  sim hC b pk sk tape hk A 0 [] (by intro e he; simp at he) ht

omit [DecidableEq S.M] in
theorem tapeOK_all {pk : S.PK} {sk : S.SK} {tape : ℕ → S.ER}
    (h : ∀ i, S.GoodE pk sk (tape i)) : ∀ (A : Adv S Bool) n, TapeOK pk sk tape A n := by
  intro A
  induction A with
  | ret a => intro n; trivial
  | enc m0 m1 k ih => intro n; exact ⟨h n, fun c => ih c (n + 1)⟩
  | eval C idx k ih => intro n r; exact ih r n
  | dec j k ih => intro n r; exact ih r n

theorem prob_eq (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, S.KeysOK (pk ω) (sk ω) ∧ ∀ i, S.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} := by
  apply measure_congr
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hgood] with ω hω
  rw [gameD_eq_gameCPA S hC b (pk ω) (sk ω) (tape ω) hω.1 _ (tapeOK_all hω.2 _ 0)]
  rfl

/-- On the good event, the two games agree. -/
theorem agree_of_good (S : HEScheme) [DecidableEq S.M] (hC : Correct S) {Coins : Type}
    (A : Coins → S.PK → Adv S Bool) (b : Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q)
    (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) (r : Coins)
    (hg : S.KeysOK pk sk ∧ ∀ i < q, S.GoodE pk sk (tape i)) :
    gameD b pk sk tape (A r pk) 0 [] = gameCPA b pk tape (reduction A r pk) 0 :=
  gameD_eq_gameCPA S hC b pk sk tape hg.1 _
    (tapeOK_of_bounded (hq _ _) 0 fun i _ hi => hg.2 i (by omega))

theorem prob_le (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool) (b : Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))} := by
  constructor
  · refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases hg : S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i)
    · left
      have := agree_of_good S hC A b q hq (pk ω) (sk ω) (tape ω) (coins ω) hg
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [← this]; exact hω
    · right; exact hg
  · refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases hg : S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i)
    · left
      have := agree_of_good S hC A b q hq (pk ω) (sk ω) (tape ω) (coins ω) hg
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [this]; exact hω
    · right; exact hg

end Validation.IndCpaD
