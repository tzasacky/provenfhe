import Challenge.IndCpaD.LMAgree

/-!
# Challenge.IndCpaD.LMEmbed — every regular fresh-only adversary has a counterpart in the game with evaluation on earlier results   (LOCKED statements; proofs in `Validation/IndCpaD/LMEmbed.lean`)

The fresh-only game `Spec.IndCpaD.gameD` (played against `freshScheme D cls ev dec`: evaluation
queries on fresh table entries addressed by index) and the game with evaluation on earlier results
`Spec.IndCpaDLM.gameLM` (queries name entries of one growing global program; admissibility judged
on the inlined program) are compared for the same scheme, class and evaluator. For each of the
three interpreters (exact BGV operations at `exactClass`, BGV with key switching at `ksClass`,
BFV at `bfvClass`, all at a constant budget) and the instances at `N = 2¹³` used by
`probLM_eq_bgvSealExact`, `probLM_eq_bgvKSSeal` and `probLM_eq_bfvSeal`:

for every **regular** fresh-only adversary `A` there is an adversary `A'` of `gameLM`, built from
`A`, its coins and the public key alone, that makes the same encryption queries on every path
(`Bounded` transfers to `BoundedLM`) and such that both games return the same bit for every
challenge bit, key pair, encryption tape and adversary coins. So every winning probability and
every advantage of `A` in the fresh-only game is one of an adversary in `gameLM`
(`embedProb_*`: equal winning probabilities under any measure on the joint randomness).

**The counterpart `A'`** (in Validation: `Validation.IndCpaDEmbed.tr`) keeps, per table index,
whether the entry is fresh and which encryption it is, the encryption counter `n` and a query
counter `k`. It names the `n`-th encryption `ename n` (a name no query uses); it answers itself an
evaluation query that the fresh-only oracle refuses (class refuses, or an index is not a fresh
entry: `none`) or for which the fresh-only evaluator returns nothing (wrong number of inputs:
`some []`); every other evaluation query is forwarded on the same indices, with the circuit's
fresh inputs renamed to the selected entries' names and every other name `x` of the circuit
renamed to the new name `tname k x`; decryption queries are forwarded unchanged.

**Regular** (`Reg`): every evaluation query `(C, idx)` that the class admits and that has as many
indices as `C` has fresh inputs satisfies `RegQ`:
* the fresh input names of `C` are distinct, and so are the indices (otherwise the forwarded
  query would not be a renaming of `C`: one global name would stand for two inputs);
* every declaration of a fresh input has scale `0` (the declaration `freshDecl` the global
  program gives a fresh entry; the class checks parts, key, level and bound of a fresh input but
  not its scale, while `gameLM` checks that a query's declaration of an entry input agrees with
  the global program, scale included);
* the body writes no fresh input name (renamed, it would overwrite the selected entry's global
  name, and `gameLM` refuses a query that writes an existing name).
Each restriction is a syntactic property of the query alone. They are what this translation by
renaming needs; that no other translation could do without them is not claimed (for example, a
body that overwrites a fresh input could be put in single-assignment form first). For irregular
adversaries nothing is claimed.
-/

namespace Challenge.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile MeasureTheory

/-- **A regular query** (module docstring). -/
def RegQ (D : AbsScheme) (C : D.Circ) (idx : List ℕ) : Prop :=
  (D.fresh C).Nodup ∧ idx.Nodup ∧
    (∀ d ∈ (D.prog C).inputs, d.name ∈ D.fresh C → d.scale = 0) ∧
    ∀ i ∈ (D.prog C).body, Trace.dst i ∉ D.fresh C

/-- **A regular fresh-only adversary** (module docstring): on every path, every evaluation query
that the class admits and that has as many indices as the circuit has fresh inputs is regular. -/
def Reg (D : AbsScheme) (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
    (dec : D.SK → CT D → M D) : Adv (freshScheme D adm ev dec) Bool → Prop
  | .ret _ => True
  | .enc _ _ k => ∀ c, Reg D adm ev dec (k c)
  | .eval C idx k => (adm C = true → idx.length = (D.fresh C).length → RegQ D C idx) ∧
      ∀ r, Reg D adm ev dec (k r)
  | .dec _ k => ∀ r, Reg D adm ev dec (k r)

/-- **Embedding, exact BGV operations at `exactClass` (constant budget).** -/
theorem embed_exact (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : Trace.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hmf : D.P.src.t < D.P.src.modulus D.lvl) (dec : D.SK → CT D → M D) [DecidableEq (M D)]
    {Coins : Type}
    (A : Coins → D.PK →
      Adv (freshScheme D (exactClass D fun _ => E) (interpEval D (exactStepFn D)) dec) Bool)
    (hA : ∀ c p, Reg D (exactClass D fun _ => E) (interpEval D (exactStepFn D)) dec (A c p)) :
    ∃ A' : Coins → D.PK → LAdv D Bool, (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mk (exactClass D fun _ => E) (interpEval D (exactStepFn D)) dec b pk sk tape
          (A' c pk) 0 [] (Global.empty D) := sorry

/-- **Embedding, BGV with key switching at `ksClass` (constant budget).** -/
theorem embed_ks (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : Trace.Budget)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true) (hmf : D.P.src.t < D.P.src.modulus D.lvl)
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] {Coins : Type}
    (A : Coins → D.PK → Adv (freshScheme D (ksClass D lay rots fun _ => E)
      (interpEval D (ksStepFn D lay rk gk)) dec) Bool)
    (hA : ∀ c p, Reg D (ksClass D lay rots fun _ => E) (interpEval D (ksStepFn D lay rk gk)) dec
      (A c p)) :
    ∃ A' : Coins → D.PK → LAdv D Bool, (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mk (ksClass D lay rots fun _ => E) (interpEval D (ksStepFn D lay rk gk)) dec b pk
          sk tape (A' c pk) 0 [] (Global.empty D) := sorry

/-- **Embedding, BFV at `bfvClass`.** -/
theorem embed_bfv (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : Challenge.BFV.decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true)
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] {Coins : Type}
    (A : Coins → D.PK → Adv (freshScheme D (bfvClass D lay rots E)
      (interpEval D (bfvStepFn D lay rk gk)) dec) Bool)
    (hA : ∀ c p, Reg D (bfvClass D lay rots E) (interpEval D (bfvStepFn D lay rk gk)) dec
      (A c p)) :
    ∃ A' : Coins → D.PK → LAdv D Bool, (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mk (bfvClass D lay rots E) (interpEval D (bfvStepFn D lay rk gk)) dec b pk sk
          tape (A' c pk) 0 [] (Global.empty D) := sorry

/-- **Embedding at `bgvSeal` (`N = 2¹³`)**, exact operations, `exactClass` at `bgvSealProfile`. -/
theorem embed_bgvSealExact [DecidableEq (M bgvSealData)] {Coins : Type}
    (A : Coins → bgvSealData.PK → Adv (freshScheme bgvSealData
      (exactClass bgvSealData bgvSealProfile) (interpEval bgvSealData (exactStepFn bgvSealData))
      bgvSealData.decBGV) Bool)
    (hA : ∀ c p, Reg bgvSealData (exactClass bgvSealData bgvSealProfile)
      (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvSealData.PK → LAdv bgvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mkSealExact (exactClass bgvSealData bgvSealProfile)
          (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV b pk sk tape
          (A' c pk) 0 [] (Global.empty bgvSealData) := sorry

/-- **Embedding at `bgvKSSeal` (`N = 2¹³`)**, key switching, the class `admSeal`. -/
theorem embed_bgvKSSeal [DecidableEq (M bgvKSSealData)] {Coins : Type}
    (A : Coins → bgvKSSealData.PK →
      Adv (freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) Bool)
    (hA : ∀ c p, Reg bgvKSSealData admSeal evSeal bgvKSSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV b pk sk tape (A' c pk) 0 []
          (Global.empty bgvKSSealData) := sorry

/-- **Embedding at `sealBFV` (`N = 2¹³`)**, the class `admBFVSeal`. -/
theorem embed_bfvSeal [DecidableEq (M bfvSealData)] {Coins : Type}
    (A : Coins → bfvSealData.PK →
      Adv (freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV) Bool)
    (hA : ∀ c p, Reg bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV (A c p)) :
    ∃ A' : Coins → bfvSealData.PK → LAdv bfvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV b pk sk tape (A' c pk) 0 []
          (Global.empty bfvSealData) := sorry

/-! ## Winning probabilities

The same counterpart has the same winning probability under every measure on the joint
randomness (keys, tape, coins), for each challenge bit; so it has the same advantage. -/

/-- **Equal winning probabilities at `bgvSeal`.** -/
theorem embedProb_bgvSealExact [DecidableEq (M bgvSealData)] {Coins : Type}
    (A : Coins → bgvSealData.PK → Adv (freshScheme bgvSealData
      (exactClass bgvSealData bgvSealProfile) (interpEval bgvSealData (exactStepFn bgvSealData))
      bgvSealData.decBGV) Bool)
    (hA : ∀ c p, Reg bgvSealData (exactClass bgvSealData bgvSealProfile)
      (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvSealData.PK → LAdv bgvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pk : Ω → bgvSealData.PK)
        (sk : Ω → bgvSealData.SK) (tape : Ω → ℕ → bgvSealData.ER) (coins : Ω → Coins) (b : Bool),
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
          μ {ω | gameLM mkSealExact (exactClass bgvSealData bgvSealProfile)
            (interpEval bgvSealData (exactStepFn bgvSealData)) bgvSealData.decBGV b (pk ω) (sk ω)
            (tape ω) (A' (coins ω) (pk ω)) 0 [] (Global.empty bgvSealData) = true} := sorry

/-- **Equal winning probabilities at `bgvKSSeal`.** -/
theorem embedProb_bgvKSSeal [DecidableEq (M bgvKSSealData)] {Coins : Type}
    (A : Coins → bgvKSSealData.PK →
      Adv (freshScheme bgvKSSealData admSeal evSeal bgvKSSealData.decBGV) Bool)
    (hA : ∀ c p, Reg bgvKSSealData admSeal evSeal bgvKSSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pk : Ω → bgvKSSealData.PK)
        (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER) (coins : Ω → Coins)
        (b : Bool),
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
          μ {ω | gameLM mkSeal admSeal evSeal bgvKSSealData.decBGV b (pk ω) (sk ω) (tape ω)
            (A' (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true} := sorry

/-- **Equal winning probabilities at `sealBFV`.** -/
theorem embedProb_bfvSeal [DecidableEq (M bfvSealData)] {Coins : Type}
    (A : Coins → bfvSealData.PK →
      Adv (freshScheme bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV) Bool)
    (hA : ∀ c p, Reg bfvSealData admBFVSeal evBFVSeal bfvSealData.decBFV (A c p)) :
    ∃ A' : Coins → bfvSealData.PK → LAdv bfvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pk : Ω → bfvSealData.PK)
        (sk : Ω → bfvSealData.SK) (tape : Ω → ℕ → bfvSealData.ER) (coins : Ω → Coins)
        (b : Bool),
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
          μ {ω | gameLM mkBFVSeal admBFVSeal evBFVSeal bfvSealData.decBFV b (pk ω) (sk ω)
            (tape ω) (A' (coins ω) (pk ω)) 0 [] (Global.empty bfvSealData) = true} := sorry

end Challenge.IndCpaDLM
