import Challenge.IndCpaD.LMExact
import Challenge.IndCpaD.LMBFV

/-!
# Challenge.IndCpaD.LMAgree — on fresh entries, the oracle with evaluation on earlier results accepts exactly what the fresh-only class accepts   (LOCKED statements; proofs in `Validation/IndCpaD/LMAgree.lean` and `LMAgreeBFV.lean`)

For the certificate classes at a CONSTANT budget `E` (the same budget for every circuit and, for
BFV, every instruction), a global program `G` the game can reach (`Spec.IndCpaDLM.Reach`), and a
query `C` on fresh entries of `G` that

* names its entry inputs by the selected entries (`C.2.1 = en.map (·.1)`, all linked),
* writes only new names (its constants and destinations are not names of `G`),
* declares its entry inputs as the fresh declarations (`freshDecl D x`) and declares no bound for
  them,

the oracle of `Spec.IndCpaDLM.gameLM` accepts `C` (`admLM`) exactly when the class accepts `C`
as a fresh-only circuit (`mk C.1 C.2.1 C.2.2`). The history `G` plays no part. The hypothesis
`hfd` (a fresh declaration is well formed: `1 ≤ D.lvl ≤ L` and `1 < 2N`) is a closed check on the
parameters; for BGV, `hmf` (`t < Q_lvl`: a fresh input passes the input check
`Challenge.Certify.inputsMsgOK?`) is another.

BGV: `admLM_fresh_bgv` (the profile class `admBGV`), `admLM_fresh_exact` (`exactClass`),
`admLM_fresh_ks` (`ksClass`). BFV: `admLM_fresh_bfv` (the profile class `admBFV` at the constant
profile `fun _ _ => E`) and `admLM_fresh_bfvClass` (`bfvClass`); these also assume that a fresh
input passes the decryption check at its level (`decOK t Q_lvl eps`, a closed check). A budget that depends on the circuit can differ between `C` and
the inlined program, and a per-instruction BFV budget is read at shifted positions in the inlined
program; for those the statement is not claimed (the constant budget is a sufficient condition; it is not
shown to be necessary). The instances `admLM_fresh_bgvKSSeal`, `admLM_fresh_bgvSealExact` and
`admLM_fresh_bfvSeal` discharge every hypothesis on the parameters at `N = 2¹³`.
-/

namespace Challenge.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile

/-- **Agreement for the BGV profile class at a constant budget.** -/
theorem admLM_fresh_bgv (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : Trace.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hmf : D.P.src.t < D.P.src.modulus D.lvl) (G : Global D)
    (hG : Reach mk (admBGV D fun _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (admBGV D fun _ => E) G C en = admBGV D (fun _ => E) (mk C.1 C.2.1 C.2.2) := sorry

/-- **Agreement for `exactClass` at a constant budget.** -/
theorem admLM_fresh_exact (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : Trace.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hmf : D.P.src.t < D.P.src.modulus D.lvl) (G : Global D)
    (hG : Reach mk (exactClass D fun _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (exactClass D fun _ => E) G C en = exactClass D (fun _ => E) (mk C.1 C.2.1 C.2.2) :=
  sorry

/-- **Agreement for `ksClass` at a constant budget.** -/
theorem admLM_fresh_ks (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : Trace.Budget)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true) (hmf : D.P.src.t < D.P.src.modulus D.lvl)
    (G : Global D)
    (hG : Reach mk (ksClass D lay rots fun _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (ksClass D lay rots fun _ => E) G C en =
      ksClass D lay rots (fun _ => E) (mk C.1 C.2.1 C.2.2) := sorry

/-- **Agreement for the BFV profile class at a constant profile.** -/
theorem admLM_fresh_bfv (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : TraceBFV.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : Challenge.BFV.decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true) (G : Global D)
    (hG : Reach mk (admBFV D fun _ _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (admBFV D fun _ _ => E) G C en = admBFV D (fun _ _ => E) (mk C.1 C.2.1 C.2.2) :=
  sorry

/-- **Agreement for `bfvClass`.** -/
theorem admLM_fresh_bfvClass (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : Challenge.BFV.decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true) (G : Global D)
    (hG : Reach mk (Challenge.IndCpaDLM.bfvClass D lay rots E) G) (C : QCirc D)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (Challenge.IndCpaDLM.bfvClass D lay rots E) G C en =
      Challenge.IndCpaDLM.bfvClass D lay rots E (mk C.1 C.2.1 C.2.2) := sorry

/-- **Agreement at `bgvKSSeal` (`N = 2¹³`), the class `admSeal` (key switching).** -/
theorem admLM_fresh_bgvKSSeal (G : Global bgvKSSealData) (hG : Reach Challenge.IndCpaDLM.mkSeal Challenge.IndCpaDLM.admSeal G) (C : QCirc bgvKSSealData)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl bgvKSSealData d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM Challenge.IndCpaDLM.mkSeal Challenge.IndCpaDLM.admSeal G C en = Challenge.IndCpaDLM.admSeal (Challenge.IndCpaDLM.mkSeal C.1 C.2.1 C.2.2) := sorry

/-- **Agreement at `bgvSeal` (`N = 2¹³`), `exactClass` at `bgvSealProfile`.** -/
theorem admLM_fresh_bgvSealExact (G : Global bgvSealData) (hG : Reach Challenge.IndCpaDLM.mkSealExact (exactClass bgvSealData bgvSealProfile) G) (C : QCirc bgvSealData)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl bgvSealData d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM Challenge.IndCpaDLM.mkSealExact (exactClass bgvSealData bgvSealProfile) G C en = (exactClass bgvSealData bgvSealProfile) (Challenge.IndCpaDLM.mkSealExact C.1 C.2.1 C.2.2) := sorry

/-- **Agreement at `sealBFV` (`N = 2¹³`), the class `admBFVSeal`.** -/
theorem admLM_fresh_bfvSeal (G : Global Challenge.IndCpaDLM.bfvSealData) (hG : Reach Challenge.IndCpaDLM.mkBFVSeal Challenge.IndCpaDLM.admBFVSeal G) (C : QCirc Challenge.IndCpaDLM.bfvSealData)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl Challenge.IndCpaDLM.bfvSealData d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM Challenge.IndCpaDLM.mkBFVSeal Challenge.IndCpaDLM.admBFVSeal G C en = Challenge.IndCpaDLM.admBFVSeal (Challenge.IndCpaDLM.mkBFVSeal C.1 C.2.1 C.2.2) := sorry

end Challenge.IndCpaDLM
