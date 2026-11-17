import Challenge.IndCpaD
import Validation.IndCpaD.Abstract
import Validation.IndCpaD.Inputs
import Validation.IndCpaD.Levels
import Validation.IndCpaD.Congr
import Validation.BFVEncrypt
import Validation.CertifyBFV.Library

/-!
# Validation.IndCpaD — proofs of the pins of `Challenge.IndCpaD`

The abstract statements are in `Validation.IndCpaD.Abstract`. BFV correctness on the class:
fresh encryptions decrypt (`encryptBFV_encrypts`, `freshError_worst`); for an admissible circuit,
the inputs meet `InputsOK` at the analysed parameters (`Inputs`), the rotation keys are extended
to every odd index without changing the library's execution (`Congr`: it reads them only at the
indices of the replay's key switches, all in `St.rots`), the library's execution does not read
the input noise (`Congr`), so `certifyBFV?_library_decrypts` applies, and the output levels are
those of the zero-message replay (`Levels`).
-/

namespace Validation.IndCpaD
open Spec NPoly Scheme Source Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
  Challenge.CertifyBFV Challenge.BFVEncrypt Challenge.IndCpaD Spec.IndCpaDBFV


variable {St : Setting}

/-- `freshDecOK`, unfolded (a local `rfl` equation: no equation lemma of a locked definition is
generated outside `Challenge`). -/
theorem freshDecOK_eq (St : Setting) : freshDecOK St =
    (decide (2 ≤ St.base.P.src.t) &&
      Challenge.BFV.decOK St.base.P.src.t (Qtop St)
        (freshNoiseBFV St.base.P.src.t (Qtop St)
          (worstError St.base.P.src.N St.base.P.secretBound St.Bk St.Bu St.B1 St.B2))) := rfl

/-- The evaluator, unfolded (as `freshDecOK_eq`). -/
theorem eval_eq (pk : PK (St := St)) (C : Circ St) (cs : List (CT (St := St))) :
    Challenge.IndCpaD.eval pk C cs =
      if cs.length = C.fresh.length then
        C.prog.outputs.map fun o =>
          (C.outLevel o, (runLibrary C.input St.A pk.rk pk.gk (C.cts cs) o).getD [])
      else [] := rfl

/-- Fresh correctness, from `encryptBFV_encrypts` and `freshError_worst`. -/
theorem fresh_correct (hSt : freshDecOK St = true)
    (pk : PK (St := St)) (sk : SK (St := St)) (hk : KeysOK pk sk)
    (m : Poly St.base.P.src.t St.base.P.src.N) (r : ER (St := St)) (hr : GoodE pk sk r) :
    dec sk (enc pk m r) = m := by
  rw [freshDecOK_eq] at hSt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSt
  obtain ⟨ht, hdec⟩ := hSt
  obtain ⟨hs, he, hpk, -⟩ := hk
  have hε := Validation.FreshNoise.freshError_worst sk.s sk.e r.1 r.2.1 r.2.2
    St.base.P.secretBound St.Bk St.Bu St.B1 St.B2 hs he hr.1 hr.2.1 hr.2.2
  exact (Validation.BFVEncrypt.encryptBFV_encrypts St.base.P.src.t (Qtop St) _ ht sk.s sk.e
    pk.b pk.a r.1 r.2.1 r.2.2 m hpk hε hdec).1

theorem analysed_cert (C : Circ St) (fc : FreshCertBFV)
    (h : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc) :
    certifyBFV? (analysed C fc.params.inputNoise) = some fc.cert := by
  obtain ⟨hp, -, hc⟩ := Validation.BFVEncrypt.certifyBFVFresh?_spec C.input _ fc h
  have : analysed C fc.params.inputNoise = { C.input with P := fc.params } := by
    rw [hp]; rfl
  rw [this]; exact hc

/-- Rotation keys that agree with `pk.gk` on `St.rots` and are valid at every other odd index. -/
theorem gk_extend (hN : ∃ k, St.base.P.src.N = 2 ^ k) (pk : PK (St := St)) (sk : SK (St := St))
    (hk : KeysOK pk sk) :
    ∃ gk' : ℕ → List (IntPoly St.base.P.src.N × IntPoly St.base.P.src.N),
      (∀ g ∈ St.rots, pk.gk g = gk' g) ∧
      ∀ g s', g % 2 = 1 → automorph g s' = sk.s →
        Budget.GadgetKeysOK St.base.P St.base.lay (top St) (.galois g) s' (gk' g) := by
  classical
  have hex : ∀ g, ∃ keys : List (IntPoly St.base.P.src.N × IntPoly St.base.P.src.N),
      g % 2 = 1 → ∀ s', automorph g s' = sk.s →
        Budget.GadgetKeysOK St.base.P St.base.lay (top St) (.galois g) s' keys := by
    intro g
    by_cases hg : g % 2 = 1
    · obtain ⟨keys, hkeys⟩ := galoisKeys_exist St.base.P St.base.lay (top St) hN g hg sk.s
      exact ⟨keys, fun _ => hkeys⟩
    · exact ⟨[], fun h => absurd h hg⟩
  choose ks hks using hex
  refine ⟨fun g => if g ∈ St.rots then pk.gk g else ks g, fun g hg => by simp [hg], ?_⟩
  intro g s' hg hs'
  by_cases hm : g ∈ St.rots
  · simp only [hm, ite_true]; exact hk.2.2.2.2 g hm s' hs'
  · simp only [hm, ite_false]; exact hks g hg s' hs'

theorem correct (St : Setting) (hSt : freshDecOK St = true) (hA : Spec.Float.Conforms St.A) :
    Spec.IndCpaD.Correct (scheme St) where
  fresh pk sk hk m r hr := fresh_correct hSt pk sk hk m r hr
  eval pk sk hk C hC ins hins := by
    change (eval pk C (ins.map fun p => enc pk p.1 p.2)).map (dec sk) = sem C (ins.map Prod.fst)
    change admissible C = true at hC
    unfold admissible at hC
    split at hC
    · rename_i fc hfc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hC
      obtain ⟨hid, hx⟩ := hC
      have hid' : AssumptionBFV.idealised ∉ fc.cert.assumed := by
        intro hm
        have : fc.cert.assumed.contains AssumptionBFV.idealised = true :=
          List.elem_eq_true_of_mem hm
        rw [this] at hid; cases hid
      have hcert := analysed_cert C fc hfc
      obtain ⟨hP, hkind, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK _ fc.cert hcert
      have hks : ksKeysIn St.base.P.src St.rots C.prog.body
          (initEnv St.base.P.src C.prog fun _ => .exact 0) = true := by
        unfold Circ.extraOK at hx
        simp only [Bool.and_eq_true] at hx
        exact hx.2
      by_cases hlen : ins.length = C.fresh.length
      · have hin := inputsOK_fresh C fc hfc hx pk sk hk ins hins hlen
        obtain ⟨gk', hagree, hgk'⟩ := gk_extend hP.N_pow2 pk sk hk
        obtain ⟨hs, -, -, hrk, -⟩ := hk
        obtain ⟨ρ, hρ, hout⟩ := Validation.CertifyBFV.certifyBFV?_library_decrypts
          (analysed C fc.params.inputNoise) fc.cert hcert hid' St.A (fun _ => hA) sk.s hs pk.rk
          hrk gk' hgk' _ _ hin
        have h1 : (ins.map fun p => enc pk p.1 p.2).length = C.fresh.length := by simpa using hlen
        have h2 : (ins.map Prod.fst).length = C.fresh.length := by simpa using hlen
        simp only [eval_eq, sem, List.length_map, hlen, ite_true]
        erw [List.map_map]
        change Source.eval St.base.P.src C.prog _ = some ρ at hρ
        erw [hρ]
        dsimp only
        apply List.map_congr_left
        intro o ho
        obtain ⟨v, ct, m, B, hv, hct, -, -, hm, -, hd⟩ := hout o ho
        have hct' : runLibrary C.input St.A pk.rk pk.gk
            (C.cts (ins.map fun p => enc pk p.1 p.2)) o = some ct := by
          have e1 := congrFun (runLibrary_gk_congr C.input St.rots St.A pk.rk pk.gk gk'
            (C.cts (ins.map fun p => enc pk p.1 p.2)) hks hagree) o
          have e2 := congrFun (runLibrary_inputNoise C.input fc.params.inputNoise St.A pk.rk gk'
            (C.cts (ins.map fun p => enc pk p.1 p.2))) o
          exact e1.trans (e2.symm.trans hct)
        simp only [Function.comp, hv, hct', hm]
        unfold dec
        rw [outLevel_eq C hkind _ ρ hρ o v hv]
        exact hd
      · have h1 : ¬ (ins.map fun p => enc pk p.1 p.2).length = C.fresh.length := by
          simpa using hlen
        have h2 : ¬ (ins.map Prod.fst).length = C.fresh.length := by simpa using hlen
        simp only [eval_eq, sem, List.length_map, hlen, ite_false]
        rfl
    · cases hC

theorem bfv_prob_eq (St : Setting) (hSt : freshDecOK St = true) (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Spec.IndCpaD.Adv (scheme St) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω) ∧ ∀ i, GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | Spec.IndCpaD.gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | Spec.IndCpaD.gameCPA (S := scheme St) b (pk ω) (tape ω)
        (Spec.IndCpaD.reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} :=
  prob_eq (scheme St) (correct St hSt hA) μ pk sk tape coins A b hgood

theorem bfv_prob_le (St : Setting) (hSt : freshDecOK St = true) (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Spec.IndCpaD.Adv (scheme St) Bool) (b : Bool) (q : ℕ)
    (hq : ∀ r p, Spec.IndCpaD.Bounded (A r p) q) :
    μ {ω | Spec.IndCpaD.gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | Spec.IndCpaD.gameCPA (S := scheme St) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | Spec.IndCpaD.gameCPA (S := scheme St) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | Spec.IndCpaD.gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} :=
  prob_le (scheme St) (correct St hSt hA) μ pk sk tape coins A b q hq

theorem admissible_tiny : freshDecOK tinySetting = true ∧ admissible tinyCirc = true := by
  decide +kernel

end Validation.IndCpaD
