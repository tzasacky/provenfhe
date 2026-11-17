import Challenge.IndCpaD.Defs
import Validation.BFVEncrypt

/-!
# Validation.IndCpaD.Inputs — fresh encryptions and the circuit's constants meet `InputsOK`
-/

namespace Validation.IndCpaD
open Spec NPoly Scheme Source Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
  Challenge.CertifyBFV Challenge.BFVEncrypt Challenge.IndCpaD Spec.IndCpaDBFV

variable {St : Setting}

/-- The circuit's input at the input noise `n` (what `certifyBFVFresh?` analyses). -/
def analysed (C : Circ St) (n : ℕ) : InputBFV :=
  { C.input with P := { St.base.P with inputNoise := n } }

/-- A stored plaintext `liftMsg m` is its own centred representative modulo `Q` once
`t − 1 ≤ Q / 2`. -/
theorem centered_liftMsg {N t Q : ℕ} (ht : 0 < t) (m : Poly t N) (h : t - 1 ≤ Q / 2) :
    centered (ofInt Q (liftMsg m)) = liftMsg m := by
  have : NeZero t := ⟨by omega⟩
  ext i
  show ((((m.coeff i).val : ℤ) : ZMod Q)).valMinAbs = ((m.coeff i).val : ℤ)
  rw [Int.cast_natCast]
  apply ZMod.valMinAbs_natCast_of_le_half
  have := ZMod.val_lt (m.coeff i)
  omega

/-- The first modulus divides into every level `≥ 1` when the moduli are positive. -/
theorem headD_le_modulus (Pr : Source.Params) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hpos : ∀ q ∈ Pr.qs, 0 < q) :
    Pr.qs.headD 0 ≤ Pr.modulus ℓ := by
  unfold Source.Params.modulus
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  cases hq : Pr.qs with
  | nil => simp
  | cons q rest =>
    rw [hq] at hpos
    simp only [List.headD_cons, List.take_succ_cons, List.prod_cons]
    have : 0 < (rest.take k).prod := List.prod_pos fun a ha =>
      hpos a (List.mem_cons_of_mem _ (List.mem_of_mem_take ha))
    exact Nat.le_mul_of_pos_right q this

/-- A one-component plaintext operand stored as `liftMsg p` meets `PlainOK` at any bound
`≥ t − 1`, when `t − 1 ≤ Q / 2` at its level. -/
theorem plainOK_liftMsg (P : FullParams) (s : IntPoly P.src.N) (b : ℕ) (v : Val P.src)
    (p : Poly P.src.t P.src.N) (hl : v.parts = 1) (hm : v.msg = .exact p) (ht : 0 < P.src.t)
    (hQ : P.src.t - 1 ≤ P.src.modulus v.level / 2) (hb : P.src.t - 1 ≤ b) :
    TraceBFV.PlainOK P s b v [liftMsg p] := by
  obtain ⟨hst1, hst2⟩ := Validation.FreshNoise.liftMsg_stored _ ht p
  refine ⟨by rw [hl]; rfl, p, hm, ?_, ?_⟩
  · show ofInt _ (centered (phase _ [ofInt _ (liftMsg p)])) = _
    rw [Validation.Source.phase_singleton, centered_liftMsg ht p hQ, hst1]
  · show normInf (centered (phase _ [ofInt _ (liftMsg p)])) ≤ _
    rw [Validation.Source.phase_singleton, centered_liftMsg ht p hQ]
    exact hst2.trans hb

/-- G1. -/
theorem inputsOK_fresh (C : Circ St) (fc : FreshCertBFV)
    (h : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc)
    (hx : C.extraOK = true)
    (pk : PK (St := St)) (sk : SK (St := St)) (hk : KeysOK pk sk)
    (ins : List (Poly St.base.P.src.t St.base.P.src.N × ER (St := St)))
    (hins : ∀ p ∈ ins, GoodE pk sk p.2) (hlen : ins.length = C.fresh.length) :
    TraceBFV.InputsOK (analysed C fc.params.inputNoise).P sk.s C.prog
      (fun x => .exact (C.msg (ins.map Prod.fst) x))
      (C.cts (ins.map fun p => enc pk p.1 p.2)) := by
  obtain ⟨hpar, hfr, hc⟩ := Validation.BFVEncrypt.certifyBFVFresh?_spec _ _ fc h
  obtain ⟨heps, -, -⟩ := Validation.BFVEncrypt.certifyBFVFresh?_worst_eps _ fc _ _ _ _ _ h
  have henc := Validation.CertifyBFV.certifyBFV?_encodeOK _ _ hc
  obtain ⟨hPok, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK _ _ hc
  obtain ⟨-, -, -, -, hra, -⟩ := Validation.CertifyBFV.certifyBFV?_spec _ _ hc
  obtain ⟨-, hallok, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hra
  have hspec := Validation.BFVEncrypt.freshOKBFV?_spec _ _ hfr
  obtain ⟨hsec, hek, hpk, -, -⟩ := hk
  have hx1 := (Bool.and_eq_true _ _).mp hx |>.1
  obtain ⟨params, cert, used, eps, drift⟩ := fc
  simp only at hpar heps henc hPok hallok
  subst hpar
  let r : Var → ER (St := St) := fun y =>
    match C.fresh.idxOf? y with
    | some i => (ins[i]?.map Prod.snd).getD (0, 0, 0)
    | none => (0, 0, 0)
  have hfresh : ∀ y ∈ C.fresh, ∃ i, ∃ hi : i < ins.length, C.fresh.idxOf? y = some i ∧
      r y = ins[i].2 ∧ C.msg (ins.map Prod.fst) y = ins[i].1 ∧
      C.cts (ins.map fun p => enc pk p.1 p.2) y = (enc pk ins[i].1 ins[i].2).2 := by
    intro y hy
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hy)
    obtain ⟨hlt, -⟩ := List.idxOf?_eq_some_iff.mp hi
    have hlt' : i < ins.length := hlen ▸ hlt
    refine ⟨i, hlt', hi, ?_, ?_, ?_⟩
    · simp only [r, hi, List.getElem?_eq_getElem hlt', Option.map_some, Option.getD_some]
    · simp only [Circ.msg, hi, List.getElem?_map, List.getElem?_eq_getElem hlt', Option.map_some,
        Option.getD_some]
    · simp only [Circ.cts, hi, List.getElem?_map, List.getElem?_eq_getElem hlt', Option.map_some,
        Option.getD_some]
  have hres := Validation.BFVEncrypt.inputsOK_of_fresh C.input _ _ h sk.s sk.e pk.b pk.a hpk
    (fun y => (r y).1) (fun y => (r y).2.1) (fun y => (r y).2.2) ?_ (C.msg (ins.map Prod.fst))
    (C.cts (ins.map fun p => enc pk p.1 p.2)) ?_
  · exact hres
  · intro y hy
    obtain ⟨i, hi, -, hr, -, -⟩ := hfresh y hy
    obtain ⟨hu, h1, h2⟩ := hins _ (List.getElem_mem hi)
    rw [heps]
    simp only [hr]
    exact Validation.FreshNoise.freshError_worst _ _ _ _ _ _ _ _ _ _ hsec hek hu h1 h2
  · refine ⟨?_, ?_⟩
    · intro y hy d hd
      change y ∈ C.fresh at hy
      have hn : d.name = y := by simpa using List.find?_some hd
      have hmem : d ∈ C.prog.inputs := List.mem_of_find?_eq_some hd
      have hlev := List.all_eq_true.mp hx1 d hmem
      rw [hn] at hlev
      simp only [hy, ↓reduceIte] at hlev
      have hlev' : d.level = top St := by simpa using hlev
      obtain ⟨i, hi, -, hr, hm, hct⟩ := hfresh y hy
      rw [hct, hm]
      simp only [hr]
      show encryptBFV _ (Qtop St) _ _ _ _ _ _ = _
      rw [hlev']
      rfl
    · intro y d hy hd
      change y ∉ C.fresh at hy
      have hn : d.name = y := by simpa using List.find?_some hd
      have hmem : d ∈ C.prog.inputs := List.mem_of_find?_eq_some hd
      have hb := List.all_eq_true.mp hx1 d hmem
      rw [hn] at hb
      simp only [hy, ↓reduceIte] at hb
      have hp1 : d.parts = 1 := by have := (hspec.2.2 d hmem).2; rw [hn] at this; exact this hy
      have hok := List.all_eq_true.mp hallok d hmem
      have hlv : 1 ≤ d.level := by
        simp only [Decl.ok, decide_eq_true_eq] at hok; exact hok.2.1
      have hnone : C.fresh.idxOf? y = none := List.idxOf?_eq_none_iff.mpr hy
      have hct : C.cts (ins.map fun p => enc pk p.1 p.2) y = [liftMsg (C.pt y)] := by
        simp only [Circ.cts, hnone]
      have hm : C.msg (ins.map Prod.fst) y = C.pt y := by simp only [Circ.msg, hnone]
      have h2t : 2 ≤ St.base.P.src.t := hPok.plaintext.1
      have ht : 0 < St.base.P.src.t := by omega
      have henc1 : St.base.P.src.t - 1 ≤ St.base.P.src.qs.headD 0 / 2 := henc.1
      have henc2 : ∀ q ∈ St.base.P.src.qs, St.base.P.src.t ≤ q := henc.2
      have hQ : St.base.P.src.t - 1 ≤ St.base.P.src.modulus d.level / 2 :=
        henc1.trans (Nat.div_le_div_right
          (headD_le_modulus _ _ hlv fun q hq => by have := henc2 q hq; omega))
      have hbd : ∀ z, St.base.P.src.t - 1 ≤ (C.prog.boundOf d.name).getD
          (if d.parts = 1 then St.base.P.src.t - 1 else z) := by
        intro z
        rw [hn]
        revert hb
        cases C.prog.boundOf y with
        | none => intro _; simp [hp1]
        | some b => intro hb; simpa using hb
      rw [hct]
      exact plainOK_liftMsg _ _ _ _ (C.pt y) hp1
        (by simp only [Correct.inputVal]; rw [hn, hm]; exact rfl) ht hQ (hbd _)

end Validation.IndCpaD
