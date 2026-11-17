import Respec.Equiv.Decrypt
import Spec.Budget
import Validation.Budget.Basic
import Validation.Budget.Restrict
import FHE.KeySwitch.Layout

/-!
# Respec.Equiv.Gadget — item 4: key-switching keys and the gadget

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Verdicts

* **A's gadget is B's OpenFHE gadget (PROVED)**: `gadgetFactor_eq_gadgetOF` :
  `(Spec.Budget.gadgetFactor Pm Qs j : ℤ) = Respec.BGV.gadgetOF Pm Qs j` for every list `Qs`,
  `Pm`, `j` (definitional up to the cast). It is not Han–Ki's `P·Q̂ⱼ` (`gadgetHK`); B's
  `#guard`s in `BGVTest` show the two are not interchangeable.
  Residues (`gadgetFactor_residue`, PROVED): for pairwise-coprime digit moduli, `gⱼ ≡ P` modulo
  every divisor of `Qⱼ` and `gⱼ ≡ 0` modulo every divisor of `Q_{j'}`, `j' ≠ j` — the
  "`P` on the limbs of the digit, nothing elsewhere" form of OpenFHE `KeySwitchGenInternal`
  (keyswitch-hybrid.cpp:113-124), SEAL and Lattigo.
* **Key validity: EQUAL UP TO THE CONVENTION `keyNoise = t·Be` (PROVED)**:
  `keyValid_imp_ksk` / `ksk_imp_keyValid` : A's `KeyValid .bgv t (t·Be) s ⟨M, g, T⟩ b a` ↔ B's
  one-digit `IsKsk` condition `KskDigitOK` (`∃ e, ‖e‖∞ ≤ Be ∧ b + a·s = t·e + g·T(s) (mod M)`,
  B's `sFrom = T(s)`, `sTo = s`; `isKsk_iff` : B's `IsKsk` is `KskDigitOK` digit by digit), the
  direction `←` needing `2·t·Be < M`. A's `keyNoise` bounds the whole error
  `t·e` (factor `t` included); B's `Be` excludes it.
* **Lower levels.** A asks, at level `ℓ`, for keys modulo `Q_ℓ·P` encrypting the level-`ℓ`
  gadget computed from the level-`ℓ` digits (`Spec.Budget.gadgetReq P lay ℓ`). OpenFHE (and B's
  `HybridKey.restrict`) uses the top-level key with limbs dropped.
  `keyValid_restrict` (PROVED): a key valid modulo `M` for the integer factor `g` is valid modulo
  every `M' ∣ M` for any factor `g' ≡ g (mod M')`, **provided `2·B < M'`** (else the centred
  error does not survive the reduction).
  `gadget_restrict` (PROVED): if every level-`ℓ` digit modulus divides the top-level modulus of
  the same digit, the two gadget entries agree modulo `Q_ℓ·P`.
  `gadgetReq_restrict` (PROVED): under those two hypotheses a key valid for the level-`L`
  `gadgetReq` meets the level-`ℓ` `gadgetReq` (the statement "Using top-level keys at a lower
  level" of A's `FHE/KeySwitch/Gadget.lean`, here with the nesting written as divisibility of
  digit moduli and with the size condition `2·B < Q_ℓ·P`).
  `nested_of_restrictsTo` (PROVED): the nesting hypothesis holds for every layout that restricts
  from `L` to `ℓ` in A's sense (`Spec.Budget.restrictsTo lay L ℓ`, `ℓ ≤ L`), from A's
  `Validation.Budget.digitModulus_dvd_of_cut`. `uniformLayout_nested` (PROVED; also tested in
  `Test.lean` §1): it holds for `uniformLayout α c` at every
  pair of levels `ℓ ≤ L`, every `α`, from A's `Validation.Budget.uniformLayout_restrictsTo`.
  `gadgetReq_restrict_of_restrictsTo`, `gadgetReq_restrict_uniform` (PROVED): `gadgetReq_restrict`
  with the nesting hypotheses discharged this way.
  B's `restrict`ed key meets A's level-2 requirement on B's test instance (TESTED, `Test.lean`
  §2). Nesting **fails** for layouts A's `KSLayout` structure also admits:
  `nonNested_differs` (PROVED by `decide`) — sizes `[1,2]` at level 3 and `[2]` at level 2 give
  level-2 and top-level gadget entries that differ modulo `Q₂·P`, so top-level keys are not
  level-2 keys there. A now states the same restriction itself: `Spec.Budget.restrictsTo` is a
  trusted definition, A's `Validation.Budget.gadgetKeys_restrict` is the key-restriction theorem
  for `L` the top level (with the weaker size condition `2·(⌊B/t⌋·t) < Q_ℓ·P` for BGV), and
  `gadgetKeys_restrict_needs_restrictsTo` is A's own counterexample for a layout that does not
  restrict. `gadgetReq_restrict` here is an independent proof of that fact under the divisibility
  form of the hypothesis and the size condition `2·B < Q_ℓ·P`.
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Spec.Budget Respec Respec.BGV Validation.Ring Validation.Scheme

variable {N : ℕ}

/-! ### The gadget entry -/

/-- **A's gadget entry is B's OpenFHE gadget entry.** -/
theorem gadgetFactor_eq_gadgetOF (Pm : ℕ) (Qs : List ℕ) (j : ℕ) :
    ((gadgetFactor Pm Qs j : ℕ) : ℤ) = gadgetOF Pm Qs j := by
  simp [gadgetFactor, gadgetOF, qhat]

/-- An element of a pairwise-coprime list at index `i ≠ j` divides the product without index `j`. -/
theorem getElem_dvd_prod_eraseIdx (Qs : List ℕ) {i j : ℕ} (hi : i < Qs.length) (hij : i ≠ j) :
    Qs[i] ∣ (Qs.eraseIdx j).prod :=
  List.dvd_prod ((List.mem_eraseIdx_iff_getElem).mpr ⟨i, hi, hij, rfl⟩)

/-- In a pairwise-coprime list, `Qs[j]` is coprime to the product of the others. -/
theorem coprime_prod_eraseIdx (Qs : List ℕ) (hcop : Qs.Pairwise Nat.Coprime) {j : ℕ}
    (hj : j < Qs.length) : Nat.Coprime (Qs.eraseIdx j).prod Qs[j] := by
  rw [Nat.coprime_list_prod_left_iff]
  intro x hx
  obtain ⟨i, hi, hij, rfl⟩ := (List.mem_eraseIdx_iff_getElem).mp hx
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact List.pairwise_iff_getElem.mp hcop i j hi hj h
  · exact (List.pairwise_iff_getElem.mp hcop j i hj hi h).symm

/-- **Residues of A's gadget entry**: `≡ Pm` modulo any divisor of its own digit modulus, `≡ 0`
modulo any divisor of another digit modulus. -/
theorem gadgetFactor_residue (Pm : ℕ) (Qs : List ℕ) (hpos : ∀ q ∈ Qs, 0 < q)
    (hcop : Qs.Pairwise Nat.Coprime)
    {j j' : ℕ} (hj : j < Qs.length) (hj' : j' < Qs.length) {m : ℕ} (hm : m ∣ Qs[j']) :
    ((gadgetFactor Pm Qs j : ℕ) : ZMod m) = if j' = j then (Pm : ZMod m) else 0 := by
  unfold gadgetFactor
  split_ifs with h
  · subst h
    have hg : Qs.getD j' 1 = Qs[j'] := by simp [hj']
    set qj := Qs.getD j' 1
    have hm' : m ∣ qj := hg ▸ hm
    haveI : NeZero qj := ⟨by rw [hg]; exact (hpos _ (List.getElem_mem _)).ne'⟩
    have hc : Nat.Coprime (Qs.eraseIdx j').prod qj := hg ▸ coprime_prod_eraseIdx Qs hcop hj'
    set h0 := (Qs.eraseIdx j').prod
    have hd : (qj : ℤ) ∣ 1 - ((h0 * ((h0 : ZMod qj)⁻¹).val : ℕ) : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Nat.cast_mul,
        ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one _ hc]
      simp
    have h1 : ((h0 * ((h0 : ZMod qj)⁻¹).val : ℕ) : ZMod m) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub (((h0 * ((h0 : ZMod qj)⁻¹).val : ℕ) : ℤ))
        1 m).mpr ((Int.natCast_dvd_natCast.mpr hm').trans hd)
      simpa using this
    rw [Nat.mul_assoc, Nat.cast_mul, h1, mul_one]
  · have hd : m ∣ (Qs.eraseIdx j).prod := hm.trans (getElem_dvd_prod_eraseIdx Qs hj' h)
    rw [Nat.cast_mul, Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr hd, mul_zero, zero_mul]

/-- A pairwise-coprime list's product divides every integer all its members divide. -/
theorem list_prod_dvd (L : List ℕ) (hL : L.Pairwise Nat.Coprime) (z : ℤ)
    (h : ∀ q ∈ L, (q : ℤ) ∣ z) : (L.prod : ℤ) ∣ z := by
  induction L with
  | nil => simp
  | cons q L ih =>
    rw [List.pairwise_cons] at hL
    rw [List.prod_cons, Nat.cast_mul]
    have hc : Nat.Coprime q L.prod := Nat.coprime_list_prod_right_iff.mpr fun x hx => hL.1 x hx
    exact (Nat.isCoprime_iff_coprime.mpr hc).mul_dvd (h q (by simp))
      (ih hL.2 fun x hx => h x (by simp [hx]))

/-- **Gadget entries at two levels agree modulo `Q_ℓ·P`** when every level-`ℓ` digit modulus
divides the top-level modulus of the same digit. -/
theorem gadget_restrict (Pm : ℕ) (QsL Qsl : List ℕ) (hposL : ∀ q ∈ QsL, 0 < q)
    (hposl : ∀ q ∈ Qsl, 0 < q) (hL : QsL.Pairwise Nat.Coprime)
    (hl : Qsl.Pairwise Nat.Coprime) (hP : ∀ q ∈ Qsl, Nat.Coprime q Pm)
    (hlen : Qsl.length ≤ QsL.length)
    (hdvd : ∀ j (h : j < Qsl.length), Qsl[j] ∣ QsL[j]'(by omega)) {j : ℕ} (hj : j < Qsl.length) :
    ((Qsl.prod * Pm : ℕ) : ℤ) ∣ (gadgetFactor Pm QsL j : ℤ) - (gadgetFactor Pm Qsl j : ℤ) := by
  have hL' : (Qsl ++ [Pm]).Pairwise Nat.Coprime := by
    rw [List.pairwise_append]
    refine ⟨hl, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb; exact hP a ha
  have := list_prod_dvd (Qsl ++ [Pm]) hL' ((gadgetFactor Pm QsL j : ℤ) - (gadgetFactor Pm Qsl j : ℤ))
  rw [List.prod_append, List.prod_singleton] at this
  apply this
  intro q hq
  rw [List.mem_append] at hq
  rcases hq with hq | hq
  · obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hq
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [gadgetFactor_residue Pm QsL hposL hL (by omega) (by omega) (hdvd j' hj'),
      gadgetFactor_residue Pm Qsl hposl hl hj hj' dvd_rfl]
  · simp only [List.mem_singleton] at hq
    subst hq
    apply dvd_sub <;> exact Int.natCast_dvd_natCast.mpr (by
      unfold gadgetFactor; exact Dvd.dvd.mul_right (Dvd.intro _ rfl) _)

/-! ### Key validity -/

/-- One digit of B's `IsKsk`, in A's notation (`sFrom = T(s)`, `sTo = s`). -/
def KskDigitOK (t Be : ℕ) {M : ℕ} (g : ℤ) (s : IntPoly N) (tgt : KeyTarget) (b a : Poly M N) :
    Prop :=
  ∃ e : IntPoly N, normInf e ≤ Be ∧
    b + a * ofInt M s = ofInt M (zscale t e) + zsmul g (ofInt M (tgt.eval s))

/-- B's `IsKsk` is the conjunction of `KskDigitOK` over the digits. -/
theorem isKsk_iff (t Be : ℕ) {M : ℕ} (gad : ℕ → ℤ) (s : IntPoly N) (tgt : KeyTarget)
    (ksk : List (KskDigit M N)) :
    IsKsk t gad (tgt.eval s) s ksk Be ↔
      ∀ j (h : j < ksk.length), KskDigitOK t Be (gad j) s tgt ksk[j].b ksk[j].a := by
  unfold IsKsk KskDigitOK
  rfl

/-- **A's key validity is B's, with `keyNoise = t·Be`** (`→` always; `←` when `2·t·Be < M`). -/
theorem keyValid_imp_ksk (t Be : ℕ) {M : ℕ} (s : IntPoly N) (g : ℤ) (tgt : KeyTarget)
    (b a : Poly M N) (h : KeyValid .bgv t (t * Be) s ⟨M, const (g : ZMod M), tgt⟩ b a) :
    KskDigitOK t Be g s tgt b a := by
  obtain ⟨hb, hd⟩ := h
  have hd' := hd rfl
  set E := centered (b + a * ofInt M s - const (g : ZMod M) * ofInt M (tgt.eval s)) with hE
  refine ⟨⟨fun i => E.coeff i / t⟩, ?_, ?_⟩
  · rw [normInf_le_iff]
    intro i
    have h1 := (normInf_le_iff _ _).mp hb i
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    · have h2 : E.coeff i = t * (E.coeff i / t) := (Int.mul_ediv_cancel' (hd' i)).symm
      have ht' : (0 : ℤ) < t := by exact_mod_cast ht
      show |E.coeff i / t| ≤ Be
      rw [h2, abs_mul, abs_of_pos ht'] at h1
      push_cast at h1
      exact le_of_mul_le_mul_left h1 ht'
  · apply eq_of_neZero; intro
    have hz : zscale t ⟨fun i => E.coeff i / t⟩ = E := by
      ext i; simp only [zscale_eq, coeff_smul']; exact Int.mul_ediv_cancel' (hd' i)
    rw [hz, hE, ofInt_centered, zsmul_eq, smul_eq_const_mul]
    ring

theorem ksk_imp_keyValid (t Be : ℕ) {M : ℕ} (hM : 2 * (t * Be) < M) (s : IntPoly N) (g : ℤ)
    (tgt : KeyTarget) (b a : Poly M N) (h : KskDigitOK t Be g s tgt b a) :
    KeyValid .bgv t (t * Be) s ⟨M, const (g : ZMod M), tgt⟩ b a := by
  obtain ⟨e, he, heq⟩ := h
  have hc : centered (b + a * ofInt M s - const (g : ZMod M) * ofInt M (tgt.eval s)) =
      zscale t e := by
    have : b + a * ofInt M s - const (g : ZMod M) * ofInt M (tgt.eval s) = ofInt M (zscale t e) := by
      apply eq_of_neZero; intro
      rw [heq, zsmul_eq, smul_eq_const_mul]; ring
    rw [this]
    apply centered_ofInt
    intro i
    simp only [zscale_eq, coeff_smul']
    have h1 := (normInf_le_iff _ _).mp he i
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg t)]
    have h2 : (t : ℤ) * |e.coeff i| ≤ t * Be := mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg t)
    have hM' : ((2 * (t * Be) : ℕ) : ℤ) < M := by exact_mod_cast hM
    push_cast at hM'
    linarith
  refine ⟨?_, fun _ i => ?_⟩
  · show normInf (centered _) ≤ _
    rw [hc, normInf_le_iff]
    intro i
    simp only [zscale_eq, coeff_smul']
    have h1 := (normInf_le_iff _ _).mp he i
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg t)]
    push_cast
    exact mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg t)
  · show (t : ℤ) ∣ (centered _).coeff i
    rw [hc]; simp only [zscale_eq, coeff_smul']; exact dvd_mul_right _ _


/-- **Transport of a key to a divisor modulus** (the formal content of "drop limbs"). -/
theorem keyValid_restrict (kind : Kind) (t B : ℕ) (s : IntPoly N) (tgt : KeyTarget) {M M' : ℕ}
    (hM : M' ∣ M) (g g' : ℤ) (hg : (g : ZMod M') = (g' : ZMod M')) (hB : 2 * B < M')
    (b a : IntPoly N)
    (h : KeyValid kind t B s ⟨M, const (g : ZMod M), tgt⟩ (ofInt M b) (ofInt M a)) :
    KeyValid kind t B s ⟨M', const (g' : ZMod M'), tgt⟩ (ofInt M' b) (ofInt M' a) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨by simp [normInf_unfold], fun _ i => i.elim0⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨hb, hd⟩ := h
  set E := centered (ofInt M b + ofInt M a * ofInt M s - const (g : ZMod M) * ofInt M (tgt.eval s))
    with hE
  -- the integer `b + a·s − g·T − E` vanishes modulo `M`, hence modulo `M'`
  have h0 : ofInt M (b + a * s - (g : IntPoly N) * tgt.eval s - E) = 0 := by
    simp only [ofInt_sub, ofInt_add, ofInt_mul, hE, ofInt_centered, FHE.KeySwitch.ofInt_intCast]
    rw [intCast_def]; ring
  have h0' : ofInt M' (b + a * s - (g : IntPoly N) * tgt.eval s - E) = 0 := by
    rw [FHE.KeySwitch.ofInt_eq_zero_iff] at h0 ⊢
    intro c; exact (Int.natCast_dvd_natCast.mpr hM).trans (h0 c)
  have hcE : centered (ofInt M' b + ofInt M' a * ofInt M' s -
      const (g' : ZMod M') * ofInt M' (tgt.eval s)) = E := by
    have : ofInt M' b + ofInt M' a * ofInt M' s - const (g' : ZMod M') * ofInt M' (tgt.eval s)
        = ofInt M' E := by
      rw [← hg, ← sub_eq_zero]
      have := h0'
      simp only [ofInt_sub, ofInt_add, ofInt_mul, FHE.KeySwitch.ofInt_intCast] at this
      rw [intCast_def] at this
      rw [← this]
    rw [this]
    apply centered_ofInt
    intro i
    have := (normInf_le_iff _ _).mp hb i
    have hB' : (2 * B : ℤ) < M' := by exact_mod_cast hB
    linarith
  exact ⟨by rw [hcE]; exact hb, by rw [hcE]; exact hd⟩

/-- The digit moduli of a usable layout are pairwise coprime and coprime to `P`. -/
theorem digitModuli_pairwise (P : FullParams) (hP : SchemeParamsOK P) (lay : KSLayout) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) :
    (digitModuli P lay ℓ).Pairwise Nat.Coprime := by
  rw [FHE.KeySwitch.digitModuli_eq P hP lay ℓ hℓ hlay, List.pairwise_ofFn]
  intro i j hij
  exact ((FHE.KeySwitch.layoutDigits lay ℓ hlay).basis _).coprime (Fin.ne_of_lt hij)

theorem modulus_coprime_special (P : FullParams) (hS : SpecialOK P) (ℓ : ℕ) :
    Nat.Coprime (P.src.modulus ℓ) (specialProd P) := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro q hq
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p hp
  exact (hS.2.2.1 p hp q (List.mem_of_mem_take hq)).symm

theorem modulus_dvd (P : Source.Params) {ℓ L : ℕ} (h : ℓ ≤ L) : P.modulus ℓ ∣ P.modulus L := by
  unfold Source.Params.modulus
  have : P.qs.take ℓ = (P.qs.take L).take ℓ := by rw [List.take_take, min_eq_left h]
  rw [this]
  exact ⟨_, (List.prod_take_mul_prod_drop _ ℓ).symm⟩

/-- **A's remark, proved**: a key valid for the top-level gadget requirement is valid for the
level-`ℓ` one, when the level-`ℓ` digits are nested in the top-level digits and `2·B < Q_ℓ·P`. -/
theorem gadgetReq_restrict (P : FullParams) (hP : SchemeParamsOK P) (hS : SpecialOK P)
    (lay : KSLayout) (L ℓ : ℕ) (hℓL : ℓ ≤ L) (hL : L ≤ P.src.qs.length)
    (hlayL : lay.okAt L = true) (hlay : lay.okAt ℓ = true)
    (hlen : (digitModuli P lay ℓ).length ≤ (digitModuli P lay L).length)
    (hnest : ∀ j (h : j < (digitModuli P lay ℓ).length),
      (digitModuli P lay ℓ)[j] ∣ (digitModuli P lay L)[j]'(by omega))
    (tgt : KeyTarget) (j : ℕ) (hj : j < (digitModuli P lay ℓ).length) (B : ℕ)
    (hB : 2 * B < P.src.modulus ℓ * specialProd P) (s b a : IntPoly P.src.N)
    (h : KeyValid P.src.kind P.src.t B s (gadgetReq P lay L tgt j)
      (ofInt _ b) (ofInt _ a)) :
    KeyValid P.src.kind P.src.t B s (gadgetReq P lay ℓ tgt j) (ofInt _ b) (ofInt _ a) := by
  have hcopl := digitModuli_pairwise P hP lay ℓ (by omega) hlay
  have hcopL := digitModuli_pairwise P hP lay L hL hlayL
  have hprod := (Validation.Budget.digitModuli_prod P lay ℓ hlay).2
  have hPc : ∀ q ∈ digitModuli P lay ℓ, Nat.Coprime q (specialProd P) := by
    intro q hq
    have hd : q ∣ P.src.modulus ℓ := hprod ▸ List.dvd_prod hq
    exact (modulus_coprime_special P hS ℓ).coprime_dvd_left hd
  have hpos : ∀ ℓ', ℓ' ≤ P.src.qs.length → lay.okAt ℓ' = true → ∀ q ∈ digitModuli P lay ℓ', 0 < q := by
    intro ℓ' h1 h2 q hq
    simp only [digitModuli, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    have := Validation.Budget.two_le_digitModulus P hP lay ℓ' h1 h2 i hi
    omega
  have hg := gadget_restrict (specialProd P) _ _ (hpos L hL hlayL) (hpos ℓ (by omega) hlay)
    hcopL hcopl hPc hlen hnest hj
  rw [hprod] at hg
  have hM : P.src.modulus ℓ * specialProd P ∣ P.src.modulus L * specialProd P :=
    Nat.mul_dvd_mul_right (modulus_dvd P.src hℓL) _
  have h' : KeyValid P.src.kind P.src.t B s
      ⟨P.src.modulus L * specialProd P,
        const (((gadgetFactor (specialProd P) (digitModuli P lay L) j : ℕ) : ℤ) :
          ZMod (P.src.modulus L * specialProd P)), tgt⟩ (ofInt _ b) (ofInt _ a) := by
    rw [Int.cast_natCast]; exact h
  have := keyValid_restrict P.src.kind P.src.t B s tgt hM _
    ((gadgetFactor (specialProd P) (digitModuli P lay ℓ) j : ℕ) : ℤ)
    ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by
      rw [← dvd_neg, neg_sub]; exact hg)) hB b a h'
  rw [Int.cast_natCast] at this; exact this

/-- **A layout that restricts (`Spec.Budget.restrictsTo`) is nested**: the level-`ℓ` digit moduli
are no more than the level-`L` ones, and each divides the level-`L` modulus of the same digit.
(From A's `Validation.Budget.cut_length_le`, `cut_take_sum`, `cut_getD_le`,
`digitModulus_dvd_of_cut`.) -/
theorem nested_of_restrictsTo (P : FullParams) (lay : KSLayout) (L ℓ : ℕ) (hℓL : ℓ ≤ L)
    (h : restrictsTo lay L ℓ = true) :
    (digitModuli P lay ℓ).length ≤ (digitModuli P lay L).length ∧
    ∀ j (_ : j < (digitModuli P lay ℓ).length) (h' : j < (digitModuli P lay L).length),
      (digitModuli P lay ℓ)[j] ∣ (digitModuli P lay L)[j] := by
  have hcut := ((Validation.Budget.restrictsTo_iff lay L ℓ).mp h).2
  have hlenl : (digitModuli P lay ℓ).length = (lay.sizes ℓ).length := by
    unfold digitModuli; rw [List.length_map, List.length_range]
  have hlenL : (digitModuli P lay L).length = (lay.sizes L).length := by
    unfold digitModuli; rw [List.length_map, List.length_range]
  refine ⟨?_, fun j hj hj' => ?_⟩
  · rw [hlenl, hlenL, hcut]; exact Validation.Budget.cut_length_le _ _
  · have e : ∀ (ℓ' : ℕ) (hh : j < (digitModuli P lay ℓ').length),
        (digitModuli P lay ℓ')[j] = digitModulus P lay ℓ' j := by
      intro ℓ' hh
      have hh' : j < ((List.range (lay.sizes ℓ').length).map (digitModulus P lay ℓ')).length := hh
      show ((List.range (lay.sizes ℓ').length).map (digitModulus P lay ℓ'))[j]'hh' = _
      rw [List.getElem_map, List.getElem_range]
    rw [e, e]
    refine Validation.Budget.digitModulus_dvd_of_cut P lay L ℓ j hℓL ?_ ?_
    · rw [hcut]; exact Validation.Budget.cut_take_sum _ _ _ (by rw [← hcut, ← hlenl]; exact hj)
    · rw [hcut]; exact Validation.Budget.cut_getD_le _ _ _

/-- **Uniform digits are nested at every pair of levels `ℓ ≤ L`**, for every digit size `α` and
either choice of representatives (the index bound is a hypothesis). From A's
`Validation.Budget.uniformLayout_restrictsTo`. -/
theorem uniformLayout_nested (P : FullParams) (α : ℕ) (c : Bool) (L ℓ : ℕ) (hℓL : ℓ ≤ L) :
    (digitModuli P (uniformLayout α c) ℓ).length ≤ (digitModuli P (uniformLayout α c) L).length ∧
    ∀ j (_ : j < (digitModuli P (uniformLayout α c) ℓ).length)
      (h' : j < (digitModuli P (uniformLayout α c) L).length),
      (digitModuli P (uniformLayout α c) ℓ)[j] ∣ (digitModuli P (uniformLayout α c) L)[j] :=
  nested_of_restrictsTo P _ L ℓ hℓL (Validation.Budget.uniformLayout_restrictsTo α c L ℓ hℓL)

/-- `gadgetReq_restrict` with its nesting hypotheses discharged by `restrictsTo`: a key valid for
the level-`L` gadget requirement is valid for the level-`ℓ` one when the layout restricts from `L`
to `ℓ` and `2·B < Q_ℓ·P`. (A's own `Validation.Budget.gadgetKeys_restrict` is the same fact for
`L` the top level, with the weaker size condition `2·(⌊B/t⌋·t) < Q_ℓ·P` and without `SpecialOK`.) -/
theorem gadgetReq_restrict_of_restrictsTo (P : FullParams) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (lay : KSLayout) (L ℓ : ℕ) (hℓL : ℓ ≤ L) (hL : L ≤ P.src.qs.length)
    (hr : restrictsTo lay L ℓ = true)
    (tgt : KeyTarget) (j : ℕ) (hj : j < (digitModuli P lay ℓ).length) (B : ℕ)
    (hB : 2 * B < P.src.modulus ℓ * specialProd P) (s b a : IntPoly P.src.N)
    (h : KeyValid P.src.kind P.src.t B s (gadgetReq P lay L tgt j)
      (ofInt _ b) (ofInt _ a)) :
    KeyValid P.src.kind P.src.t B s (gadgetReq P lay ℓ tgt j) (ofInt _ b) (ofInt _ a) :=
  have hn := nested_of_restrictsTo P lay L ℓ hℓL hr
  gadgetReq_restrict P hP hS lay L ℓ hℓL hL ((Validation.Budget.restrictsTo_iff lay L ℓ).mp hr).1
    (Validation.Budget.restrictsTo_okAt lay L ℓ hℓL hr) hn.1
    (fun j h => hn.2 j h (by omega)) tgt j hj B hB s b a h

/-- For uniform digits: a top-level key meets every lower level's gadget requirement. -/
theorem gadgetReq_restrict_uniform (P : FullParams) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (α : ℕ) (c : Bool) (L ℓ : ℕ) (hℓL : ℓ ≤ L) (hL : L ≤ P.src.qs.length)
    (tgt : KeyTarget) (j : ℕ) (hj : j < (digitModuli P (uniformLayout α c) ℓ).length) (B : ℕ)
    (hB : 2 * B < P.src.modulus ℓ * specialProd P) (s b a : IntPoly P.src.N)
    (h : KeyValid P.src.kind P.src.t B s (gadgetReq P (uniformLayout α c) L tgt j)
      (ofInt _ b) (ofInt _ a)) :
    KeyValid P.src.kind P.src.t B s (gadgetReq P (uniformLayout α c) ℓ tgt j)
      (ofInt _ b) (ofInt _ a) :=
  gadgetReq_restrict_of_restrictsTo P hP hS _ L ℓ hℓL hL
    (Validation.Budget.uniformLayout_restrictsTo α c L ℓ hℓL) tgt j hj B hB s b a h

/-- **Non-nested layouts do not restrict**: sizes `[1, 2]` at level 3 and `[2]` at level 2, on the
chain `7, 11, 13` with `P = 17`: the level-2 gadget entry of digit 0 is `≡ P (mod 11)`, the
top-level one is `≡ 0 (mod 11)`, so they differ modulo `Q₂·P = 7·11·17`. -/
theorem nonNested_differs :
    gadgetFactor 17 [7 * 11] 0 % (7 * 11 * 17) ≠ gadgetFactor 17 [7, 11 * 13] 0 % (7 * 11 * 17) := by
  decide +kernel

end Respec.Equiv
