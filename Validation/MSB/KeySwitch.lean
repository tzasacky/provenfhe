import Validation.MSB.Steps
import Validation.Budget.Restrict
import FHE.KeySwitch.Core

/-!
# Validation.MSB.KeySwitch — MSB keys, MSB key switching and MSB rescaling

Proofs of the key pins (item 2) and of the algorithm pins (item 4) of `Challenge.MSB`.

**Key switching** is reduced to the integer core of hybrid key switching that the LSB proofs use,
`FHE.KeySwitch.ks_core` (exact phase equation) and `ks_core_bound` (worst-case bound), at
plaintext modulus `1`: the MSB ModDown `(x − [x]_P)/P` is the core's ModDown with `t = 1` and
`f = −[x]_P`. The digits are the centred residues `[c]_{Qⱼ}` (`2‖Dⱼ‖∞ ≤ Qⱼ ≤ ℓⱼ·Qⱼ`), so the MSB
error is within the centred bound `⌊(N·B·Σⱼ ℓⱼQⱼ + k·P·(1 + N·B_s)) / (2P)⌋`, and `t` times it is
within `Spec.Budget.ksBoundAt` when `t·B ≤ keyNoise` (centred or canonical weights). The gadget
identity is `Validation.Budget.gadgetFactor_reconstruct` on the digit moduli of the layout.

**Rescaling** follows `Validation.Trace.stepOK_modSwitch_textbook_parts` with the correction
`−[c]_q` in place of `t·[−c·t⁻¹]_q`.
-/

namespace Validation.MSB
open Spec NPoly Scheme Source Spec.MSB Spec.Budget
open Validation.Ring Validation.Scheme

/-! ## Keys -/

theorem keyValidMSB_iff_kind {N : ℕ} (kind : Kind) (B : ℕ) (s : IntPoly N) (req : KeyReq N)
    (b a : Poly req.modulus N) :
    KeyValidMSB B s req b a ↔ KeyValid kind 1 B s req b a := by
  constructor
  · intro h; exact ⟨h, fun _ i => by simp⟩
  · intro h; exact h.1

theorem keyValidMSB_iff {N : ℕ} (B : ℕ) (s : IntPoly N) (req : KeyReq N)
    (b a : Poly req.modulus N) :
    KeyValidMSB B s req b a ↔ KeyValid .bgv 1 B s req b a :=
  keyValidMSB_iff_kind .bgv B s req b a

theorem gadgetKeysOK_iff (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (tgt : KeyTarget) (B : ℕ)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    MSB.GadgetKeysOK P lay ℓ tgt B s keys ↔
      Budget.GadgetKeysOK { P with src := { P.src with t := 1 }, keyNoise := B } lay ℓ tgt s
        keys :=
  and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun _ =>
    keyValidMSB_iff_kind P.src.kind B s _ _ _)

theorem keyValidMSB_toLSB {N : ℕ} (t B M : ℕ) (hM : 2 * (t * B) < M) (s : IntPoly N)
    (g : ZMod M) (tgt : KeyTarget) (b a : IntPoly N)
    (h : KeyValidMSB B s ⟨M, const g, tgt⟩ (ofInt M b) (ofInt M a)) :
    KeyValid .bgv t (t * B) s ⟨M, const ((t : ZMod M) * g), tgt⟩
      ((t : ZMod M) • ofInt M b) ((t : ZMod M) • ofInt M a) := by
  set e := centered (ofInt M b + ofInt M a * ofInt M s - const g * ofInt M (tgt.eval s))
  have he : normInf e ≤ B := h
  have hrel : (t : ZMod M) • ofInt M b + (t : ZMod M) • ofInt M a * ofInt M s -
      const ((t : ZMod M) * g) * ofInt M (tgt.eval s) = ofInt M ((t : ℤ) • e) := by
    rw [ofInt_smul, ofInt_centered]
    apply eq_of_neZero; intro
    simp only [smul_eq_const_mul]
    rw [← algebraMap_eq_const, ← algebraMap_eq_const, ← algebraMap_eq_const, map_mul]
    ring
  have hsmall : ∀ i, 2 * |((t : ℤ) • e).coeff i| < M := by
    intro i
    show 2 * |(t : ℤ) * e.coeff i| < M
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)]
    have h1 : (t : ℤ) * |e.coeff i| ≤ t * B :=
      mul_le_mul_of_nonneg_left ((abs_coeff_le_normInf e i).trans (by exact_mod_cast he))
        (by positivity)
    have h2 : ((2 * (t * B) : ℕ) : ℤ) < M := by exact_mod_cast hM
    push_cast at h2
    linarith
  show normInf (centered _) ≤ t * B ∧ (Kind.bgv = .bgv → ∀ i, (t : ℤ) ∣ (centered _).coeff i)
  rw [hrel, centered_ofInt _ hsmall]
  exact ⟨(normInf_smul_le t e).trans (Nat.mul_le_mul_left _ he), fun _ i => ⟨e.coeff i, rfl⟩⟩

theorem gadgetKeys_restrict (P : FullParams) (lay : KSLayout) (tgt : KeyTarget)
    (hP : SchemeParamsOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true) (B : ℕ)
    (hB : 2 * B < P.src.modulus ℓ * specialProd P)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay P.src.qs.length tgt B s keys) :
    MSB.GadgetKeysOK P lay ℓ tgt B s (keys.take (lay.sizes ℓ).length) := by
  obtain ⟨hlenK, hval⟩ := hkeys
  have hcut := ((Validation.Budget.restrictsTo_iff lay _ ℓ).mp hlay).2
  have hlen : (lay.sizes ℓ).length ≤ (lay.sizes P.src.qs.length).length := by
    rw [hcut]; exact Validation.Budget.cut_length_le _ _
  have hlt : (keys.take (lay.sizes ℓ).length).length = (lay.sizes ℓ).length := by
    rw [List.length_take]; omega
  refine ⟨hlt, fun j hj => ?_⟩
  have hjK : j < keys.length := by omega
  have hj' : j < (lay.sizes ℓ).length := by omega
  rw [List.getElem_take]
  have hM : P.src.modulus ℓ * specialProd P ∣ P.src.modulus P.src.qs.length * specialProd P := by
    apply Nat.mul_dvd_mul_right
    unfold Source.Params.modulus
    have : P.src.qs.take ℓ = (P.src.qs.take P.src.qs.length).take ℓ := by
      rw [List.take_take, min_eq_left hℓ]
    rw [this]
    exact (List.take_prefix _ _).sublist.prod_dvd_prod
  rw [keyValidMSB_iff]
  have h := (keyValidMSB_iff B s _ _ _).mp (hval j hjK)
  exact Validation.Budget.keyValid_restrict tgt hM
    (Validation.Budget.gadgetFactor_restrict P lay hP (specialProd P) ℓ hℓ hlay j hj')
    (fun _ => by simpa using hB) _ _ h

/-! ## Lists and finite sums -/

theorem sum_zipWith_fin {α β γ : Type} [AddCommMonoid γ] (f : α → β → γ) (l1 : List α)
    (l2 : List β) (h : l1.length = l2.length) :
    (List.zipWith f l1 l2).sum = ∑ j : Fin l1.length, f l1[j] (l2[j]'(h ▸ j.isLt)) := by
  have : List.zipWith f l1 l2 =
      List.ofFn (fun j : Fin l1.length => f l1[j] (l2[j]'(h ▸ j.isLt))) := by
    apply List.ext_getElem
    · simp [h]
    · intro i h1 h2; simp
  rw [this, List.sum_ofFn]

/-! ## The MSB gadget product -/

section Gadget
variable (P : FullParams)

/-- The centred ModDown: `p · divRound p x = x − [x]_p`. -/
theorem divRound_spec {N : ℕ} (p : ℕ) (x : IntPoly N) (i : Fin N) :
    (p : ℤ) * (divRound p x).coeff i = x.coeff i + -(((x.coeff i : ℤ) : ZMod p).valMinAbs) := by
  show (p : ℤ) * ((x.coeff i - ((x.coeff i : ℤ) : ZMod p).valMinAbs) / p) = _
  rw [Int.mul_ediv_cancel']
  · ring
  · rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.coe_valMinAbs]

theorem two_mul_abs_valMinAbs_le (p : ℕ) (z : ℤ) (hp : 0 < p) :
    2 * |(((z : ZMod p)).valMinAbs : ℤ)| ≤ p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have h := Validation.Source.abs_valMinAbs_le ((z : ZMod p))
  have h2 : 2 * (p / 2) ≤ p := Nat.mul_div_le p 2
  have : (2 : ℤ) * ((p / 2 : ℕ) : ℤ) ≤ p := by exact_mod_cast h2
  linarith

theorem specialProd_pos (hS : SpecialOK P) : 0 < specialProd P :=
  List.prod_pos fun p hp => by have := (hS.1 p hp).1; omega

/-- **The MSB gadget product, exact phase equation and bound.** -/
theorem gadgetProduct_spec (lay : KSLayout) (hP : SchemeParamsOK P) (hS : SpecialOK P)
    (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) (tgt : KeyTarget) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : normInf s ≤ P.secretBound)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ tgt B s keys) (c : IntPoly P.src.N) :
    ∃ e : IntPoly P.src.N,
      ofInt (P.src.modulus ℓ) (gadgetProduct P lay ℓ c keys).1 +
        ofInt (P.src.modulus ℓ) (gadgetProduct P lay ℓ c keys).2 * ofInt (P.src.modulus ℓ) s =
        ofInt (P.src.modulus ℓ) c * ofInt (P.src.modulus ℓ) (tgt.eval s) +
          ofInt (P.src.modulus ℓ) e ∧
      P.src.t * normInf e ≤ ksBoundAt P lay ℓ := by
  haveI : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  obtain ⟨hlenK, hval⟩ := hkeys
  obtain ⟨hQlen, hQprod⟩ := Validation.Budget.digitModuli_prod P lay ℓ hlay
  set Qs := digitModuli P lay ℓ with hQs
  set Pm := specialProd P with hPmdef
  set Q := P.src.modulus ℓ
  set T := tgt.eval s
  have hPm : 0 < Pm := specialProd_pos P hS
  have hKQ : keys.length = Qs.length := by rw [hlenK, hQlen]
  -- digit moduli: positive, pairwise coprime (they are the moduli of the library's digit basis)
  have hQfn := FHE.KeySwitch.digitModuli_eq P hP lay ℓ hℓ hlay
  have hpos : ∀ q ∈ Qs, 0 < q := by
    rw [hQs, hQfn]; intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact FHE.RNS.Basis.pos _ j
  have hcop : Qs.Pairwise Nat.Coprime := by
    rw [hQs, hQfn, List.pairwise_ofFn]
    intro i j hij
    exact FHE.RNS.Basis.coprime _ (Fin.ne_of_lt hij)
  have hQj : ∀ j : Fin Qs.length, 0 < Qs[j] := fun j => hpos _ (List.getElem_mem _)
  -- the data of the core equation
  let n := Qs.length
  let D : Fin n → IntPoly P.src.N := fun j => centered (ofInt Qs[j] c)
  let Kb : Fin n → IntPoly P.src.N := fun j => (keys[j]'(by rw [hKQ]; exact j.isLt)).1
  let Ka : Fin n → IntPoly P.src.N := fun j => (keys[j]'(by rw [hKQ]; exact j.isLt)).2
  let G : Fin n → ℤ := fun j => ((gadgetFactor Pm Qs j : ℕ) : ℤ)
  let E : Fin n → IntPoly P.src.N := fun j =>
    centered (ofInt (Q * Pm) (Kb j) + ofInt (Q * Pm) (Ka j) * ofInt (Q * Pm) s -
      const (((gadgetFactor Pm Qs j : ℕ) : ZMod (Q * Pm))) * ofInt (Q * Pm) T)
  set u0 : IntPoly P.src.N := ∑ j, D j * Kb j with hu0
  set u1 : IntPoly P.src.N := ∑ j, D j * Ka j with hu1
  -- the gadget product is the divided inner products
  have hDlen : (Qs.map fun Qj => centered (ofInt Qj c)).length = keys.length := by
    rw [List.length_map, hKQ]
  have hgp : gadgetProduct P lay ℓ c keys = (divRound Pm u0, divRound Pm u1) := by
    have e0 := sum_zipWith_fin (fun d (k : IntPoly P.src.N × IntPoly P.src.N) => d * k.1)
      (Qs.map fun Qj => centered (ofInt Qj c)) keys hDlen
    have e1 := sum_zipWith_fin (fun d (k : IntPoly P.src.N × IntPoly P.src.N) => d * k.2)
      (Qs.map fun Qj => centered (ofInt Qj c)) keys hDlen
    have hl : (Qs.map fun Qj => centered (ofInt Qj c)).length = n := List.length_map _
    show (divRound Pm (List.zipWith (fun d k => d * k.1)
        (Qs.map fun Qj => centered (ofInt Qj c)) keys).sum,
      divRound Pm (List.zipWith (fun d k => d * k.2)
        (Qs.map fun Qj => centered (ofInt Qj c)) keys).sum) = _
    rw [e0, e1]
    congr 2
    · exact Fintype.sum_equiv (finCongr hl) _ _ (fun j => by simp [D, Kb])
    · exact Fintype.sum_equiv (finCongr hl) _ _ (fun j => by simp [D, Ka])
  -- the gadget identity
  have hgad : ofInt (Q * Pm) (∑ j, (G j : IntPoly P.src.N) * D j - (Pm : IntPoly P.src.N) * c)
      = 0 := by
    rw [FHE.KeySwitch.ofInt_eq_zero_iff]
    intro i
    rw [coeff_sub', FHE.KeySwitch.coeff_sum', FHE.KeySwitch.coeff_natCast_mul']
    simp only [FHE.KeySwitch.coeff_intCast_mul']
    have h := Validation.Budget.gadgetFactor_reconstruct Pm Qs hpos hcop (c.coeff i)
      (fun j => if h : j < Qs.length then (D ⟨j, h⟩).coeff i else 0) (fun j hj => by
        simp only [hj, dite_true, D, coeff_centered, coeff_ofInt]
        rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.coe_valMinAbs])
    rw [hQprod, Finset.sum_range] at h
    have hsum : ∑ j : Fin Qs.length,
        (if h : (j : ℕ) < Qs.length then (D ⟨j, h⟩).coeff i else 0) *
          ((gadgetFactor Pm Qs j : ℕ) : ℤ) = ∑ j, G j * (D j).coeff i :=
      Finset.sum_congr rfl fun j _ => by simp [G, mul_comm]
    rw [hsum] at h
    exact_mod_cast h
  -- the keys
  have hkey : ∀ j, ofInt (Q * Pm) (Kb j + Ka j * s - (G j : IntPoly P.src.N) * T - E j) = 0 := by
    intro j
    simp only [E, ofInt_sub, ofInt_add, ofInt_mul, ofInt_centered, FHE.KeySwitch.ofInt_intCast]
    simp only [G]
    rw [intCast_def, Int.cast_natCast]
    ring
  -- ModDown
  have h0 : ∀ i, (Pm : ℤ) * (divRound Pm u0).coeff i =
      u0.coeff i + (1 : ℕ) * (-centered (ofInt Pm u0)).coeff i := by
    intro i; rw [divRound_spec]; simp
  have h1 : ∀ i, (Pm : ℤ) * (divRound Pm u1).coeff i =
      u1.coeff i + (1 : ℕ) * (-centered (ofInt Pm u1)).coeff i := by
    intro i; rw [divRound_spec]; simp
  obtain ⟨err, herr, herrc⟩ := FHE.KeySwitch.ks_core (Q := Q) (t := 1) hPm G D Kb Ka E c T s
    (divRound Pm u0) (divRound Pm u1) (-centered (ofInt Pm u0)) (-centered (ofInt Pm u1))
    hgad hkey h0 h1
  -- the bound
  set k := P.store.special.length
  set w : ℕ → ℕ → ℕ := fun m q => if lay.canonical then 2 * (m * (q - 1)) else m * q
  have hsizes : (lay.sizes ℓ).length = n := hQlen.symm
  let Mw : Fin n → ℕ := fun j => w ((lay.sizes ℓ)[j]'(by rw [hsizes]; exact j.isLt)) Qs[j]
  have hD : ∀ j, 2 * normInf (D j) ≤ Mw j := by
    intro j
    have h2 : 2 * normInf (D j) ≤ Qs[j] := FHE.RNS.two_mul_normInf_le fun i =>
      two_mul_abs_valMinAbs_le _ _ (hQj j)
    refine h2.trans ?_
    have hjs : (j : ℕ) < (lay.sizes ℓ).length := by rw [hsizes]; exact j.isLt
    have hsz : 1 ≤ (lay.sizes ℓ)[j] := by
      simp only [KSLayout.okAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        decide_eq_true_eq] at hlay
      exact hlay.2 _ (List.getElem_mem _)
    have hQ2 : 2 ≤ Qs[j] := by
      have := Validation.Budget.two_le_digitModulus P hP lay ℓ hℓ hlay j hjs
      simpa [hQs, digitModuli] using this
    show Qs[j] ≤ w _ _
    simp only [w]
    split_ifs
    · exact (Nat.le_mul_of_pos_left _ hsz).trans
        (Validation.Budget.mul_le_two_mul_pred _ _ hQ2)
    · exact Nat.le_mul_of_pos_left _ hsz
  have hE : ∀ j, normInf (E j) ≤ B := by
    intro j
    have := hval j (by rw [hKQ]; exact j.isLt)
    exact this
  have hf : ∀ u : IntPoly P.src.N, 2 * normInf (-centered (ofInt Pm u)) ≤ k * Pm := by
    intro u
    refine FHE.RNS.two_mul_normInf_le fun i => ?_
    show 2 * |-(((u.coeff i : ℤ) : ZMod Pm)).valMinAbs| ≤ ((k * Pm : ℕ) : ℤ)
    rw [abs_neg]
    have h := two_mul_abs_valMinAbs_le Pm (u.coeff i) hPm
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hnil : P.store.special = [] := List.length_eq_zero_iff.mp hk0
      have hP1 : (Pm : ℤ) = 1 := by
        have : Pm = 1 := by rw [hPmdef, specialProd, hnil]; rfl
        exact_mod_cast this
      rw [hP1] at h
      rw [hk0, Nat.zero_mul, Nat.cast_zero]
      have := abs_nonneg ((((u.coeff i : ℤ) : ZMod Pm)).valMinAbs)
      omega
    · have : (Pm : ℤ) ≤ ((k * Pm : ℕ) : ℤ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hk0
      linarith
  have hbd := FHE.KeySwitch.ks_core_bound hPm D E Mw s _ _ err hD hE hs (hf u0) (hf u1) herrc
  refine ⟨err, ?_, ?_⟩
  · rw [hgp]
    simp only
    rw [← ofInt_mul, ← ofInt_add, herr, ofInt_add, ofInt_mul]
  · have hsum : ∑ j, Mw j = (List.zipWith w (lay.sizes ℓ) Qs).sum := by
      rw [sum_zipWith_fin w (lay.sizes ℓ) Qs hQlen.symm]
      exact (Fintype.sum_equiv (finCongr hsizes) _ _ fun j => rfl).symm
    have hks : ksBoundAt P lay ℓ = (P.src.N * P.keyNoise * (List.zipWith w (lay.sizes ℓ) Qs).sum +
        P.src.t * (if lay.canonical then 2 * (k * (Pm - 1)) else k * Pm) *
          (1 + P.src.N * P.secretBound)) / (2 * Pm) := rfl
    have hF : k * Pm ≤ (if lay.canonical then 2 * (k * (Pm - 1)) else k * Pm) := by
      split_ifs
      · rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0]; simp
        · have hne : P.store.special.map (·.q) ≠ [] := by
            intro h; apply Nat.ne_of_gt hk0
            have h' : P.store.special = [] := by simpa using congrArg List.length h
            show P.store.special.length = 0
            rw [h']; rfl
          have h2 : 2 ≤ Pm := Validation.Budget.two_le_prod_of_ne_nil _ hne
            (fun p hp => (hS.1 p hp).1)
          exact Validation.Budget.mul_le_two_mul_pred _ _ h2
      · exact le_refl _
    rw [hks, ← hsum]
    unfold FHE.KeySwitch.ksBound at hbd
    set S := ∑ j, Mw j
    set F := (if lay.canonical then 2 * (k * (Pm - 1)) else k * Pm)
    set X := 1 + P.src.N * P.secretBound
    calc P.src.t * normInf err
        ≤ P.src.t * ((P.src.N * B * S + 1 * (k * Pm) * X) / (2 * Pm)) :=
          Nat.mul_le_mul_left _ hbd
      _ ≤ (P.src.t * (P.src.N * B * S + 1 * (k * Pm) * X)) / (2 * Pm) :=
          Nat.mul_div_le_mul_div_assoc _ _ _
      _ ≤ _ := by
          apply Nat.div_le_div_right
          have e1 : P.src.t * (P.src.N * B * S + 1 * (k * Pm) * X) =
              P.src.N * (P.src.t * B) * S + P.src.t * (k * Pm) * X := by ring
          rw [e1]
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hB)
          · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hF)

end Gadget

/-! ## The MSB algorithms meet their contracts -/

section Algorithms
variable (P : FullParams)

theorem keySwitch_stepOK (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ (.galois x.key) B s keys) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.keySwitch P lay ℓ ca keys)) (.keySwitch d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 2
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  rw [hg] at hlen
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, ca = [c0, c1] := by
    match ca, hlen with
    | [c0, c1], _ => exact ⟨_, _, rfl⟩
  subst hl
  obtain ⟨e, he, hb⟩ := gadgetProduct_spec P lay hP hS _ hℓ hlay (.galois x.key) B hB s hs keys
    hkeys c1
  refine ⟨{ x with key := 1 }, MSB.keySwitch P lay x.level [c0, c1] keys, ?_, ?_, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg]
  · simp [MSB.keySwitch, hg]
  refine ⟨x, [c0, c1], e, hx, hca, hb.trans hE, ?_⟩
  simp only [MSB.keySwitch, Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase,
    ofInt_add, KeyTarget.eval] at he ⊢
  linear_combination he

theorem relin_stepOK (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ .square B s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.relin P lay ℓ ca keys)) (.relin d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 3 ∧ x.key = 1
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  rw [hg.1] at hlen
  obtain ⟨c0, c1, c2, rfl⟩ : ∃ c0 c1 c2, ca = [c0, c1, c2] := by
    match ca, hlen with
    | [c0, c1, c2], _ => exact ⟨_, _, _, rfl⟩
  subst hl
  obtain ⟨e, he, hb⟩ := gadgetProduct_spec P lay hP hS _ hℓ hlay .square B hB s hs keys
    hkeys c2
  refine ⟨{ x with parts := 2 }, MSB.relin P lay x.level [c0, c1, c2] keys, ?_, rfl, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg.2]
  refine ⟨x, [c0, c1, c2], e, hx, hca, hb.trans hE, ?_⟩
  simp only [MSB.relin, Trace.phaseAt, hg.2, FHE.KeySwitch.automorph_one, List.map, phase,
    ofInt_add, KeyTarget.eval] at he ⊢
  rw [ofInt_mul] at he
  linear_combination he

theorem rescale_stepOK (hP : SchemeParamsOK P) (E : Trace.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hE : msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (hca : σ a = some ca) (hlen : ca.length = x.parts) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca))
      (.modSwitch d a) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨hℓ, h3⟩ := Validation.Trace.guard_bind_eq_some hstep
  have hlt : x.level - 1 < P.src.qs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h3
    simp at h3
  have hℓL : x.level ≤ P.src.qs.length := by omega
  have hgetD : P.src.qs[x.level - 1]? = some P.src.qs[x.level - 1]! := by simp [hlt]
  rw [hgetD, Option.bind_some] at h3
  cases h3
  refine ⟨_, _, Validation.Source.set_self _ _ _, ?_, rfl, ?_⟩
  · simp [MSB.rescale, hlen]
  obtain ⟨hqp, -⟩ := Validation.Source.qLast_facts P hP (x.level - 1) hlt
  have hQQ : P.src.modulus x.level = P.src.modulus (x.level - 1) * P.src.qs[x.level - 1]! :=
    Validation.Source.modulus_pred _ _ (by omega) hℓL
  refine ⟨x, ca, ?_⟩
  try dsimp only
  generalize P.src.qs[x.level - 1]! = q at hgetD hqp hQQ ⊢
  have hq0 : 0 < q := hqp.pos
  have : NeZero q := ⟨hq0.ne'⟩
  unfold Trace.phaseAt
  rw [hQQ]
  generalize hsk : automorph x.key s = sk
  generalize P.src.modulus (x.level - 1) = Q'
  show ∃ δ q', _
  unfold MSB.rescale
  rw [Validation.Source.phase_map_ofInt, Validation.Source.phase_map_ofInt]
  set Φ := centered (ofInt (Q' * q) (Validation.Source.intPhase sk ca)) with hΦ
  have hE' : ofInt (Q' * q) (Validation.Source.intPhase sk ca) = ofInt (Q' * q) Φ := by
    rw [hΦ, ofInt_centered]
  let dl : IntPoly P.src.N → IntPoly P.src.N := fun c =>
    ⟨fun i => -((((c.coeff i : ℤ) : ZMod q)).valMinAbs)⟩
  have hdiv : ∀ c : IntPoly P.src.N, ∀ i,
      (q : ℤ) * (divRound q c).coeff i = c.coeff i + (dl c).coeff i :=
    fun c i => divRound_spec q c i
  have hdl : ∀ c : IntPoly P.src.N, ∀ i, |(dl c).coeff i| ≤ ((q / 2 : ℕ) : ℤ) := by
    intro c i
    show |-(_ : ℤ)| ≤ _
    rw [abs_neg]
    exact Validation.Source.abs_valMinAbs_le _
  obtain ⟨e, he, hqe⟩ := Validation.Trace.divq_gen Q' q (Validation.Source.intPhase sk ca)
    (Validation.Source.intPhase sk (ca.map (divRound q))) Φ
    (Validation.Source.intPhase sk (ca.map dl)) hE'
    (Validation.Trace.intPhase_switch q sk _ dl hdiv ca)
  have hS : (∑ j, |sk.coeff j|) ≤ ((P.src.N * P.secretBound : ℕ) : ℤ) := by
    rw [← hsk]; push_cast
    exact (Validation.Source.sum_abs_automorph_le _ _).trans
      (sum_abs_le s _ ((normInf_le_iff _ _).mp hs))
  refine ⟨Validation.Source.intPhase sk (ca.map dl), q, hx, hca, hgetD, ?_, ?_, ?_⟩
  · -- the bound, read through `t`
    set G : ℕ := ((List.range x.parts).map fun i => (P.src.N * P.secretBound) ^ i).sum with hG
    have hnorm : normInf (Validation.Source.intPhase sk (ca.map dl)) ≤ q / 2 * G := by
      rw [normInf_le_iff]
      intro i
      have hb := Validation.Trace.abs_coeff_intPhase_le sk (P.src.N * P.secretBound)
        ((q / 2 : ℕ) : ℤ) hS (by positivity) (ca.map dl)
        (fun d' hd' j => by
          obtain ⟨c, -, rfl⟩ := List.mem_map.mp hd'
          exact hdl c j) i
      rw [List.length_map, hlen] at hb
      rw [← hG] at hb
      exact_mod_cast hb
    have h1 : P.src.t * G ≤ 2 * E.modSwitchAt x.parts := by
      have : (P.src.t * G + 1) / 2 ≤ E.modSwitchAt x.parts := hE
      omega
    have h2 : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
    calc P.src.t * normInf (Validation.Source.intPhase sk (ca.map dl))
        ≤ P.src.t * (q / 2 * G) := Nat.mul_le_mul_left _ hnorm
      _ = (P.src.t * G) * (q / 2) := by ring
      _ ≤ (2 * E.modSwitchAt x.parts) * (q / 2) := Nat.mul_le_mul_right _ h1
      _ = (2 * (q / 2)) * E.modSwitchAt x.parts := by ring
      _ ≤ q * E.modSwitchAt x.parts := Nat.mul_le_mul_right _ h2
  · -- q ∣ Ψ + δ
    intro j
    exact ⟨e.coeff j, (hqe j).symm⟩
  · -- the new phase
    rw [he]
    congr 1
    ext j
    show e.coeff j = (Φ.coeff j + (Validation.Source.intPhase sk (ca.map dl)).coeff j) / q
    rw [← hqe j, Int.mul_ediv_cancel_left _ (by exact_mod_cast hq0.ne')]

end Algorithms

end Validation.MSB
