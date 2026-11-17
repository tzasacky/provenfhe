import Challenge.BFVMul.KSLeveled
import FHE.BFV.FloatLeveled
import FHE.KeySwitch.Order

/-!
# FHE.BFV.KSLeveled — key switching with an internal drop: the phase error

`Challenge.BFVMul.Fl.leveledKS S qs drop core` (OpenFHE `RelinearizeCore` under
`HPSPOVERQLEVELED`): the switched component `c` is scaled from `Q` to `Q_l` (`Fl.scaleDown`),
key-switched there by `core`, and the result is multiplied by `D = Q/Q_l` (`Fl.scaleUp`).

* `scaleDown_spec`: `Fl.scaleDown S qs l c` is `X mod Q_l` for an integer polynomial `X` with
  `2·F·|D·X − c| ≤ D·(F + 2·doubleSr (qs.drop l))`, `F = 2⁵³`;
* `ofInt_scaleUp`: `Fl.scaleUp qs l y ≡ D·y (mod Q)`;
* `leveledKS_phase`: for `core` meeting `KSCoreOK` at `Q_l` with error at most `ksl` and
  `‖tgt‖∞ ≤ btgt`: `up(core(d)₀) + up(core(d)₁)·s = c·tgt + err (mod Q)` with
  `err = (D·X − c)·tgt + D·e`, `‖err‖∞ ≤ Spec.BudgetBFV.ksLeveled N D ksl btgt r1`, and
  `‖err‖∞ ≤ ksl` when no limb is dropped;
* `step_keyOdd`: `Source.step` keeps every key odd.
-/

namespace FHE.BFV.KSLeveled
open Spec NPoly Scheme Source Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.POverQ
open Validation.Ring Validation.Scheme
open FHE.RNS FHE.BFV.MulHPS FHE.BFV.MulPOverQ FHE.BFV.FloatPOverQ Spec.BudgetBFV

variable {N : ℕ}

/-! ### The locked definitions, by `rfl` -/

theorem scaleDown_def (S : Fl.Sums) (qs : List ℕ) (l : ℕ) (c : IntPoly N) :
    Fl.scaleDown S qs l c =
      reconstruct (qs.take l) (Fl.scaleRoundOut S 1 (qs.drop l) (qs.take l)
        ((toLimbs qs c).drop l) ((toLimbs qs c).take l)) :=
  rfl

theorem scaleUp_def (qs : List ℕ) (l : ℕ) (y : IntPoly N) :
    Fl.scaleUp qs l y = reconstruct qs (expandQlHat qs (qs.take l) (toLimbs (qs.take l) y)) :=
  rfl

theorem leveledKS_three (S : Fl.Sums) (qs : List ℕ) (drop : ℕ)
    (core : IntPoly N → IntPoly N × IntPoly N) (c0 c1 c2 : IntPoly N) :
    Fl.leveledKS S qs drop core [c0, c1, c2] =
      [c0 + Fl.scaleUp qs (qs.length - drop)
          (core (Fl.scaleDown S qs (qs.length - drop) c2)).1,
       c1 + Fl.scaleUp qs (qs.length - drop)
          (core (Fl.scaleDown S qs (qs.length - drop) c2)).2] :=
  rfl

theorem leveledKS_two (S : Fl.Sums) (qs : List ℕ) (drop : ℕ)
    (core : IntPoly N → IntPoly N × IntPoly N) (c0 c1 : IntPoly N) :
    Fl.leveledKS S qs drop core [c0, c1] =
      [c0 + Fl.scaleUp qs (qs.length - drop)
          (core (Fl.scaleDown S qs (qs.length - drop) c1)).1,
       Fl.scaleUp qs (qs.length - drop)
          (core (Fl.scaleDown S qs (qs.length - drop) c1)).2] :=
  rfl

theorem KSCoreOK_def (Q B : ℕ) (s tgt : IntPoly N) (core : IntPoly N → IntPoly N × IntPoly N) :
    KSCoreOK Q B s tgt core ↔
      ∀ d : IntPoly N, ∃ e : IntPoly N, normInf e ≤ B ∧
        ofInt Q (core d).1 + ofInt Q (core d).2 * ofInt Q s =
          ofInt Q d * ofInt Q tgt + ofInt Q e :=
  Iff.rfl

/-! ### The two scalings -/

/-- **Scaling down**: `Fl.scaleDown S qs l c` is `X mod Q_l` with
`2·F·|D·X − c| ≤ D·(F + 2·doubleSr (qs.drop l))`. -/
theorem scaleDown_spec (S : Fl.Sums) (hS : Fl.SumsOK S) (qs : List ℕ) (l : ℕ)
    (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime) (hfq : floatBasisOK qs = true)
    (c : IntPoly N) :
    ∃ X : IntPoly N, Fl.scaleDown S qs l c = modPoly (qs.take l).prod X ∧
      ∀ i, 2 * (floatDen : ℤ) * |((qs.drop l).prod : ℤ) * X.coeff i - c.coeff i| ≤
        ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr (qs.drop l) : ℤ)) := by
  have hposl : ∀ q ∈ qs.take l, 0 < q := fun q hq => hpos q (List.mem_of_mem_take hq)
  have hcopl : (qs.take l).Pairwise Nat.Coprime := hcop.sublist (List.take_sublist _ _)
  have hfd : floatBasisOK (qs.drop l) = true := floatBasisOK_sublist (List.drop_sublist _ _) hfq
  have hposdl : ∀ m ∈ qs.drop l ++ qs.take l, 0 < m := fun m hm => hpos m (by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_of_mem_drop h
    · exact List.mem_of_mem_take h)
  have hcopdl : (qs.drop l ++ qs.take l).Pairwise Nat.Coprime :=
    pairwise_swap _ _ (by rw [List.take_append_drop]; exact hcop)
  obtain ⟨X, hX, hXb⟩ :=
    scaleRoundOut_toLimbs_fl S hS 1 (qs.drop l) (qs.take l) hposdl hcopdl hfd c
  refine ⟨X, ?_, fun i => ?_⟩
  · have e1 : (toLimbs qs c).drop l = toLimbs (qs.drop l) c := List.map_drop.symm
    have e2 : (toLimbs qs c).take l = toLimbs (qs.take l) c := List.map_take.symm
    rw [scaleDown_def, e1, e2, hX, reconstruct_toLimbs _ hposl hcopl]
  · have h := hXb i
    simp only [Nat.cast_one, one_mul] at h
    exact h

/-- **Scaling up**: `Fl.scaleUp qs l y ≡ D·y (mod Q)`. -/
theorem ofInt_scaleUp (qs : List ℕ) (l : ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (y : IntPoly N) :
    ofInt qs.prod (Fl.scaleUp qs l y) =
      ofInt qs.prod (const (((qs.drop l).prod : ℕ) : ℤ) * y) := by
  rw [scaleUp_def, expandQlHat_toLimbs qs l hpos, reconstruct_toLimbs qs hpos hcop,
    ofInt_modPoly]
  ext i
  simp only [coeff_ofInt, coeff_const_mul]

/-- A congruence modulo `Q_l` multiplied by `D` is a congruence modulo `Q_l·D`. -/
theorem ofInt_const_mul_lift (Ql D : ℕ) (u v : IntPoly N) (h : ofInt Ql u = ofInt Ql v) :
    ofInt (Ql * D) (const ((D : ℕ) : ℤ) * u) = ofInt (Ql * D) (const ((D : ℕ) : ℤ) * v) := by
  ext i
  have hi := congrArg (fun p => p.coeff i) h
  simp only [coeff_ofInt] at hi
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hi
  simp only [coeff_ofInt, coeff_const_mul]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨k, ?_⟩
  push_cast
  linear_combination (D : ℤ) * hk

/-- `‖s·s‖∞ ≤ N·B·B` for `‖s‖∞ ≤ B`. -/
theorem normInf_sq_le (s : IntPoly N) (B : ℕ) (hs : normInf s ≤ B) :
    normInf (s * s) ≤ N * B * B := by
  have hb : ∀ i, |s.coeff i| ≤ (B : ℤ) := (normInf_le_iff _ _).mp hs
  refine (normInf_le_iff _ _).mpr fun k => ?_
  have := abs_coeff_mul_le_N s s B B hb hb k
  push_cast
  exact this

/-! ### The phase error -/

/-- **The phase of the key switch with an internal drop.** -/
theorem leveledKS_phase [NeZero N] (S : Fl.Sums) (hS : Fl.SumsOK S) (qs : List ℕ) (l : ℕ)
    (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime) (hfq : floatBasisOK qs = true)
    (s tgt : IntPoly N) (ksl btgt : ℕ) (htgt : normInf tgt ≤ btgt)
    (core : IntPoly N → IntPoly N × IntPoly N)
    (hcore : KSCoreOK (qs.take l).prod ksl s tgt core) (c : IntPoly N) :
    ∃ err : IntPoly N,
      ofInt qs.prod (Fl.scaleUp qs l (core (Fl.scaleDown S qs l c)).1) +
          ofInt qs.prod (Fl.scaleUp qs l (core (Fl.scaleDown S qs l c)).2) * ofInt qs.prod s =
        ofInt qs.prod c * ofInt qs.prod tgt + ofInt qs.prod err ∧
      normInf err ≤ ksLeveled N (qs.drop l).prod ksl btgt (doubleSr (qs.drop l)) ∧
      (qs.length ≤ l → normInf err ≤ ksl) := by
  obtain ⟨X, hX, hXb⟩ := scaleDown_spec S hS qs l hpos hcop hfq c
  obtain ⟨e, heb, heq⟩ := (KSCoreOK_def _ _ _ _ _).mp hcore (Fl.scaleDown S qs l c)
  generalize core (Fl.scaleDown S qs l c) = ab at heq ⊢
  have hF : (0 : ℤ) < (floatDen : ℤ) := by exact_mod_cast FloatScalar.floatDen_pos
  have hD0 : (0 : ℤ) ≤ ((qs.drop l).prod : ℤ) := Nat.cast_nonneg _
  have hebz : ∀ i, |e.coeff i| ≤ (ksl : ℤ) := (normInf_le_iff _ _).mp heb
  have htz : ∀ i, |tgt.coeff i| ≤ (btgt : ℤ) := (normInf_le_iff _ _).mp htgt
  refine ⟨(const (((qs.drop l).prod : ℕ) : ℤ) * X - c) * tgt +
    const (((qs.drop l).prod : ℕ) : ℤ) * e, ?_, ?_, ?_⟩
  · rw [ofInt_scaleUp qs l hpos hcop, ofInt_scaleUp qs l hpos hcop]
    have h1 : ofInt (qs.take l).prod (ab.1 + ab.2 * s) =
        ofInt (qs.take l).prod (X * tgt + e) := by
      rw [ofInt_add, ofInt_mul, heq, hX, ofInt_modPoly, ofInt_add, ofInt_mul]
    have h2 := ofInt_const_mul_lift _ (qs.drop l).prod _ _ h1
    rw [prod_take_mul_drop] at h2
    simp only [ofInt_add, ofInt_mul, ofInt_sub] at h2 ⊢
    linear_combination h2
  · have hco : ∀ i, 2 * (floatDen : ℤ) *
        |((const (((qs.drop l).prod : ℕ) : ℤ) * X - c) * tgt +
          const (((qs.drop l).prod : ℕ) : ℤ) * e).coeff i| ≤
        ((qs.drop l).prod : ℤ) * (((floatDen : ℤ) + 2 * (doubleSr (qs.drop l) : ℤ)) * N * btgt +
          2 * ksl * floatDen) := fun i => by
      have hp := abs_coeff_mul_scaled (const (((qs.drop l).prod : ℕ) : ℤ) * X - c) tgt
        (2 * (floatDen : ℤ)) 1 _ (btgt : ℤ) (by linarith) one_pos
        (fun j => by rw [coeff_sub', coeff_const_mul]; exact hXb j)
        (fun j => by rw [one_mul]; exact htz j) i
      rw [coeff_add', coeff_const_mul]
      have h3 := abs_add_le (((const (((qs.drop l).prod : ℕ) : ℤ) * X - c) * tgt).coeff i)
        (((qs.drop l).prod : ℤ) * e.coeff i)
      rw [abs_mul, abs_of_nonneg hD0] at h3
      have h4 := mul_le_mul_of_nonneg_left (hebz i) hD0
      have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℤ) ≤ 2 * (floatDen : ℤ))
      have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℤ) ≤ 2 * (floatDen : ℤ))
      linarith
    refine (normInf_le_iff _ _).mpr fun i => ?_
    show _ ≤ (((qs.drop l).prod * ((floatDen + 2 * doubleSr (qs.drop l)) * N * btgt +
      2 * ksl * floatDen) / (2 * floatDen) : ℕ) : ℤ)
    have h2F : (0 : ℤ) < ((2 * floatDen : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_pos two_pos FloatScalar.floatDen_pos
    rw [Int.natCast_ediv, Int.le_ediv_iff_mul_le h2F]
    have := hco i
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    linarith
  · intro hl
    have hnil : qs.drop l = [] := List.drop_eq_nil_of_le hl
    have hFv : (floatDen : ℤ) = 2 ^ 53 := by norm_num [floatDen]
    have hXc : ∀ i, X.coeff i = c.coeff i := fun i => by
      have h := hXb i
      rw [hnil] at h
      simp only [List.prod_nil, Nat.cast_one, one_mul, doubleSr, List.length_nil, List.sum_nil,
        zero_add, add_zero, mul_one, hFv] at h
      have h7 : |X.coeff i - c.coeff i| < 1 := by
        by_contra hc
        have : (1 : ℤ) ≤ |X.coeff i - c.coeff i| := not_lt.mp hc
        norm_num at h
        linarith
      have := abs_lt.mp h7
      omega
    have hz : const (((qs.drop l).prod : ℕ) : ℤ) * X - c = 0 := by
      ext i
      rw [coeff_sub', coeff_const_mul, hnil, hXc i]
      simp
    refine (normInf_le_iff _ _).mpr fun i => ?_
    have h0 : ((0 : IntPoly N) * tgt).coeff i = 0 := by simp
    rw [hz, coeff_add', coeff_const_mul, hnil, h0]
    simpa using hebz i

/-! ### Keys stay odd -/

/-- Every value of the environment is under an odd key. -/
def KeyOdd {Pr : Params} (ρ : Env Pr) : Prop := ∀ a x, ρ a = some x → x.key % 2 = 1

theorem KeyOdd.set {Pr : Params} {ρ : Env Pr} (h : KeyOdd ρ) (d : Var) (v : Val Pr)
    (hv : v.key % 2 = 1) : KeyOdd (ρ.set d v) := by
  intro a x hx
  unfold Env.set at hx
  split at hx
  · cases hx; exact hv
  · exact h a x hx

theorem mul_mod_odd (k g n : ℕ) (hk : k % 2 = 1) (hg : g % 2 = 1) :
    (k * g) % (2 * n) % 2 = 1 := by
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro n rfl), Nat.mul_mod, hk, hg]

/-- One step of `Source.step` keeps every key odd. -/
theorem step_keyOdd {Pr : Params} {ρ ρ' : Env Pr} (i : Instr) (h : step Pr ρ i = some ρ')
    (hρ : KeyOdd ρ) : KeyOdd ρ' := by
  cases i <;>
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, guard] at h
  all_goals
    obtain ⟨x, hx, h⟩ := h
    have hk := hρ _ _ hx
  case automorph d a g =>
    obtain ⟨_, hg, rfl⟩ := h
    have hg' : g % 2 = 1 := by
      by_contra hc
      simp [hc] at hg
    exact hρ.set _ _ (mul_mod_odd _ _ _ hk hg')
  all_goals
    obtain ⟨_, -, _, -, _, -, rfl⟩ := h
    exact hρ.set _ _ (by first | exact hk | rfl)

/-- A run of `Source.step` keeps every key odd. -/
theorem foldlM_keyOdd {Pr : Params} (pre : List Instr) {ρ ρ' : Env Pr}
    (h : pre.foldlM (step Pr) ρ = some ρ') (hρ : KeyOdd ρ) : KeyOdd ρ' := by
  induction pre generalizing ρ with
  | nil => simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; exact h ▸ hρ
  | cons i pre ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ₁, h1, h2⟩ := h
    exact ih h2 (step_keyOdd i h1 hρ)

/-- The initial environment of well-formed declarations has odd keys. -/
theorem initEnv_keyOdd (Pr : Params) (prog : Program) (msgs : Var → Msg Pr.t Pr.N)
    (hin : (prog.inputs.all fun d => d.ok Pr) = true) : KeyOdd (initEnv Pr prog msgs) := by
  intro a x hx
  simp only [initEnv, Option.map_eq_some_iff] at hx
  obtain ⟨dcl, hd, rfl⟩ := hx
  have hm := List.mem_of_find?_eq_some hd
  have hok := List.all_eq_true.mp hin dcl hm
  simp only [Decl.ok, decide_eq_true_eq] at hok
  exact hok.2.2.2.1

end FHE.BFV.KSLeveled
