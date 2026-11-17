import Challenge.BFVMul.POverQ
import FHE.BFV.MulHPS

/-!
# FHE.BFV.MulPOverQ — the slack of the idealised P-over-Q multiplication

`Challenge.BFVMul.poverqMul` (limb by limb: exact extension of operand 1, fast scaling by `P/Q`
of operand 2, limb-wise tensor product, RNS scale-and-round by `t/P`) is proved to multiply
integer representatives of bounded size and to round within a bounded distance, under
`poverqAuxOK?` (positive, pairwise coprime moduli):

* `poverqMul_eq`: `poverqMul t qs ps [a₀, a₁] [b₀, b₁]` is, coefficient by coefficient modulo
  `Q`, `⌊t·(A ⊗ W)ⱼ/P⌉`, where `Aᵢ = liftA qs aᵢ` (the representative in `[-Q/2, Q/2)`) and
  `Wᵢ = liftW qs ps bᵢ` (the representative in `[-P/2, P/2)` of `S/Q` modulo `P`,
  `S = Σ_q [−P·b·(Q/q)⁻¹]_q·(Q/q)`);
* `poverqMul_lifted`: with `Bᵢ = liftB qs ps bᵢ = (Q·Wᵢ − Sᵢ)/P`, the lists `A`, `B`,
  `X = (A ⊗ W).map ⌊t·/P⌉` satisfy the hypotheses of `Challenge.BFVMul.stepOK_mul_lifted` with
  `e`, `rho` those of `Spec.BudgetBFV.poverqSlack t N Q P k 0 0`:
  `A ≡ c`, `B ≡ d (mod Q)`, `2·‖Aᵢ‖∞, 2·‖Bᵢ‖∞ ≤ Q + ⌈2kQ/P⌉`,
  `2·|Q·Xⱼ − t·(A ⊗ B)ⱼ| ≤ Q·(1 + ⌈2tNkQ/P⌉)`, and `poverqMul … ≡ X (mod Q)`.

The scalar facts: `approx1_eq` (the fast conversion computes the residues of `S·Q⁻¹ mod P`),
`sVal_dvd`, `sVal_bounds`, `bVal_spec`, `bVal_dvd`, `bVal_bound` (the representative `B`), and
`round_combo` (the final inequality). The scaling formula is `FHE.BFV.MulHPS.scale1_eq` with the
two bases exchanged.
-/

namespace FHE.BFV.MulPOverQ
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.POverQ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS

/-! ### Lists and arithmetic -/

theorem sum_map_bounds {α : Type} (l : List α) (f : α → ℤ) (M : ℤ)
    (h : ∀ a ∈ l, 0 ≤ f a ∧ f a ≤ M) :
    0 ≤ (l.map f).sum ∧ (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := h a List.mem_cons_self
    obtain ⟨h3, h4⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor
    · linarith
    · linarith

theorem sum_map_modEq_mem {α : Type} (n : ℤ) (l : List α) (f g : α → ℤ)
    (h : ∀ a ∈ l, f a ≡ g a [ZMOD n]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa using Int.ModEq.add (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem le_ceilDiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ BudgetBFV.ceilDiv a b * b := by
  unfold BudgetBFV.ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : (a + b - 1) / b * b = b * ((a + b - 1) / b) := Nat.mul_comm _ _
  omega

/-- `invMod a m · a ≡ 1 (mod m)` for coprime `a`, `m`. -/
theorem invMod_mul_modEq (a m : ℕ) (hm : 0 < m) (h : Nat.Coprime a m) :
    invMod a m * (a : ℤ) ≡ 1 [ZMOD m] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [cast_invMod a m hm, mul_comm]
  exact ZMod.coe_mul_inv_eq_one a h

theorem coprime_prod_prod (qs ps : List ℕ) (hcop : (qs ++ ps).Pairwise Nat.Coprime) :
    Nat.Coprime qs.prod ps.prod := by
  have h := (List.pairwise_append.mp hcop).2.2
  exact Nat.coprime_list_prod_left_iff.mpr fun q hq =>
    Nat.coprime_list_prod_right_iff.mpr fun p hp => h q hq p hp

theorem pairwise_swap (qs ps : List ℕ) (hcop : (qs ++ ps).Pairwise Nat.Coprime) :
    (ps ++ qs).Pairwise Nat.Coprime := by
  obtain ⟨h1, h2, h3⟩ := List.pairwise_append.mp hcop
  exact List.pairwise_append.mpr ⟨h2, h1, fun p hp q hq => (h3 q hq p hp).symm⟩

/-! ### The fast scaling by `P/Q` -/

/-- `y_q = [x·(−P)·(Q/q)⁻¹]_q`, as `negPDigits` computes it from `x mod q`. -/
def yVal (qs : List ℕ) (P : ℕ) (x : ℤ) (q : ℕ) : ℤ :=
  x % q * (-((P : ℤ) * invMod (qs.prod / q) q) % q) % q

/-- `S = Σ_q y_q·(Q/q)`. -/
def sVal (qs : List ℕ) (P : ℕ) (x : ℤ) : ℤ :=
  (qs.map fun q => yVal qs P x q * ((qs.prod / q : ℕ) : ℤ)).sum

/-- The integer whose residues modulo `ps` the fast conversion computes: `S·[Q⁻¹]_P`. -/
def w0Val (qs ps : List ℕ) (x : ℤ) : ℤ := sVal qs ps.prod x * invMod qs.prod ps.prod

/-- `W`: the representative in `[-P/2, P/2)` of `S/Q` modulo `P`. -/
def wVal (qs ps : List ℕ) (x : ℤ) : ℤ := switchVal ps (w0Val qs ps x)

/-- `B = (Q·W − S)/P`. -/
def bVal (qs ps : List ℕ) (x : ℤ) : ℤ := (qs.prod * wVal qs ps x - sVal qs ps.prod x) / ps.prod

theorem negPDigits_map (qs : List ℕ) (P : ℕ) (x : ℤ) :
    negPDigits qs P (qs.map fun q : ℕ => x % q) = qs.map (yVal qs P x) :=
  zipWith_map_self _ _ _

/-- `S ≡ −P·x (mod Q)`. -/
theorem sVal_dvd (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime)
    (P : ℕ) (x : ℤ) : (qs.prod : ℤ) ∣ sVal qs P x - (-(P : ℤ) * x) :=
  crt_dvd qs hpos hcop (-(P : ℤ) * x) (yVal qs P x) fun q hq => by
    unfold yVal
    rw [ZMod.intCast_mod, Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_mod, Int.cast_neg,
      Int.cast_mul, cast_invMod _ _ (hpos q hq)]
    push_cast
    ring

/-- `0 ≤ S ≤ k·Q`. -/
theorem sVal_bounds (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (P : ℕ) (x : ℤ) :
    0 ≤ sVal qs P x ∧ sVal qs P x ≤ qs.length * (qs.prod : ℤ) := by
  refine sum_map_bounds qs _ _ fun q hq => ?_
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hpos q hq
  have h1 : 0 ≤ yVal qs P x q := Int.emod_nonneg _ hq0.ne'
  have h2 : yVal qs P x q < q := Int.emod_lt_of_pos _ hq0
  have h3 : (0 : ℤ) ≤ ((qs.prod / q : ℕ) : ℤ) := by positivity
  have h4 : (q : ℤ) * ((qs.prod / q : ℕ) : ℤ) = qs.prod := by
    exact_mod_cast Nat.mul_div_cancel' (List.dvd_prod hq)
  constructor
  · positivity
  · nlinarith

/-- **The fast conversion**: `approx1` on the digits of `x` is `S·[Q⁻¹]_P mod p`. -/
theorem approx1_eq (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (x : ℤ) (p : ℕ) (hp : p ∈ ps) :
    approx1 qs (qs.map (yVal qs ps.prod x)) p = w0Val qs ps x % p := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hP : 0 < ps.prod := prod_pos' ps hposp
  have hQP := coprime_prod_prod qs ps hcop
  have hpP : (p : ℤ) ∣ (ps.prod : ℤ) := by exact_mod_cast List.dvd_prod hp
  have hinv : invMod qs.prod ps.prod * (qs.prod : ℤ) ≡ 1 [ZMOD p] :=
    (invMod_mul_modEq _ _ hP hQP).of_dvd hpP
  unfold approx1 w0Val sVal
  rw [zipWith_map_self, ← List.sum_map_mul_right]
  show _ ≡ _ [ZMOD p]
  refine sum_map_modEq_mem _ _ _ _ fun q hq => ?_
  · have hqp : Nat.Coprime q p := (List.pairwise_append.mp hcop).2.2 q hq p hp
    have h1 := invMod_mul_modEq q p (hposp p hp) hqp
    have h4 : ((qs.prod / q : ℕ) : ℤ) * (q : ℤ) = qs.prod := by
      exact_mod_cast Nat.div_mul_cancel (List.dvd_prod hq)
    -- both `invMod q p` and `(Q/q)·invMod Q P` are inverses of `q` modulo `p`
    have h2 : ((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod * (q : ℤ) ≡ 1 [ZMOD p] := by
      have e : ((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod * (q : ℤ) =
          invMod qs.prod ps.prod * (qs.prod : ℤ) := by rw [← h4]; ring
      rw [e]; exact hinv
    have h3 : invMod q p ≡ ((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod [ZMOD p] := by
      have a1 := (h2.mul_left (invMod q p)).symm
      have a2 := h1.mul_right (((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod)
      rw [mul_one] at a1
      rw [one_mul] at a2
      refine a1.trans (Int.ModEq.trans ?_ a2)
      rw [show invMod q p * (((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod * (q : ℤ)) =
        invMod q p * (q : ℤ) * (((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod) by ring]
    have := h3.mul_left (yVal qs ps.prod x q)
    rw [show yVal qs ps.prod x q * ((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod =
      yVal qs ps.prod x q * (((qs.prod / q : ℕ) : ℤ) * invMod qs.prod ps.prod) by ring]
    exact this

/-! ### The representative `B` -/

theorem wVal_bounds (qs ps : List ℕ) (hP : 0 < ps.prod) (x : ℤ) :
    -(ps.prod : ℤ) ≤ 2 * wVal qs ps x ∧ 2 * wVal qs ps x < ps.prod :=
  switchVal_bounds ps hP _

/-- `Q·W = P·B + S`. -/
theorem bVal_spec (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (x : ℤ) :
    (qs.prod : ℤ) * wVal qs ps x = ps.prod * bVal qs ps x + sVal qs ps.prod x := by
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hP : 0 < ps.prod := prod_pos' ps hposp
  have hQP := coprime_prod_prod qs ps hcop
  have h1 : (ps.prod : ℤ) ∣ wVal qs ps x - w0Val qs ps x := switchVal_dvd ps hposp hcopp _
  have h2 := invMod_mul_modEq _ _ hP hQP
  have h3 : (ps.prod : ℤ) ∣ qs.prod * wVal qs ps x - sVal qs ps.prod x := by
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, hv⟩ := (Int.modEq_iff_dvd.mp h2.symm)
    refine ⟨qs.prod * u + sVal qs ps.prod x * v, ?_⟩
    have e : wVal qs ps x = w0Val qs ps x + ps.prod * u := by linarith
    rw [e]
    unfold w0Val
    linear_combination sVal qs ps.prod x * hv
  unfold bVal
  have := Int.mul_ediv_cancel' h3
  linarith

/-- `B ≡ x (mod Q)`. -/
theorem bVal_dvd (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (x : ℤ) : (qs.prod : ℤ) ∣ bVal qs ps x - x := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hQP : IsCoprime (qs.prod : ℤ) (ps.prod : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (coprime_prod_prod qs ps hcop)
  have h1 := bVal_spec qs ps hpos hcop x
  obtain ⟨u, hu⟩ := sVal_dvd qs hposq hcopq ps.prod x
  have h2 : (qs.prod : ℤ) ∣ (ps.prod : ℤ) * (bVal qs ps x - x) :=
    ⟨wVal qs ps x - u, by linear_combination -h1 - hu⟩
  exact hQP.dvd_of_dvd_mul_left h2

/-- `2·|B|·P ≤ P·Q + 2·k·Q`. -/
theorem bVal_bound (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (x : ℤ) :
    2 * |bVal qs ps x| * ps.prod ≤ (ps.prod : ℤ) * qs.prod + 2 * qs.length * qs.prod := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hP : 0 < ps.prod := prod_pos' ps hposp
  have hQ : (0 : ℤ) < qs.prod := by exact_mod_cast prod_pos' qs hposq
  have h1 := bVal_spec qs ps hpos hcop x
  obtain ⟨h2, h3⟩ := sVal_bounds qs hposq ps.prod x
  obtain ⟨h4, h5⟩ := wVal_bounds qs ps hP x
  have h6 : (qs.prod : ℤ) * (2 * wVal qs ps x) < qs.prod * ps.prod :=
    mul_lt_mul_of_pos_left h5 hQ
  have h7 : (qs.prod : ℤ) * (-(ps.prod : ℤ)) ≤ qs.prod * (2 * wVal qs ps x) :=
    mul_le_mul_of_nonneg_left h4 hQ.le
  rcases abs_cases (bVal qs ps x) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> nlinarith

/-! ### The final inequality -/

/-- From `Q·T' = P·T + E`, `2·|P·x − t·T'| ≤ P` (a rounding) and `2·t·|E| ≤ c·P·Q`:
`2·|Q·x − t·T| ≤ Q·(1 + c)`. -/
theorem round_combo (Q P t c x T' T E : ℤ) (hP : 0 < P) (hQ : 0 ≤ Q) (ht : 0 ≤ t)
    (h1 : Q * T' = P * T + E) (h2 : 2 * |P * x - t * T'| ≤ P)
    (h3 : 2 * (t * |E|) ≤ c * P * Q) : 2 * |Q * x - t * T| ≤ Q * (1 + c) := by
  have e : P * (Q * x - t * T) = Q * (P * x - t * T') + t * E := by linear_combination t * h1
  have h4 : |P * (Q * x - t * T)| ≤ Q * |P * x - t * T'| + t * |E| := by
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hQ, abs_of_nonneg ht]
  rw [abs_mul, abs_of_pos hP] at h4
  have h5 : Q * (2 * |P * x - t * T'|) ≤ Q * P := mul_le_mul_of_nonneg_left h2 hQ
  have h6 : P * (2 * |Q * x - t * T|) ≤ P * (Q * (1 + c)) := by nlinarith
  exact le_of_mul_le_mul_left h6 hP

/-! ### Polynomials -/

variable {N : ℕ}

/-- Operand 1 as the algorithm multiplies it: the representative in `[-Q/2, Q/2)`. -/
def liftA (qs : List ℕ) (a : IntPoly N) : IntPoly N := ⟨fun i => switchVal qs (a.coeff i)⟩

/-- Operand 2 after the scaling by `P/Q`: `W`. -/
def liftW (qs ps : List ℕ) (b : IntPoly N) : IntPoly N := ⟨fun i => wVal qs ps (b.coeff i)⟩

/-- Operand 2 as the algorithm multiplies it: `B = (Q·W − S)/P`. -/
def liftB (qs ps : List ℕ) (b : IntPoly N) : IntPoly N := ⟨fun i => bVal qs ps (b.coeff i)⟩

/-- The excess `S` of the fast conversion. -/
def liftS (qs ps : List ℕ) (b : IntPoly N) : IntPoly N := ⟨fun i => sVal qs ps.prod (b.coeff i)⟩

theorem toLimbs_congr (ms : List ℕ) (a b : IntPoly N)
    (h : ∀ m ∈ ms, ∀ i, ((m : ℕ) : ℤ) ∣ a.coeff i - b.coeff i) : toLimbs ms a = toLimbs ms b := by
  rw [toLimbs_eq, toLimbs_eq]
  refine List.map_congr_left fun m hm => ?_
  ext i
  show a.coeff i % m = b.coeff i % m
  exact Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp (h m hm i))

/-- **Exact extension**, with no oddness assumption: the limbs modulo `qs ++ ps` of `liftA`. -/
theorem expand_toLimbs' (qs ps : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (a : IntPoly N) :
    expand qs ps (toLimbs qs a) = toLimbs (qs ++ ps) (liftA qs a) := by
  unfold expand
  rw [switchBasis_toLimbs qs ps a (liftA qs a) (fun _ => rfl)]
  have e : toLimbs (qs ++ ps) (liftA qs a) = toLimbs qs (liftA qs a) ++ toLimbs ps (liftA qs a) :=
    List.map_append
  rw [e]
  congr 1
  refine (toLimbs_congr qs _ _ fun q hq i => ?_).symm
  exact dvd_trans (by exact_mod_cast List.dvd_prod hq) (switchVal_dvd qs hpos hcop _)

theorem fastExpand_def (qs ps ql : List ℕ) (x : List (IntPoly N)) :
    fastExpand qs ps ql x = switchBasis ps ql (fastScale qs ps x) ++ fastScale qs ps x := rfl

/-- **The fast expansion**: the limbs modulo `ql ++ ps` of `liftW` (`ql = qs` for
`poverqMul`). -/
theorem fastExpand_toLimbs (qs ps ql : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (b : IntPoly N) :
    fastExpand qs ps ql (toLimbs qs b) = toLimbs (ql ++ ps) (liftW qs ps b) := by
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have h1 : fastScale qs ps (toLimbs qs b) =
      toLimbs ps (⟨fun i => w0Val qs ps (b.coeff i)⟩ : IntPoly N) := by
    unfold fastScale
    rw [toLimbs_eq]
    refine List.map_congr_left fun p hp => ?_
    ext i
    show approx1 qs (negPDigits qs ps.prod (residues (toLimbs qs b) i)) p = _
    rw [residues_toLimbs, negPDigits_map, approx1_eq qs ps hpos hcop _ p hp]
  have h2 : toLimbs ps (⟨fun i => w0Val qs ps (b.coeff i)⟩ : IntPoly N) =
      toLimbs ps (liftW qs ps b) :=
    (toLimbs_congr ps _ _ fun p hp i =>
      dvd_trans (by exact_mod_cast List.dvd_prod hp) (switchVal_dvd ps hposp hcopp _)).symm
  have e : toLimbs (ql ++ ps) (liftW qs ps b) =
      toLimbs ql (liftW qs ps b) ++ toLimbs ps (liftW qs ps b) := List.map_append
  have h3 : switchBasis ps ql (toLimbs ps (⟨fun i => w0Val qs ps (b.coeff i)⟩ : IntPoly N)) =
      toLimbs ql (liftW qs ps b) :=
    switchBasis_toLimbs ps ql _ _ fun i => by
      show switchVal ps (w0Val qs ps (b.coeff i)) = wVal qs ps (b.coeff i)
      unfold wVal
      rfl
  rw [fastExpand_def, h1, h3, h2, e]

/-- **Scale and round**, any input and output bases: the limbs modulo `outs` of `⌊t·T/I⌉`. -/
theorem scaleRoundOut_toLimbs (t : ℕ) (ins outs : List ℕ) (hpos : ∀ m ∈ ins ++ outs, 0 < m)
    (hcop : (ins ++ outs).Pairwise Nat.Coprime) (T : IntPoly N) :
    scaleRoundOut t ins outs (toLimbs ins T) (toLimbs outs T) =
      toLimbs outs (Challenge.BFV.scaleRound t ins.prod T) := by
  unfold scaleRoundOut
  apply List.ext_getElem
  · simp [toLimbs_eq]
  · intro n h1 h2
    have hn : n < outs.length := by simpa [toLimbs_eq] using h2
    simp only [List.getElem_zipWith, toLimbs_eq, List.getElem_map]
    ext i
    show scale1 t ins outs (residues (toLimbs ins T) i) outs[n] (T.coeff i % outs[n]) =
      roundDiv (t * T.coeff i) ins.prod % outs[n]
    rw [residues_toLimbs]
    exact scale1_eq t ins outs hpos hcop (T.coeff i) ⟨n, hn⟩

/-- The definition of the locked `poverqAuxOK?`, by `rfl` (no equation lemma of the locked
definition is realised here). -/
theorem poverqAuxOK_def (t N : ℕ) (qs ps : List ℕ) :
    poverqAuxOK? t N qs ps =
      ((qs ++ ps).all (fun m => decide (0 < m)) && decide ((qs ++ ps).Pairwise Nat.Coprime)) :=
  rfl

theorem poverqAuxOK_iff (t N : ℕ) (qs ps : List ℕ) :
    poverqAuxOK? t N qs ps = true ↔
      (∀ m ∈ qs ++ ps, 0 < m) ∧ (qs ++ ps).Pairwise Nat.Coprime := by
  simp only [poverqAuxOK_def, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

/-- **What `poverqMul` computes**: `⌊t·(A ⊗ W)ⱼ/P⌉ mod Q`, with `A = liftA`, `W = liftW`. -/
theorem poverqMul_eq (t : ℕ) (qs ps : List ℕ) (haux : poverqAuxOK? t N qs ps = true)
    (a₀ a₁ b₀ b₁ : IntPoly N) :
    poverqMul t qs ps [a₀, a₁] [b₀, b₁] =
      (Challenge.Source.tensor [liftA qs a₀, liftA qs a₁] [liftW qs ps b₀, liftW qs ps b₁]).map
        fun T => modPoly qs.prod (Challenge.BFV.scaleRound t ps.prod T) := by
  obtain ⟨hpos, hcop⟩ := (poverqAuxOK_iff t N qs ps).mp haux
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hpos' : ∀ m ∈ ps ++ qs, 0 < m := fun m hm => hpos m (by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h)
  unfold poverqMul
  simp only [List.map_cons, List.map_nil, expand_toLimbs' qs ps hposq hcopq,
    fastExpand_toLimbs qs ps qs hpos hcop, tensor_toLimbs, List.map_map]
  refine List.map_congr_left fun T _ => ?_
  have e : toLimbs (qs ++ ps) T = toLimbs qs T ++ toLimbs ps T := List.map_append
  have hl : (toLimbs qs T).length = qs.length := List.length_map _
  show reconstruct qs (scaleRoundOut t ps qs ((toLimbs (qs ++ ps) T).drop qs.length)
    ((toLimbs (qs ++ ps) T).take qs.length)) = _
  rw [e, List.take_left' hl, List.drop_left' hl,
    scaleRoundOut_toLimbs t ps qs hpos' (pairwise_swap qs ps hcop),
    reconstruct_toLimbs qs hposq hcopq]

/-- Bilinearity of the negacyclic product, coefficient by coefficient: from
`q·w = p·b + s` coefficientwise, `q·(a·w) = p·(a·b) + a·s`. -/
theorem coeff_mul_combo (a w b s : IntPoly N) (q p : ℤ)
    (h : ∀ i, q * w.coeff i = p * b.coeff i + s.coeff i) (k : Fin N) :
    q * (a * w).coeff k = p * (a * b).coeff k + (a * s).coeff k := by
  simp only [coeff_mul', Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · linear_combination a.coeff i * h _
  · linear_combination -(a.coeff i) * h _

theorem two_normInf_le (p : IntPoly N) (M : ℕ) (h : ∀ i, 2 * |p.coeff i| ≤ (M : ℤ)) :
    2 * normInf p ≤ M := by
  have h' : normInf p ≤ M / 2 := (normInf_le_iff _ _).mpr fun i => Validation.BFV.abs_le_half (h i)
  omega

/-! ### The slack -/

/-- The lift excess of `poverqSlack` at zero tolerances is at least `2kQ/P`. -/
theorem slack_e (t N Q P k : ℕ) (hP : 0 < P) :
    2 * k * Q ≤ (BudgetBFV.poverqSlack t N Q P k 0 0).e * P := by
  have h := le_ceilDiv_mul (2 * Q * 0 * P + 2 * k * Q * BudgetBFV.floatDen)
    (BudgetBFV.floatDen * P) (Nat.mul_pos (by unfold BudgetBFV.floatDen; positivity) hP)
  have hF : 0 < BudgetBFV.floatDen := by unfold BudgetBFV.floatDen; positivity
  show 2 * k * Q ≤ BudgetBFV.ceilDiv (2 * Q * 0 * P + 2 * k * Q * BudgetBFV.floatDen)
    (BudgetBFV.floatDen * P) * P
  generalize BudgetBFV.ceilDiv (2 * Q * 0 * P + 2 * k * Q * BudgetBFV.floatDen)
    (BudgetBFV.floatDen * P) = c at h ⊢
  refine Nat.le_of_mul_le_mul_right ?_ hF
  calc 2 * k * Q * BudgetBFV.floatDen = 2 * Q * 0 * P + 2 * k * Q * BudgetBFV.floatDen := by ring
    _ ≤ c * (BudgetBFV.floatDen * P) := h
    _ = c * P * BudgetBFV.floatDen := by ring

/-- The rounding slack of `poverqSlack` at zero tolerances is `1 + c` with `c ≥ 2tNkQ/P`. -/
theorem slack_rho (t N Q P k : ℕ) (hP : 0 < P) :
    ∃ c : ℕ, (BudgetBFV.poverqSlack t N Q P k 0 0).rho = 1 + c ∧ 2 * t * N * k * Q ≤ c * P := by
  have hF : 0 < BudgetBFV.floatDen := by unfold BudgetBFV.floatDen; positivity
  refine ⟨BudgetBFV.ceilDiv (2 * 0 * P + 2 * t * N * k * Q * (BudgetBFV.floatDen + 2 * 0))
    (P * BudgetBFV.floatDen), rfl, ?_⟩
  have h := le_ceilDiv_mul (2 * 0 * P + 2 * t * N * k * Q * (BudgetBFV.floatDen + 2 * 0))
    (P * BudgetBFV.floatDen) (Nat.mul_pos hP hF)
  generalize BudgetBFV.ceilDiv (2 * 0 * P + 2 * t * N * k * Q * (BudgetBFV.floatDen + 2 * 0))
    (P * BudgetBFV.floatDen) = c at h ⊢
  refine Nat.le_of_mul_le_mul_right ?_ hF
  calc 2 * t * N * k * Q * BudgetBFV.floatDen =
        2 * 0 * P + 2 * t * N * k * Q * (BudgetBFV.floatDen + 2 * 0) := by ring
    _ ≤ c * (P * BudgetBFV.floatDen) := h
    _ = c * P * BudgetBFV.floatDen := by ring

/-- `round_combo` with the sizes of the P-over-Q multiplication: `|E| ≤ N·k·Q²` and
`2tNkQ ≤ c·P`. -/
theorem round_final (Q P t N k c : ℕ) (x T' T E : ℤ) (hP : 0 < P)
    (h1 : (Q : ℤ) * T' = P * T + E) (h2 : 2 * |(P : ℤ) * x - t * T'| ≤ P)
    (hE : |E| ≤ (N : ℤ) * k * Q * Q) (hc : 2 * t * N * k * Q ≤ c * P) :
    2 * |(Q : ℤ) * x - t * T| ≤ (Q : ℤ) * ((1 + c : ℕ) : ℤ) := by
  have hc' : (2 : ℤ) * t * N * k * Q ≤ c * P := by exact_mod_cast hc
  have h3 : 2 * ((t : ℤ) * |E|) ≤ (c : ℤ) * P * Q := by
    have a1 : (t : ℤ) * |E| ≤ t * ((N : ℤ) * k * Q * Q) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    have a2 : (2 : ℤ) * t * N * k * Q * Q ≤ c * P * Q :=
      mul_le_mul_of_nonneg_right hc' (by positivity)
    linarith
  have := round_combo Q P t c x T' T E (by exact_mod_cast hP) (by positivity) (by positivity)
    h1 h2 h3
  push_cast
  exact this

/-! ### The theorem -/

theorem ofInt_eq_of_dvd (Q : ℕ) (a b : IntPoly N) (h : ∀ i, (Q : ℤ) ∣ a.coeff i - b.coeff i) :
    ofInt Q a = ofInt Q b := by
  ext i
  show ((a.coeff i : ℤ) : ZMod Q) = ((b.coeff i : ℤ) : ZMod Q)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact dvd_sub_comm.mp (h i)

/-- The excess term of one product: `|(A·S)ᵢ| ≤ N·⌊Q_l/2⌋·k·Q` (`A` a representative modulo
`Q_l = ql.prod` in `[-Q_l/2, Q_l/2)`; `ql = qs` for `poverqMul`). -/
theorem abs_coeff_liftA_mul_liftS (ql qs ps : List ℕ) (hposl : ∀ q ∈ ql, 0 < q)
    (hposq : ∀ q ∈ qs, 0 < q) (a b : IntPoly N) (i : Fin N) :
    |(liftA ql a * liftS qs ps b).coeff i| ≤
      (N : ℤ) * ((ql.prod / 2 : ℕ) : ℤ) * (qs.length * (qs.prod : ℤ)) := by
  have hQ : 0 < ql.prod := prod_pos' ql hposl
  refine abs_coeff_mul_le_N _ _ _ _ (fun j => ?_) (fun j => ?_) i
  · obtain ⟨h1, h2⟩ := switchVal_bounds ql hQ (a.coeff j)
    refine Validation.BFV.abs_le_half ?_
    show 2 * |switchVal ql (a.coeff j)| ≤ (ql.prod : ℤ)
    rcases abs_cases (switchVal ql (a.coeff j)) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> omega
  · obtain ⟨h1, h2⟩ := sVal_bounds qs hposq ps.prod (b.coeff j)
    show |sVal qs ps.prod (b.coeff j)| ≤ _
    rw [abs_of_nonneg h1]
    exact h2

/-- **The idealised P-over-Q multiplication multiplies representatives of bounded size and rounds
within a bounded distance**: the hypotheses of `Challenge.BFVMul.stepOK_mul_lifted` at
`Q = qs.prod`, with the slack `Spec.BudgetBFV.poverqSlack t N Q P k 0 0`, `k = qs.length`. -/
theorem poverqMul_lifted (t : ℕ) (qs ps : List ℕ) (haux : poverqAuxOK? t N qs ps = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤
        qs.prod + (BudgetBFV.poverqSlack t N qs.prod ps.prod qs.length 0 0).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤
        qs.prod + (BudgetBFV.poverqSlack t N qs.prod ps.prod qs.length 0 0).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) * (BudgetBFV.poverqSlack t N qs.prod ps.prod qs.length 0 0).rho) ∧
      (poverqMul t qs ps c d).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨hpos, hcop⟩ := (poverqAuxOK_iff t N qs ps).mp haux
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  have hP : 0 < ps.prod := prod_pos' ps hposp
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  have he := slack_e t N qs.prod ps.prod qs.length hP
  obtain ⟨cc, hrho, hcc⟩ := slack_rho t N qs.prod ps.prod qs.length hP
  rw [hrho]
  generalize (BudgetBFV.poverqSlack t N qs.prod ps.prod qs.length 0 0).e = e at he ⊢
  -- sizes of the representatives
  have hAn : ∀ a : IntPoly N, 2 * normInf (liftA qs a) ≤ qs.prod + e := fun a =>
    two_normInf_le _ _ fun i => by
      obtain ⟨h1, h2⟩ := switchVal_bounds qs hQ (a.coeff i)
      show 2 * |switchVal qs (a.coeff i)| ≤ ((qs.prod + e : ℕ) : ℤ)
      rw [Nat.cast_add]
      rcases abs_cases (switchVal qs (a.coeff i)) with ⟨e', _⟩ | ⟨e', _⟩ <;> rw [e'] <;> omega
  have hBn : ∀ b : IntPoly N, 2 * normInf (liftB qs ps b) ≤ qs.prod + e := fun b =>
    two_normInf_le _ _ fun i => by
      have h1 := bVal_bound qs ps hpos hcop (b.coeff i)
      show 2 * |bVal qs ps (b.coeff i)| ≤ ((qs.prod + e : ℕ) : ℤ)
      have he' : (2 : ℤ) * qs.length * qs.prod ≤ e * ps.prod := by exact_mod_cast he
      have hP' : (0 : ℤ) < ps.prod := by exact_mod_cast hP
      rw [Nat.cast_add]
      have h2 : 2 * |bVal qs ps (b.coeff i)| * (ps.prod : ℤ) ≤ ((qs.prod : ℤ) + e) * ps.prod := by
        linarith
      exact le_of_mul_le_mul_right h2 hP'
  -- the rounding of one product, coefficient by coefficient
  have hW : ∀ (b : IntPoly N) (i : Fin N), (qs.prod : ℤ) * (liftW qs ps b).coeff i =
      (ps.prod : ℤ) * (liftB qs ps b).coeff i + (liftS qs ps b).coeff i := fun b i =>
    bVal_spec qs ps hpos hcop (b.coeff i)
  have hE := abs_coeff_liftA_mul_liftS (N := N) qs qs ps hposq hposq
  have hhalf : 2 * ((qs.prod / 2 : ℕ) : ℤ) ≤ qs.prod := two_mul_half_le _
  have hnn : (0 : ℤ) ≤ (N : ℤ) * (qs.length * (qs.prod : ℤ)) := by positivity
  have hE1 : ∀ (a b : IntPoly N) (i : Fin N), 2 * |(liftA qs a * liftS qs ps b).coeff i| ≤
      (N : ℤ) * qs.length * qs.prod * qs.prod := fun a b i => by
    have := hE a b i
    nlinarith [mul_le_mul_of_nonneg_left hhalf hnn]
  have hEnn : (0 : ℤ) ≤ (N : ℤ) * qs.length * qs.prod * qs.prod := by positivity
  refine ⟨[liftA qs a₀, liftA qs a₁], [liftB qs ps b₀, liftB qs ps b₁],
    (Challenge.Source.tensor [liftA qs a₀, liftA qs a₁] [liftW qs ps b₀, liftW qs ps b₁]).map
      (Challenge.BFV.scaleRound t ps.prod), rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [ofInt_eq_of_dvd _ (liftA qs a₀) a₀ fun i => switchVal_dvd qs hposq hcopq _,
      ofInt_eq_of_dvd _ (liftA qs a₁) a₁ fun i => switchVal_dvd qs hposq hcopq _]
  · simp only [List.map_cons, List.map_nil]
    rw [ofInt_eq_of_dvd _ (liftB qs ps b₀) b₀ fun i => bVal_dvd qs ps hpos hcop _,
      ofInt_eq_of_dvd _ (liftB qs ps b₁) b₁ fun i => bVal_dvd qs ps hpos hcop _]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hAn _
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hBn _
  · intro j i
    rcases j with _ | _ | _ | j
    · show 2 * |(qs.prod : ℤ) *
          roundDiv (t * (liftA qs a₀ * liftW qs ps b₀).coeff i) ps.prod -
        (t : ℤ) * (liftA qs a₀ * liftB qs ps b₀).coeff i| ≤ _
      refine round_final _ _ _ N qs.length cc _ _ _ _ hP
        (coeff_mul_combo _ _ _ _ _ _ (hW b₀) i)
        (Validation.BFV.two_abs_roundDiv_sub_le _ _ hP) ?_ hcc
      have := hE1 a₀ b₀ i
      have := abs_nonneg ((liftA qs a₀ * liftS qs ps b₀).coeff i)
      linarith
    · show 2 * |(qs.prod : ℤ) *
          roundDiv (t * (liftA qs a₀ * liftW qs ps b₁ + liftA qs a₁ * liftW qs ps b₀).coeff i)
            ps.prod -
        (t : ℤ) * (liftA qs a₀ * liftB qs ps b₁ + liftA qs a₁ * liftB qs ps b₀).coeff i| ≤ _
      refine round_final _ _ _ N qs.length cc _ _ _
        ((liftA qs a₀ * liftS qs ps b₁).coeff i + (liftA qs a₁ * liftS qs ps b₀).coeff i) hP ?_
        (Validation.BFV.two_abs_roundDiv_sub_le _ _ hP) ?_ hcc
      · rw [coeff_add', coeff_add', mul_add, mul_add,
          coeff_mul_combo _ _ _ _ _ _ (hW b₁) i, coeff_mul_combo _ _ _ _ _ _ (hW b₀) i]
        ring
      · have h1 := hE1 a₀ b₁ i
        have h2 := hE1 a₁ b₀ i
        have := abs_add_le ((liftA qs a₀ * liftS qs ps b₁).coeff i)
          ((liftA qs a₁ * liftS qs ps b₀).coeff i)
        linarith
    · show 2 * |(qs.prod : ℤ) *
          roundDiv (t * (liftA qs a₁ * liftW qs ps b₁).coeff i) ps.prod -
        (t : ℤ) * (liftA qs a₁ * liftB qs ps b₁).coeff i| ≤ _
      refine round_final _ _ _ N qs.length cc _ _ _ _ hP
        (coeff_mul_combo _ _ _ _ _ _ (hW b₁) i)
        (Validation.BFV.two_abs_roundDiv_sub_le _ _ hP) ?_ hcc
      have := hE1 a₁ b₁ i
      have := abs_nonneg ((liftA qs a₁ * liftS qs ps b₁).coeff i)
      linarith
    · show 2 * |(qs.prod : ℤ) * (0 : IntPoly N).coeff i - (t : ℤ) * (0 : IntPoly N).coeff i| ≤ _
      simp only [coeff_zero', mul_zero, sub_zero, abs_zero]
      positivity
  · rw [poverqMul_eq t qs ps haux, List.map_map, List.map_map]
    exact List.map_congr_left fun T _ => ofInt_modPoly _ _

end FHE.BFV.MulPOverQ
