import Challenge.BFV
import Validation.Source

/-!
# Validation.BFV.Core — BFV noise at the level of the phase: definitions and the carry lemma

`NoiseLe t B φ m` is the noise clause of `Spec.Scheme.BFVEncrypts` for a ciphertext with phase
`φ`: `‖[φ − ⌊Q/t⌋·m]_Q‖∞ ≤ B`, message representatives in `[0, t)`.

`noiseLe_intro` is the one fact every operation uses: if the phase is `Δ·M + e (mod Q)` for an
integer polynomial `M ≡ m (mod t)` whose coefficients lie in `[−κ·t, (κ+1)·t)`, then the noise is
at most `‖e‖∞ + (Q mod t)·κ`. (Reducing `M` modulo `t` subtracts `t·k` with `|k| ≤ κ`, and
`Δ·t = Q − (Q mod t)`.)
-/

namespace Validation.BFV
open Spec NPoly Scheme
open Validation.Ring Validation.Scheme

variable {N : ℕ}

/-- `⌊Q/t⌋·m` with `m`'s representatives in `[0, t)`, exactly as in `BFVEncrypts`. -/
def scaled (t Q : ℕ) (m : Poly t N) : IntPoly N :=
  ⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩

/-- The noise clause of `BFVEncrypts`, as a predicate on the phase. -/
def NoiseLe (t B : ℕ) {Q : ℕ} (φ : Poly Q N) (m : Poly t N) : Prop :=
  normInf (centered (φ - ofInt Q (scaled t Q m))) ≤ B

/-- A plaintext polynomial `p` (its phase modulo `Q`): congruent to `mp` modulo `t`, coefficients
of the centred lift at most `b`. This is `BGVEncrypts` on the phase. -/
def PlainLe (t b : ℕ) {Q : ℕ} (p : Poly Q N) (mp : Poly t N) : Prop :=
  ofInt t (centered p) = mp ∧ ∀ i, |(centered p).coeff i| ≤ b

theorem bfvEncrypts_iff {t B Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) :
    BFVEncrypts t B s ct m ↔ bfvDecrypt t s ct = m ∧ NoiseLe t B (phase (ofInt Q s) ct) m :=
  Iff.rfl

/-- `|[x]_Q| ≤ |x|` for the centred representative. -/
theorem abs_valMinAbs_intCast_le {Q : ℕ} (hQ : 0 < Q) (x : ℤ) :
    |((x : ZMod Q)).valMinAbs| ≤ |x| := by
  haveI : NeZero Q := ⟨hQ.ne'⟩
  have h := ZMod.natAbs_min_of_le_div_two Q ((x : ZMod Q)).valMinAbs x
    (by rw [ZMod.coe_valMinAbs]) (ZMod.natAbs_valMinAbs_le _)
  rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
  exact_mod_cast h

/-- The noise as an integer polynomial: the phase is `Δ·m̃ + e` with `‖e‖∞ ≤ B`. -/
theorem noiseLe_elim {t B Q : ℕ} {φ : Poly Q N} {m : Poly t N} (h : NoiseLe t B φ m) :
    ∃ e : IntPoly N, (∀ i, |e.coeff i| ≤ B) ∧ φ = ofInt Q (scaled t Q m + e) := by
  refine ⟨centered (φ - ofInt Q (scaled t Q m)), (normInf_le_iff _ _).mp h, ?_⟩
  rw [ofInt_add, ofInt_centered]
  ext i; simp

/-- If the phase is the reduction of `x` and `x − Δ·m̃` is bounded by `B`, the noise is at most
`B`. -/
theorem noiseLe_of_eq {t B Q : ℕ} (hQ : 0 < Q) {φ : Poly Q N} {m : Poly t N} (e : IntPoly N)
    (hφ : φ = ofInt Q (scaled t Q m + e)) (he : ∀ i, |e.coeff i| ≤ B) : NoiseLe t B φ m := by
  unfold NoiseLe
  rw [normInf_le_iff]
  intro i
  have : (φ - ofInt Q (scaled t Q m)).coeff i = ((e.coeff i : ℤ) : ZMod Q) := by
    rw [hφ, ofInt_add]; simp
  rw [coeff_centered, this]
  exact (abs_valMinAbs_intCast_le hQ _).trans (he i)

/-- **The carry lemma.** -/
theorem noiseLe_intro {t Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ : Poly Q N} {m : Poly t N}
    (M e : IntPoly N) (κ b : ℕ)
    (hφ : φ = ofInt Q (⟨fun i => ((Q / t : ℕ) : ℤ) * M.coeff i⟩ + e))
    (hm : ofInt t M = m)
    (hM : ∀ i, -((κ * t : ℕ) : ℤ) ≤ M.coeff i ∧ M.coeff i < (((κ + 1) * t : ℕ) : ℤ))
    (he : ∀ i, |e.coeff i| ≤ b) : NoiseLe t (b + Q % t * κ) φ m := by
  haveI : NeZero t := ⟨ht.ne'⟩
  have htz : (0 : ℤ) < t := by exact_mod_cast ht
  -- the quotient `k` of `M` by `t`
  have hval : ∀ i, ((m.coeff i).val : ℤ) = M.coeff i % t := by
    intro i
    have : m.coeff i = ((M.coeff i : ℤ) : ZMod t) := by rw [← hm]; rfl
    rw [this, ZMod.val_intCast]
  have hk : ∀ i, |M.coeff i / (t : ℤ)| ≤ κ := by
    intro i
    obtain ⟨h1, h2⟩ := hM i
    push_cast at h1 h2
    rw [abs_le]
    constructor
    · rw [Int.le_ediv_iff_mul_le htz]; linarith
    · have : M.coeff i / (t : ℤ) < κ + 1 := by
        rw [Int.ediv_lt_iff_lt_mul htz]; linarith
      linarith
  refine noiseLe_of_eq hQ
    ⟨fun i => e.coeff i - ((Q % t : ℕ) : ℤ) * (M.coeff i / (t : ℤ))⟩ ?_ ?_
  · rw [hφ]
    ext i
    simp only [coeff_ofInt, coeff_add', scaled]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-(M.coeff i / (t : ℤ)), ?_⟩
    have hdm := Int.emod_add_mul_ediv (M.coeff i) (t : ℤ)
    have hQd : ((Q / t : ℕ) : ℤ) * t + ((Q % t : ℕ) : ℤ) = Q := by
      exact_mod_cast Nat.div_add_mod' Q t
    simp only [Nat.cast_mul]
    rw [hval i]
    set k := M.coeff i / (t : ℤ)
    set μ := M.coeff i % (t : ℤ)
    have hM' : M.coeff i = μ + t * k := by linarith
    rw [hM']
    first | linear_combination (-k) * hQd | linear_combination k * hQd
  · intro i
    have h1 := he i
    have h2 := hk i
    have h3 : |((Q % t : ℕ) : ℤ) * (M.coeff i / (t : ℤ))| ≤ ((Q % t : ℕ) : ℤ) * κ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((Q % t : ℕ) : ℤ))]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    push_cast
    calc |e.coeff i - ((Q % t : ℕ) : ℤ) * (M.coeff i / (t : ℤ))|
        ≤ |e.coeff i| + |((Q % t : ℕ) : ℤ) * (M.coeff i / (t : ℤ))| := abs_sub _ _
      _ ≤ b + ((Q % t : ℕ) : ℤ) * κ := add_le_add h1 h3
      _ = _ := by push_cast; ring

end Validation.BFV
