import Challenge.Sanity.Conventions
import Validation.BFVDecrypt.Main
import Validation.Scheme.Basic

/-!
# Validation.Sanity.Conventions — proofs of the pins of `Challenge.Sanity.Conventions`
-/

namespace Validation.Sanity
open Spec NPoly Scheme Correct Validation.Scheme

variable {N : ℕ}

theorem roundDiv_eq_floor (a : ℤ) (b : ℕ) (hb : 0 < b) :
    roundDiv a b = ⌊(a : ℚ) / b + 1 / 2⌋ := Validation.BFVDecrypt.roundDiv_eq a b hb

/-- Shifting the argument by a multiple of `Q` shifts `⌊t·a/Q⌉` by `t·k`. -/
theorem roundDiv_shift (t Q : ℕ) (hQ : 0 < Q) (c k : ℤ) :
    roundDiv (t * (c + Q * k)) Q = roundDiv (t * c) Q + t * k := by
  show (2 * (t * (c + Q * k)) + (Q : ℤ)) / (2 * Q) = (2 * (t * c) + Q) / (2 * Q) + t * k
  have h2 : (2 * (Q : ℤ)) ≠ 0 := by positivity
  rw [show 2 * ((t : ℤ) * (c + Q * k)) + Q = (2 * (t * c) + Q) + (t * k) * (2 * Q) by ring,
    Int.add_mul_ediv_right _ _ h2]

theorem bfvDecrypt_any_lift (t Q : ℕ) (hQ : 0 < Q) (s : IntPoly N) (ct : List (Poly Q N))
    (a : IntPoly N) (ha : ofInt Q a = phase (ofInt Q s) ct) :
    bfvDecrypt t s ct = ⟨fun i => (roundDiv (t * a.coeff i) Q : ZMod t)⟩ := by
  ext i
  show (roundDiv (t * (centeredPhase s ct).coeff i) Q : ZMod t) = (roundDiv (t * a.coeff i) Q : ZMod t)
  have hc : (((centeredPhase s ct).coeff i : ℤ) : ZMod Q) = (a.coeff i : ZMod Q) := by
    have h1 : ((phase (ofInt Q s) ct).coeff i).valMinAbs = (centeredPhase s ct).coeff i := rfl
    have h2 : (a.coeff i : ZMod Q) = (phase (ofInt Q s) ct).coeff i := by
      rw [← ha]; rfl
    rw [h2, ← h1, ZMod.coe_valMinAbs]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hc
  have : a.coeff i = (centeredPhase s ct).coeff i + Q * k := by linarith
  rw [this, roundDiv_shift t Q hQ]
  push_cast
  simp

theorem bfvDecrypt_canonical (t Q : ℕ) (hQ : 0 < Q) (s : IntPoly N) (ct : List (Poly Q N)) :
    bfvDecrypt t s ct =
      ⟨fun i => (roundDiv (t * ((canonical (phase (ofInt Q s) ct)).coeff i : ℤ)) Q : ZMod t)⟩ := by
  have : NeZero Q := ⟨hQ.ne'⟩
  refine bfvDecrypt_any_lift t Q hQ s ct ⟨fun i => ((canonical (phase (ofInt Q s) ct)).coeff i : ℤ)⟩ ?_
  ext i
  show (((((phase (ofInt Q s) ct).coeff i).val : ℕ) : ℤ) : ZMod Q) = _
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem encrypts_mono (P : FullParams) (s : IntPoly P.src.N) (B B' : ℕ) (hB : B ≤ B')
    (v : Source.Val P.src) (ct : List (IntPoly P.src.N)) (h : Encrypts P s B v ct) :
    Encrypts P s B' v ct := by
  rcases v with ⟨⟨m⟩, parts, level, key, scale⟩
  obtain ⟨hl, h⟩ := h
  refine ⟨hl, ?_⟩
  revert h
  show (match P.src.kind, Source.Msg.exact m with
    | .bgv, .exact m => BGVEncrypts P.src.t B _ _ m
    | .bfv, .exact m => BFVEncrypts P.src.t B _ _ m) →
    (match P.src.kind, Source.Msg.exact m with
    | .bgv, .exact m => BGVEncrypts P.src.t B' _ _ m
    | .bfv, .exact m => BFVEncrypts P.src.t B' _ _ m)
  cases P.src.kind with
  | bgv => exact fun h => ⟨h.1, le_trans h.2 hB⟩
  | bfv => exact fun h => ⟨h.1, le_trans h.2 hB⟩

theorem encrypts_msg_unique (P : FullParams) (s : IntPoly P.src.N) (B B' : ℕ)
    (v v' : Source.Val P.src) (ct : List (IntPoly P.src.N)) (hl : v.level = v'.level)
    (hk : v.key = v'.key) (h : Encrypts P s B v ct) (h' : Encrypts P s B' v' ct) :
    v.msg = v'.msg := by
  rcases v with ⟨⟨m⟩, parts, level, key, scale⟩
  rcases v' with ⟨⟨m'⟩, parts', level', key', scale'⟩
  simp only at hl hk
  subst hl hk
  obtain ⟨-, h⟩ := h
  obtain ⟨-, h'⟩ := h'
  revert h h'
  show (match P.src.kind, Source.Msg.exact m with
    | .bgv, .exact m => BGVEncrypts P.src.t B _ _ m
    | .bfv, .exact m => BFVEncrypts P.src.t B _ _ m) →
    (match P.src.kind, Source.Msg.exact m' with
    | .bgv, .exact m => BGVEncrypts P.src.t B' _ _ m
    | .bfv, .exact m => BFVEncrypts P.src.t B' _ _ m) → _
  cases P.src.kind with
  | bgv => exact fun h h' => by rw [← h.1, ← h'.1]
  | bfv => exact fun h h' => by rw [← h.1, ← h'.1]

theorem natAbs_vma_add_le (Q : ℕ) (z : ZMod Q) (w : ℤ) :
    ((z + (w : ZMod Q)).valMinAbs).natAbs ≤ z.valMinAbs.natAbs + w.natAbs := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · exact Int.natAbs_add_le z w
  · have : NeZero Q := ⟨hQ.ne'⟩
    have hX := ZMod.natAbs_valMinAbs_le (z + (w : ZMod Q))
    have he : (((z + (w : ZMod Q)).valMinAbs : ℤ) : ZMod Q) = ((z.valMinAbs + w : ℤ) : ZMod Q) := by
      push_cast; simp only
    exact (ZMod.natAbs_min_of_le_div_two Q _ _ he hX).trans (Int.natAbs_add_le _ _)

theorem bfvEncrypts_centred_noise (t B Q : ℕ) (ht : 0 < t) (s : IntPoly N) (ct : List (Poly Q N))
    (m : Poly t N) (h : BFVEncrypts t B s ct m) :
    normInf (centered (phase (ofInt Q s) ct -
      ofInt Q ⟨fun i => ((Q / t : ℕ) : ℤ) * (m.coeff i).valMinAbs⟩)) ≤ B + Q % t := by
  have : NeZero t := ⟨ht.ne'⟩
  obtain ⟨-, h2⟩ := h
  unfold normInf at h2 ⊢
  rw [Finset.sup_le_iff] at h2 ⊢
  intro i _
  have hx := h2 i (Finset.mem_univ _)
  set φ := phase (ofInt Q s) ct
  set z := (φ - ofInt Q ⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩).coeff i with hz
  -- the two subtrahends differ by `⌊Q/t⌋·(val − valMinAbs)`, which is `0` or `⌊Q/t⌋·t`
  have hd : (m.coeff i).val - (m.coeff i).valMinAbs = 0 ∨
      ((m.coeff i).val : ℤ) - (m.coeff i).valMinAbs = t := by
    rw [ZMod.valMinAbs_def_pos]
    split_ifs <;> simp
  have hcoef : (φ - ofInt Q ⟨fun i => ((Q / t : ℕ) : ℤ) * (m.coeff i).valMinAbs⟩).coeff i =
      z + ((((Q / t : ℕ) : ℤ) * (((m.coeff i).val : ℤ) - (m.coeff i).valMinAbs) : ℤ) : ZMod Q) := by
    rw [hz]
    show φ.coeff i - ((((Q / t : ℕ) : ℤ) * (m.coeff i).valMinAbs : ℤ) : ZMod Q) =
      (φ.coeff i - (((Q / t * (m.coeff i).val : ℕ) : ℤ) : ZMod Q)) + _
    push_cast; ring
  show ((φ - ofInt Q ⟨fun i => ((Q / t : ℕ) : ℤ) * (m.coeff i).valMinAbs⟩).coeff i).valMinAbs.natAbs
    ≤ B + Q % t
  rw [hcoef]
  rcases hd with hd | hd
  · rw [show ((m.coeff i).val : ℤ) - (m.coeff i).valMinAbs = 0 by exact_mod_cast hd]
    simp only [mul_zero, Int.cast_zero, add_zero]
    exact le_trans hx (Nat.le_add_right _ _)
  · rw [hd]
    have hw : ((((Q / t : ℕ) : ℤ) * t : ℤ) : ZMod Q) = (((-(Q % t : ℕ) : ℤ)) : ZMod Q) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      refine ⟨-1, ?_⟩
      have := Nat.div_add_mod Q t
      push_cast
      have h' : ((t : ℤ) * ((Q / t : ℕ) : ℤ) + ((Q % t : ℕ) : ℤ)) = Q := by exact_mod_cast this
      push_cast at h'
      linarith
    rw [hw]
    refine le_trans (natAbs_vma_add_le Q z _) ?_
    have : (-((Q % t : ℕ) : ℤ)).natAbs = Q % t := by rw [Int.natAbs_neg, Int.natAbs_natCast]
    rw [this]
    exact Nat.add_le_add_right hx _

example := (@roundDiv_eq_floor : type_of% @Challenge.Sanity.roundDiv_eq_floor)
example := (@bfvDecrypt_any_lift : type_of% @Challenge.Sanity.bfvDecrypt_any_lift)
example := (@bfvDecrypt_canonical : type_of% @Challenge.Sanity.bfvDecrypt_canonical)
example := (@bfvEncrypts_centred_noise : type_of% @Challenge.Sanity.bfvEncrypts_centred_noise)
example := (@encrypts_mono : type_of% @Challenge.Sanity.encrypts_mono)
example := (@encrypts_msg_unique : type_of% @Challenge.Sanity.encrypts_msg_unique)

end Validation.Sanity
