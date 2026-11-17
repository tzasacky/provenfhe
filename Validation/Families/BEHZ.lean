import Challenge.Families.BEHZ
import Validation.BFVMul.BEHZ
import Validation.BFV.Params
import Mathlib.Data.Nat.Size

/-!
# Validation.Families.BEHZ — proofs of the pins of `Challenge.Families.BEHZ`

`behzAuxOK_sealRule` goes through the characterisation `FHE.BFV.MulBEHZ.behzAuxOK_iff`:
coprimality from distinct primes, `2³²` coprime to odd moduli, and the size condition from
`32·t·N·Q ≤ B·m_sk` with `k ≤ Q`, `2(k−1) ≤ 2³²` and `m_sk ≤ 2·(m_sk − 1 − 2|B|)`. The
contract statements are `Validation.BFVMul.stepOK_mul_behz`, `stepOK_square_behz` at
`m̃ = 2³²`. The closed facts at `sealBFV` are kernel computations (`decide +kernel`). No locked
definition is unfolded by name.
-/

namespace Validation.Families
open Spec NPoly Scheme Source Challenge.BFV Challenge.BFVMul Challenge.Families

theorem sealRule_of_bits (t n Q Bm : ℕ) (h : 5 + Nat.size t + n + Nat.size Q ≤ Nat.size Bm - 1) :
    32 * t * 2 ^ n * Q ≤ Bm := by
  have ht : t < 2 ^ Nat.size t := Nat.lt_size_self t
  have hQ : Q < 2 ^ Nat.size Q := Nat.lt_size_self Q
  have hB : 2 ^ (Nat.size Bm - 1) ≤ Bm := Nat.lt_size.mp (by omega)
  calc 32 * t * 2 ^ n * Q ≤ 2 ^ 5 * 2 ^ Nat.size t * 2 ^ n * 2 ^ Nat.size Q := 
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) ht.le) le_rfl) hQ.le
    _ = 2 ^ (5 + Nat.size t + n + Nat.size Q) := by rw [pow_add, pow_add, pow_add]
    _ ≤ 2 ^ (Nat.size Bm - 1) := Nat.pow_le_pow_right (by norm_num) h
    _ ≤ Bm := hB

/-- A list of moduli at least `2` has at most as many elements as its product. -/
theorem length_le_prod (l : List ℕ) (h : ∀ q ∈ l, 2 ≤ q) : l.length ≤ l.prod ∧ 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 2 ≤ a := h a (by simp)
    obtain ⟨h1, h2⟩ := ih fun q hq => h q (by simp [hq])
    simp only [List.length_cons, List.prod_cons]
    constructor <;> nlinarith

theorem behzAuxOK_sealRule (t N : ℕ) (qs bs : List ℕ) (msk : ℕ) (ht : 1 ≤ t) (hN : 1 ≤ N)
    (hprime : ∀ m ∈ qs ++ bs ++ [msk], Nat.Prime m)
    (hodd : ∀ m ∈ qs ++ bs ++ [msk], m % 2 = 1)
    (hnd : (qs ++ bs ++ [msk]).Nodup)
    (hk : qs.length ≤ 2 ^ 31) (hmsk : 4 * bs.length + 2 ≤ msk)
    (hsize : 32 * t * N * qs.prod ≤ bs.prod * msk) :
    behzAuxOK? t N qs bs msk (2 ^ 32) = true := by
  have hcop2 : ∀ m ∈ qs ++ bs ++ [msk], Nat.Coprime (2 ^ 32) m := fun m hm =>
    Nat.Coprime.pow_left 32 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (hodd m hm)))
  have hqs : ∀ q ∈ qs, q ∈ qs ++ bs ++ [msk] := fun q hq => by simp [hq]
  -- the size condition
  obtain ⟨hkQ, -⟩ := length_le_prod qs fun q hq => (hprime q (hqs q hq)).two_le
  have hX : qs.length ≤ t * N * qs.prod := by
    have : 1 ≤ t * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc qs.length ≤ qs.prod := hkQ
      _ = 1 * qs.prod := (one_mul _).symm
      _ ≤ t * N * qs.prod := Nat.mul_le_mul_right _ this
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hK : 2 ^ 32 + 2 * (qs.length - 1) ≤ 2 * 2 ^ 32 := by omega
  have hsq : (2 ^ 32 + 2 * (qs.length - 1)) ^ 2 ≤ 4 * (2 ^ 32) ^ 2 := by
    calc (2 ^ 32 + 2 * (qs.length - 1)) ^ 2 ≤ (2 * 2 ^ 32) ^ 2 := Nat.pow_le_pow_left hK 2
      _ = 4 * (2 ^ 32) ^ 2 := by ring
  have hR : msk ≤ 2 * (msk - 1 - 2 * bs.length) := by omega
  have hsize' : 32 * (t * N * qs.prod) ≤ bs.prod * (2 * (msk - 1 - 2 * bs.length)) := by
    calc 32 * (t * N * qs.prod) = 32 * t * N * qs.prod := by ring
      _ ≤ bs.prod * msk := hsize
      _ ≤ bs.prod * (2 * (msk - 1 - 2 * bs.length)) := Nat.mul_le_mul_left _ hR
  have hmain : t * N * qs.prod * (2 ^ 32 + 2 * (qs.length - 1)) ^ 2 +
      2 * qs.length * (2 ^ 32) ^ 2 ≤
      (2 ^ 32) ^ 2 * bs.prod * (msk - 1 - 2 * bs.length) := by
    generalize t * N * qs.prod = X at hX hsize'
    generalize (2 ^ 32 + 2 * (qs.length - 1)) ^ 2 = S at hsq
    generalize ((2 : ℕ) ^ 32) ^ 2 = M at hsq ⊢
    generalize msk - 1 - 2 * bs.length = R at hsize'
    generalize bs.prod = B at hsize'
    have e1 : X * S ≤ X * (4 * M) := Nat.mul_le_mul_left _ hsq
    have e2 : 2 * qs.length * M ≤ 2 * X * M := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hX)
    have e3 : 32 * X * M ≤ B * (2 * R) * M := by
      calc 32 * X * M = 32 * (X) * M := rfl
        _ ≤ B * (2 * R) * M := Nat.mul_le_mul_right _ hsize'
    nlinarith
  refine (FHE.BFV.MulBEHZ.behzAuxOK_iff t N qs bs msk (2 ^ 32)).mpr
    ⟨fun m hm => (hprime m hm).pos, ?_, hcop2, by omega, hmain, by omega, ?_, by norm_num,
      by norm_num⟩
  · exact hnd.imp_of_mem fun ha hb hne => (Nat.coprime_primes (hprime _ ha) (hprime _ hb)).mpr hne
  · exact Nat.coprime_list_prod_right_iff.mpr fun q hq => hcop2 q (hqs q hq)

variable (P : FullParams)

theorem stepOK_mul_behz_sealRule (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (bs : List ℕ) (msk : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length (2 ^ 32)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ht : 1 ≤ P.src.t) (hN : 1 ≤ P.src.N)
    (hprime : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], Nat.Prime m)
    (hodd : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], m % 2 = 1)
    (hnd : (P.src.qs.take x.level ++ bs ++ [msk]).Nodup)
    (hk : x.level ≤ 2 ^ 31) (hmsk : 4 * bs.length + 2 ≤ msk)
    (hsize : 32 * P.src.t * P.src.N * (P.src.qs.take x.level).prod ≤ bs.prod * msk) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk (2 ^ 32) ca cb)) (.mul d a b) :=
  Validation.BFVMul.stepOK_mul_behz P hP E s hs ρ ρ' σ d a b x y ca cb bs msk (2 ^ 32) hL hR
    hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL
    (behzAuxOK_sealRule _ _ _ bs msk ht hN hprime hodd hnd
      ((List.length_take_le _ _).trans hk) hmsk hsize)

theorem stepOK_square_behz_sealRule (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (bs : List ℕ) (msk : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length (2 ^ 32)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ht : 1 ≤ P.src.t) (hN : 1 ≤ P.src.N)
    (hprime : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], Nat.Prime m)
    (hodd : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], m % 2 = 1)
    (hnd : (P.src.qs.take x.level ++ bs ++ [msk]).Nodup)
    (hk : x.level ≤ 2 ^ 31) (hmsk : 4 * bs.length + 2 ≤ msk)
    (hsize : 32 * P.src.t * P.src.N * (P.src.qs.take x.level).prod ≤ bs.prod * msk) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk (2 ^ 32) ca ca)) (.square d a) :=
  Validation.BFVMul.stepOK_square_behz P hP E s hs ρ ρ' σ d a x ca bs msk (2 ^ 32) hL hR
    hstep hx ha hla h2x hℓ hℓL
    (behzAuxOK_sealRule _ _ _ bs msk ht hN hprime hodd hnd
      ((List.length_take_le _ _).trans hk) hmsk hsize)

theorem sealBFV_behzAuxOK : ∀ ℓ ∈ [1, 2, 3, 4],
    behzAuxOK? sealBFV.src.t sealBFV.src.N (sealBFV.src.qs.take ℓ) (sealAuxB ℓ) sealMsk (2 ^ 32)
      = true := by
  decide +kernel

theorem sealBFV_sealRule : ∀ ℓ ∈ [1, 2, 3, 4],
    5 + Nat.size sealBFV.src.t + 13 + Nat.size (sealBFV.src.qs.take ℓ).prod ≤
        Nat.size ((sealAuxB ℓ).prod * sealMsk) - 1 ∧
      32 * sealBFV.src.t * sealBFV.src.N * (sealBFV.src.qs.take ℓ).prod ≤
        (sealAuxB ℓ).prod * sealMsk := by
  decide +kernel

theorem stepOK_mul_behz_sealBFV (E : TraceBFV.Budget)
    (s : IntPoly sealBFV.src.N) (hs : SecretOK sealBFV.secretBound s) (ρ ρ' : Env sealBFV.src)
    (σ : Trace.CtEnv sealBFV) (d a b : Var) (x y : Val sealBFV.src)
    (ca cb : List (IntPoly sealBFV.src.N))
    (hL : BudgetBFV.mulLiftNormAt sealBFV x.level
            (BudgetBFV.behzSlack sealBFV.src.t sealBFV.src.N (sealBFV.src.modulus x.level)
              (sealAuxB x.level).prod sealMsk x.level (sealAuxB x.level).length (2 ^ 32)).e
          ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox sealBFV (2 * x.level) ≤ E.mulRound)
    (hstep : step sealBFV.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ sealBFV.src.qs.length) :
    TraceBFV.StepOK sealBFV E s ρ ρ' σ
      (σ.set d (behzMul sealBFV.src.t (sealBFV.src.qs.take x.level) (sealAuxB x.level) sealMsk
        (2 ^ 32) ca cb)) (.mul d a b) := by
  have hlen : sealBFV.src.qs.length = 4 := by decide +kernel
  have hmem : x.level ∈ [1, 2, 3, 4] := by
    rw [hlen] at hℓL
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  exact Validation.BFVMul.stepOK_mul_behz sealBFV Validation.BFV.sealBFV_ok E s hs ρ ρ' σ d a b
    x y ca cb (sealAuxB x.level) sealMsk (2 ^ 32) hL hR hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL
    (sealBFV_behzAuxOK x.level hmem)

theorem openfhe_behzOK :
    (behzAuxOK? 65537 8192 openfheQs8 openfheAuxB8 openfheMsk8 (2 ^ 16) &&
      behzWordOK? 65537 8192 openfheQs8 openfheAuxB8 openfheMsk8 (2 ^ 16)) = true ∧
    (behzAuxOK? 68718428161 16384 openfheQs16 openfheAuxB16 openfheMsk16 (2 ^ 16) &&
      behzWordOK? 68718428161 16384 openfheQs16 openfheAuxB16 openfheMsk16 (2 ^ 16)) = true := by
  decide +kernel

end Validation.Families
