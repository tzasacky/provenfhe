import FHE.RNS.Basis
import Spec.Params

/-!
# FHE.RNS.Params — RNS bases from `Spec` parameters

Under `Spec.ParamsOK` all moduli (ciphertext limbs and special limbs) are distinct odd primes,
so they form RNS bases:

* `levelBasis P hP ℓ h` — the basis `q₀, …, q_{ℓ-1}` of a ciphertext at level `ℓ`, with
  product `P.src.modulus ℓ` (`levelBasis_prod`); `dropLast` of level `ℓ+1` is level `ℓ`
  (`levelBasis_dropLast`, by `rfl`) and its last modulus is `qs[ℓ]` (`levelBasis_last`);
* `specialBasis P hP` — the special moduli `p₀, …` of hybrid key switching, each coprime to every
  `qᵢ` (`special_coprime`);
* `t_coprime_q`, `t_coprime_special` — the plaintext modulus is coprime to every modulus
  (BGV/BFV).
-/

namespace FHE.RNS

open Spec

variable (P : FullParams) (hP : ParamsOK P)
include hP

theorem allLimbs_q_coprime : (P.allLimbs.map (·.q)).Pairwise Nat.Coprime :=
  Basis.pairwise_coprime_of_prime_nodup
    (by simpa using fun lp h => hP.prime lp h) hP.distinct

theorem qs_eq : P.src.qs = P.store.limbs.map (·.q) := hP.limbs_match.symm

theorem qs_pairwise_coprime : P.src.qs.Pairwise Nat.Coprime := by
  have h := allLimbs_q_coprime P hP
  rw [FullParams.allLimbs, List.map_append, List.pairwise_append] at h
  rw [qs_eq P hP]; exact h.1

theorem qs_pos : ∀ q ∈ P.src.qs, 0 < q := by
  intro q hq
  rw [qs_eq P hP, List.mem_map] at hq
  obtain ⟨lp, hlp, rfl⟩ := hq
  exact (hP.prime lp (List.mem_append_left _ hlp)).pos

theorem special_pairwise_coprime : (P.store.special.map (·.q)).Pairwise Nat.Coprime := by
  have h := allLimbs_q_coprime P hP
  rw [FullParams.allLimbs, List.map_append, List.pairwise_append] at h
  exact h.2.1

theorem special_pos : ∀ q ∈ P.store.special.map (·.q), 0 < q := by
  intro q hq
  rw [List.mem_map] at hq
  obtain ⟨lp, hlp, rfl⟩ := hq
  exact (hP.prime lp (List.mem_append_right _ hlp)).pos

/-- The basis of a ciphertext at level `ℓ`. -/
def levelBasis (ℓ : ℕ) (h : ℓ ≤ P.src.qs.length) : Basis ℓ :=
  Basis.take P.src.qs ℓ h (qs_pos P hP) (qs_pairwise_coprime P hP)

theorem levelBasis_prod (ℓ : ℕ) (h : ℓ ≤ P.src.qs.length) :
    (levelBasis P hP ℓ h).prod = P.src.modulus ℓ :=
  Basis.take_prod _ _ _ _ _

theorem levelBasis_dropLast (ℓ : ℕ) (h : ℓ + 1 ≤ P.src.qs.length) :
    (levelBasis P hP (ℓ + 1) h).dropLast = levelBasis P hP ℓ (by omega) := rfl

theorem levelBasis_last (ℓ : ℕ) (h : ℓ + 1 ≤ P.src.qs.length) :
    (levelBasis P hP (ℓ + 1) h).last = P.src.qs[ℓ] := rfl

/-- The special basis `p₀, …` (hybrid key switching). -/
def specialBasis : Basis (P.store.special.map (·.q)).length :=
  Basis.ofList _ (special_pos P hP) (special_pairwise_coprime P hP)

theorem specialBasis_prod : (specialBasis P hP).prod = (P.store.special.map (·.q)).prod :=
  Basis.ofList_prod _ _ _

/-- Every special modulus is coprime to every ciphertext modulus. -/
theorem special_coprime {p q : ℕ} (hp : p ∈ P.store.special.map (·.q)) (hq : q ∈ P.src.qs) :
    Nat.Coprime p q := by
  have h := allLimbs_q_coprime P hP
  rw [FullParams.allLimbs, List.map_append, List.pairwise_append] at h
  rw [qs_eq P hP] at hq
  exact (h.2.2 q hq p hp).symm

/-- `P = ∏ pⱼ` is coprime to every ciphertext modulus. -/
theorem specialProd_coprime {q : ℕ} (hq : q ∈ P.src.qs) :
    Nat.Coprime (specialBasis P hP).prod q :=
  Nat.coprime_prod_left_iff.mpr fun _ _ => special_coprime P hP (List.getElem_mem _) hq

theorem t_coprime_q {q : ℕ} (hq : q ∈ P.src.qs) :
    Nat.Coprime P.src.t q := by
  rw [qs_eq P hP, List.mem_map] at hq
  obtain ⟨lp, hlp, rfl⟩ := hq
  exact hP.plaintext.2 lp (List.mem_append_left _ hlp)

theorem t_coprime_special {p : ℕ}
    (hp : p ∈ P.store.special.map (·.q)) : Nat.Coprime P.src.t p := by
  rw [List.mem_map] at hp
  obtain ⟨lp, hlp, rfl⟩ := hp
  exact hP.plaintext.2 lp (List.mem_append_right _ hlp)

end FHE.RNS
