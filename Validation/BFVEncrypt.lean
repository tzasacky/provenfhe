import Challenge.BFVEncrypt
import Validation.CertifyBFV
import Validation.BFV.PerInstr
import Validation.Certify
import Validation.FreshNoise.Basic
import Validation.FreshNoise.Tail
import Validation.FreshNoise.L2
import Validation.BFV.Core
import Validation.BFV.Sound

/-!
# Validation.BFVEncrypt — proofs of the pins of `Challenge.BFVEncrypt`

The encryption: the phase identity is BGV's (`Validation.FreshNoise.phase_encrypt`) at `t = 1`;
the noise is `freshError + (⌈Q·p/t⌉ − ⌊Q/t⌋·p)` and the second term lies in `[0, encodeDev]`.
The certificates: `certifyBFVFresh?` is `certifyBFV?` at the analysed parameters, whose inputs
are met by fresh encryptions within `fc.eps` (`inputsOK_of_fresh`); the rest is
`Validation.CertifyBFV.certifyBFV?_sound` and the tail bounds of `Validation.FreshNoise`, with the
union bound as in `Validation.Certify`.

No `Challenge.*` definition is unfolded with `simp`/`rw`/`unfold`: the `rfl` equations below give
the needed forms.
-/

namespace Validation.BFVEncrypt
open Spec NPoly Scheme Source Correct Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV
open Challenge.BFV Challenge.CertifyBFV Challenge.FreshNoise Challenge.FreshNoiseL2
open Challenge.BFVEncrypt MeasureTheory ProbabilityTheory
open Validation.Ring Validation.Scheme

variable {N : ℕ}

/-! ## 1. The encryption -/

theorem scaleUpCeil_coeff (t Q : ℕ) (p : IntPoly N) (i : Fin N) :
    (scaleUpCeil t Q p).coeff i =
      ((Q : ℤ) * p.coeff i + (-((Q : ℤ) * p.coeff i)) % (t : ℤ)) / (t : ℤ) := rfl

/-- `t·z = Q·p + [−Q·p]_t`. -/
theorem scaleUpCeil_mul (t Q : ℕ) (ht : 0 < t) (p : IntPoly N) (i : Fin N) :
    (t : ℤ) * (scaleUpCeil t Q p).coeff i =
      (Q : ℤ) * p.coeff i + (-((Q : ℤ) * p.coeff i)) % (t : ℤ) := by
  rw [scaleUpCeil_coeff]
  have hdvd : (t : ℤ) ∣ (Q : ℤ) * p.coeff i + (-((Q : ℤ) * p.coeff i)) % (t : ℤ) := by
    rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _),
      ← Int.add_emod, add_neg_cancel, Int.zero_emod]
  exact Int.mul_ediv_cancel' hdvd

theorem scaleUpCeil_spec (t Q : ℕ) (ht : 0 < t) (p : IntPoly N) (i : Fin N) :
    0 ≤ (t : ℤ) * (scaleUpCeil t Q p).coeff i - (Q : ℤ) * p.coeff i ∧
      (t : ℤ) * (scaleUpCeil t Q p).coeff i - (Q : ℤ) * p.coeff i < t := by
  have ht' : (0 : ℤ) < t := by exact_mod_cast ht
  rw [scaleUpCeil_mul t Q ht]
  have h0 := Int.emod_nonneg (-((Q : ℤ) * p.coeff i)) ht'.ne'
  have h1 := Int.emod_lt_of_pos (-((Q : ℤ) * p.coeff i)) ht'
  constructor <;> linarith

theorem scaleUpCeil_timesQovert (t Q q : ℕ) (ht : 0 < t) (hq : q ∣ Q) (hcop : Nat.Coprime t q)
    (p : IntPoly N) (i : Fin N) (hp0 : 0 ≤ p.coeff i) (hpq : p.coeff i < q) :
    (((scaleUpCeil t Q p).coeff i : ℤ) : ZMod q) =
      (((p.coeff i).toNat % q * (t - Q % t) % t : ℕ) : ZMod q) * (t : ZMod q)⁻¹ := by
  set P := p.coeff i with hP
  set z := (scaleUpCeil t Q p).coeff i with hz
  have hx : (P.toNat % q : ℕ) = P.toNat := Nat.mod_eq_of_lt (by omega)
  have hPn : ((P.toNat : ℕ) : ℤ) = P := Int.toNat_of_nonneg hp0
  have hr : Q % t < t := Nat.mod_lt Q ht
  -- the library's value equals `[−Q·p]_t` as an integer
  have hy : (((P.toNat % q * (t - Q % t) % t : ℕ)) : ℤ) = (-((Q : ℤ) * P)) % (t : ℤ) := by
    rw [hx]
    push_cast [Nat.cast_sub hr.le]
    rw [hPn]
    have hmod : P * ((t : ℤ) - (Q : ℤ) % (t : ℤ)) ≡ -((Q : ℤ) * P) [ZMOD (t : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-((Q : ℤ) / t * P) - P, ?_⟩
      have := Int.emod_add_mul_ediv (Q : ℤ) (t : ℤ)
      linear_combination P * this
    exact hmod
  -- in `ZMod q`: `t·z = Q·p + [−Q·p]_t ≡ [−Q·p]_t`
  have hzq : ((t : ZMod q)) * ((z : ℤ) : ZMod q) =
      (((P.toNat % q * (t - Q % t) % t : ℕ) : ℤ) : ZMod q) := by
    have h1 := scaleUpCeil_mul t Q ht p i
    rw [← hz, ← hP] at h1
    have h2 : (((t : ℤ) * z : ℤ) : ZMod q) =
        (((Q : ℤ) * P + (-((Q : ℤ) * P)) % (t : ℤ) : ℤ) : ZMod q) := by rw [h1]
    push_cast at h2
    rw [hy]
    have hQ0 : ((Q : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff Q q).mpr hq
    rw [hQ0, zero_mul, zero_add] at h2
    exact_mod_cast h2
  have hu : (t : ZMod q) * (t : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one t hcop
  have hcast : (((P.toNat % q * (t - Q % t) % t : ℕ) : ℤ) : ZMod q) =
      (((P.toNat % q * (t - Q % t) % t : ℕ)) : ZMod q) := Int.cast_natCast _
  rw [← hcast, ← hzq]
  calc ((z : ℤ) : ZMod q) = ((z : ℤ) : ZMod q) * ((t : ZMod q) * (t : ZMod q)⁻¹) := by
        rw [hu, mul_one]
    _ = (t : ZMod q) * ((z : ℤ) : ZMod q) * (t : ZMod q)⁻¹ := by ring

theorem encryptBFV_eq (t Q : ℕ) (b a p u e₁ e₂ : IntPoly N) :
    encryptBFV t Q b a p u e₁ e₂ = encrypt 1 b a (scaleUpCeil t Q p) u e₁ e₂ := rfl

theorem phase_encryptBFV (t Q : ℕ) (s e b a p u e₁ e₂ : IntPoly N)
    (hpk : PublicKeyOK 1 Q s e b a) :
    phase (ofInt Q s) ((encryptBFV t Q b a p u e₁ e₂).map (ofInt Q)) =
      ofInt Q (scaleUpCeil t Q p + freshError s e u e₁ e₂) := by
  rw [encryptBFV_eq, Validation.FreshNoise.phase_encrypt 1 Q s e b a _ u e₁ e₂ hpk]
  congr 1
  ext i
  simp

/-- The deterministic encoding term `⌈Q·p/t⌉ − ⌊Q/t⌋·p` lies in `[0, encodeDev t Q]` for
`p ∈ [0, t)`. -/
theorem encode_dev_bounds (t Q : ℕ) (ht : 0 < t) (p : IntPoly N) (i : Fin N)
    (hp0 : 0 ≤ p.coeff i) (hpt : p.coeff i ≤ (t : ℤ) - 1) :
    0 ≤ (scaleUpCeil t Q p).coeff i - ((Q / t : ℕ) : ℤ) * p.coeff i ∧
      (scaleUpCeil t Q p).coeff i - ((Q / t : ℕ) : ℤ) * p.coeff i ≤ (encodeDev t Q : ℤ) := by
  obtain ⟨h0, h1⟩ := scaleUpCeil_spec t Q ht p i
  have ht' : (0 : ℤ) < t := by exact_mod_cast ht
  have hQ : (Q : ℤ) = (t : ℤ) * (Q / t : ℕ) + (Q % t : ℕ) := by
    have := Nat.div_add_mod Q t
    exact_mod_cast this.symm
  have hr0 : (0 : ℤ) ≤ (Q % t : ℕ) := Int.natCast_nonneg _
  set z := (scaleUpCeil t Q p).coeff i
  set D : ℤ := ((Q / t : ℕ) : ℤ)
  set r : ℤ := ((Q % t : ℕ) : ℤ)
  set P := p.coeff i
  rw [hQ] at h0 h1
  -- `t·(z − D·P) = r·P + y` with `y ∈ [0, t)`
  have hd : (t : ℤ) * (z - D * P) = (t * z - (t * D + r) * P) + r * P := by ring
  have hrP : 0 ≤ r * P := mul_nonneg hr0 hp0
  have hrP' : r * P ≤ r * ((t : ℤ) - 1) := mul_le_mul_of_nonneg_left hpt hr0
  refine ⟨?_, ?_⟩
  · have : 0 ≤ (t : ℤ) * (z - D * P) := by rw [hd]; linarith
    by_contra hc
    push Not at hc
    have := mul_neg_of_pos_of_neg ht' hc
    linarith
  · have hlt : (t : ℤ) * (z - D * P) < r * ((t : ℤ) - 1) + t := by rw [hd]; linarith
    have hle : (z - D * P) * t ≤ r * ((t : ℤ) - 1) + ((t : ℤ) - 1) := by linarith
    have henc : (encodeDev t Q : ℤ) = (r * ((t : ℤ) - 1) + ((t : ℤ) - 1)) / t := by
      unfold encodeDev
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr ht.ne')]
      rfl
    rw [henc]
    exact (Int.le_ediv_iff_mul_le ht').mpr hle

theorem decOK_mono {t Q B B' : ℕ} (h : decOK t Q B' = true) (hB : B ≤ B') : decOK t Q B = true := by
  have e : ∀ X, decOK t Q X = decide (2 * (t * X + Q % t * (t - 1)) < Q) := fun _ => rfl
  rw [e] at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  have : t * B ≤ t * B' := Nat.mul_le_mul_left t hB
  omega

theorem encryptBFV_encrypts (t Q ε : ℕ) (ht : 2 ≤ t) (s e b a u e₁ e₂ : IntPoly N)
    (m : Poly t N) (hpk : PublicKeyOK 1 Q s e b a)
    (hε : normInf (freshError s e u e₁ e₂) ≤ ε) (hdec : decOK t Q (freshNoiseBFV t Q ε) = true) :
    BFVEncrypts t (freshNoiseBFV t Q ε) s
      ((encryptBFV t Q b a (liftMsg m) u e₁ e₂).map (ofInt Q)) m := by
  have ht0 : 0 < t := by omega
  have : NeZero t := ⟨by omega⟩
  have hQ : 0 < Q := by
    have e : decOK t Q (freshNoiseBFV t Q ε) =
        decide (2 * (t * freshNoiseBFV t Q ε + Q % t * (t - 1)) < Q) := rfl
    rw [e] at hdec
    simp only [decide_eq_true_eq] at hdec
    omega
  refine Validation.BFV.bfv_decrypt_of_noise t Q _ ht0 s _ m ?_ hdec
  -- the noise is `freshError + (⌈Q·p/t⌉ − ⌊Q/t⌋·p)`
  set p := liftMsg m
  set E : IntPoly N := freshError s e u e₁ e₂ +
    (scaleUpCeil t Q p - ⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩)
  have hφ : phase (ofInt Q s) ((encryptBFV t Q b a p u e₁ e₂).map (ofInt Q)) =
      ofInt Q (Validation.BFV.scaled t Q m + E) := by
    rw [phase_encryptBFV t Q s e b a p u e₁ e₂ hpk]
    congr 1
    ext i
    show (scaleUpCeil t Q p).coeff i + (freshError s e u e₁ e₂).coeff i =
      ((Q / t * (m.coeff i).val : ℕ) : ℤ) + ((freshError s e u e₁ e₂).coeff i +
        ((scaleUpCeil t Q p).coeff i - ((Q / t * (m.coeff i).val : ℕ) : ℤ)))
    ring
  have hE : ∀ i, |E.coeff i| ≤ (freshNoiseBFV t Q ε : ℤ) := by
    intro i
    have hpi : p.coeff i = ((m.coeff i).val : ℤ) := rfl
    have hv : (m.coeff i).val < t := ZMod.val_lt _
    obtain ⟨d0, d1⟩ := encode_dev_bounds t Q ht0 p i (by rw [hpi]; positivity)
      (by rw [hpi]; omega)
    have hf : |(freshError s e u e₁ e₂).coeff i| ≤ (ε : ℤ) := (normInf_le_iff _ _).mp hε i
    have hc : E.coeff i = (freshError s e u e₁ e₂).coeff i +
        ((scaleUpCeil t Q p).coeff i - ((Q / t : ℕ) : ℤ) * p.coeff i) := by
      show (freshError s e u e₁ e₂).coeff i +
          ((scaleUpCeil t Q p).coeff i - ((Q / t * (m.coeff i).val : ℕ) : ℤ)) = _
      rw [hpi]; push_cast; ring
    rw [hc]
    have hfn : ((freshNoiseBFV t Q ε : ℕ) : ℤ) = (ε : ℤ) + (encodeDev t Q : ℤ) := by
      unfold freshNoiseBFV; push_cast; ring
    rw [hfn]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg d0]
    linarith
  exact Validation.BFV.noiseLe_of_eq hQ E hφ hE

theorem encodeDev_needed :
    PublicKeyOK 1 100 (0 : IntPoly 1) 0 0 0 ∧ freshNoiseBFV 3 100 0 = 1 ∧
    BFVEncrypts 3 (freshNoiseBFV 3 100 0) (0 : IntPoly 1)
      ((encryptBFV 3 100 0 0 (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) 0 0 0).map (ofInt 100))
      ⟨fun _ => 2⟩ ∧
    ¬ BFVEncrypts 3 0 (0 : IntPoly 1)
      ((encryptBFV 3 100 0 0 (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) 0 0 0).map (ofInt 100))
      ⟨fun _ => 2⟩ := by
  have hpk : PublicKeyOK 1 100 (0 : IntPoly 1) 0 0 0 := by
    show ofInt 100 ((0 : IntPoly 1) + 0 * 0) = ofInt 100 (((1 : ℕ) : ℤ) • (0 : IntPoly 1))
    simp
  have hfe : freshError (0 : IntPoly 1) 0 0 0 0 = 0 := Validation.FreshNoise.freshError_zero
  refine ⟨hpk, rfl, ?_, ?_⟩
  · refine encryptBFV_encrypts 3 100 0 (by norm_num) 0 0 0 0 0 0 0 _ hpk ?_ (by decide)
    rw [hfe, normInf_zero]
  · rintro ⟨-, hn⟩
    have hφ := phase_encryptBFV 3 100 (0 : IntPoly 1) 0 0 0
      (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) 0 0 0 hpk
    rw [hφ, hfe] at hn
    have h1 := abs_coeff_le_normInf (centered (ofInt 100
      (scaleUpCeil 3 100 (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) + 0) -
      ofInt 100 ⟨fun i => ((100 / 3 * ((⟨fun _ => 2⟩ : Poly 3 1).coeff i).val : ℕ) : ℤ)⟩)) 0
    have h2 : (centered (ofInt 100
      (scaleUpCeil 3 100 (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) + 0) -
      ofInt 100 ⟨fun i => ((100 / 3 * ((⟨fun _ => 2⟩ : Poly 3 1).coeff i).val : ℕ) : ℤ)⟩)).coeff 0
        = 1 := by decide
    rw [h2, abs_one] at h1
    have : ((normInf (centered (ofInt 100
      (scaleUpCeil 3 100 (liftMsg (⟨fun _ => 2⟩ : Poly 3 1)) + 0) -
      ofInt 100 ⟨fun i => ((100 / 3 * ((⟨fun _ => 2⟩ : Poly 3 1).coeff i).val : ℕ) : ℤ)⟩)) : ℕ) : ℤ)
        ≤ 0 := by exact_mod_cast hn
    omega

/-! ## 2. The inputs -/

theorem freshOKBFV?_spec (prog : Program) (fresh : List Var) (h : freshOKBFV? prog fresh = true) :
    fresh ≠ [] ∧ (∀ x ∈ fresh, ∃ d ∈ prog.inputs, d.name = x) ∧
    ∀ d ∈ prog.inputs,
      (d.name ∈ fresh → d.parts = 2 ∧ d.key = 1 ∧ prog.boundOf d.name = none) ∧
      (d.name ∉ fresh → d.parts = 1) := by
  unfold freshOKBFV? at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hne, hin⟩, hall⟩ := h
  refine ⟨hne, hin, fun d hd => ?_⟩
  have := hall d hd
  by_cases hx : d.name ∈ fresh
  · simp only [hx, ite_true, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at this
    exact ⟨fun _ => ⟨this.1.1, this.1.2, this.2⟩, fun h => absurd hx h⟩
  · simp only [hx, ite_false, beq_iff_eq] at this
    exact ⟨fun h => absurd h hx, fun _ => this⟩

/-! ## 3. The certificate -/

/-- The analysed parameters. -/
abbrev params' (x : InputBFV) (fresh : List Var) (ε : ℕ) : FullParams :=
  { x.P with inputNoise := freshInputNoise x.P x.prog fresh ε }

theorem certifyAt?_eq (x : InputBFV) (fresh : List Var) (ε : ℕ) (used : Certify.NoiseUsed)
    (drift : ℕ) : certifyAt? x fresh ε used drift =
      (do guard (freshOKBFV? x.prog fresh)
          let c ← certifyBFV? { x with P := params' x fresh ε }
          pure (⟨params' x fresh ε, c, used, ε, drift⟩ : FreshCertBFV)) := rfl

theorem certifyAt?_some {x : InputBFV} {fresh : List Var} {ε : ℕ} {used : Certify.NoiseUsed}
    {drift : ℕ} {fc : FreshCertBFV} (h : certifyAt? x fresh ε used drift = some fc) :
    freshOKBFV? x.prog fresh = true ∧ fc.params = params' x fresh ε ∧
      certifyBFV? { x with P := params' x fresh ε } = some fc.cert ∧
      fc.used = used ∧ fc.eps = ε ∧ fc.drift = drift := by
  rw [certifyAt?_eq] at h
  cases hf : freshOKBFV? x.prog fresh
  · simp [hf, guard] at h
  · cases hc : certifyBFV? { x with P := params' x fresh ε } with
    | none => simp [hf, hc, guard] at h
    | some c =>
      simp [hf, hc, guard] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem certifyBFVFresh?_worst_eq (x : InputBFV) (fresh : List Var) (Bk Bu B1 B2 : ℕ) :
    certifyBFVFresh? x (.worst fresh Bk Bu B1 B2) =
      certifyAt? x fresh (worstError x.P.src.N x.P.secretBound Bk Bu B1 B2) .freshWorst 0 := rfl

theorem certifyBFVFresh?_kappa_eq (x : InputBFV) (fresh : List Var) (Bk Bu B1 B2 mn md κ : ℕ) :
    certifyBFVFresh? x (.kappa fresh Bk Bu B1 B2 mn md κ) =
      (do guard (0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
          guard (0 < md)
          let r := Certify.freshEps x.P fresh.length Bk Bu B1 B2 mn md κ
          certifyAt? x fresh r.1 r.2.1 r.2.2) := rfl

theorem certifyBFVFresh?_kappaL2_eq (x : InputBFV) (fresh : List Var)
    (E2 S2 Vu V1 V2 mn md κ : ℕ) :
    certifyBFVFresh? x (.kappaL2 fresh E2 S2 Vu V1 V2 mn md κ) =
      (do guard (0 < varProxyL2 E2 S2 Vu V1 V2)
          guard (0 < md)
          certifyAt? x fresh
            (epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ +
              meanDrift (E2 + 1 + S2) mn md) .freshKappaL2 (meanDrift (E2 + 1 + S2) mn md)) := rfl

theorem kappa_some {x : InputBFV} {fresh : List Var} {Bk Bu B1 B2 mn md κ : ℕ} {fc : FreshCertBFV}
    (h : certifyBFVFresh? x (.kappa fresh Bk Bu B1 B2 mn md κ) = some fc) :
    0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ 0 < md ∧
      certifyAt? x fresh (Certify.freshEps x.P fresh.length Bk Bu B1 B2 mn md κ).1
        (Certify.freshEps x.P fresh.length Bk Bu B1 B2 mn md κ).2.1
        (Certify.freshEps x.P fresh.length Bk Bu B1 B2 mn md κ).2.2 = some fc := by
  rw [certifyBFVFresh?_kappa_eq] at h
  by_cases h1 : 0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2
  · by_cases h2 : 0 < md
    · simp [h1, h2, guard] at h
      exact ⟨h1, h2, h⟩
    · simp [h2, guard] at h
  · simp [h1, guard] at h

theorem kappaL2_some {x : InputBFV} {fresh : List Var} {E2 S2 Vu V1 V2 mn md κ : ℕ}
    {fc : FreshCertBFV}
    (h : certifyBFVFresh? x (.kappaL2 fresh E2 S2 Vu V1 V2 mn md κ) = some fc) :
    0 < varProxyL2 E2 S2 Vu V1 V2 ∧ 0 < md ∧
      certifyAt? x fresh
        (epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ +
          meanDrift (E2 + 1 + S2) mn md) .freshKappaL2 (meanDrift (E2 + 1 + S2) mn md) =
        some fc := by
  rw [certifyBFVFresh?_kappaL2_eq] at h
  by_cases h1 : 0 < varProxyL2 E2 S2 Vu V1 V2
  · by_cases h2 : 0 < md
    · simp [h1, h2, guard] at h
      exact ⟨h1, h2, h⟩
    · simp [h2, guard] at h
  · simp [h1, guard] at h

/-- Every mode reduces to `certifyAt?` at `fc.eps`. -/
theorem mode_some {x : InputBFV} {mode : FreshModeBFV} {fc : FreshCertBFV}
    (h : certifyBFVFresh? x mode = some fc) :
    certifyAt? x mode.fresh fc.eps fc.used fc.drift = some fc := by
  cases mode with
  | worst fresh Bk Bu B1 B2 =>
    have h' := h
    rw [certifyBFVFresh?_worst_eq] at h'
    obtain ⟨-, -, -, hu, he, hd⟩ := certifyAt?_some h'
    show certifyAt? x fresh fc.eps fc.used fc.drift = some fc
    rw [hu, he, hd]; exact h'
  | kappa fresh Bk Bu B1 B2 mn md κ =>
    obtain ⟨-, -, h'⟩ := kappa_some h
    obtain ⟨-, -, -, hu, he, hd⟩ := certifyAt?_some h'
    show certifyAt? x fresh fc.eps fc.used fc.drift = some fc
    rw [hu, he, hd]; exact h'
  | kappaL2 fresh E2 S2 Vu V1 V2 mn md κ =>
    obtain ⟨-, -, h'⟩ := kappaL2_some h
    obtain ⟨-, -, -, hu, he, hd⟩ := certifyAt?_some h'
    show certifyAt? x fresh fc.eps fc.used fc.drift = some fc
    rw [hu, he, hd]; exact h'

theorem certifyBFVFresh?_spec (x : InputBFV) (mode : FreshModeBFV) (fc : FreshCertBFV)
    (h : certifyBFVFresh? x mode = some fc) :
    fc.params = { x.P with inputNoise := freshInputNoise x.P x.prog mode.fresh fc.eps } ∧
    freshOKBFV? x.prog mode.fresh = true ∧
    certifyBFV? { x with P := fc.params } = some fc.cert := by
  obtain ⟨hf, hp, hc, -, -, -⟩ := certifyAt?_some (mode_some h)
  exact ⟨hp, hf, by rw [hp]; exact hc⟩

theorem certifyBFVFresh?_worst_eps (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 : ℕ) (h : certifyBFVFresh? x (.worst fresh Bk Bu B1 B2) = some fc) :
    fc.eps = worstError x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ fc.used = .freshWorst ∧
      fc.drift = 0 := by
  rw [certifyBFVFresh?_worst_eq] at h
  obtain ⟨-, -, -, hu, he, hd⟩ := certifyAt?_some h
  exact ⟨he, hu, hd⟩

theorem certifyBFVFresh?_kappa_eps (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 mn md κ : ℕ) (h : certifyBFVFresh? x (.kappa fresh Bk Bu B1 B2 mn md κ) = some fc) :
    0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ 0 < md ∧
    ((fc.used = .freshKappa ∧
        fc.drift = meanDrift (x.P.src.N * Bk + 1 + x.P.src.N * x.P.secretBound) mn md ∧
        fc.eps = epsFor (varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
          (fresh.length * (2 * x.P.src.N)) κ + fc.drift ∧
        fc.eps < worstError x.P.src.N x.P.secretBound Bk Bu B1 B2) ∨
      (fc.used = .freshWorst ∧ fc.drift = 0 ∧
        fc.eps = worstError x.P.src.N x.P.secretBound Bk Bu B1 B2)) := by
  obtain ⟨h1, h2, h'⟩ := kappa_some h
  obtain ⟨-, -, -, hu, he, hd⟩ := certifyAt?_some h'
  refine ⟨h1, h2, ?_⟩
  have e : Certify.freshEps x.P fresh.length Bk Bu B1 B2 mn md κ =
      (let drift := Certify.freshDrift x.P Bk mn md
       let epsK := epsFor (varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
         (fresh.length * (2 * x.P.src.N)) κ + drift
       let worst := worstError x.P.src.N x.P.secretBound Bk Bu B1 B2
       if worst ≤ epsK then (worst, .freshWorst, 0) else (epsK, .freshKappa, drift)) := rfl
  have hdr : Certify.freshDrift x.P Bk mn md =
      meanDrift (x.P.src.N * Bk + 1 + x.P.src.N * x.P.secretBound) mn md := rfl
  rw [e] at hu he hd
  simp only at hu he hd
  split_ifs at hu he hd with hw
  · exact Or.inr ⟨hu, hd, he⟩
  · refine Or.inl ⟨hu, by rw [hd, hdr], by rw [he, hd], ?_⟩
    rw [he]; omega

theorem certifyBFVFresh?_kappaL2_eps (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (E2 S2 Vu V1 V2 mn md κ : ℕ)
    (h : certifyBFVFresh? x (.kappaL2 fresh E2 S2 Vu V1 V2 mn md κ) = some fc) :
    0 < varProxyL2 E2 S2 Vu V1 V2 ∧ 0 < md ∧ fc.used = .freshKappaL2 ∧
    fc.drift = meanDrift (E2 + 1 + S2) mn md ∧
    fc.eps = epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + fc.drift := by
  obtain ⟨h1, h2, h'⟩ := kappaL2_some h
  obtain ⟨-, -, -, hu, he, hd⟩ := certifyAt?_some h'
  exact ⟨h1, h2, hu, hd, by rw [he, hd]⟩

/-- The analysed parameters differ from the declared ones in the input noise only. -/
theorem params_src {x : InputBFV} {mode : FreshModeBFV} {fc : FreshCertBFV}
    (h : certifyBFVFresh? x mode = some fc) :
    fc.params.src = x.P.src ∧ fc.params.secretBound = x.P.secretBound := by
  obtain ⟨hp, -, -⟩ := certifyBFVFresh?_spec x mode fc h
  rw [hp]; exact ⟨rfl, rfl⟩

theorem le_foldl_max : ∀ (l : List ℕ) (i : ℕ), i ≤ l.foldl max i ∧ ∀ a ∈ l, a ≤ l.foldl max i
  | [], i => ⟨le_refl _, by simp⟩
  | b :: l, i => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max i b)
    refine ⟨le_trans (le_max_left _ _) h1, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_trans (le_max_right _ _) h1
    · exact h2 a ha

/-- **The deterministic core**: fresh encryptions with error at most `fc.eps` meet the input
hypothesis of `certifyBFV?_sound` at the analysed parameters. -/
theorem inputsOK_of_fresh (x : InputBFV) (mode : FreshModeBFV) (fc : FreshCertBFV)
    (h : certifyBFVFresh? x mode = some fc)
    (s e b a : IntPoly fc.params.src.N)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly fc.params.src.N)
    (hgood : ∀ y ∈ mode.fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ fc.eps)
    (m : Var → Poly fc.params.src.t fc.params.src.N) (cts : Var → List (IntPoly fc.params.src.N))
    (hin : FreshInputsBFV fc.params x.prog mode.fresh s b a u e₁ e₂ m cts) :
    TraceBFV.InputsOK fc.params s x.prog (fun y => .exact (m y)) cts := by
  obtain ⟨hpar, hfr, hc⟩ := certifyBFVFresh?_spec x mode fc h
  set x' : InputBFV := { x with P := fc.params }
  obtain ⟨hP, hk, -, -, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK x' fc.cert hc
  obtain ⟨-, -, -, -, hra, -⟩ := Validation.CertifyBFV.certifyBFV?_spec x' fc.cert hc
  obtain ⟨-, hallok, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hra
  have hspec := freshOKBFV?_spec x.prog mode.fresh hfr
  intro y d hd
  have hn : d.name = y := by simpa using List.find?_some hd
  have hmem : d ∈ x.prog.inputs := List.mem_of_find?_eq_some hd
  have hok : d.ok fc.params.src = true := List.all_eq_true.mp hallok d hmem
  have hd' := hspec.2.2 d hmem
  rw [hn] at hd'
  by_cases hy : y ∈ mode.fresh
  · obtain ⟨hparts, hkey, hbo⟩ := hd'.1 hy
    have hp1 : d.parts ≠ 1 := by omega
    rw [if_neg hp1]
    have ht : 2 ≤ fc.params.src.t := (hP.plaintext).1
    set Q := fc.params.src.modulus d.level
    have hpk' : PublicKeyOK 1 Q s e b a :=
      Validation.Source.ofInt_eq_of_dvd (Validation.FreshNoise.modulus_dvd_full _ d.level) hpk
    -- the analysed input noise covers this encryption's noise
    have hbound : TraceBFV.inputBound fc.params x.prog d = fc.params.inputNoise := by
      show ((x.prog.boundOf d.name).getD
        (if d.parts = 1 then fc.params.src.t - 1 else fc.params.inputNoise)) = _
      rw [hn, hbo, if_neg hp1]; rfl
    have hdec := Validation.CertifyBFV.certifyBFV?_inputs x' fc.cert hc d hmem hp1 hok
    rw [hbound] at hdec
    have hle : freshNoiseBFV fc.params.src.t Q fc.eps ≤ fc.params.inputNoise := by
      have hin' : fc.params.inputNoise = freshInputNoise x.P x.prog mode.fresh fc.eps := by
        rw [hpar]
      rw [hin']
      unfold freshNoiseBFV freshInputNoise
      have hsrc : fc.params.src = x.P.src := by rw [hpar]
      have hdm : d ∈ x.prog.inputs.filter fun d => d.name ∈ mode.fresh := by
        rw [List.mem_filter]; exact ⟨hmem, by rw [hn]; simpa using hy⟩
      have := (le_foldl_max ((x.prog.inputs.filter fun d => d.name ∈ mode.fresh).map
        fun d : Decl => encodeDev x.P.src.t (x.P.src.modulus d.level)) 0).2 _
        (List.mem_map_of_mem hdm)
      show _ + encodeDev fc.params.src.t (fc.params.src.modulus d.level) ≤ _
      rw [hsrc]
      omega
    have henc := encryptBFV_encrypts fc.params.src.t Q fc.eps ht s e b a (u y) (e₁ y) (e₂ y)
      (m y) hpk' (hgood y hy) (decOK_mono hdec hle)
    rw [Validation.BFV.SoundAux.encrypts_bfv_iff fc.params hk]
    have hct := hin.1 y hy d hd
    refine ⟨by rw [hct]; exact hparts.symm, m y, by show Msg.exact (m d.name) = _; rw [hn], ?_⟩
    show BFVEncrypts fc.params.src.t _ (automorph d.key s)
      ((cts y).map (ofInt (fc.params.src.modulus d.level))) (m y)
    rw [hkey, FHE.KeySwitch.automorph_one, hct, hbound]
    exact ⟨henc.1, henc.2.trans hle⟩
  · have hp1 : d.parts = 1 := hd'.2 hy
    rw [if_pos hp1]
    exact hin.2 y d hy hd

theorem certifyBFVFresh?_core (x : InputBFV) (mode : FreshModeBFV) (fc : FreshCertBFV)
    (h : certifyBFVFresh? x mode = some fc)
    (s e b a : IntPoly fc.params.src.N)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly fc.params.src.N)
    (hgood : ∀ y ∈ mode.fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ fc.eps)
    (m : Var → Poly fc.params.src.t fc.params.src.N) (cts : Var → List (IntPoly fc.params.src.N))
    (hin : FreshInputsBFV fc.params x.prog mode.fresh s b a u e₁ e₂ m cts) :
    OutputsCertifiedBFV fc.params fc.cert.budget x.prog fc.cert.outputs s
      (fun y => .exact (m y)) cts := by
  obtain ⟨-, -, hc⟩ := certifyBFVFresh?_spec x mode fc h
  exact Validation.CertifyBFV.certifyBFV?_sound { x with P := fc.params } fc.cert hc s _ cts
    (inputsOK_of_fresh x mode fc h s e b a hpk u e₁ e₂ hgood m cts hin)

theorem certifyBFVFresh?_worst (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 : ℕ) (h : certifyBFVFresh? x (.worst fresh Bk Bu B1 B2) = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : SecretOK fc.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly fc.params.src.N)
    (hrand : ∀ y ∈ fresh, normInf (u y) ≤ Bu ∧ normInf (e₁ y) ≤ B1 ∧ normInf (e₂ y) ≤ B2)
    (m : Var → Poly fc.params.src.t fc.params.src.N) (cts : Var → List (IntPoly fc.params.src.N))
    (hin : FreshInputsBFV fc.params x.prog fresh s b a u e₁ e₂ m cts) :
    OutputsCertifiedBFV fc.params fc.cert.budget x.prog fc.cert.outputs s
      (fun y => .exact (m y)) cts := by
  obtain ⟨heps, -, -⟩ := certifyBFVFresh?_worst_eps x fc fresh Bk Bu B1 B2 h
  obtain ⟨hsrc, hsB⟩ := params_src h
  refine certifyBFVFresh?_core x (.worst fresh Bk Bu B1 B2) fc h s e b a hpk u e₁ e₂
    (fun y hy => ?_) m cts hin
  have hN : fc.params.src.N = x.P.src.N := by rw [hsrc]
  rw [heps, ← hN, ← hsB]
  exact Validation.FreshNoise.freshError_worst s e (u y) (e₁ y) (e₂ y) fc.params.secretBound
    Bk Bu B1 B2 hs he (hrand y hy).1 (hrand y hy).2.1 (hrand y hy).2.2

/-- The failure event lies in the union of the events "the error of fresh input `y` exceeds
`fc.eps`". -/
theorem fails_sub (x : InputBFV) (mode : FreshModeBFV) (fc : FreshCertBFV)
    (h : certifyBFVFresh? x mode = some fc)
    (s e b a : IntPoly fc.params.src.N)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    {Ω : Type*} (u e₁ e₂ : Var → Ω → IntPoly fc.params.src.N) :
    {ω | FreshFailsBFV fc.params fc.cert.budget x.prog fc.cert.outputs mode.fresh s b a
      u e₁ e₂ ω} ⊆
      ⋃ y ∈ mode.fresh, {ω | ¬ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) ≤ fc.eps} := by
  intro ω hω
  by_contra hne
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hne
  obtain ⟨m, cts, hin, hno⟩ := hω
  exact hno (certifyBFVFresh?_core x mode fc h s e b a hpk (fun y => u y ω) (fun y => e₁ y ω)
    (fun y => e₂ y ω) hne m cts hin)

theorem certifyBFVFresh?_kappa (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (Bk Bu B1 B2 mn md κ : ℕ) (h : certifyBFVFresh? x (.kappa fresh Bk Bu B1 B2 mn md κ) = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : SecretOK fc.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly fc.params.src.N)
    (hsamp : ∀ y ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | FreshFailsBFV fc.params fc.cert.budget x.prog fc.cert.outputs fresh s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  obtain ⟨hV, hmd, hcase⟩ := certifyBFVFresh?_kappa_eps x fc fresh Bk Bu B1 B2 mn md κ h
  obtain ⟨hsrc, hsB⟩ := params_src h
  have hN : x.P.src.N = fc.params.src.N := by rw [hsrc]
  rw [hN, ← hsB] at hV hcase
  have hsub := fails_sub x (.kappa fresh Bk Bu B1 B2 mn md κ) fc h s e b a hpk u e₁ e₂
  have hP : SchemeParamsOK fc.params := by
    obtain ⟨-, -, hc⟩ := certifyBFVFresh?_spec x _ fc h
    exact (Validation.CertifyBFV.certifyBFV?_paramsOK _ fc.cert hc).1
  rcases hcase with ⟨-, hdr, heps, -⟩ | ⟨-, -, heps⟩
  · have hN0 : 0 < fc.params.src.N := by
      obtain ⟨k, hk'⟩ := hP.N_pow2
      rw [hk']; exact Nat.pos_of_ne_zero (by positivity)
    have hD := Validation.FreshNoise.meanDrift_spec
      (fc.params.src.N * Bk + 1 + fc.params.src.N * fc.params.secretBound) mn md hmd
    rw [← hdr] at hD
    have hsub2 : (⋃ y ∈ fresh,
        {ω | ¬ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) ≤ fc.eps}) ⊆
        ⋃ y ∈ fresh,
          {ω | ((epsFor (varProxy fc.params.src.N fc.params.secretBound Bk Bu B1 B2)
              (fresh.length * (2 * fc.params.src.N)) κ : ℕ) : ℝ) + (mn : ℝ) / md *
              ((fc.params.src.N * Bk + 1 + fc.params.src.N * fc.params.secretBound : ℕ) : ℝ) ≤
            (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ)} := by
      refine Set.iUnion₂_mono fun y _ ω hω => ?_
      have h1 : fc.eps ≤ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) :=
        (Nat.lt_of_not_le hω).le
      rw [heps] at h1
      have h2 : ((epsFor (varProxy fc.params.src.N fc.params.secretBound Bk Bu B1 B2)
          (fresh.length * (2 * fc.params.src.N)) κ : ℕ) : ℝ) + (fc.drift : ℝ) ≤
          (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ) := by exact_mod_cast h1
      show (_ : ℝ) ≤ _
      linarith
    have h1 := Validation.FreshNoise.measureReal_biUnion_list_le μ _ _ fresh fun y hy =>
        Validation.FreshNoise.freshError_tail μ hN0 s e fc.params.secretBound Bk Bu B1 B2 mn md
          hs he (u y) (e₁ y) (e₂ y) (hsamp y hy)
          ((epsFor (varProxy fc.params.src.N fc.params.secretBound Bk Bu B1 B2)
              (fresh.length * (2 * fc.params.src.N)) κ : ℕ) : ℝ) (Nat.cast_nonneg _)
    have h2 := Validation.FreshNoise.epsFor_spec
      (varProxy fc.params.src.N fc.params.secretBound Bk Bu B1 B2)
      (fresh.length * (2 * fc.params.src.N)) κ hV
    push_cast at h2
    refine (measureReal_mono (hsub.trans hsub2) (measure_ne_top μ _)).trans (h1.trans ?_)
    refine le_trans (le_of_eq ?_) h2
    ring
  · have hae : ∀ᵐ ω ∂μ, ∀ y ∈ fresh,
        normInf (u y ω) ≤ Bu ∧ normInf (e₁ y ω) ≤ B1 ∧ normInf (e₂ y ω) ≤ B2 :=
      Validation.Certify.ae_list μ _ fresh fun y hy =>
        Validation.Certify.sampler_bounds μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y) (hsamp y hy)
    have hnull : μ {ω | FreshFailsBFV fc.params fc.cert.budget x.prog fc.cert.outputs fresh s b a
        u e₁ e₂ ω} = 0 := by
      refine measure_mono_null hsub ?_
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with ω hω hmem
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
      obtain ⟨y, hy, hbad⟩ := hmem
      refine hbad ?_
      rw [heps]
      exact Validation.FreshNoise.freshError_worst s e (u y ω) (e₁ y ω) (e₂ y ω)
        fc.params.secretBound Bk Bu B1 B2 hs he (hω y hy).1 (hω y hy).2.1 (hω y hy).2.2
    rw [Measure.real, hnull]
    simp only [ENNReal.toReal_zero]
    positivity

theorem certifyBFVFresh?_kappaL2 (x : InputBFV) (fc : FreshCertBFV) (fresh : List Var)
    (E2 S2 Vu V1 V2 mn md κ : ℕ)
    (h : certifyBFVFresh? x (.kappaL2 fresh E2 S2 Vu V1 V2 mn md κ) = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly fc.params.src.N)
    (hsamp : ∀ y ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | FreshFailsBFV fc.params fc.cert.budget x.prog fc.cert.outputs fresh s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  obtain ⟨hV, hmd, -, hdr, heps⟩ := certifyBFVFresh?_kappaL2_eps x fc fresh E2 S2 Vu V1 V2 mn md κ h
  obtain ⟨hsrc, -⟩ := params_src h
  have hN : x.P.src.N = fc.params.src.N := by rw [hsrc]
  rw [hN] at heps
  have hP : SchemeParamsOK fc.params := by
    obtain ⟨-, -, hc⟩ := certifyBFVFresh?_spec x _ fc h
    exact (Validation.CertifyBFV.certifyBFV?_paramsOK _ fc.cert hc).1
  have hN0 : 0 < fc.params.src.N := by
    obtain ⟨k, hk'⟩ := hP.N_pow2
    rw [hk']; exact Nat.pos_of_ne_zero (by positivity)
  have hD := Validation.FreshNoise.meanDrift_spec (E2 + 1 + S2) mn md hmd
  rw [← hdr] at hD
  have hsub := fails_sub x (.kappaL2 fresh E2 S2 Vu V1 V2 mn md κ) fc h s e b a hpk u e₁ e₂
  have hsub2 : (⋃ y ∈ fresh,
      {ω | ¬ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) ≤ fc.eps}) ⊆
      ⋃ y ∈ fresh,
        {ω | ((epsFor (varProxyL2 E2 S2 Vu V1 V2)
              (fresh.length * (2 * fc.params.src.N)) κ : ℕ) : ℝ) + (mn : ℝ) / md *
              ((E2 + 1 + S2 : ℕ) : ℝ) ≤
          (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ)} := by
    refine Set.iUnion₂_mono fun y _ ω hω => ?_
    have h1 : fc.eps ≤ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) :=
      (Nat.lt_of_not_le hω).le
    rw [heps] at h1
    have h2 : ((epsFor (varProxyL2 E2 S2 Vu V1 V2)
        (fresh.length * (2 * fc.params.src.N)) κ : ℕ) : ℝ) + (fc.drift : ℝ) ≤
        (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ) := by exact_mod_cast h1
    show (_ : ℝ) ≤ _
    linarith
  have h1 := Validation.FreshNoise.measureReal_biUnion_list_le μ _ _ fresh fun y hy =>
      Validation.FreshNoiseL2.freshError_tail_l2 μ hN0 s e E2 S2 Vu V1 V2 mn md hs he
        (u y) (e₁ y) (e₂ y) (hsamp y hy)
        ((epsFor (varProxyL2 E2 S2 Vu V1 V2)
            (fresh.length * (2 * fc.params.src.N)) κ : ℕ) : ℝ) (Nat.cast_nonneg _)
  have h2 := Validation.FreshNoise.epsFor_spec (varProxyL2 E2 S2 Vu V1 V2)
    (fresh.length * (2 * fc.params.src.N)) κ hV
  push_cast at h2
  refine (measureReal_mono (hsub.trans hsub2) (measure_ne_top μ _)).trans (h1.trans ?_)
  refine le_trans (le_of_eq ?_) h2
  ring

theorem certifyBFVFresh?_run_exists (x : InputBFV) (mode : FreshModeBFV) (fc : FreshCertBFV)
    (h : certifyBFVFresh? x mode = some fc)
    (s e b a : IntPoly fc.params.src.N) (hs : SecretOK fc.params.secretBound s)
    (hpk : PublicKeyOK 1 (fc.params.src.modulus fc.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly fc.params.src.N)
    (hgood : ∀ y ∈ mode.fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ fc.eps)
    (m : Var → Poly fc.params.src.t fc.params.src.N) (cts : Var → List (IntPoly fc.params.src.N))
    (hin : FreshInputsBFV fc.params x.prog mode.fresh s b a u e₁ e₂ m cts) :
    ∃ σ, TraceBFV.RunAt fc.params fc.cert.budget s 0 x.prog.body
      (initEnv fc.params.src x.prog fun y => .exact (m y)) (Trace.initCt fc.params x.prog cts) σ := by
  obtain ⟨-, -, hc⟩ := certifyBFVFresh?_spec x mode fc h
  exact Validation.CertifyBFV.certifyBFV?_textbook_run_exists { x with P := fc.params } fc.cert hc
    s hs _ cts (inputsOK_of_fresh x mode fc h s e b a hpk u e₁ e₂ hgood m cts hin)

/-! ## 4. Discrimination -/

theorem certifyBFVFresh?_accepts_mulProg :
    (certifyBFVFresh? (tinyFresh 0) (.worst ["a", "b"] 2 1 2 2)).map
      (fun fc => (fc.params.inputNoise, fc.eps)) = some (27, 18) := by
  decide +kernel

theorem certifyBFVFresh?_rejects_declaredBound :
    (certifyBFVFresh? { tinyFresh 0 with prog := { mulProg with bounds := [("a", 0)] } }
      (.worst ["a", "b"] 2 1 2 2)).isSome = false := by
  decide +kernel

theorem certifyBFVFresh?_rejects_unnamedCiphertext :
    (certifyBFVFresh? (tinyFresh 0) (.worst ["a"] 2 1 2 2)).isSome = false := by
  decide +kernel

end Validation.BFVEncrypt
