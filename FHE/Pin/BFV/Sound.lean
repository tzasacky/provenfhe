import FHE.Pin.Sound
import Spec.TraceBFV

/-!
# FHE.Pin.BFV.Sound — the deciding mirrors of the BFV contracts, with soundness proofs
(UNTRUSTED glue; the theorems are kernel-checked)

The BFV counterpart of `FHE.Pin.Sound`:

* `stepOKb` decides the phase contract `Spec.TraceBFV.StepOK` of one instruction on forced phases
  (`FHE.Pin.Ph`). The existentials of the contract are instantiated by computed witnesses:
  `δ := centered (φ − (φ_a ± Δ·φ_p))` for `addPlain`/`subPlain`, `e := centered (φ − φ_a)` for
  `relin`/`keySwitch`, `δ := q·Φ' − Φ_a` for `modSwitch`, and for `mul`/`square` the lifts `k_a`,
  `k_b` are *supplied by the caller* (arrays `ka`, `kb`, untrusted), `X` is the representative of
  `φ` nearest to `t·A·B/Q` and `D := Q·X − t·A·B`. `stepOKb_sound`: a verdict `some true` with the
  default `Hooks` is a proof of `StepOK`, for arbitrary `ka`, `kb`.
* `inputCtOKb`, `inputPtOKb`, `inputOKb` decide the input hypothesis of one input
  (`Spec.Correct.Encrypts` for BFV, `Spec.TraceBFV.PlainOK`); `noiseA` is the measured noise of
  `BFVEncrypts` and `decryptBFVA` the forced `Spec.Scheme.bfvDecrypt`.

Only soundness is proved: a `false` verdict says that *these* witnesses fail.
-/

namespace FHE.Pin.BFV
open Spec Spec.NPoly Spec.Scheme Spec.Source Validation.Scheme Validation.Ring FHE.Pin

/-- Mutation hooks; the default record is the trusted contract. -/
structure Hooks where
  /-- Δ of `addPlain`/`subPlain`: `Q / t`. -/
  delta : ℕ → ℕ → ℕ := fun Q t => Q / t
  /-- The factor `t` of the scale-invariant product. -/
  tfac : ℕ → ℤ := fun t => (t : ℤ)
  /-- The bound tested for `mul`'s rounding term: `2·‖D‖ ≤ Q · mulRound`. -/
  roundOK : ℕ → ℕ → ℕ → Bool := fun normD Q mulRound => decide (2 * normD ≤ Q * mulRound)
  /-- The negacyclic product over `ℤ` (of `mul`, `square`, `mulPlain`), as an array of `N`
  coefficients (`FHE.Pin.mulArr`, Kronecker substitution; an array, so that the compiled code
  computes it once). -/
  mul : {N : ℕ} → IntPoly N → IntPoly N → Array ℤ := fun a b => mulArr a b

/-- The forced centred lift modulo `Q` of an integer array. -/
def centredZ (N K Q : ℕ) (z : Array ℤ) : Array ℤ :=
  toArr K (centered (ofInt Q (ofArr (N := N) z)))

/-- The lift `Φ + Q·k` of the contract of `mul`, forced; `z` is any integer representative of
the operand's phase. -/
def liftA (N K Q : ℕ) (z k : Array ℤ) : Array ℤ :=
  toArr K (centered (ofInt Q (ofArr (N := N) z)) + (Q : ℤ) • ofArr k)

/-- `T := tfac · (A · B)`, forced (the product is materialised first). -/
def prodA (N K : ℕ) (h : Hooks) (t : ℕ) (A B : Array ℤ) : Array ℤ :=
  let AB := h.mul (ofArr (N := N) A) (ofArr B)
  toArr K (h.tfac t • ofArr (N := N) AB)

/-- The witness `X` of `mul`: the representative `Φd + Q·m` of the result's phase nearest to
`T / Q`, with `m_j := ⌊(T_j − Q·Φd_j) / Q²⌉`. -/
def mulXA (N K Q : ℕ) (Φd T : Array ℤ) : Array ℤ :=
  toArr K (ofArr (N := N) Φd + (Q : ℤ) • (⟨fun j =>
    roundDiv ((ofArr (N := N) T).coeff j - (Q : ℤ) * (ofArr (N := N) Φd).coeff j) (Q * Q)⟩ :
      IntPoly N))

/-- The witness `D := Q·X − T` of `mul`. -/
def mulDA (N K Q : ℕ) (X T : Array ℤ) : Array ℤ :=
  toArr K ((Q : ℤ) • ofArr (N := N) X - ofArr T)

/-- The witness `D` of the product of the phases with integer representatives `xZ`, `yZ` and
lifts `ka`, `kb`, for the result phase representative `dZ` (the caller may print its norm). -/
def mulWitD (N K : ℕ) (h : Hooks) (Q t : ℕ) (dZ xZ yZ ka kb : Array ℤ) : Array ℤ :=
  let T := prodA N K h t (liftA N K Q xZ ka) (liftA N K Q yZ kb)
  mulDA N K Q (mulXA N K Q (centredZ N K Q dZ) T) T

/-- The decision of the `mul`/`square` clause. -/
def mulOKb (N K : ℕ) (h : Hooks) (E : TraceBFV.Budget) (Q t : ℕ) (dZ xZ yZ ka kb : Array ℤ) :
    Bool :=
  decide (normA N ka ≤ E.mulLift) && decide (normA N kb ≤ E.mulLift) &&
    h.roundOK (normA N (mulWitD N K h Q t dZ xZ yZ ka kb)) Q E.mulRound

/-- **The decision of the BFV `e.step`.** The conjuncts of `Spec.TraceBFV.StepOK` about phases,
for the destination phase `d` (at level `vLevel`) of instruction `i`; `get` gives the phase and
the number of components of an operand; `ka`, `kb` are the lift witnesses of `mul` (first and
second operand) and `square` (`ka` only), ignored otherwise. `none`: an operand has no ciphertext
data (or, for `modSwitch`, the operand's level has no last modulus). -/
def stepOKb (P : FullParams) (E : TraceBFV.Budget) (K : ℕ) (h : Hooks) (i : Instr) (vLevel : ℕ)
    (d : Ph) (get : Var → Option (Ph × ℕ)) (ka kb : Array ℤ) : Option Bool :=
  let N := P.src.N
  let Q := P.src.modulus vLevel
  let t := P.src.t
  let φ : Array (ZMod Q) := toArr K (ofInt Q (ofArr (N := N) d.Z))
  let eqv : Poly Q N → Bool := fun rhs => toArr K rhs == φ
  match i with
  | .add _ a b =>
    (get a).bind fun x => (get b).map fun y => eqv (ofInt Q (ofArr x.1.Z) + ofInt Q (ofArr y.1.Z))
  | .sub _ a b =>
    (get a).bind fun x => (get b).map fun y => eqv (ofInt Q (ofArr x.1.Z) - ofInt Q (ofArr y.1.Z))
  | .addPlain _ a b =>
    (get a).bind fun x => (get b).map fun y =>
      let δ := toArr K (centered (ofInt Q (ofArr (N := N) d.Z) -
        (ofInt Q (ofArr x.1.Z) + ((h.delta Q t : ℕ) : ZMod Q) • ofInt Q (ofArr y.1.Z))))
      decide (normA N δ ≤ E.plainAdd)
  | .subPlain _ a b =>
    (get a).bind fun x => (get b).map fun y =>
      let δ := toArr K (centered (ofInt Q (ofArr (N := N) d.Z) -
        (ofInt Q (ofArr x.1.Z) - ((h.delta Q t : ℕ) : ZMod Q) • ofInt Q (ofArr y.1.Z))))
      decide (normA N δ ≤ E.plainAdd)
  | .mulPlain _ a b =>
    (get a).bind fun x => (get b).map fun y =>
      eqv (ofInt Q (ofArr (N := N)
        (h.mul (ofArr (N := N) (repFor x.1 vLevel)) (ofArr (repFor y.1 vLevel)))))
  | .mul _ a b =>
    (get a).bind fun x => (get b).map fun y => mulOKb N K h E Q t d.Z x.1.Z y.1.Z ka kb
  | .square _ a =>
    (get a).map fun x => mulOKb N K h E Q t d.Z x.1.Z x.1.Z ka ka
  | .mulConst _ a c => (get a).map fun x => eqv ((c : ZMod Q) • ofInt Q (ofArr x.1.Z))
  | .copy _ a | .toEval _ a | .toCoeff _ a => (get a).map fun x => eqv (ofInt Q (ofArr x.1.Z))
  | .automorph _ a g => (get a).map fun x => eqv (autoF g (ofInt Q (ofArr (repFor x.1 vLevel))))
  | .relin _ a | .keySwitch _ a =>
    (get a).map fun x =>
      let e := toArr K (centered (ofInt Q (ofArr (N := N) d.Z) - ofInt Q (ofArr x.1.Z)))
      decide (normA N e ≤ E.keySwitch)
  | .modSwitch _ a =>
    (get a).bind fun x => (P.src.qs[x.1.level - 1]?).map fun (q : ℕ) =>
      let δ := toArr K ((q : ℤ) • ofArr (N := N) d.Φ - ofArr x.1.Φ)
      decide (normA N δ ≤ q * E.modSwitch) && decide (x.1.level = vLevel + 1) && decide (0 < q)
  | .dropLimbs _ _ _ => some false

/-! ### Soundness of `stepOKb` -/

/-- Adding a multiple of `Q` does not change the residue. -/
theorem ofInt_add_smul {N : ℕ} (Q : ℕ) (a m : IntPoly N) :
    ofInt Q (a + (Q : ℤ) • m) = ofInt Q a := by
  ext i; simp

/-- **The `mul` witnesses.** For arbitrary lifts, the computed `X` and `D` satisfy the two
equations of the contract; only the three norm bounds are tested on data. -/
theorem mulOKb_sound {N K : ℕ} {E : TraceBFV.Budget} {Q t : ℕ} {dZ xZ yZ ka kb : Array ℤ}
    (h : mulOKb N K {} E Q t dZ xZ yZ ka kb = true) :
    ∃ X D : IntPoly N, normInf (ofArr (N := N) ka) ≤ E.mulLift ∧
      normInf (ofArr (N := N) kb) ≤ E.mulLift ∧ 2 * normInf D ≤ Q * E.mulRound ∧
      (Q : ℤ) • X = (t : ℤ) • ((centered (ofInt Q (ofArr xZ)) + (Q : ℤ) • ofArr ka) *
        (centered (ofInt Q (ofArr yZ)) + (Q : ℤ) • ofArr kb)) + D ∧
      ofInt Q (ofArr dZ) = ofInt Q X := by
  simp only [mulOKb, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1 := of_decide_eq_true h1
  have h2 := of_decide_eq_true h2
  have h3 := of_decide_eq_true h3
  refine ⟨ofArr (mulXA N K Q (centredZ N K Q dZ)
      (prodA N K {} t (liftA N K Q xZ ka) (liftA N K Q yZ kb))),
    ofArr (mulWitD N K {} Q t dZ xZ yZ ka kb), h1, h2, h3, ?_, ?_⟩
  · simp only [mulWitD, mulDA, prodA, liftA, ofArr_toArr, ofArr_mulArr]
    ext i
    simp
  · simp only [mulXA, centredZ, ofArr_toArr, ofInt_add_smul, ofInt_centered]

section StepSound
variable {P : FullParams} {K : ℕ} {s : Array ℤ}

/-- **Soundness of the BFV `e.step` decision.** If `stepOKb` (default hooks) answers `some true`
for the destination phase `d` of the ciphertext `d.comps` (which has the key, level and number of
components that `ρ'` records for the destination) and operand phases that are those of the
ciphertexts in `σ`, then the step that assigns `d.comps` to the destination meets
`Spec.TraceBFV.StepOK`, whatever the arrays `ka`, `kb` are. -/
theorem stepOKb_sound (E : TraceBFV.Budget) (i : Instr) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P)
    (v : Val P.src) (d : Ph) (get : Var → Option (Ph × ℕ)) (ka kb : Array ℤ)
    (hv : ρ' (Trace.dst i) = some v) (hd : d.Good P K s) (hdk : d.key = v.key)
    (hdl : d.level = v.level) (hparts : d.comps.length = v.parts) (hget : GetOK P K s ρ σ get)
    (h : stepOKb P E K {} i v.level d get ka kb = some true) :
    TraceBFV.StepOK P E (ofArr s) ρ ρ' σ (σ.set (Trace.dst i) (d.comps.map ofArr)) i := by
  refine ⟨v, d.comps.map ofArr, hv, by simpa using hparts, rfl, ?_⟩
  have hφ : Trace.phaseAt P (P.src.modulus v.level) v.key (ofArr s) (d.comps.map ofArr) =
      ofInt _ (ofArr d.Z) := by rw [← hdk]; exact (hd.phase _).symm
  -- two-operand and one-operand unpacking of `h`
  have two : ∀ {a b : Var} {f : Ph × ℕ → Ph × ℕ → Bool},
      ((get a).bind fun x => (get b).map fun y => f x y) = some true →
      ∃ x y vx vy, get a = some x ∧ get b = some y ∧ f x y = true ∧
        ρ a = some vx ∧ σ a = some (x.1.comps.map ofArr) ∧ x.1.Good P K s ∧ x.1.key = vx.key ∧
        ρ b = some vy ∧ σ b = some (y.1.comps.map ofArr) ∧ y.1.Good P K s ∧ y.1.key = vy.key := by
    intro a b f h
    cases hx : get a with
    | none => simp [hx] at h
    | some x =>
      cases hy : get b with
      | none => simp [hx, hy] at h
      | some y =>
        obtain ⟨vx, h1, h2, h3, h4, -, -⟩ := hget a x.1 x.2 hx
        obtain ⟨vy, h5, h6, h7, h8, -, -⟩ := hget b y.1 y.2 hy
        exact ⟨x, y, vx, vy, rfl, rfl, by simpa [hx, hy] using h, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have one : ∀ {a : Var} {f : Ph × ℕ → Bool}, ((get a).map fun x => f x) = some true →
      ∃ x vx, get a = some x ∧ f x = true ∧ ρ a = some vx ∧ σ a = some (x.1.comps.map ofArr) ∧
        x.1.Good P K s ∧ x.1.key = vx.key ∧ x.1.level = vx.level ∧ x.2 = vx.parts := by
    intro a f h
    cases hx : get a with
    | none => simp [hx] at h
    | some x =>
      obtain ⟨vx, h1, h2, h3, h4, h5, h6⟩ := hget a x.1 x.2 hx
      exact ⟨x, vx, rfl, by simpa [hx] using h, h1, h2, h3, h4, h5, h6⟩
  cases i with
  | add _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.phase, ← gy.phase]; exact (eqv_sound he).symm
  | sub _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.phase, ← gy.phase]; exact (eqv_sound he).symm
  | addPlain _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    simp only [decide_eq_true_eq, normA, ofArr_toArr] at he
    refine ⟨vx, vy, _, _, _, h1, h3, h2, h4, he, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.phase, ← gy.phase]; exact ks_witness _ _
  | subPlain _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    simp only [decide_eq_true_eq, normA, ofArr_toArr] at he
    refine ⟨vx, vy, _, _, _, h1, h3, h2, h4, he, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.phase, ← gy.phase]; exact ks_witness _ _
  | mulPlain _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.rep, ← gy.rep, ← ofInt_mul]
    have := eqv_sound he
    simp only [ofArr_toArr, ofArr_mulArr] at this
    exact this.symm
  | mul _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    obtain ⟨X, D, m1, m2, m3, m4, m5⟩ := mulOKb_sound he
    refine ⟨vx, vy, _, _, _, _, X, D, h1, h3, h2, h4, m1, m2, m3, ?_, ?_⟩
    · rw [← kx, ← ky, ← gx.phase, ← gy.phase]; exact m4
    · rw [hφ]; exact m5
  | square _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    obtain ⟨X, D, m1, -, m3, m4, m5⟩ := mulOKb_sound he
    refine ⟨vx, _, _, X, D, h1, h2, m1, m3, ?_, ?_⟩
    · rw [← kx, ← gx.phase]; exact m4
    · rw [hφ]; exact m5
  | mulConst _ a c =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    refine ⟨vx, _, h1, h2, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact (eqv_sound he).symm
  | copy _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    refine ⟨vx, _, h1, h2, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact (eqv_sound he).symm
  | toEval _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    refine ⟨vx, _, h1, h2, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact (eqv_sound he).symm
  | toCoeff _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    refine ⟨vx, _, h1, h2, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact (eqv_sound he).symm
  | automorph _ a g =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    refine ⟨vx, _, h1, h2, ?_⟩
    rw [hφ, ← kx, ← gx.rep, ← autoF_eq]; exact (eqv_sound he).symm
  | relin _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    simp only [decide_eq_true_eq, normA, ofArr_toArr] at he
    refine ⟨vx, _, _, h1, h2, he, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact ks_witness _ _
  | keySwitch _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    simp only [decide_eq_true_eq, normA, ofArr_toArr] at he
    refine ⟨vx, _, _, h1, h2, he, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact ks_witness _ _
  | modSwitch _ a =>
    have h' : ((get a).bind fun x => (P.src.qs[x.1.level - 1]?).map fun (q : ℕ) =>
        (decide (normA P.src.N (toArr K ((q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ)) ≤
            q * E.modSwitch) &&
          decide (x.1.level = v.level + 1) && decide (0 < q))) = some true := h
    cases hx : get a with
    | none => simp [hx] at h'
    | some x =>
      obtain ⟨vx, h1, h2, gx, kx, lx, px⟩ := hget a x.1 x.2 hx
      cases hq : P.src.qs[x.1.level - 1]? with
      | none => simp [hx, hq] at h'
      | some q =>
        have h2 : (decide (normA P.src.N (toArr K ((q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ)) ≤
              q * E.modSwitch) &&
            decide (x.1.level = v.level + 1) && decide (0 < q)) = true := by
          rw [hx, Option.bind_some, hq, Option.map_some] at h'
          exact Option.some.inj h'
        rw [Bool.and_eq_true, Bool.and_eq_true] at h2
        obtain ⟨⟨hn, -⟩, hq0⟩ := h2
        simp only [decide_eq_true_eq, normA, ofArr_toArr] at hn hq0
        have hΦ := gx.centred
        rw [kx, lx] at hΦ
        obtain ⟨hw1, hw2⟩ := ms_witness q (Nat.pos_iff_ne_zero.mp hq0)
          (ofArr (N := P.src.N) x.1.Φ) (ofArr (N := P.src.N) d.Φ)
        refine ⟨vx, _, (q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ, q, h1, h2,
          by rw [← lx]; exact hq, ?_⟩
        show normInf _ ≤ q * E.modSwitch ∧ _
        rw [← hΦ]
        refine ⟨hn, hw1, ?_⟩
        rw [hw2, hφ]
        have hc := hd.centred
        rw [hdl, hdk] at hc
        rw [hc, ofInt_centered, hφ]
  | dropLimbs _ a k => simp [stepOKb] at h

end StepSound

/-! ### Decryption and the input contracts -/

/-- Forced BFV decryption `[⌊t·Φ/Q⌉]_t` from a forced centred phase `Φ`. -/
def decryptBFVOfPhaseA (N K t Q : ℕ) (Φ : Array ℤ) : Array (ZMod t) :=
  toArr K (⟨fun i => (roundDiv (t * (ofArr (N := N) Φ).coeff i) Q : ZMod t)⟩ : Poly t N)

/-- Forced `Spec.Scheme.bfvDecrypt`. -/
def decryptBFVA (N K : ℕ) (m : Mut) (t Q : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    Array (ZMod t) :=
  decryptBFVOfPhaseA N K t Q (centredPhaseA N K m Q s ct)

/-- **`Spec.Scheme.bfvDecrypt`.** -/
theorem decryptBFVA_spec (N K t Q : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    ofArr (N := N) (decryptBFVA N K .none t Q s ct) =
      bfvDecrypt t (ofArr s) (ct.map fun c => ofInt Q (ofArr c)) := by
  simp [decryptBFVA, decryptBFVOfPhaseA, bfvDecrypt, centredPhaseA_spec]

/-- The centred phase of a `Good` phase is the `centeredPhase` that `Spec.Scheme` decrypts. -/
theorem good_centeredPhase {P : FullParams} {K : ℕ} {s : Array ℤ} {p : Ph} (hp : p.Good P K s) :
    ofArr (N := P.src.N) p.Φ =
      centeredPhase (automorph p.key (ofArr s))
        ((p.comps.map ofArr).map (ofInt (P.src.modulus p.level))) :=
  hp.centred

/-- **`Spec.Scheme.bfvDecrypt` from a forced phase**, under the phase's key and at its level. -/
theorem decryptBFVOfPhaseA_spec {P : FullParams} {K : ℕ} {s : Array ℤ} {p : Ph}
    (hp : p.Good P K s) :
    ofArr (N := P.src.N)
        (decryptBFVOfPhaseA P.src.N K P.src.t (P.src.modulus p.level) p.Φ) =
      bfvDecrypt P.src.t (automorph p.key (ofArr s))
        ((p.comps.map ofArr).map (ofInt (P.src.modulus p.level))) := by
  simp only [decryptBFVOfPhaseA, ofArr_toArr, bfvDecrypt, good_centeredPhase hp]

/-- The measured noise of a BFV ciphertext with integer phase `Z` for the message `m`:
`‖[Z − ⌊Q/t⌋·m]_Q‖∞` (`m`'s representatives in `[0, t)`). -/
def noiseA (N K t Q : ℕ) (Z : Array ℤ) (m : Array (ZMod t)) : ℕ :=
  normA N (toArr K (centered (ofInt Q (ofArr (N := N) Z) -
    ofInt Q ⟨fun i => ((Q / t * ((ofArr (N := N) m).coeff i).val : ℕ) : ℤ)⟩)))

/-- **`noiseA` is the noise of `Spec.Scheme.BFVEncrypts`.** -/
theorem noiseA_spec {P : FullParams} {K : ℕ} {s : Array ℤ} {p : Ph} (hp : p.Good P K s)
    (m : Array (ZMod P.src.t)) :
    noiseA P.src.N K P.src.t (P.src.modulus p.level) p.Z m =
      normInf (centered
        (phase (ofInt (P.src.modulus p.level) (automorph p.key (ofArr s)))
            ((p.comps.map ofArr).map (ofInt (P.src.modulus p.level))) -
          ofInt (P.src.modulus p.level)
            ⟨fun i => ((P.src.modulus p.level / P.src.t *
              ((ofArr (N := P.src.N) m).coeff i).val : ℕ) : ℤ)⟩)) := by
  simp only [noiseA, normA, ofArr_toArr, hp.phase]
  rfl

/-- **The decision of the input contract of a BFV ciphertext**: it decrypts (`bfvDecrypt`) to
`m`, and its noise (`noiseA`) is at most `B`. -/
def inputCtOKb (P : FullParams) (K B : ℕ) (ph : Ph) (m : Array (ZMod P.src.t)) : Bool :=
  let Q := P.src.modulus ph.level
  (toArr K (ofArr (N := P.src.N) (decryptBFVOfPhaseA P.src.N K P.src.t Q ph.Φ)) ==
      toArr K (ofArr (N := P.src.N) m)) &&
    decide (noiseA P.src.N K P.src.t Q ph.Z m ≤ B)

/-- **The decision of the input contract of a BFV plaintext** (`Spec.TraceBFV.PlainOK`): the
centred phase reduces to `m` modulo `t` and has norm at most `b`. -/
def inputPtOKb (P : FullParams) (K b : ℕ) (ph : Ph) (m : Array (ZMod P.src.t)) : Bool :=
  (toArr K (ofInt P.src.t (ofArr (N := P.src.N) ph.Φ)) == toArr K (ofArr (N := P.src.N) m)) &&
    decide (normA P.src.N ph.Φ ≤ b)

/-- The decision of the input contract of one input with `parts` components
(`Spec.TraceBFV.InputsOK`: a plaintext if `parts = 1`, a ciphertext otherwise). -/
def inputOKb (P : FullParams) (K B parts : ℕ) (ph : Ph) (m : Array (ZMod P.src.t)) : Bool :=
  if parts = 1 then inputPtOKb P K B ph m else inputCtOKb P K B ph m

section InputSound
variable {P : FullParams} {K : ℕ} {s : Array ℤ}

/-- **Soundness of `inputCtOKb`**: `Spec.Correct.Encrypts` for BFV. -/
theorem inputCtOKb_sound (hk : P.src.kind = .bfv) (B : ℕ) (v : Val P.src) (ph : Ph)
    (m : Array (ZMod P.src.t)) (hp : ph.Good P K s) (hpk : ph.key = v.key)
    (hpl : ph.level = v.level) (hparts : ph.comps.length = v.parts)
    (hm : v.msg = .exact (ofArr m)) (h : inputCtOKb P K B ph m = true) :
    Correct.Encrypts P (ofArr s) B v (ph.comps.map ofArr) := by
  simp only [inputCtOKb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1 := eqv_sound h1
  rw [decryptBFVOfPhaseA_spec hp] at h1
  rw [noiseA_spec hp] at h2
  rw [hpk, hpl] at h1 h2
  simp only [Correct.Encrypts, hk, hm]
  exact ⟨by simpa using hparts, h1, h2⟩

/-- **Soundness of `inputPtOKb`**: `Spec.TraceBFV.PlainOK`. -/
theorem inputPtOKb_sound (b : ℕ) (v : Val P.src) (ph : Ph)
    (m : Array (ZMod P.src.t)) (hp : ph.Good P K s) (hpk : ph.key = v.key)
    (hpl : ph.level = v.level) (hparts : ph.comps.length = v.parts)
    (hm : v.msg = .exact (ofArr m)) (h : inputPtOKb P K b ph m = true) :
    TraceBFV.PlainOK P (ofArr s) b v (ph.comps.map ofArr) := by
  simp only [inputPtOKb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1 := eqv_sound h1
  unfold normA at h2
  rw [good_centeredPhase hp, hpk, hpl] at h1 h2
  exact ⟨by simpa using hparts, _, hm, h1, h2⟩

/-- **Soundness of `inputOKb`**: the clause of `Spec.TraceBFV.InputsOK` for one input. -/
theorem inputOKb_sound (hk : P.src.kind = .bfv) (B : ℕ) (v : Val P.src) (ph : Ph)
    (m : Array (ZMod P.src.t)) (hp : ph.Good P K s) (hpk : ph.key = v.key)
    (hpl : ph.level = v.level) (hparts : ph.comps.length = v.parts)
    (hm : v.msg = .exact (ofArr m)) (h : inputOKb P K B v.parts ph m = true) :
    if v.parts = 1 then TraceBFV.PlainOK P (ofArr s) B v (ph.comps.map ofArr)
    else Correct.Encrypts P (ofArr s) B v (ph.comps.map ofArr) := by
  unfold inputOKb at h
  split
  · rename_i h1; simp only [h1, ite_true] at h
    exact inputPtOKb_sound B v ph m hp hpk hpl hparts hm h
  · rename_i h1; simp only [h1, ite_false] at h
    exact inputCtOKb_sound hk B v ph m hp hpk hpl hparts hm h

end InputSound

end FHE.Pin.BFV
