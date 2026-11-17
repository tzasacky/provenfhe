import FHE.Pin.Force
import Spec.Budget

/-!
# FHE.Pin.Sound — the two deciding mirrors of `openfhe_pin`, with soundness proofs
(UNTRUSTED glue; the theorems are kernel-checked)

Two checks of the differential harness decide a trusted *predicate* (not an equation between
computed values), by a function written for speed on arrays:

* `e.step` decides the phase contract `Spec.Trace.StepOK` of one instruction. `StepOK` is
  existential (a key-switching error `e`, a modulus-switching correction `δ`); the decision
  `stepOKb` computes the witnesses `e := centered (φ' − φ_a)` and `δ := q·Φ' − Φ_a` and tests the
  remaining conjuncts. `stepOKb_sound`: if it answers `some true` on phases that are the forced
  phases of the ciphertexts (`Ph.Good`), then `StepOK` holds of those ciphertexts.
* `d.key` decides `Spec.Budget.GadgetKeysOK` at one level from the forced `b + a·s` of every
  stored digit. `gadgetKeysCheck_sound`: if it answers `true`, then `GadgetKeysOK` holds of the
  first digits of the stored key.

Both functions are the ones the checks call (`FHE.Pin.stepCheck` takes its verdict from
`stepOKb`, `FHE.Pin.checkD` from `gadgetKeysCheck`), so the statements are about the code that
runs, at `Mut.none`. Only soundness is proved (a `true` verdict is a proof of the predicate);
completeness is not (a `false` verdict of `stepOKb` says that *these* witnesses fail).

Not covered by a theorem: that the context builds phases satisfying `Ph.Good` (`Cx.mkPh` calls
exactly the functions named in `Ph.Good`, through a per-key cache in `IO`), the JSON loading and
the CRT lift (verified against every limb at run time), and the composite modulus switch through
object-less intermediates (`e.step` lines with `"composite": true`).
-/

namespace FHE.Pin
open Spec Spec.NPoly Spec.Scheme Spec.Source Validation.Scheme

/-- `‖a‖∞` by the trusted `normInf`. -/
def normA (N : ℕ) (a : Array ℤ) : ℕ := normInf (ofArr (N := N) a)

/-- Every coefficient divisible by `t` (decided on the wrapped array). -/
def dvdA (N t : ℕ) (a : Array ℤ) : Bool :=
  decide (∀ i : Fin N, (t : ℤ) ∣ (ofArr (N := N) a).coeff i)

/-- A forced phase of a ciphertext under a key: components, integer phase `Z` (unreduced) and
centred phase `Φ` modulo the modulus of `level`. -/
structure Ph where
  comps : List (Array ℤ)
  level : ℕ
  key : ℕ
  Z : Array ℤ
  Φ : Array ℤ
  deriving Inhabited

/-- `ph` holds the forced phases of its own components under `σ_key(s)`: `Z` is `phaseAtZ` and
`Φ` its centred lift modulo the modulus of `ph.level`. -/
structure Ph.Good (P : FullParams) (K : ℕ) (s : Array ℤ) (ph : Ph) : Prop where
  Z : ph.Z = phaseAtZ P.src.N K .none ph.key s ph.comps
  Φ : ph.Φ = centredA P.src.N K .none (P.src.modulus ph.level) ph.Z

/-- The integer representative of a phase to use modulo the modulus of `lvl`: the centred phase
if the value is at that level (small integers), the unreduced integer phase otherwise (both are
congruent to `Spec.Trace.phaseAt` modulo that modulus: `Ph.Good.rep`). -/
def repFor (r : Ph) (lvl : ℕ) : Array ℤ := if r.level = lvl then r.Φ else r.Z

/-- **The decision of `e.step`.** The conjuncts of `Spec.Trace.StepOK` about phases, for the
destination phase `d` (at level `vLevel`) of instruction `i`; `get` gives the phase and the
number of components of an operand. `none`: an operand has no ciphertext data (or, for
`modSwitch`, the operand's level has no last modulus). -/
def stepOKb (P : FullParams) (E : Trace.Budget) (K : ℕ) (mt : Mut) (i : Instr) (vLevel : ℕ)
    (d : Ph) (get : Var → Option (Ph × ℕ)) : Option Bool :=
  let N := P.src.N
  let Q := P.src.modulus vLevel
  let φ : Array (ZMod Q) := toArr K (ofInt Q (ofArr (N := N) d.Z))
  let eqv : Poly Q N → Bool := fun rhs => toArr K rhs == φ
  match i with
  | .add _ a b | .addPlain _ a b =>
    (get a).bind fun x => (get b).map fun y => eqv (ofInt Q (ofArr x.1.Z) + ofInt Q (ofArr y.1.Z))
  | .sub _ a b | .subPlain _ a b =>
    (get a).bind fun x => (get b).map fun y => eqv (ofInt Q (ofArr x.1.Z) - ofInt Q (ofArr y.1.Z))
  | .mul _ a b | .mulPlain _ a b =>
    (get a).bind fun x => (get b).map fun y =>
      eqv (ofInt Q (ofArr (toArr K
        (mulMF mt (ofArr (N := N) (repFor x.1 vLevel)) (ofArr (repFor y.1 vLevel))))))
  | .square _ a =>
    (get a).map fun x =>
      eqv (ofInt Q (ofArr (toArr K
        (mulMF mt (ofArr (N := N) (repFor x.1 vLevel)) (ofArr (repFor x.1 vLevel))))))
  | .mulConst _ a c => (get a).map fun x => eqv ((c : ZMod Q) • ofInt Q (ofArr x.1.Z))
  | .copy _ a | .toEval _ a | .toCoeff _ a => (get a).map fun x => eqv (ofInt Q (ofArr x.1.Z))
  | .automorph _ a g => (get a).map fun x => eqv (autoF g (ofInt Q (ofArr (repFor x.1 vLevel))))
  | .relin _ a | .keySwitch _ a =>
    (get a).map fun x =>
      let e := toArr K (centered (ofInt Q (ofArr (N := N) d.Z) - ofInt Q (ofArr x.1.Z)))
      decide (normA N e ≤ E.keySwitch) && dvdA N P.src.t e
  | .modSwitch _ a =>
    (get a).bind fun x => (P.src.qs[x.1.level - 1]?).map fun (q : ℕ) =>
      let δ := toArr K ((q : ℤ) • ofArr (N := N) d.Φ - ofArr x.1.Φ)
      decide (normA N δ ≤ q * mt.msBudgetM E x.2) && dvdA N P.src.t δ &&
        decide (x.1.level = vLevel + 1) && decide (0 < q)
  | .dropLimbs _ a _ => (get a).map fun x => eqv (ofInt Q (ofArr x.1.Φ))

/-! ### Soundness of `stepOKb` -/

section StepSound
variable {P : FullParams} {K : ℕ} {s : Array ℤ}

theorem Ph.Good.phase {p : Ph} (hp : p.Good P K s) (Q : ℕ) :
    ofInt Q (ofArr (N := P.src.N) p.Z) =
      Trace.phaseAt P Q p.key (ofArr s) (p.comps.map ofArr) := by
  rw [hp.Z]; exact phaseAtZ_spec P K Q p.key s p.comps

theorem Ph.Good.centred {p : Ph} (hp : p.Good P K s) :
    ofArr (N := P.src.N) p.Φ =
      centered (Trace.phaseAt P (P.src.modulus p.level) p.key (ofArr s) (p.comps.map ofArr)) := by
  rw [hp.Φ, hp.Z]; exact centredA_phaseAtZ_spec P K _ p.key s p.comps

theorem Ph.Good.rep {p : Ph} (hp : p.Good P K s) (lvl : ℕ) :
    ofInt (P.src.modulus lvl) (ofArr (N := P.src.N) (repFor p lvl)) =
      Trace.phaseAt P (P.src.modulus lvl) p.key (ofArr s) (p.comps.map ofArr) := by
  unfold repFor
  split
  · rename_i h; subst h; rw [hp.centred, ofInt_centered]
  · exact hp.phase _

theorem eqv_sound {Q N : ℕ} {a b : Poly Q N} (h : (toArr K a == toArr K b) = true) : a = b :=
  toArr_inj (eq_of_beq h)

/-- What `get` must return for the soundness statement: the forced phase of the operand's
ciphertext in `σ`, with the key, level and number of components `ρ` records. -/
def GetOK (P : FullParams) (K : ℕ) (s : Array ℤ) (ρ : Env P.src) (σ : Trace.CtEnv P)
    (get : Var → Option (Ph × ℕ)) : Prop :=
  ∀ a p k, get a = some (p, k) → ∃ x, ρ a = some x ∧ σ a = some (p.comps.map ofArr) ∧
    p.Good P K s ∧ p.key = x.key ∧ p.level = x.level ∧ k = x.parts

/-- **Soundness of the `e.step` decision.** If `stepOKb` answers `some true` for the destination
phase `d` of the ciphertext `d.comps` (which has the key, level and number of components that
`ρ'` records for the destination) and operand phases that are those of the ciphertexts in `σ`,
then the step that assigns `d.comps` to the destination meets `Spec.Trace.StepOK`. -/
theorem stepOKb_sound (E : Trace.Budget) (i : Instr) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P)
    (v : Val P.src) (d : Ph) (get : Var → Option (Ph × ℕ))
    (hv : ρ' (Trace.dst i) = some v) (hd : d.Good P K s) (hdk : d.key = v.key)
    (hdl : d.level = v.level) (hparts : d.comps.length = v.parts) (hget : GetOK P K s ρ σ get)
    (h : stepOKb P E K .none i v.level d get = some true) :
    Trace.StepOK P E (ofArr s) ρ ρ' σ (σ.set (Trace.dst i) (d.comps.map ofArr)) i := by
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
  | addPlain _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.phase, ← gy.phase]; exact (eqv_sound he).symm
  | sub _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.phase, ← gy.phase]; exact (eqv_sound he).symm
  | subPlain _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.phase, ← gy.phase]; exact (eqv_sound he).symm
  | mul _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.rep, ← gy.rep, ← ofInt_mul]
    have := eqv_sound he
    rw [ofArr_toArr, mulMF_none] at this
    exact this.symm
  | mulPlain _ a b =>
    obtain ⟨x, y, vx, vy, -, -, he, h1, h2, gx, kx, h3, h4, gy, ky⟩ := two h
    refine ⟨vx, vy, _, _, h1, h3, h2, h4, ?_⟩
    rw [hφ, ← kx, ← ky, ← gx.rep, ← gy.rep, ← ofInt_mul]
    have := eqv_sound he
    rw [ofArr_toArr, mulMF_none] at this
    exact this.symm
  | square _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    refine ⟨vx, _, h1, h2, ?_⟩
    rw [hφ, ← kx, ← gx.rep, ← ofInt_mul]
    have := eqv_sound he
    rw [ofArr_toArr, mulMF_none] at this
    exact this.symm
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
    simp only [Bool.and_eq_true, decide_eq_true_eq, normA, dvdA, ofArr_toArr] at he
    refine ⟨vx, _, _, h1, h2, he.1, he.2, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact ks_witness _ _
  | keySwitch _ a =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, -, -⟩ := one h
    simp only [Bool.and_eq_true, decide_eq_true_eq, normA, dvdA, ofArr_toArr] at he
    refine ⟨vx, _, _, h1, h2, he.1, he.2, ?_⟩
    rw [hφ, ← kx, ← gx.phase]; exact ks_witness _ _
  | modSwitch _ a =>
    have h' : ((get a).bind fun x => (P.src.qs[x.1.level - 1]?).map fun (q : ℕ) =>
        (decide (normA P.src.N (toArr K ((q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ)) ≤
            q * Mut.none.msBudgetM E x.2) &&
          dvdA P.src.N P.src.t (toArr K ((q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ)) &&
          decide (x.1.level = v.level + 1) && decide (0 < q))) = some true := h
    cases hx : get a with
    | none => simp [hx] at h'
    | some x =>
      obtain ⟨vx, h1, h2, gx, kx, lx, px⟩ := hget a x.1 x.2 hx
      cases hq : P.src.qs[x.1.level - 1]? with
      | none => simp [hx, hq] at h'
      | some q =>
        have h2 : (decide (normA P.src.N (toArr K ((q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ)) ≤
              q * Mut.none.msBudgetM E x.2) &&
            dvdA P.src.N P.src.t (toArr K ((q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ)) &&
            decide (x.1.level = v.level + 1) && decide (0 < q)) = true := by
          rw [hx, Option.bind_some, hq, Option.map_some] at h'
          exact Option.some.inj h'
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
        obtain ⟨⟨⟨hn, hdv⟩, -⟩, hq0⟩ := h2
        simp only [decide_eq_true_eq, normA, dvdA, ofArr_toArr, Mut.msBudget_none] at hn hdv hq0
        have hΦ := gx.centred
        rw [kx, lx] at hΦ
        obtain ⟨hw1, hw2⟩ := ms_witness q (Nat.pos_iff_ne_zero.mp hq0)
          (ofArr (N := P.src.N) x.1.Φ) (ofArr (N := P.src.N) d.Φ)
        refine ⟨vx, _, (q : ℤ) • ofArr (N := P.src.N) d.Φ - ofArr x.1.Φ, q, h1, h2,
          by rw [← lx]; exact hq, ?_⟩
        show normInf _ ≤ q * E.modSwitchAt vx.parts ∧ _
        rw [← hΦ, ← px]
        refine ⟨hn, hdv, hw1, ?_⟩
        rw [hw2, hφ]
        have hc := hd.centred
        rw [hdl, hdk] at hc
        rw [hc, ofInt_centered, hφ]
  | dropLimbs _ a k =>
    obtain ⟨x, vx, -, he, h1, h2, gx, kx, lx, -⟩ := one h
    refine ⟨vx, _, h1, h2, ?_⟩
    have hΦ := gx.centred
    rw [kx, lx] at hΦ
    rw [hφ, ← hΦ]; exact (eqv_sound he).symm

end StepSound

/-! ### `d.key`: the gadget keys of one level -/

/-- **The decision of `d.key`** at level `ℓ`, from the forced `b + a·s` of each stored digit
(`lhs`, `keyLhsZ`) and the forced target (`tg`, `targetZ`), both computed once for all levels:
the key has at least as many digits as the layout, and each of the first `(lay.sizes ℓ).length`
is valid for its gadget factor (`keyValidOfErr` of `keyErrA`). -/
def gadgetKeysCheck (P : FullParams) (lay : Budget.KSLayout) (ℓ K : ℕ) (mt : Mut)
    (lhs : Array (Array ℤ)) (tg : Array ℤ) : Bool :=
  let M := P.src.modulus ℓ * Budget.specialProd P
  decide ((lay.sizes ℓ).length ≤ lhs.size) &&
    (List.range (lay.sizes ℓ).length).all fun j =>
      keyValidOfErr P.src.N P.src.t P.keyNoise
        (keyErrA P.src.N K M
          ((mt.gadgetFactorM (Budget.specialProd P) (Budget.digitModuli P lay ℓ) j : ℕ) : ZMod M)
          lhs[j]! tg)

/-- **Soundness of the `d.key` decision.** If `gadgetKeysCheck` answers `true` on the forced
`b + a·s` of the stored digits `keys` and the forced target of `tgt`, then the first
`(lay.sizes ℓ).length` stored digits are valid gadget keys at level `ℓ`:
`Spec.Budget.GadgetKeysOK`. -/
theorem gadgetKeysCheck_sound (P : FullParams) (lay : Budget.KSLayout) (ℓ K : ℕ) (tgt : KeyTarget)
    (s : Array ℤ) (keys : Array (Array ℤ × Array ℤ))
    (h : gadgetKeysCheck P lay ℓ K .none
      (keys.map fun k => keyLhsZ P.src.N K .none k.1 k.2 s) (targetZ P.src.N K .none s tgt) = true) :
    Budget.GadgetKeysOK P lay ℓ tgt (ofArr s)
      ((keys.toList.take (lay.sizes ℓ).length).map fun k => (ofArr k.1, ofArr k.2)) := by
  simp only [gadgetKeysCheck, Bool.and_eq_true, decide_eq_true_eq, Array.size_map, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  have hl : ((keys.toList.take (lay.sizes ℓ).length).map
      fun k => ((ofArr k.1 : IntPoly P.src.N), (ofArr k.2 : IntPoly P.src.N))).length =
      (lay.sizes ℓ).length := by
    simp only [List.length_map, List.length_take, Array.length_toList]; omega
  refine ⟨hl, fun j hj => ?_⟩
  have hjn : j < (lay.sizes ℓ).length := hl ▸ hj
  have hjk : j < keys.size := lt_of_lt_of_le hjn hlen
  have hv := hall j hjn
  rw [getElem!_pos _ _ (by simpa using hjk), Array.getElem_map, Mut.gadgetFactor_none] at hv
  have hkv := (keyValid_iff P.src.N K _ P.src.t P.keyNoise _ tgt keys[j].1 keys[j].2 s).mp hv
  have hget : ((keys.toList.take (lay.sizes ℓ).length).map
      fun k => ((ofArr k.1 : IntPoly P.src.N), (ofArr k.2 : IntPoly P.src.N)))[j] =
      (ofArr keys[j].1, ofArr keys[j].2) := by
    simp only [List.getElem_map, List.getElem_take, Array.getElem_toList]
  rw [hget]
  exact ⟨hkv.1, fun _ => hkv.2 rfl⟩

end FHE.Pin
