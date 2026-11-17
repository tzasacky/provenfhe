import Validation.BFV.Ops
import Validation.BFV.Mul

/-!
# Validation.BFV.Sound — the BFV noise headline

`Challenge.BFV.refAnalyzeBFV` is sound against every ciphertext-level run meeting the
`Spec.TraceBFV` phase contracts (`refAnalyzeBFV_sound`), with the scope and decryption pins.

**Invariant.** Along a run, every variable `x` with a tracked bound `β x = some b` holds a
ciphertext that `Encrypts` its value with noise at most `b` (`b = .ct _`), or a plaintext within
`b` (`b = .pt _`, `TraceBFV.PlainOK`). Each rule of `refBoundBFV` is the bound of one phase-level
lemma of `Validation.BFV.Ops` / `Validation.BFV.Mul`; the `decOK` check that the analysis performs
at each step gives the decryption clause of `BFVEncrypts` (`decrypt_of_noiseLe`).

**Messages.** The reference analysis runs `Source.step` on all-zero messages; the run uses the
real ones. For BFV, with every message `.exact`, zeroing the messages commutes with `step`
(`step_zenv`).

No `Challenge.*` definition is unfolded with `simp`/`rw`/`unfold`: the local `rfl` lemmas below
give the needed equations, so no `Challenge.*` equation lemma is generated here.
-/

namespace Validation.BFV
open Spec NPoly Scheme Source Correct Challenge.BFV
open Spec.TraceBFV (Bnd)
open Validation.Ring Validation.Scheme Validation.Source

namespace SoundAux

/-! ### Zeroing messages -/

section Zero
variable {Pr : Params}

/-- The value with its message replaced by the exact zero message. -/
def zv (v : Val Pr) : Val Pr := { v with msg := .exact 0 }

/-- The environment with every message replaced by zero. -/
def zenv (ρ : Env Pr) : Env Pr := fun x => (ρ x).map zv

/-- Every message is exact. -/
def AllExact (ρ : Env Pr) : Prop := ∀ x v, ρ x = some v → ∃ m, v.msg = .exact m

theorem zenv_set (ρ : Env Pr) (d : Var) (v : Val Pr) :
    zenv (ρ.set d v) = (zenv ρ).set d (zv v) := by
  funext y; simp only [zenv, Env.set]; split_ifs <;> rfl

theorem allExact_set {ρ : Env Pr} (h : AllExact ρ) (d : Var) (v : Val Pr) (m : Poly Pr.t Pr.N)
    (hm : v.msg = .exact m) : AllExact (ρ.set d v) := by
  intro y w hw
  simp only [Env.set] at hw
  split_ifs at hw
  · cases hw; exact ⟨m, hm⟩
  · exact h y w hw

theorem npoly_zero_add {R : Type} [CommRing R] {N : ℕ} : (0 : NPoly R N) + 0 = 0 := by ext; simp
theorem npoly_zero_sub {R : Type} [CommRing R] {N : ℕ} : (0 : NPoly R N) - 0 = 0 := by ext; simp
theorem npoly_zero_mul {R : Type} [CommRing R] {N : ℕ} : (0 : NPoly R N) * 0 = 0 := by
  ext k; simp [coeff_mul']
theorem npoly_mul_zero {R : Type} [CommRing R] {N : ℕ} (a : NPoly R N) : a * 0 = 0 := by
  ext k; simp [coeff_mul']
theorem npoly_add_zero {R : Type} [CommRing R] {N : ℕ} (a : NPoly R N) : a + 0 = a := by
  ext; simp
theorem npoly_smul_zero {R : Type} [CommRing R] {N : ℕ} (c : R) : c • (0 : NPoly R N) = 0 := by
  ext; simp

theorem step_zenv (hk : Pr.kind = .bfv) {ρ : Env Pr} (hρ : AllExact ρ) (i : Instr) :
    step Pr (zenv ρ) i = (step Pr ρ i).map zenv ∧ ∀ ρ', step Pr ρ i = some ρ' → AllExact ρ' := by
  cases i with
  | add d a b | sub d a b | mul d a b | addPlain d a b | subPlain d a b | mulPlain d a b =>
    rcases h1 : ρ a with _ | x
    · simp [step, zenv, h1]
    rcases h2 : ρ b with _ | y
    · simp [step, zenv, h1, h2]
    obtain ⟨m, hm⟩ := hρ a x h1
    obtain ⟨m', hm'⟩ := hρ b y h2
    simp only [step, zenv, h1, h2, zv, hm, hm', Msg.lift₂, hk, Option.map_some, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, guard]
    refine ⟨?_, ?_⟩
    · split_ifs <;> simp [zenv_set, zv, npoly_zero_add, npoly_zero_sub, npoly_zero_mul]
    · intro ρ' h; split_ifs at h <;> simp at h
      all_goals (subst h; exact allExact_set hρ _ _ _ rfl)
  | square d a | mulConst d a _ | copy d a | toEval d a | toCoeff d a | relin d a | keySwitch d a
  | automorph d a _ | modSwitch d a | dropLimbs d a _ =>
    rcases h1 : ρ a with _ | x
    · simp [step, zenv, h1]
    obtain ⟨m, hm⟩ := hρ a x h1
    rcases hq : Pr.qs[x.level - 1]? with _ | q
    all_goals simp only [step, zenv, h1, zv, hm, hq, Msg.lift₂, Msg.lift₁, hk, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.pure_def, guard]
    all_goals refine ⟨?_, ?_⟩
    all_goals first
    | (try split_ifs
       all_goals simp [zenv_set, zv, npoly_zero_mul, npoly_smul_zero, automorph_zero]
       done)
    | (intro ρ' h
       try split_ifs at h
       all_goals simp at h
       all_goals (subst h; first | exact allExact_set hρ _ _ _ rfl | exact allExact_set hρ _ _ _ hm))
end Zero

/-! ### Equations of the reference analysis (by `rfl`) -/

theorem decOK_iff {t Q B : ℕ} : decOK t Q B = true ↔ 2 * (t * B + Q % t * (t - 1)) < Q := by
  have e : decOK t Q B = decide (2 * (t * B + Q % t * (t - 1)) < Q) := rfl
  rw [e, decide_eq_true_iff]

section Ref
variable (P : FullParams) (E : TraceBFV.Budget)

theorem refRun_nil (ρ : Env P.src) (β : Var → Option Bnd) :
    refRunBFV P E [] ρ β = some (ρ, β) := rfl

theorem refRun_cons_some {i : Instr} {is : List Instr} {ρ : Env P.src} {β : Var → Option Bnd}
    {r : Env P.src × (Var → Option Bnd)} (h : refRunBFV P E (i :: is) ρ β = some r) :
    ∃ ρ' v b, step P.src ρ i = some ρ' ∧ ρ' (Trace.dst i) = some v ∧
      refBoundBFV P E v.level β i = some b ∧ bndOK P v.level b = true ∧
      refRunBFV P E is ρ' (fun y => if y = Trace.dst i then some b else β y) = some r ∧
      domainOK ρ i = true := by
  have e : refRunBFV P E (i :: is) ρ β = (do
      guard (domainOK ρ i)
      let ρ' ← step P.src ρ i
      let v ← ρ' (Trace.dst i)
      let b ← refBoundBFV P E v.level β i
      guard (bndOK P v.level b)
      refRunBFV P E is ρ' (fun y => if y = Trace.dst i then some b else β y)) := rfl
  rw [e] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard] at h
  obtain ⟨_, h0, ρ', h1, v, h2, b, h3, h4⟩ := h
  have hd : domainOK ρ i = true := by by_contra hd; simp [hd] at h0
  split_ifs at h4 with hq
  · exact ⟨ρ', v, b, h1, h2, h3, hq, by simpa using h4, hd⟩
  · simp at h4

variable {P E} {ℓ : ℕ} {β : Var → Option Bnd} {b : Bnd} {d a c : Var}

theorem bound_add (h : refBoundBFV P E ℓ β (.add d a c) = some b) :
    ∃ x y, β a = some (.ct x) ∧ β c = some (.ct y) ∧
      b = .ct (x + y + P.src.modulus ℓ % P.src.t) := by
  have e : refBoundBFV P E ℓ β (.add d a c) = (match β a, β c with
    | some (.ct x), some (.ct y) => some (.ct (x + y + P.src.modulus ℓ % P.src.t))
    | _, _ => none) := rfl
  rw [e] at h
  split at h
  · next x y h1 h2 => exact ⟨x, y, h1, h2, (Option.some.inj h).symm⟩
  · cases h

theorem bound_sub (h : refBoundBFV P E ℓ β (.sub d a c) = some b) :
    ∃ x y, β a = some (.ct x) ∧ β c = some (.ct y) ∧
      b = .ct (x + y + P.src.modulus ℓ % P.src.t) := by
  have e : refBoundBFV P E ℓ β (.sub d a c) = (match β a, β c with
    | some (.ct x), some (.ct y) => some (.ct (x + y + P.src.modulus ℓ % P.src.t))
    | _, _ => none) := rfl
  rw [e] at h
  split at h
  · next x y h1 h2 => exact ⟨x, y, h1, h2, (Option.some.inj h).symm⟩
  · cases h

theorem bound_addPlain (h : refBoundBFV P E ℓ β (.addPlain d a c) = some b) :
    ∃ x y, β a = some (.ct x) ∧ β c = some (.pt y) ∧
      b = .ct (x + P.src.modulus ℓ % P.src.t * ((y + P.src.t - 1) / P.src.t) + E.plainAdd) := by
  have e : refBoundBFV P E ℓ β (.addPlain d a c) = (match β a, β c with
    | some (.ct x), some (.pt y) =>
      some (.ct (x + P.src.modulus ℓ % P.src.t * ((y + P.src.t - 1) / P.src.t) + E.plainAdd))
    | _, _ => none) := rfl
  rw [e] at h
  split at h
  · next x y h1 h2 => exact ⟨x, y, h1, h2, (Option.some.inj h).symm⟩
  · cases h

theorem bound_subPlain (h : refBoundBFV P E ℓ β (.subPlain d a c) = some b) :
    ∃ x y, β a = some (.ct x) ∧ β c = some (.pt y) ∧
      b = .ct (x + P.src.modulus ℓ % P.src.t * ((y + P.src.t - 1) / P.src.t) + E.plainAdd) := by
  have e : refBoundBFV P E ℓ β (.subPlain d a c) = (match β a, β c with
    | some (.ct x), some (.pt y) =>
      some (.ct (x + P.src.modulus ℓ % P.src.t * ((y + P.src.t - 1) / P.src.t) + E.plainAdd))
    | _, _ => none) := rfl
  rw [e] at h
  split at h
  · next x y h1 h2 => exact ⟨x, y, h1, h2, (Option.some.inj h).symm⟩
  · cases h

theorem bound_mulPlain (h : refBoundBFV P E ℓ β (.mulPlain d a c) = some b) :
    ∃ x y, β a = some (.ct x) ∧ β c = some (.pt y) ∧
      b = .ct (P.src.N * y * (x + P.src.modulus ℓ % P.src.t)) := by
  have e : refBoundBFV P E ℓ β (.mulPlain d a c) = (match β a, β c with
    | some (.ct x), some (.pt y) => some (.ct (P.src.N * y * (x + P.src.modulus ℓ % P.src.t)))
    | _, _ => none) := rfl
  rw [e] at h
  split at h
  · next x y h1 h2 => exact ⟨x, y, h1, h2, (Option.some.inj h).symm⟩
  · cases h

theorem bound_mul (h : refBoundBFV P E ℓ β (.mul d a c) = some b) :
    ∃ x y, β a = some (.ct x) ∧ β c = some (.ct y) ∧
      b = .ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x y) := by
  have e : refBoundBFV P E ℓ β (.mul d a c) = (match β a, β c with
    | some (.ct x), some (.ct y) =>
      some (.ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x y))
    | _, _ => none) := rfl
  rw [e] at h
  split at h
  · next x y h1 h2 => exact ⟨x, y, h1, h2, (Option.some.inj h).symm⟩
  · cases h

theorem bound_square (h : refBoundBFV P E ℓ β (.square d a) = some b) :
    ∃ x, β a = some (.ct x) ∧
      b = .ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x x) := by
  have e : refBoundBFV P E ℓ β (.square d a) = (match β a with
    | some (.ct x) =>
      some (.ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x x))
    | _ => none) := rfl
  rw [e] at h
  split at h
  · next x h1 => exact ⟨x, h1, (Option.some.inj h).symm⟩
  · cases h

theorem bound_mulConst {k : ℤ} (h : refBoundBFV P E ℓ β (.mulConst d a k) = some b) :
    ∃ x, β a = some (.ct x) ∧ b = .ct (k.natAbs * (x + P.src.modulus ℓ % P.src.t)) := by
  have e : refBoundBFV P E ℓ β (.mulConst d a k) = (match β a with
    | some (.ct x) => some (.ct (k.natAbs * (x + P.src.modulus ℓ % P.src.t)))
    | _ => none) := rfl
  rw [e] at h
  split at h
  · next x h1 => exact ⟨x, h1, (Option.some.inj h).symm⟩
  · cases h

theorem bound_automorph {g : ℕ} (h : refBoundBFV P E ℓ β (.automorph d a g) = some b) :
    ∃ x, β a = some (.ct x) ∧ b = .ct (x + P.src.modulus ℓ % P.src.t) := by
  have e : refBoundBFV P E ℓ β (.automorph d a g) = (match β a with
    | some (.ct x) => some (.ct (x + P.src.modulus ℓ % P.src.t))
    | _ => none) := rfl
  rw [e] at h
  split at h
  · next x h1 => exact ⟨x, h1, (Option.some.inj h).symm⟩
  · cases h

theorem bound_relin (h : refBoundBFV P E ℓ β (.relin d a) = some b) :
    ∃ x, β a = some (.ct x) ∧ b = .ct (x + E.keySwitch) := by
  have e : refBoundBFV P E ℓ β (.relin d a) = (match β a with
    | some (.ct x) => some (.ct (x + E.keySwitch))
    | _ => none) := rfl
  rw [e] at h
  split at h
  · next x h1 => exact ⟨x, h1, (Option.some.inj h).symm⟩
  · cases h

theorem bound_keySwitch (h : refBoundBFV P E ℓ β (.keySwitch d a) = some b) :
    ∃ x, β a = some (.ct x) ∧ b = .ct (x + E.keySwitch) := by
  have e : refBoundBFV P E ℓ β (.keySwitch d a) = (match β a with
    | some (.ct x) => some (.ct (x + E.keySwitch))
    | _ => none) := rfl
  rw [e] at h
  split at h
  · next x h1 => exact ⟨x, h1, (Option.some.inj h).symm⟩
  · cases h

theorem bound_modSwitch (h : refBoundBFV P E ℓ β (.modSwitch d a) = some b) :
    ∃ x q, β a = some (.ct x) ∧ P.src.qs[ℓ]? = some q ∧
      b = .ct (x / q + E.modSwitch + P.src.modulus ℓ % P.src.t) := by
  have e : refBoundBFV P E ℓ β (.modSwitch d a) = (match β a, P.src.qs[ℓ]? with
    | some (.ct x), some q => some (.ct (x / q + E.modSwitch + P.src.modulus ℓ % P.src.t))
    | _, _ => none) := rfl
  rw [e] at h
  split at h
  · next x q h1 h2 => exact ⟨x, q, h1, h2, (Option.some.inj h).symm⟩
  · cases h

theorem ctBound_some {o : Var} {n : ℕ} (h : ctBound β o = some n) : β o = some (.ct n) := by
  have e : ctBound β o = (match β o with
    | some (.ct b) => some b
    | _ => none) := rfl
  rw [e] at h
  split at h
  · next x h1 => cases h; exact h1
  · cases h

end Ref

/-! ### The invariant -/

section Inv
variable (P : FullParams)

/-- What a tracked bound says of a variable's value and ciphertext. -/
@[reducible] def Sem (s : IntPoly P.src.N) : Bnd → Val P.src → List (IntPoly P.src.N) → Prop
  | .ct b, v, ct => Encrypts P s b v ct
  | .pt b, v, ct => TraceBFV.PlainOK P s b v ct

/-- Every tracked bound holds of the variable's ciphertext for its value. -/
def Inv (s : IntPoly P.src.N) (ρ : Env P.src) (β : Var → Option Bnd) (σ : Trace.CtEnv P) : Prop :=
  ∀ x b, β x = some b → ∃ v ct, ρ x = some v ∧ σ x = some ct ∧ Sem P s b v ct

theorem encrypts_bfv_iff (hk : P.src.kind = .bfv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (ct : List (IntPoly P.src.N)) :
    Encrypts P s B v ct ↔ ct.length = v.parts ∧ ∃ m, v.msg = .exact m ∧
      BFVEncrypts P.src.t B (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) m := by
  unfold Encrypts
  simp only [hk]
  cases h : v.msg with
  | exact m => simp [h]

variable {P}

theorem enc_elim (hk : P.src.kind = .bfv) {s : IntPoly P.src.N} {b : ℕ} {v : Val P.src}
    {ct : List (IntPoly P.src.N)} (h : Encrypts P s b v ct) :
    ∃ m, v.msg = .exact m ∧ ct.length = v.parts ∧
      NoiseLe P.src.t b (Trace.phaseAt P (P.src.modulus v.level) v.key s ct) m := by
  rw [encrypts_bfv_iff P hk] at h
  obtain ⟨hl, m, hm, -, hb⟩ := h
  exact ⟨m, hm, hl, hb⟩

theorem enc_intro (hk : P.src.kind = .bfv) (ht : 0 < P.src.t) {s : IntPoly P.src.N} {b : ℕ}
    {v : Val P.src} {ct : List (IntPoly P.src.N)} {m : Poly P.src.t P.src.N}
    (hm : v.msg = .exact m) (hl : ct.length = v.parts)
    (hn : NoiseLe P.src.t b (Trace.phaseAt P (P.src.modulus v.level) v.key s ct) m)
    (hQ : decOK P.src.t (P.src.modulus v.level) b = true) : Encrypts P s b v ct :=
  (encrypts_bfv_iff P hk s b v ct).mpr
    ⟨hl, m, hm, decrypt_of_noiseLe ht hn (decOK_iff.mp hQ), hn⟩

theorem plain_iff {s : IntPoly P.src.N} {b : ℕ} {v : Val P.src} {ct : List (IntPoly P.src.N)} :
    TraceBFV.PlainOK P s b v ct ↔ ct.length = v.parts ∧ ∃ m, v.msg = .exact m ∧
      ofInt P.src.t (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)) = m ∧
      normInf (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)) ≤ b := Iff.rfl

theorem plain_elim {s : IntPoly P.src.N} {b : ℕ} {v : Val P.src} {ct : List (IntPoly P.src.N)}
    (h : TraceBFV.PlainOK P s b v ct) :
    ∃ m, v.msg = .exact m ∧
      PlainLe P.src.t b (Trace.phaseAt P (P.src.modulus v.level) v.key s ct) m := by
  obtain ⟨-, m, hm, h1, h2⟩ := plain_iff.mp h
  exact ⟨m, hm, h1, (normInf_le_iff _ _).mp h2⟩

theorem encrypts_mono (hk : P.src.kind = .bfv) {s : IntPoly P.src.N} {b b' : ℕ} {v : Val P.src}
    {ct : List (IntPoly P.src.N)} (h : Encrypts P s b v ct) (hbb : b ≤ b') :
    Encrypts P s b' v ct := by
  rw [encrypts_bfv_iff P hk] at h ⊢
  obtain ⟨hl, m, hm, h1, h2⟩ := h
  exact ⟨hl, m, hm, h1, h2.trans hbb⟩

/-- The operand of a step: what the invariant says about it. -/
theorem operand {s : IntPoly P.src.N} {ρ : Env P.src} {β : Var → Option Bnd} {σ : Trace.CtEnv P}
    (h : Inv P s ρ β σ) {a : Var} {b : Bnd} {x : Val P.src} {ca : List (IntPoly P.src.N)}
    (hβ : β a = some b) (hx : ρ a = some x) (hc : σ a = some ca) : Sem P s b x ca := by
  obtain ⟨x', ca', hx', hc', he⟩ := h a b hβ
  rw [hx] at hx'; rw [hc] at hc'
  cases hx'; cases hc'
  exact he

theorem modulus_pos (hP : SchemeParamsOK P) (ℓ : ℕ) : 0 < P.src.modulus ℓ := by
  unfold Params.modulus
  apply List.prod_pos
  intro q hq
  exact (hP.prime q (List.mem_of_mem_take hq)).pos

end Inv

theorem ite_bind_some {p : Prop} [Decidable p] {α : Type} {f : Unit → Option α} {r : α}
    (h : (if p then some () else none).bind f = some r) : p ∧ f () = some r := by
  by_cases hp : p
  · simp only [hp, ite_true, Option.bind_some] at h; exact ⟨hp, h⟩
  · simp [hp] at h

/-- `noiseLe_modSwitch` with the modulus equation as a hypothesis. -/
theorem noiseLe_modSwitch' {N t B E Q Q' q : ℕ} (ht : 0 < t) (hQ' : 0 < Q') (hq : 0 < q)
    (hQ : Q = Q' * q) {φ : Poly Q N} {m : Poly t N} (δ : IntPoly N) (h : NoiseLe t B φ m)
    (hδ : normInf δ ≤ q * E) (hdvd : ∀ j, (q : ℤ) ∣ (centered φ).coeff j + δ.coeff j) :
    NoiseLe t (B / q + E + Q' % t)
      (ofInt Q' ⟨fun j => ((centered φ).coeff j + δ.coeff j) / q⟩) m := by
  subst hQ
  exact noiseLe_modSwitch ht hQ' hq δ h hδ hdvd

section DstOK
variable {P : FullParams}

/-- **One step.** -/
theorem dst_ok (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) {ρ ρ' : Env P.src} {σ σ' : Trace.CtEnv P} {β : Var → Option Bnd}
    {i : Instr} {b : Bnd} {v : Val P.src} (hinv : Inv P s ρ β σ)
    (hb : refBoundBFV P E v.level β i = some b)
    (hstep : step P.src ρ i = some ρ') (hv : ρ' (Trace.dst i) = some v)
    (hQ : bndOK P v.level b = true) (hok : TraceBFV.StepOK P E s ρ ρ' σ σ' i) :
    ∃ ct, σ' = σ.set (Trace.dst i) ct ∧ Sem P s b v ct := by
  have ht : 0 < P.src.t := by
    have := (hP.plaintext).1
    omega
  have hpos : ∀ ℓ, 0 < P.src.modulus ℓ := modulus_pos hP
  obtain ⟨v', ct, hv', hlen, hσ', hφ⟩ := hok
  rw [hv] at hv'; cases hv'
  refine ⟨ct, hσ', ?_⟩
  cases i with
  | add d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    obtain ⟨bx, by', hbx, hby, rfl⟩ := bound_add hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', -, hn'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨hl, hkey⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hn'
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_add ht (hpos _) hn hn'
  | sub d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    obtain ⟨bx, by', hbx, hby, rfl⟩ := bound_sub hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', -, hn'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨hl, hkey⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hn'
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_sub ht (hpos _) hn hn'
  | mul d a c =>
    obtain ⟨x, y, ca, cc, ka, kb, X, D, hx, hy, hca, hcc, hka, hkb, hD, hX, hφ⟩ := hφ
    obtain ⟨bx, by', hbx, hby, rfl⟩ := bound_mul hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', -, hn'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨hl, hkey, -⟩ := hg
    dsimp only at hφ hQ hD hX ⊢
    rw [← hl] at hn'
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_mul ht (hpos _) ka kb X D hn hn' hka hkb hD hX
  | square d a =>
    obtain ⟨x, ca, ka, X, D, hx, hca, hka, hD, hX, hφ⟩ := hφ
    obtain ⟨bx, hbx, rfl⟩ := bound_square hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, hm, Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ hD hX ⊢
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_mul ht (hpos _) ka ka X D hn hn hka hka hD hX
  | mulConst d a c =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    obtain ⟨bx, hbx, rfl⟩ := bound_mulConst hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, hm, Msg.lift₁] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_mulConst ht (hpos _) c hn
  | copy d a | toEval d a | toCoeff d a =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    have hb' : β a = some b := hb
    have hsem := operand hinv hb' hx hca
    simp [step, hx] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    cases b with
    | ct b =>
      obtain ⟨m, hm, -, hn⟩ := enc_elim hk hsem
      refine enc_intro hk ht hm hlen ?_ hQ
      rw [hφ]; exact hn
    | pt b =>
      obtain ⟨-, m, hm, h1, h2⟩ := plain_iff.mp hsem
      refine plain_iff.mpr ⟨hlen, m, hm, ?_, ?_⟩
      · rw [hφ]; exact h1
      · rw [hφ]; exact h2
  | automorph d a g =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    obtain ⟨bx, hbx, rfl⟩ := bound_automorph hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, hm, Msg.lift₁, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_automorph ht (hpos _) hP.N_pow2 hg hn
  | relin d a =>
    obtain ⟨x, ca, er, hx, hca, her, hφ⟩ := hφ
    obtain ⟨bx, hbx, rfl⟩ := bound_relin hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk ht hm hlen ?_ hQ
    rw [hφ]; exact noiseLe_keySwitch (hpos _) er hn her
  | keySwitch d a =>
    obtain ⟨x, ca, er, hx, hca, her, hφ⟩ := hφ
    obtain ⟨bx, hbx, rfl⟩ := bound_keySwitch hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk ht hm hlen ?_ hQ
    rw [hφ]; exact noiseLe_keySwitch (hpos _) er hn her
  | modSwitch d a =>
    obtain ⟨x, ca, δ, q, hx, hca, hq, hδ, hqδ, hφ⟩ := hφ
    obtain ⟨bx, q', hbx, hq', rfl⟩ := bound_modSwitch hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨hlt, hqe⟩ := List.getElem?_eq_some_iff.mp hq
    have hfacts := qLast_facts P hP _ hlt
    have hqb : P.src.qs[x.level - 1]! = q := by simp [hlt, hqe]
    rw [hqb] at hfacts
    have hqpos : 0 < q := hfacts.1.pos
    simp [step, hx, hm, hq, hk, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ hδ hqδ hq' ⊢
    rw [hq] at hq'; cases hq'
    have hQeq : P.src.modulus x.level = P.src.modulus (x.level - 1) * q := by
      rw [modulus_pred P.src x.level (by omega) (by omega), hqb]
    refine enc_intro hk ht (m := m) rfl hlen ?_ hQ
    rw [hφ]
    exact noiseLe_modSwitch' ht (hpos _) hqpos hQeq δ hn hδ hqδ
  | addPlain d a c =>
    obtain ⟨x, y, ca, cc, δ, hx, hy, hca, hcc, hδ, hφ⟩ := hφ
    obtain ⟨bx, by', hbx, hby, rfl⟩ := bound_addPlain hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hn'⟩ := plain_elim (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨-, hl⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hn'
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_addPlain ht (hpos _) δ hn hn' hδ
  | subPlain d a c =>
    obtain ⟨x, y, ca, cc, δ, hx, hy, hca, hcc, hδ, hφ⟩ := hφ
    obtain ⟨bx, by', hbx, hby, rfl⟩ := bound_subPlain hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hn'⟩ := plain_elim (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨-, hl⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hn'
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_subPlain ht (hpos _) δ hn hn' hδ
  | mulPlain d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    obtain ⟨bx, by', hbx, hby, rfl⟩ := bound_mulPlain hb
    obtain ⟨m, hm, -, hn⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hn'⟩ := plain_elim (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨-, hl, -⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hn'
    refine enc_intro hk ht rfl hlen ?_ hQ
    rw [hφ]; exact noiseLe_mulPlain ht (hpos _) hn hn'
  | dropLimbs d a k => exact hφ.elim
end DstOK

/-- `step` changes only the destination. -/
theorem step_set {Pr : Params} {ρ ρ' : Env Pr} {i : Instr} (h : step Pr ρ i = some ρ') :
    ∃ v, ρ' = ρ.set (Trace.dst i) v := by
  cases i <;> simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, guard] at h
  all_goals (simp only [Trace.dst]; aesop)

/-! ### The run -/

section Run
variable {P : FullParams}

theorem run_sound (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) : ∀ (body : List Instr) (ρ : Env P.src) (β : Var → Option Bnd)
    (r : Env P.src × (Var → Option Bnd)), AllExact ρ → refRunBFV P E body (zenv ρ) β = some r →
    ∃ ρf, body.foldlM (step P.src) ρ = some ρf ∧ r.1 = zenv ρf ∧
      ∀ σ σf, Inv P s ρ β σ → TraceBFV.Run P E s body ρ σ σf → Inv P s ρf r.2 σf := by
  intro body
  induction body with
  | nil =>
    intro ρ β r _ h
    rw [refRun_nil] at h
    cases h
    refine ⟨ρ, rfl, rfl, ?_⟩
    intro σ σf hinv hrun
    have : σf = σ := hrun
    subst this; exact hinv
  | cons i is ih =>
    intro ρ β r hρ h
    obtain ⟨ρz', vz, b, h1, h3, h2, h4, h5, -⟩ := refRun_cons_some P E h
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    rw [hz] at h1
    obtain ⟨ρ', hs, rfl⟩ := Option.map_eq_some_iff.mp h1
    have hρ' := hex ρ' hs
    obtain ⟨ρf, hf, hr, hinvf⟩ := ih ρ' _ r hρ' h5
    refine ⟨ρf, ?_, hr, ?_⟩
    · simp only [List.foldlM_cons, hs, Option.bind_eq_bind, Option.bind_some]; exact hf
    intro σ σf hinv hrun
    obtain ⟨ρ'', σ', hs', hok, hrun'⟩ := hrun
    rw [hs] at hs'; cases hs'
    simp only [zenv] at h3
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h3
    have h2' : refBoundBFV P E v.level β i = some b := h2
    have h4' : bndOK P v.level b = true := h4
    obtain ⟨ct, hσ', hct⟩ := dst_ok hk hP E s hinv h2' hs hv h4' hok
    refine hinvf σ' σf ?_ hrun'
    obtain ⟨w, hw⟩ := step_set hs
    intro y by' hy
    by_cases hyd : y = Trace.dst i
    · subst hyd
      simp only [ite_true, Option.some.injEq] at hy
      subst hy
      refine ⟨v, ct, hv, ?_, hct⟩
      rw [hσ']; simp [Trace.CtEnv.set]
    · simp only [hyd, ite_false] at hy
      obtain ⟨v', ct', h1', h2', h3'⟩ := hinv y by' hy
      refine ⟨v', ct', ?_, ?_, h3'⟩
      · rw [hw]; simp [Env.set, hyd, h1']
      · rw [hσ']; simp [Trace.CtEnv.set, hyd, h2']

end Run

/-! ### Lists -/

theorem le_foldl_max_init (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons x l ih => exact (le_max_left a x).trans (ih _)

theorem le_foldl_max {b : ℕ} : ∀ {l : List ℕ} (a : ℕ), b ∈ l → b ≤ l.foldl max a
  | x :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right a b).trans (le_foldl_max_init l _)
    · exact le_foldl_max (max a x) h

theorem mapM_some {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → ∀ o ∈ l, ∃ b ∈ bs, f o = some b
  | [], _, _, o, ho => by simp at ho
  | x :: l, bs, h, o, ho => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs', rfl⟩ := h
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨b, List.mem_cons_self .., hb⟩
    · obtain ⟨b', hb', hfb'⟩ := mapM_some f l bs' hbs' o ho
      exact ⟨b', List.mem_cons_of_mem _ hb', hfb'⟩

/-! ### The headline -/

section Main
variable {P : FullParams}

theorem refAnalyze_some {E : TraceBFV.Budget} {prog : Program} {B : ℕ}
    (h : refAnalyzeBFV P E prog = some B) :
    P.src.kind = .bfv ∧ (prog.inputs.all fun d => d.ok P.src) = true ∧
      ∃ ρz β, refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0)
        (fun x => (prog.inputs.find? (·.name = x)).map fun d =>
          if d.parts = 1 then .pt (TraceBFV.inputBound P prog d)
          else .ct (TraceBFV.inputBound P prog d)) = some (ρz, β) ∧
      (prog.outputs.all fun o => (ρz o).isSome) = true ∧
      ∃ bs, prog.outputs.mapM (ctBound β) = some bs ∧ bs.foldl max 0 = B := by
  have e : refAnalyzeBFV P E prog = (do
      guard (P.src.kind = .bfv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let β₀ : Var → Option Bnd := fun x => (prog.inputs.find? (·.name = x)).map fun d =>
        if d.parts = 1 then .pt (TraceBFV.inputBound P prog d)
        else .ct (TraceBFV.inputBound P prog d)
      let (ρ, β) ← refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0) β₀
      guard (prog.outputs.all fun o => (ρ o).isSome)
      let bs ← prog.outputs.mapM (ctBound β)
      pure (bs.foldl max 0)) := rfl
  rw [e] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard] at h
  obtain ⟨_, h0, _, hd, ⟨ρz, β⟩, h1, _, h2, bs, h3, h4⟩ := h
  have hk : P.src.kind = .bfv := by by_contra hk; simp [hk] at h0
  have hd' : (prog.inputs.all fun d => d.ok P.src) = true := by by_contra hd'; simp [hd'] at hd
  by_cases hc : (prog.outputs.all fun o => (ρz o).isSome) = true
  · exact ⟨hk, hd', ρz, β, h1, hc, bs, h3, by simpa using h4⟩
  · simp [hc] at h2

theorem refAnalyze_sound : NoiseSoundBFV refAnalyzeBFV := by
  intro P E prog B hP hk hB s msgs cts hin
  obtain ⟨-, hdecl, ρz, βf, hrun, hout, bs, hbs, hB'⟩ := refAnalyze_some hB
  have hfind : ∀ x d, prog.inputs.find? (·.name = x) = some d → d.name = x ∧
      (∃ m, msgs x = .exact m) := by
    intro x d hd
    have hn : d.name = x := by simpa using List.find?_some hd
    have he := hin x d hd
    refine ⟨hn, ?_⟩
    rw [← hn]
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, -⟩ := plain_elim he
      exact ⟨m, hm⟩
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, -⟩ := enc_elim hk he
      exact ⟨m, hm⟩
  have hρ0 : AllExact (initEnv P.src prog msgs) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact (hfind x d hd).2
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  obtain ⟨ρf, hf, hr, hinv⟩ := run_sound hk hP E s prog.body _ _ _ hρ0 hrun
  simp only at hr
  refine ⟨ρf, ?_, ?_⟩
  · have hfits : (prog.inputs.all fun dcl => (msgs dcl.name).fits P.src.kind) = true := by
      rw [List.all_eq_true]; intro dcl hdcl
      obtain ⟨d, hd⟩ : ∃ d, prog.inputs.find? (·.name = dcl.name) = some d := by
        rw [← Option.isSome_iff_exists, List.find?_isSome]
        exact ⟨dcl, hdcl, by simp⟩
      obtain ⟨m, hm⟩ := (hfind _ d hd).2
      rw [hm, hk]; rfl
    have hout' : (prog.outputs.all fun o => (ρf o).isSome) = true := by
      rw [hr] at hout; simpa [zenv] using hout
    simp only [List.all_eq_true] at hout'
    simp only [eval, hdecl, hfits, hf, guard, List.all_eq_true, Option.bind_eq_bind, ite_true,
      Option.pure_def, Option.bind_some]
    have hc : (∀ x ∈ prog.outputs, (ρf x).isSome = true) = True := eq_true hout'
    simp only [hc, ite_true, Option.bind_some]
  · intro σ hrunσ o ho
    have hinv0 : Inv P s (initEnv P.src prog msgs)
        (fun x => (prog.inputs.find? (·.name = x)).map fun d =>
          if d.parts = 1 then .pt (TraceBFV.inputBound P prog d)
          else .ct (TraceBFV.inputBound P prog d))
        (Trace.initCt P prog cts) := by
      intro x b hb
      obtain ⟨d, hd, hbe⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨hn, -⟩ := hfind x d hd
      have he := hin x d hd
      have he' : Sem P s b (inputVal P msgs d) (cts x) := by
        by_cases hp : d.parts = 1
        · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
        · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
      unfold inputVal at he'; rw [hn] at he'
      exact ⟨_, cts x, by simp [initEnv, hd], by simp [Trace.initCt, hd], he'⟩
    obtain ⟨b, hb, hβ⟩ := mapM_some (ctBound βf) _ bs hbs o ho
    obtain ⟨v, ct, hv, hct, he⟩ := hinv _ σ hinv0 hrunσ o (.ct b) (ctBound_some hβ)
    exact ⟨v, ct, hv, hct, encrypts_mono hk he (hB' ▸ le_foldl_max 0 hb)⟩

theorem refAnalyze_nonBFV (E : TraceBFV.Budget) (prog : Program) (hk : P.src.kind ≠ .bfv) :
    refAnalyzeBFV P E prog = none := by
  rcases h : refAnalyzeBFV P E prog with _ | B
  · rfl
  · exact absurd (refAnalyze_some h).1 hk

end Main

theorem phase_replicate_zero {N q : ℕ} (s : Poly q N) (n : ℕ) :
    phase s (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, phase_cons, ih]
    ext k; simp [coeff_mul']

end SoundAux

/-! ### The pins -/

open SoundAux

/-- **The decryption condition.** -/
theorem bfv_decrypt_of_noise {N : ℕ} (t Q B : ℕ) (ht : 0 < t) (s : IntPoly N)
    (ct : List (Poly Q N)) (m : Poly t N)
    (hnoise : normInf (centered (phase (ofInt Q s) ct -
      ofInt Q ⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decOK t Q B = true) : BFVEncrypts t B s ct m :=
  ⟨decrypt_of_noiseLe (φ := phase (ofInt Q s) ct) ht hnoise (decOK_iff.mp hB), hnoise⟩

/-- `Encrypts`, for BFV, in terms of `Trace.phaseAt`. -/
theorem encrypts_bfv_iff_phase (P : FullParams) (hk : P.src.kind = .bfv) (s : IntPoly P.src.N)
    (B : ℕ) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (ct : List (IntPoly P.src.N)) :
    Encrypts P s B v ct ↔
      ct.length = v.parts ∧
      (⟨fun i => (roundDiv (P.src.t *
          (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)).coeff i)
          (P.src.modulus v.level) : ZMod P.src.t)⟩ : Poly P.src.t P.src.N) = m ∧
      normInf (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct -
        ofInt (P.src.modulus v.level)
          ⟨fun i => ((P.src.modulus v.level / P.src.t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B := by
  rw [encrypts_bfv_iff P hk]
  constructor
  · rintro ⟨hl, m', hm', h1, h2⟩
    rw [hm] at hm'
    cases hm'
    exact ⟨hl, h1, h2⟩
  · rintro ⟨hl, h1, h2⟩
    exact ⟨hl, m, hm, h1, h2⟩

/-- For BFV, a ciphertext that `Encrypts` a value decrypts to its message exactly. -/
theorem encrypts_bfv_decrypts (P : FullParams) (hk : P.src.kind = .bfv) (s : IntPoly P.src.N)
    (B : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N)) (h : Encrypts P s B v ct) :
    ∃ m, v.msg = .exact m ∧
      bfvDecrypt P.src.t (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) = m := by
  obtain ⟨-, m, hm, h1, -⟩ := (encrypts_bfv_iff P hk s B v ct).mp h
  exact ⟨m, hm, h1⟩

/-- **BFV noise headline: the reference analyzer is sound.** -/
theorem refAnalyzeBFV_sound : NoiseSoundBFV refAnalyzeBFV := refAnalyze_sound

/-- **Scope.** Nothing outside BFV is accepted. -/
theorem refAnalyzeBFV_rejects_nonBFV : NoiseRejectsNonBFV refAnalyzeBFV :=
  fun _ E prog hk => refAnalyze_nonBFV E prog hk

/-- The reference analyzer rejects every program with an ill-formed input declaration. -/
theorem refAnalyzeBFV_badDecl (P : FullParams) (E : TraceBFV.Budget) (prog : Source.Program)
    (d : Decl) (hd : d ∈ prog.inputs)
    (h : d.parts = 0 ∨ d.level = 0 ∨ P.src.qs.length < d.level ∨ d.key % 2 = 0 ∨
      2 * P.src.N ≤ d.key) :
    refAnalyzeBFV P E prog = none := by
  rcases h' : refAnalyzeBFV P E prog with _ | B
  · rfl
  · have hall := (refAnalyze_some h').2.1
    have hok := List.all_eq_true.mp hall d hd
    simp only [Decl.ok, decide_eq_true_eq] at hok
    omega

/-- Every message has a BFV encryption with noise `0`. -/
theorem bfv_inputs_exist (P : FullParams) (hk : P.src.kind = .bfv) (ht : 0 < P.src.t)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (hp : 1 ≤ v.parts) (hQ : decOK P.src.t (P.src.modulus v.level) 0 = true) :
    ∃ ct, Encrypts P s 0 v ct := by
  have hQpos : 0 < P.src.modulus v.level := by
    have := decOK_iff.mp hQ
    omega
  refine ⟨scaled P.src.t (P.src.modulus v.level) m :: List.replicate (v.parts - 1) 0, ?_⟩
  refine enc_intro hk ht hm (by simp; omega) ?_ hQ
  refine noiseLe_of_eq hQpos 0 ?_ (fun i => by simp)
  unfold Trace.phaseAt
  rw [List.map_cons, phase_cons, List.map_replicate, ofInt_zero, phase_replicate_zero]
  ext k; simp [coeff_mul']

example := (@refAnalyzeBFV_sound : type_of% @Challenge.BFV.refAnalyzeBFV_sound)
example := (@refAnalyzeBFV_rejects_nonBFV : type_of% @Challenge.BFV.refAnalyzeBFV_rejects_nonBFV)
example := (@refAnalyzeBFV_badDecl : type_of% @Challenge.BFV.refAnalyzeBFV_badDecl)
example := (@bfv_decrypt_of_noise : type_of% @Challenge.BFV.bfv_decrypt_of_noise)
example := (@encrypts_bfv_iff_phase : type_of% @Challenge.BFV.encrypts_bfv_iff_phase)
example := (@encrypts_bfv_decrypts : type_of% @Challenge.BFV.encrypts_bfv_decrypts)
example := (@bfv_inputs_exist : type_of% @Challenge.BFV.bfv_inputs_exist)

end Validation.BFV
