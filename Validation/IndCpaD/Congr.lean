import Challenge.IndCpaD.Defs
import Validation.CertifyBFV.Library
import Validation.Budget.RunExists

/-!
# Validation.IndCpaD.Congr — what the library's execution reads
-/

namespace Validation.IndCpaD
open Spec NPoly Scheme Source Spec.CertifyBFV Challenge.CertifyBFV Challenge.IndCpaD Spec.IndCpaDBFV
  Challenge.RealizeBFV

/-! No `Challenge.*` definition is named in `simp`, `rw` or `unfold` here (that would generate
equation lemmas in the `Challenge` namespace inside this module, which the gate refuses): the
definitions are unfolded by `rfl`, `exact` up to definitional equality, or the local `rfl`
equation `runLibraryAux_cons`. -/

theorem ksBFV_inputNoise (P : FullParams) (n : ℕ) (lay : Budget.KSLayout) (ℓ : ℕ)
    (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksBFV { P with inputNoise := n } lay ℓ d keys = ksBFV P lay ℓ d keys := by
  cases P; rfl

theorem relinBFV_inputNoise (P : FullParams) (n : ℕ) (lay : Budget.KSLayout) (ℓ : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    relinBFV { P with inputNoise := n } lay ℓ ca keys = relinBFV P lay ℓ ca keys := by
  cases P; rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, cs⟩⟩⟩⟩ <;> rfl

theorem keySwitchBFV_inputNoise (P : FullParams) (n : ℕ) (lay : Budget.KSLayout) (ℓ : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    keySwitchBFV { P with inputNoise := n } lay ℓ ca keys = keySwitchBFV P lay ℓ ca keys := by
  cases P; rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, cs⟩⟩⟩ <;> rfl

theorem libKS_inputNoise (x : InputBFV) (n : ℕ) (A : Spec.Float.Arith) (m ℓ : ℕ)
    (ca : List (IntPoly x.P.src.N)) (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)) :
    libKS { x with P := { x.P with inputNoise := n } } A m ℓ ca keys = libKS x A m ℓ ca keys := by
  obtain ⟨P, lay, prog, mul, ft, pa, ms, dr⟩ := x
  cases P
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, cs⟩⟩⟩⟩ <;> rfl

theorem libStep_inputNoise (x : InputBFV) (n : ℕ) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (m : ℕ) (ρ : Env x.P.src)
    (σ : Trace.CtEnv x.P) (i : Instr) :
    libStep { x with P := { x.P with inputNoise := n } } A rk gk m ρ σ i =
      libStep x A rk gk m ρ σ i := by
  cases i
  case relin d a =>
    exact libKS_inputNoise x n A m (levelOf ρ a) ((σ a).getD []) rk
  case keySwitch d a =>
    exact congrArg (List.map (automorph (((ρ a).map (·.key)).getD 1)))
      (libKS_inputNoise x n A m (levelOf ρ a)
        (((σ a).getD []).map (automorph (rotInv x.P.src.N (((ρ a).map (·.key)).getD 1))))
        (gk (((ρ a).map (·.key)).getD 1)))
  all_goals rfl

/-- One step of `runLibraryAux`, as a local `rfl` equation. -/
theorem runLibraryAux_cons (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (m : ℕ) (i : Instr)
    (is : List Instr) (ρ : Env x.P.src) (σ : Trace.CtEnv x.P) :
    runLibraryAux x A rk gk m (i :: is) ρ σ =
      (match step x.P.src ρ i with
        | some ρ' => runLibraryAux x A rk gk (m + 1) is ρ' (σ.set (Trace.dst i) (libStep x A rk gk m ρ σ i))
        | none => σ) := rfl

theorem runLibraryAux_inputNoise (x : InputBFV) (n : ℕ) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (body : List Instr) :
    ∀ (m : ℕ) (ρ : Env x.P.src) (σ : Trace.CtEnv x.P),
    runLibraryAux { x with P := { x.P with inputNoise := n } } A rk gk m body ρ σ =
      runLibraryAux x A rk gk m body ρ σ := by
  induction body with
  | nil => intro m ρ σ; rfl
  | cons i is ih =>
    intro m ρ σ
    rw [runLibraryAux_cons, runLibraryAux_cons, libStep_inputNoise]
    cases step x.P.src ρ i with
    | none => rfl
    | some ρ' => exact ih _ _ _

theorem libStep_gk_congr (x : InputBFV) (rots : List ℕ) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk gk' : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hg : ∀ g ∈ rots, gk g = gk' g) (m : ℕ) (ρ : Env x.P.src) (σ : Trace.CtEnv x.P) (i : Instr)
    (hi : (match i with
        | .keySwitch _ a => rots.contains (((ρ a).map (·.key)).getD 1)
        | _ => true) = true) :
    libStep x A rk gk m ρ σ i = libStep x A rk gk' m ρ σ i := by
  cases i
  case keySwitch d a =>
    have hi' : ((ρ a).map (·.key)).getD 1 ∈ rots := List.contains_iff_mem.mp hi
    exact congrArg (libKeySwitch x A m (levelOf ρ a) (((ρ a).map (·.key)).getD 1) ((σ a).getD []))
      (hg _ hi')
  all_goals rfl

theorem runLibraryAux_gk_congr (x : InputBFV) (rots : List ℕ) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk gk' : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hg : ∀ g ∈ rots, gk g = gk' g) (body : List Instr) :
    ∀ (m : ℕ) (ρ : Env x.P.src) (σ : Trace.CtEnv x.P),
    ksKeysIn x.P.src rots body ρ = true →
    runLibraryAux x A rk gk m body ρ σ = runLibraryAux x A rk gk' m body ρ σ := by
  induction body with
  | nil => intro m ρ σ _; rfl
  | cons i is ih =>
    intro m ρ σ hks
    rw [runLibraryAux_cons, runLibraryAux_cons]
    simp only [ksKeysIn] at hks
    cases hs : step x.P.src ρ i with
    | none => rfl
    | some ρ' =>
      rw [hs] at hks
      simp only [Bool.and_eq_true] at hks
      rw [libStep_gk_congr x rots A rk gk gk' hg m ρ σ i hks.1]
      exact ih _ _ _ hks.2

/-- G2: the library's execution does not read the declared input noise. -/
theorem runLibrary_inputNoise (x : InputBFV) (n : ℕ) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (cts : Var → List (IntPoly x.P.src.N)) :
    runLibrary { x with P := { x.P with inputNoise := n } } A rk gk cts = runLibrary x A rk gk cts :=
  runLibraryAux_inputNoise x n A rk gk _ _ _ _

/-- G4a: the library's execution reads the rotation keys only at the indices of its key
switches in the message-independent replay. -/
theorem runLibrary_gk_congr (x : InputBFV) (rots : List ℕ) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk gk' : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (cts : Var → List (IntPoly x.P.src.N))
    (hks : ksKeysIn x.P.src rots x.prog.body (initEnv x.P.src x.prog fun _ => .exact 0) = true)
    (hg : ∀ g ∈ rots, gk g = gk' g) :
    runLibrary x A rk gk cts = runLibrary x A rk gk' cts :=
  runLibraryAux_gk_congr x rots A rk gk gk' hg _ _ _ _ hks

/-- G4b: valid rotation keys exist for every odd index and every secret (when `N` is a power of
two, `σ_g` is injective, so the keys are valid for the only `s'` with `σ_g(s') = s`). -/
theorem galoisKeys_exist (P : FullParams) (lay : Budget.KSLayout) (ℓ : ℕ)
    (hN : ∃ k, P.src.N = 2 ^ k) (g : ℕ) (hg : g % 2 = 1) (s : IntPoly P.src.N) :
    ∃ keys : List (IntPoly P.src.N × IntPoly P.src.N),
      ∀ s', automorph g s' = s → Budget.GadgetKeysOK P lay ℓ (.galois g) s' keys := by
  obtain ⟨keys, hk⟩ :=
    Validation.Budget.RunAux.gadgetKeys_exist P lay ℓ (.galois g) (automorph (rotInv P.src.N g) s)
  refine ⟨keys, fun s' hs' => ?_⟩
  have : s' = automorph (rotInv P.src.N g) s := by
    rw [← hs', Validation.CertifyBFV.rotInv_automorph _ _ hN hg]
  rw [this]; exact hk

/-- G4c (non-vacuity pin `Challenge.IndCpaD.keysOK_exist`, same statement). -/
theorem keysOK_exist (St : Setting) (hN : ∃ k, St.base.P.src.N = 2 ^ k)
    (hodd : ∀ g ∈ St.rots, g % 2 = 1) (s : IntPoly St.base.P.src.N)
    (hs : SecretOK St.base.P.secretBound s) :
    ∃ (pk : PK (St := St)) (e : IntPoly St.base.P.src.N), KeysOK pk ⟨s, e⟩ := by
  obtain ⟨rk, hrk⟩ :=
    Validation.Budget.RunAux.gadgetKeys_exist St.base.P St.base.lay (top St) .square s
  have hgk : ∀ g, ∃ keys : List (IntPoly St.base.P.src.N × IntPoly St.base.P.src.N),
      g ∈ St.rots → ∀ s', automorph g s' = s →
        Budget.GadgetKeysOK St.base.P St.base.lay (top St) (.galois g) s' keys := by
    intro g
    by_cases hg : g ∈ St.rots
    · obtain ⟨keys, hk⟩ := galoisKeys_exist St.base.P St.base.lay (top St) hN g (hodd g hg) s
      exact ⟨keys, fun _ => hk⟩
    · exact ⟨[], fun h => absurd h hg⟩
  choose gk hgk using hgk
  refine ⟨⟨0, 0, rk, gk⟩, 0, hs, ?_, ?_, hrk, fun g hg s' hs' => hgk g hg s' hs'⟩
  · rw [Validation.Scheme.normInf_zero]; exact Nat.zero_le _
  · show ofInt _ (0 + 0 * s) = ofInt _ (((1 : ℕ) : ℤ) • (0 : IntPoly St.base.P.src.N))
    have : NeZero St.base.P.src.N :=
      ⟨by obtain ⟨k, hk⟩ := hN; rw [hk]; exact pow_ne_zero _ two_ne_zero⟩
    rw [zero_mul, add_zero, smul_zero]

end Validation.IndCpaD
