import Challenge.CertifyBFV.Library
import Validation.CertifyBFV
import Validation.RealizeBFV
import Validation.BFVMul.Scaled

/-!
# Validation.CertifyBFV.Library — proofs of `Challenge.CertifyBFV.Library`

* The key switch (`certifyBFV?_libRelin`, `certifyBFV?_libKeySwitch`): under
  `HPSPOVERQLEVELED` at the top level, `FHE.BFV.KSLeveled.leveledKS_phase` with the transcribed
  core (`Validation.RealizeBFV.ksBFV_coreOK_top`) and the bound of `ks_facts`; otherwise the core
  at the operand's level within `ksBoundAt`. With drop `0` the arithmetic is replaced by the exact
  one (`Validation.BFVMul.leveledKS_drop_zero`). The rotation is the key switch for
  `(s', σ_g(s') = s)` of the operand rotated back by `σ_g⁻¹`, followed by `σ_g`.
* The composition (`certifyBFV?_library_run`): induction along the body with the invariants of
  the soundness proof (`Validation.BFV.SoundAux.Inv`: each tracked variable meets its bound), the
  shape and the levels; each step is one of the realizability pins at `c.budget n`.
-/

namespace Validation.CertifyBFV
open Spec NPoly Scheme Source Correct Spec.BudgetBFV Challenge.BFV Challenge.BFVMul
open Spec.CertifyBFV Challenge.CertifyBFV Challenge.RealizeBFV

/-! ## Unfolding `libKS` -/

theorem libKS_top {x : InputBFV} {Ps : List ℕ} (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (n ℓ : ℕ) (htop : ℓ = x.P.src.qs.length)
    (ca : List (IntPoly x.P.src.N)) (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)) :
    libKS x A n ℓ ca keys =
      Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take ℓ) (x.drops.getD n 0)
        (fun c => ksBFV x.P x.lay (ℓ - x.drops.getD n 0) c keys) ca := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm
  exact if_pos htop

theorem libKS_plain {x : InputBFV} (A : Spec.Float.Arith) (n ℓ : ℕ)
    (hnot : ¬((∃ Ps, x.mul = some (.leveled Ps)) ∧ ℓ = x.P.src.qs.length))
    (ca : List (IntPoly x.P.src.N)) (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)) :
    libKS x A n ℓ ca keys =
      if ca.length = 3 then relinBFV x.P x.lay ℓ ca keys else keySwitchBFV x.P x.lay ℓ ca keys := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  rcases mul with _ | m
  · rfl
  · cases m with
    | leveled Ps =>
      have : ℓ ≠ P.src.qs.length := fun h => hnot ⟨⟨Ps, rfl⟩, h⟩
      exact if_neg this
    | _ => rfl

/-- The arithmetic of a leveled key switch: `A` itself if it drops limbs (then `Conforms A` is
available), the exact one otherwise (the result does not depend on it). -/
theorem leveled_sums (A : Spec.Float.Arith) (dr : ℕ) (hA : dr ≠ 0 → Spec.Float.Conforms A) :
    ∃ S : Fl.Sums, Fl.SumsOK S ∧ ∀ {N : ℕ} (qs : List ℕ) (core : IntPoly N → IntPoly N × IntPoly N)
      (ct : List (IntPoly N)), Fl.leveledKS (Fl.floatSums A) qs dr core ct =
        Fl.leveledKS S qs dr core ct := by
  by_cases h0 : dr = 0
  · subst h0
    exact ⟨_, Validation.BFVMul.floatSums_ok _ Validation.BFVMul.exact_conforms,
      fun qs core ct => Validation.BFVMul.leveledKS_drop_zero A Spec.Float.exact qs core ct⟩
  · exact ⟨_, Validation.BFVMul.floatSums_ok A (hA h0), fun _ _ _ => rfl⟩

/-! ## Relinearization -/

theorem libRelin_aux (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hks : ksDeclOK? x.P x.lay = true) (A : Spec.Float.Arith) (n : ℕ)
    (hA : (∃ Ps, x.mul = some (.leveled Ps)) → x.drops.getD n 0 ≠ 0 → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (d a : Var) (ρ ρ' : Env x.P.src)
    (hat : AtInstr x msgs n (.relin d a) ρ) (σ : Trace.CtEnv x.P) (xa : Val x.P.src)
    (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.relin d a) = some ρ') (hx : ρ a = some xa) (ha : σ a = some ca)
    (hla : ca.length = xa.parts) (h1 : 1 ≤ xa.level) (hL : xa.level ≤ x.P.src.qs.length) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ (σ.set d (libKS x A n xa.level ca rk))
      (.relin d a) := by
  obtain ⟨hP, hk, hS, hlay, -⟩ := certifyBFV?_paramsOK x c h
  have h3 : xa.parts = 3 := by
    simp only [step, hx, guard] at hstep
    by_cases hg : xa.parts = 3 ∧ xa.key = 1
    · exact hg.1
    · simp [hg] at hstep
  by_cases hlev : (∃ Ps, x.mul = some (.leveled Ps)) ∧ xa.level = x.P.src.qs.length
  · obtain ⟨⟨Ps, hm⟩, htop⟩ := hlev
    rw [libKS_top hm A n xa.level htop]
    obtain ⟨hdrop, haux, hE⟩ := ks_facts h hm hin hat (i := .relin d a) rfl hx htop
      (x.P.src.N * x.P.secretBound * x.P.secretBound) (fun _ _ => rfl)
    obtain ⟨S, hSok, hSeq⟩ := leveled_sums A (x.drops.getD n 0) (hA ⟨Ps, hm⟩)
    rw [hSeq]
    have hco := Validation.RealizeBFV.ksBFV_coreOK_top x.P x.lay hP hk hS hks
      (xa.level - x.drops.getD n 0) (by omega) (by omega)
      (hlay _ (by omega) (by omega)).2 s hs .square rk hrk
    exact Validation.BFVMul.stepOK_relin_leveled_tol x.P S hSok hP (c.budget n) s hs ρ ρ' σ d a xa
      ca (x.drops.getD n 0) (ksBoundAt x.P x.lay (xa.level - x.drops.getD n 0)) _ hco hE hstep hx
      ha (by omega) hL hdrop haux
  · rw [libKS_plain A n xa.level hlev, if_pos (by omega)]
    obtain ⟨-, -, -, hks', -⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
    have hE := hks' d a xa (Or.inl rfl) hx
    have hkeys := Validation.Budget.gadgetKeys_restrict x.P x.lay .square hP xa.level hL
      (hlay _ h1 hL).2 (fun hb => by rw [hk] at hb; cases hb) s rk hrk
    have := Validation.RealizeBFV.relinBFV_stepOK x.P x.lay hP hS hks xa.level h1 hL
      (hlay _ h1 hL).1 (c.budget n) hE s hs _ hkeys ρ ρ' σ d a xa ca hstep hx ha rfl hla
    have e : relinBFV x.P x.lay xa.level ca (rk.take (x.lay.sizes xa.level).length) =
        relinBFV x.P x.lay xa.level ca rk := by
      obtain ⟨c0, c1, c2, rfl⟩ : ∃ c0 c1 c2, ca = [c0, c1, c2] := by
        rw [h3] at hla
        match ca, hla with
        | [c0, c1, c2], _ => exact ⟨_, _, _, rfl⟩
      show [_, _] = [_, _]
      rw [Validation.RealizeBFV.ksBFV_take x.P x.lay hks xa.level h1 hL]
    rwa [e] at this

/-! ## Key switch: rotation by the operand's key -/

theorem rotInv_mul (N g : ℕ) (hN : ∃ k, N = 2 ^ k) (hg : g % 2 = 1) :
    (rotInv N g * g) % (2 * N) = 1 := by
  obtain ⟨k, rfl⟩ := hN
  have h2 : 1 < 2 * 2 ^ k := by have := Nat.one_le_two_pow (n := k); omega
  have : NeZero (2 * 2 ^ k) := ⟨by omega⟩
  have hcop : Nat.Coprime g (2 * 2 ^ k) := by
    rw [← pow_succ']
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr
      (by omega))))
  have h := ZMod.coe_mul_inv_eq_one g hcop
  have h' : (((rotInv (2 ^ k) g * g : ℕ)) : ZMod (2 * 2 ^ k)) = ((1 : ℕ) : ZMod (2 * 2 ^ k)) := by
    rw [Nat.cast_mul, show rotInv (2 ^ k) g = ((g : ZMod (2 * 2 ^ k))⁻¹).val from rfl,
      ZMod.natCast_zmod_val, Nat.cast_one]; exact (mul_comm _ _).trans h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  rw [h', Nat.mod_eq_of_lt h2]

theorem rotInv_odd (N g : ℕ) (hN : ∃ k, N = 2 ^ k) (hg : g % 2 = 1) : rotInv N g % 2 = 1 := by
  have h := rotInv_mul N g hN hg
  obtain ⟨k, rfl⟩ := hN
  have h' : rotInv (2 ^ k) g * g % 2 = 1 := by
    have := Nat.mod_mod_of_dvd (rotInv (2 ^ k) g * g) (dvd_mul_right 2 (2 ^ k))
    rw [← this, h]
  rw [Nat.mul_mod, hg, mul_one, Nat.mod_mod] at h'
  exact h'

/-- `σ_g ∘ σ_{g⁻¹} = id`. -/
theorem automorph_rotInv {R : Type} [CommRing R] (N g : ℕ) (hN : ∃ k, N = 2 ^ k)
    (hg : g % 2 = 1) (a : NPoly R N) : automorph g (automorph (rotInv N g) a) = a := by
  rw [Validation.Source.automorph_automorph hg, ← Validation.Source.automorph_mod,
    rotInv_mul N g hN hg, FHE.KeySwitch.automorph_one]

/-- `σ_{g⁻¹} ∘ σ_g = id`. -/
theorem rotInv_automorph {R : Type} [CommRing R] (N g : ℕ) (hN : ∃ k, N = 2 ^ k)
    (hg : g % 2 = 1) (a : NPoly R N) : automorph (rotInv N g) (automorph g a) = a := by
  rw [Validation.Source.automorph_automorph (rotInv_odd N g hN hg), ← Validation.Source.automorph_mod,
    mul_comm, rotInv_mul N g hN hg, FHE.KeySwitch.automorph_one]

theorem libKeySwitch_aux (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hks : ksDeclOK? x.P x.lay = true) (A : Spec.Float.Arith) (n : ℕ)
    (hA : (∃ Ps, x.mul = some (.leveled Ps)) → x.drops.getD n 0 ≠ 0 → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (d a : Var) (ρ ρ' : Env x.P.src)
    (hat : AtInstr x msgs n (.keySwitch d a) ρ) (σ : Trace.CtEnv x.P) (xa : Val x.P.src)
    (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some xa) (ha : σ a = some ca)
    (hla : ca.length = xa.parts) (hodd : xa.key % 2 = 1) (h1 : 1 ≤ xa.level)
    (hL : xa.level ≤ x.P.src.qs.length)
    (s' : IntPoly x.P.src.N) (hs' : automorph xa.key s' = s)
    (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hkeys : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois xa.key) s' keys) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (libKeySwitch x A n xa.level xa.key ca keys)) (.keySwitch d a) := by
  obtain ⟨hP, hk, hS, hlay, -⟩ := certifyBFV?_paramsOK x c h
  have : NeZero x.P.src.N := Validation.RealizeBFV.neZero_N x.P hP
  have h2 : xa.parts = 2 := by
    simp only [step, hx, guard] at hstep
    by_cases hg : xa.parts = 2
    · exact hg
    · simp [hg] at hstep
  obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, ca = [m0, m1] := by
    rw [h2] at hla
    match ca, hla with
    | [m0, m1], _ => exact ⟨_, _, rfl⟩
  set g := xa.key with hgdef
  set gi := rotInv x.P.src.N g with hgi
  set Q := x.P.src.modulus xa.level with hQ
  have hs'b : SecretOK x.P.secretBound s' :=
    (Validation.Realize.normInf_le_of_automorph_eq hP.N_pow2 hodd hs').trans hs
  have hT : KeyTarget.eval s' (.galois g) = s := hs'
  -- the key switch of the operand rotated back: phase under `s'` within the budget
  have hcore : ∃ y0 y1 e : IntPoly x.P.src.N,
      libKS x A n xa.level [automorph gi m0, automorph gi m1] keys = [y0, y1] ∧
      normInf e ≤ (c.budget n).keySwitch ∧
      ofInt Q y0 + ofInt Q y1 * ofInt Q s' =
        ofInt Q (automorph gi m0) + ofInt Q (automorph gi m1) * ofInt Q s + ofInt Q e := by
    by_cases hlev : (∃ Ps, x.mul = some (.leveled Ps)) ∧ xa.level = x.P.src.qs.length
    · obtain ⟨⟨Ps, hm⟩, htop⟩ := hlev
      rw [libKS_top hm A n xa.level htop]
      obtain ⟨hdrop, haux, hE⟩ := ks_facts h hm hin hat (i := .keySwitch d a) rfl hx htop
        x.P.secretBound (fun _ _ => rfl)
      obtain ⟨S, hSok, hSeq⟩ := leveled_sums A (x.drops.getD n 0) (hA ⟨Ps, hm⟩)
      rw [hSeq, FHE.BFV.KSLeveled.leveledKS_two]
      have hco := Validation.RealizeBFV.ksBFV_coreOK_top x.P x.lay hP hk hS hks
        (xa.level - x.drops.getD n 0) (by omega) (by omega)
        (hlay _ (by omega) (by omega)).2 s' hs'b (.galois g) keys hkeys
      rw [hT] at hco
      obtain ⟨hfq, -, hpos, hcop⟩ := FHE.BFV.FloatPOverQ.floatAuxOK_imp haux
      rw [List.append_nil] at hpos hcop
      obtain ⟨hb1, hb2, hb3⟩ := Validation.BFVMul.leveled_basis x.P xa.level (x.drops.getD n 0) hL
        hpos
      have hco' : KSCoreOK ((x.P.src.qs.take xa.level).take
          ((x.P.src.qs.take xa.level).length - x.drops.getD n 0)).prod
          (ksBoundAt x.P x.lay (xa.level - x.drops.getD n 0)) s' s
          (fun c => ksBFV x.P x.lay (xa.level - x.drops.getD n 0) c keys) := by
        rw [hb1]; exact hco
      obtain ⟨err, he, hn1, hn2⟩ := FHE.BFV.KSLeveled.leveledKS_phase S hSok
        (x.P.src.qs.take xa.level) ((x.P.src.qs.take xa.level).length - x.drops.getD n 0) hpos
        hcop hfq s' s _ x.P.secretBound hs _ hco' (automorph gi m1)
      refine ⟨_, _, err, rfl, ?_, ?_⟩
      · by_cases hd : x.drops.getD n 0 = 0
        · rw [ite_eq_left hd] at hE
          exact (hn2 (by rw [List.length_take]; omega)).trans hE
        · rw [ite_eq_right hd, hb3] at hE
          rw [hb2] at hn1
          exact hn1.trans hE
      · have he' : ofInt Q _ + ofInt Q _ * ofInt Q s' =
            ofInt Q (automorph gi m1) * ofInt Q s + ofInt Q err := he
        rw [Validation.Scheme.ofInt_add]
        linear_combination he'
    · rw [libKS_plain A n xa.level hlev, if_neg (by simp)]
      obtain ⟨-, -, -, hks', -⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
      have hE := hks' d a xa (Or.inr rfl) hx
      have hco := Validation.RealizeBFV.ksBFV_coreOK_top x.P x.lay hP hk hS hks xa.level h1 hL
        (hlay _ h1 hL).2 s' hs'b (.galois g) keys hkeys
      rw [hT] at hco
      obtain ⟨e, hb, heq⟩ := (FHE.BFV.KSLeveled.KSCoreOK_def _ _ _ _ _).mp hco (automorph gi m1)
      refine ⟨_, _, e, rfl, hb.trans hE, ?_⟩
      rw [Validation.Scheme.ofInt_add]
      linear_combination heq
  obtain ⟨y0, y1, e, hout, he, heq⟩ := hcore
  have hlib : libKeySwitch x A n xa.level g [m0, m1] keys = [automorph g y0, automorph g y1] := by
    unfold libKeySwitch
    rw [List.map_cons, List.map_cons, List.map_nil, hout]
    rfl
  rw [hlib]
  refine Validation.RealizeBFV.keySwitch_stepOK_of_automorph_error x.P hP (c.budget n) s hstep hx
    ha hodd e he rfl ?_
  have hN := hP.N_pow2
  simp only [Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase]
  have hp := Validation.RealizeBFV.phase_automorph_pair Q hodd s s' hs' y0 y1
  have hp' : ofInt Q (automorph g y0) + ofInt Q (automorph g y1) * ofInt Q s =
      ofInt Q m0 + ofInt Q m1 * ofInt Q (automorph g s) + automorph g (ofInt Q e) := by
    rw [hp, heq, Validation.Source.automorph_add, Validation.Source.automorph_add,
      Validation.Source.automorph_mul hodd, ← Validation.Scheme.ofInt_automorph,
      ← Validation.Scheme.ofInt_automorph, ← Validation.Scheme.ofInt_automorph,
      automorph_rotInv _ _ hN hodd, automorph_rotInv _ _ hN hodd]
  linear_combination hp'

/-! ## Unfolding the library's other steps -/

theorem libPlain_rounded {x : InputBFV} (hpa : x.plainAdd = some .rounded) (Q : ℕ) f ca c :
    libPlain x Q f ca c =
      Challenge.Source.padZip f ca [scaleUp x.P.src.t Q (centered (ofInt Q c))] := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hpa; rfl

theorem libPlain_scaled {x : InputBFV} (hpa : x.plainAdd = some .scaled) (Q : ℕ) f ca c :
    libPlain x Q f ca c =
      Challenge.Source.padZip f ca [ceilScale x.P.src.t Q (centered (ofInt Q c))] := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hpa; rfl

theorem libPlain_delta {x : InputBFV} (hpa : x.plainAdd ≠ some .rounded ∧ x.plainAdd ≠ some .scaled)
    (Q : ℕ) f ca c :
    libPlain x Q f ca c = Challenge.Source.padZip f ca [((Q / x.P.src.t : ℕ) : ℤ) • c] := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  rcases pa with _ | (_ | _ | _)
  · rfl
  · rfl
  · exact absurd rfl hpa.1
  · exact absurd rfl hpa.2

theorem plainAddAt_rounded {x : InputBFV} (hpa : x.plainAdd = some .rounded) (ℓ : ℕ) :
    plainAddAt x ℓ = plainAddRoundedAt x.P ℓ (maxPlainBound x.P x.prog) := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hpa; rfl

theorem plainAddAt_scaled {x : InputBFV} (hpa : x.plainAdd = some .scaled) (ℓ : ℕ) :
    plainAddAt x ℓ = plainAddScaledAt x.P ℓ (maxPlainBound x.P x.prog) := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hpa; rfl

theorem libMul_none {x : InputBFV} (hm : x.mul = none ∨ x.mul = some .textbook) A n ℓ ca cb :
    libMul x A n ℓ ca cb = bfvMul x.P.src.t (x.P.src.modulus ℓ) ca cb := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  rcases hm with hm | hm <;> cases hm <;> rfl

theorem libMul_hps {x : InputBFV} {R : List ℕ} (hm : x.mul = some (.hps R)) A n ℓ ca cb :
    libMul x A n ℓ ca cb = Fl.hpsMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take ℓ) R ca cb := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm; rfl

theorem libMul_poverq {x : InputBFV} {Ps : List ℕ} (hm : x.mul = some (.poverq Ps)) A n ℓ ca cb :
    libMul x A n ℓ ca cb =
      Fl.poverqMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take ℓ) (Ps.take ℓ) ca cb := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm; rfl

theorem libMul_leveled {x : InputBFV} {Ps : List ℕ} (hm : x.mul = some (.leveled Ps)) A n ℓ ca cb :
    libMul x A n ℓ ca cb =
      if ℓ = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0 then
        Fl.leveledMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take ℓ) Ps (x.drops.getD n 0) ca cb
      else Fl.poverqMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take ℓ) (Ps.take ℓ) ca cb := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm; rfl

theorem libMul_behz {x : InputBFV} {B : List ℕ} {msk mt : ℕ} (hm : x.mul = some (.behz B msk mt))
    A n ℓ ca cb :
    libMul x A n ℓ ca cb = behzMul x.P.src.t (x.P.src.qs.take ℓ) B msk mt ca cb := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm; rfl

/-! ## Facts from the certificate -/

theorem body_at {x : InputBFV} {msgs : Var → Msg x.P.src.t x.P.src.N} {n : ℕ} {i : Instr}
    {ρ : Env x.P.src} (hat : AtInstr x msgs n i ρ) : x.prog.body[n]? = some i := by
  obtain ⟨pre, post, hb, rfl, -⟩ := hat
  rw [hb, List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl

/-- No `square` under the P-over-Q techniques (item 3 of `checksOK`). -/
theorem noSquare {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
    (hm : (∃ Ps, x.mul = some (.poverq Ps)) ∨ ∃ Ps, x.mul = some (.leveled Ps)) :
    x.prog.body.any isSquare = false := by
  have hc := (certifyBFV?_some h).1
  unfold checksOK at hc
  obtain ⟨hc, -⟩ := band hc
  obtain ⟨hc, -⟩ := band hc
  obtain ⟨hc, -⟩ := band hc
  obtain ⟨hc, -⟩ := band hc
  obtain ⟨-, h10⟩ := band hc
  rcases hm with ⟨Ps, hm⟩ | ⟨Ps, hm⟩ <;> rw [hm] at h10 <;> simpa using h10

/-- The platform hypothesis at a key switch with a nonzero drop. -/
theorem conforms_ks {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
    (hft : x.floatTol = false →
      (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
      ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
    {A : Spec.Float.Arith} (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    {n : ℕ} {i : Instr} (hn : x.prog.body[n]? = some i) (hi : isKS i = true) :
    (∃ Ps, x.mul = some (.leveled Ps)) → x.drops.getD n 0 ≠ 0 → Spec.Float.Conforms A := by
  rintro ⟨Ps, hm⟩ hd
  have hks : ksDropped x = true := (ksDropped_iff x).mpr ⟨n, i, hn, hi, hd⟩
  cases hf : x.floatTol
  · rw [(hft hf).2 Ps hm] at hks; cases hks
  · exact hA ((certifyBFV?_assumed x c h).1.mpr ⟨hf, Or.inr ⟨⟨n, i, hn, hi, hd⟩, Ps, hm⟩⟩)

/-- The platform hypothesis and `floatTol` at a multiplication of the HPS family. -/
theorem conforms_mul {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
    (hft : x.floatTol = false →
      (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
      ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
    {A : Spec.Float.Arith} (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    (hne : c.mulLevels ≠ [])
    (hfam : (∃ R, x.mul = some (.hps R)) ∨ (∃ Ps, x.mul = some (.poverq Ps)) ∨
      ∃ Ps, x.mul = some (.leveled Ps)) :
    x.floatTol = true ∧ Spec.Float.Conforms A := by
  cases hf : x.floatTol
  · exfalso
    rcases (hft hf).1 with h0 | h0 | ⟨B, msk, mt, h0⟩
    · exact hne h0
    · rcases hfam with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> rw [h0] at h1 <;> cases h1
    · rcases hfam with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> rw [h0] at h1 <;> cases h1
  · exact ⟨rfl, hA ((certifyBFV?_assumed x c h).1.mpr ⟨hf, Or.inl ⟨hne, hfam⟩⟩)⟩

/-! ## Plaintext addition with the centred representative -/

/-- `ceilScale` is within one unit of `Q·p/t`. -/
theorem ceilScale_near (t Q : ℕ) (ht : 0 < t) {N : ℕ} (p : IntPoly N) (i : Fin N) :
    |(t : ℤ) * (ceilScale t Q p).coeff i - (Q : ℤ) * p.coeff i| ≤ t := by
  show |(t : ℤ) * -((-((Q : ℤ) * p.coeff i)) / (t : ℤ)) - (Q : ℤ) * p.coeff i| ≤ t
  have htz : (0 : ℤ) < t := by exact_mod_cast ht
  have h1 := Int.mul_ediv_add_emod (-((Q : ℤ) * p.coeff i)) t
  have h2 := Int.emod_nonneg (-((Q : ℤ) * p.coeff i)) htz.ne'
  have h3 := Int.emod_lt_of_pos (-((Q : ℤ) * p.coeff i)) htz
  have e : (t : ℤ) * -((-((Q : ℤ) * p.coeff i)) / (t : ℤ)) - (Q : ℤ) * p.coeff i =
      (-((Q : ℤ) * p.coeff i)) % t := by linarith
  rw [e, abs_of_nonneg h2]; exact h3.le

/-- **Changing the stored plaintext to another with the same residues modulo `Q`** keeps an
`addPlain` step. -/
theorem stepOK_addPlain_transfer (P : FullParams) (E : TraceBFV.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a p : Var) (hap : a ≠ p) (c c' : IntPoly P.src.N)
    (hσp : σ p = some [c])
    (hcc : ∀ v, ρ' d = some v →
      ofInt (P.src.modulus v.level) c' = ofInt (P.src.modulus v.level) c)
    (ct : List (IntPoly P.src.N))
    (hok : TraceBFV.StepOK P E s ρ ρ' (σ.set p [c']) ((σ.set p [c']).set d ct) (.addPlain d a p)) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ct) (.addPlain d a p) := by
  obtain ⟨v, ct', hv, hlen, hσ', x, y, ca, cb, δ, hx, hy, ha, hb, hδ, hφ⟩ := hok
  have hct : ct' = ct := by
    have := congrFun hσ' d
    simp [Trace.CtEnv.set, Trace.dst] at this
    exact this.symm
  subst hct
  have ha' : σ a = some ca := by simpa [Trace.CtEnv.set, hap] using ha
  have hb' : cb = [c'] := by simpa [Trace.CtEnv.set] using hb.symm
  subst hb'
  refine ⟨v, ct', hv, hlen, rfl, x, y, ca, [c], δ, hx, hy, ha', hσp, hδ, ?_⟩
  rw [hφ]
  simp only [Trace.phaseAt, List.map, hcc v hv]

theorem stepOK_subPlain_transfer (P : FullParams) (E : TraceBFV.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a p : Var) (hap : a ≠ p) (c c' : IntPoly P.src.N)
    (hσp : σ p = some [c])
    (hcc : ∀ v, ρ' d = some v →
      ofInt (P.src.modulus v.level) c' = ofInt (P.src.modulus v.level) c)
    (ct : List (IntPoly P.src.N))
    (hok : TraceBFV.StepOK P E s ρ ρ' (σ.set p [c']) ((σ.set p [c']).set d ct) (.subPlain d a p)) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ct) (.subPlain d a p) := by
  obtain ⟨v, ct', hv, hlen, hσ', x, y, ca, cb, δ, hx, hy, ha, hb, hδ, hφ⟩ := hok
  have hct : ct' = ct := by
    have := congrFun hσ' d
    simp [Trace.CtEnv.set, Trace.dst] at this
    exact this.symm
  subst hct
  have ha' : σ a = some ca := by simpa [Trace.CtEnv.set, hap] using ha
  have hb' : cb = [c'] := by simpa [Trace.CtEnv.set] using hb.symm
  subst hb'
  refine ⟨v, ct', hv, hlen, rfl, x, y, ca, [c], δ, hx, hy, ha', hσp, hδ, ?_⟩
  rw [hφ]
  simp only [Trace.phaseAt, List.map, hcc v hv]

/-! ## The invariants of the composition -/

section Comp
open Validation.BFV Validation.BFV.SoundAux
open Validation.Budget.RunAux (Shape Levels levels_step)

/-- Every defined variable has at least one component. -/
def PartsPos {Pr : Params} (ρ : Env Pr) : Prop := ∀ y v, ρ y = some v → 1 ≤ v.parts

/-- Every tracked plaintext bound is at most the largest declared one. -/
def PtB (x : InputBFV) (β : Var → Option TraceBFV.Bnd) : Prop :=
  ∀ y b, β y = some (.pt b) → b ≤ maxPlainBound x.P x.prog

theorem partsPos_set {Pr : Params} {ρ : Env Pr} (h : PartsPos ρ) (d : Var) (v : Val Pr)
    (hv : 1 ≤ v.parts) : PartsPos (ρ.set d v) := by
  intro y w hw
  simp only [Env.set] at hw
  split_ifs at hw
  · cases hw; exact hv
  · exact h y w hw

theorem partsPos_step {Pr : Params} {ρ ρ' : Env Pr} {i : Instr} (h : PartsPos ρ)
    (hstep : step Pr ρ i = some ρ') : PartsPos ρ' := by
  cases i with
  | add d a b | sub d a b | addPlain d a b | subPlain d a b | mul d a b | mulPlain d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨hg, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    have hxa := h a x hx
    have hyb := h b y hy
    refine partsPos_set h _ _ ?_
    first
    | (show 1 ≤ max x.parts y.parts; omega)
    | (show 1 ≤ x.parts + y.parts - 1; omega)
    | exact hxa
  | square d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨hg, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    exact partsPos_set h _ _ (by show 1 ≤ 2 * x.parts - 1; omega)
  | mulConst d a _ | copy d a | toEval d a | toCoeff d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hstep
    subst hstep
    exact partsPos_set h _ _ (h a x hx)
  | relin d a | keySwitch d a | automorph d a _ | dropLimbs d a _ =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨hg, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    cases h2
    refine partsPos_set h _ _ ?_
    first | (show 1 ≤ 2; omega) | exact h a x hx
  | modSwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨hg, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    obtain ⟨q, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    exact partsPos_set h _ _ (h a x hx)

/-- A plaintext bound produced by the reference analysis is one it already tracked. -/
theorem refBound_pt {P : FullParams} {E : TraceBFV.Budget} {ℓ : ℕ}
    {β : Var → Option TraceBFV.Bnd} {i : Instr} {b : ℕ}
    (h : refBoundBFV P E ℓ β i = some (.pt b)) : ∃ y, β y = some (.pt b) := by
  cases i with
  | copy d a | toEval d a | toCoeff d a => exact ⟨a, h⟩
  | add d a c => obtain ⟨_, _, -, -, h'⟩ := bound_add h; cases h'
  | sub d a c => obtain ⟨_, _, -, -, h'⟩ := bound_sub h; cases h'
  | addPlain d a c => obtain ⟨_, _, -, -, h'⟩ := bound_addPlain h; cases h'
  | subPlain d a c => obtain ⟨_, _, -, -, h'⟩ := bound_subPlain h; cases h'
  | mulPlain d a c => obtain ⟨_, _, -, -, h'⟩ := bound_mulPlain h; cases h'
  | mul d a c => obtain ⟨_, _, -, -, h'⟩ := bound_mul h; cases h'
  | square d a => obtain ⟨_, -, h'⟩ := bound_square h; cases h'
  | mulConst d a _ => obtain ⟨_, -, h'⟩ := bound_mulConst h; cases h'
  | automorph d a _ => obtain ⟨_, -, h'⟩ := bound_automorph h; cases h'
  | relin d a => obtain ⟨_, -, h'⟩ := bound_relin h; cases h'
  | keySwitch d a => obtain ⟨_, -, h'⟩ := bound_keySwitch h; cases h'
  | modSwitch d a => obtain ⟨_, _, -, -, h'⟩ := bound_modSwitch h; cases h'
  | dropLimbs d a k =>
    have e : refBoundBFV P E ℓ β (.dropLimbs d a k) = none := rfl
    rw [e] at h; cases h

theorem getD_of {α : Type} {o : Option (List α)} {l : List α} (h : o = some l) : o.getD [] = l := by
  rw [h]; rfl

/-- The guards of a plaintext addition. -/
theorem plain_guard {Pr : Params} {ρ ρ' : Env Pr} {i : Instr} {d a p : Var}
    (hi : i = .addPlain d a p ∨ i = .subPlain d a p) {xa xp : Val Pr}
    (hstep : step Pr ρ i = some ρ') (hx : ρ a = some xa) (hy : ρ p = some xp) :
    xp.parts = 1 ∧ xa.level = xp.level ∧ ∀ v, ρ' d = some v → v.level = xa.level := by
  rcases hi with rfl | rfl <;>
  · simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨⟨h1, h2⟩, h3⟩ := Validation.Trace.guard_bind_eq_some hstep
    obtain ⟨m, -, h4⟩ := Option.bind_eq_some_iff.mp h3
    cases h4
    refine ⟨h1, h2, fun v hv => ?_⟩
    simp [Env.set] at hv
    rw [← hv]

end Comp

/-! ## One step of the library -/

section Steps
open Validation.BFV Validation.BFV.SoundAux
open Validation.Budget.RunAux (Shape Levels levels_step)

variable {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
  (hft : x.floatTol = false →
    (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
    ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
  {A : Spec.Float.Arith} (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
  {s : IntPoly x.P.src.N} (hs : SecretOK x.P.secretBound s)
  {msgs : Var → Msg x.P.src.t x.P.src.N} {cts : Var → List (IntPoly x.P.src.N)}
  (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)

include h hft hA hs hin in
/-- **The library's multiplication** at a `mul` meets the contract within the budget. -/
theorem lib_mul_ok (n : ℕ) (d a b : Var) (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ (σ.set d (libMul x A n xa.level ca cb))
      (.mul d a b) := by
  have hne : c.mulLevels ≠ [] := by
    obtain ⟨pre, post, hbody, -, hρ⟩ := hat
    have := certifyBFV?_mulLevels x c h s msgs cts hin pre post _ hbody ρ hρ a xa
      (Or.inl ⟨d, b, rfl⟩) hx
    exact List.ne_nil_of_mem this
  rcases hm : x.mul with _ | m
  · rw [libMul_none (Or.inl hm)]
    exact certifyBFV?_textbook_mul x c h s hs msgs cts hin n d a b ρ ρ' hat σ xa xb ca cb hstep hx
      hy ha hb hla hlb h2x h2y
  · cases m with
    | textbook =>
      rw [libMul_none (Or.inr hm)]
      exact certifyBFV?_textbook_mul x c h s hs msgs cts hin n d a b ρ ρ' hat σ xa xb ca cb hstep
        hx hy ha hb hla hlb h2x h2y
    | hps R =>
      obtain ⟨hf, hA'⟩ := conforms_mul h hft hA hne (Or.inl ⟨R, hm⟩)
      rw [libMul_hps hm]
      exact certifyBFV?_hps_mul_float x c h R hm hf A hA' s hs msgs cts hin n d a b ρ ρ' hat σ xa
        xb ca cb hstep hx hy ha hb hla hlb h2x h2y
    | poverq Ps =>
      obtain ⟨hf, hA'⟩ := conforms_mul h hft hA hne (Or.inr (Or.inl ⟨Ps, hm⟩))
      rw [libMul_poverq hm]
      exact certifyBFV?_poverq_mul_float x c h Ps hm hf A hA' s hs msgs cts hin n d a b ρ ρ' hat σ
        xa xb ca cb hstep hx hy ha hb hla hlb h2x h2y
    | leveled Ps =>
      obtain ⟨hf, hA'⟩ := conforms_mul h hft hA hne (Or.inr (Or.inr ⟨Ps, hm⟩))
      rw [libMul_leveled hm]
      exact certifyBFV?_leveled_mul_float x c h Ps hm hf A hA' s hs msgs cts hin n d a b ρ ρ' hat
        σ xa xb ca cb hstep hx hy ha hb hla hlb h2x h2y
    | behz B msk mt =>
      rw [libMul_behz hm]
      exact certifyBFV?_behz_mul x c h B msk mt hm s hs msgs cts hin n d a b ρ ρ' hat σ xa xb ca cb
        hstep hx hy ha hb hla hlb h2x h2y

include h hft hA hs hin in
/-- **The library's squaring** at a `square` meets the contract within the budget. -/
theorem lib_square_ok (n : ℕ) (d a : Var) (ρ ρ' : Env x.P.src)
    (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ (σ.set d (libMul x A n xa.level ca ca))
      (.square d a) := by
  have hne : c.mulLevels ≠ [] := by
    obtain ⟨pre, post, hbody, -, hρ⟩ := hat
    have := certifyBFV?_mulLevels x c h s msgs cts hin pre post _ hbody ρ hρ a xa
      (Or.inr ⟨d, rfl⟩) hx
    exact List.ne_nil_of_mem this
  have hsq : x.prog.body.any isSquare = true := by
    obtain ⟨pre, post, hbody, -, -⟩ := hat
    rw [hbody, List.any_eq_true]
    exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩
  rcases hm : x.mul with _ | m
  · rw [libMul_none (Or.inl hm)]
    exact certifyBFV?_textbook_square x c h s hs msgs cts hin n d a ρ ρ' hat σ xa ca hstep hx ha
      hla h2x
  · cases m with
    | textbook =>
      rw [libMul_none (Or.inr hm)]
      exact certifyBFV?_textbook_square x c h s hs msgs cts hin n d a ρ ρ' hat σ xa ca hstep hx ha
        hla h2x
    | hps R =>
      obtain ⟨hf, hA'⟩ := conforms_mul h hft hA hne (Or.inl ⟨R, hm⟩)
      rw [libMul_hps hm]
      exact certifyBFV?_hps_square_float x c h R hm hf A hA' s hs msgs cts hin n d a ρ ρ' hat σ xa
        ca hstep hx ha hla h2x
    | poverq Ps =>
      rw [noSquare h (Or.inl ⟨Ps, hm⟩)] at hsq; cases hsq
    | leveled Ps =>
      rw [noSquare h (Or.inr ⟨Ps, hm⟩)] at hsq; cases hsq
    | behz B msk mt =>
      rw [libMul_behz hm]
      exact certifyBFV?_behz_square x c h B msk mt hm s hs msgs cts hin n d a ρ ρ' hat σ xa ca
        hstep hx ha hla h2x

end Steps

/-! ## Every step of the library -/

theorem libStep_keySwitch (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (n : ℕ) (ρ : Env x.P.src)
    (σ : Trace.CtEnv x.P) (d a : Var) :
    libStep x A rk gk n ρ σ (.keySwitch d a) =
      libKeySwitch x A n (levelOf ρ a) (((ρ a).map (·.key)).getD 1) ((σ a).getD [])
        (gk (((ρ a).map (·.key)).getD 1)) := rfl

section Run
open Validation.BFV Validation.BFV.SoundAux Validation.BFV.PerInstrAux
open Validation.Budget.RunAux (Shape Levels levels_step)

variable {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
  (hks : ksDeclOK? x.P x.lay = true)
  (hft : x.floatTol = false →
    (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
    ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
  {A : Spec.Float.Arith} (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
  {s : IntPoly x.P.src.N} (hs : SecretOK x.P.secretBound s)
  {rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N)}
  (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
  {gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)}
  (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
    Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
  {msgs : Var → Msg x.P.src.t x.P.src.N} {cts : Var → List (IntPoly x.P.src.N)}
  (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)

include h hks hft hA hs hrk hgk hin in
/-- **One instruction of the library** meets its contract within its budget. -/
theorem lib_stepOK (n : ℕ) (i : Instr) (ρ ρ' : Env x.P.src) (σ : Trace.CtEnv x.P)
    (β : Var → Option TraceBFV.Bnd) (v : Val x.P.src) (b : TraceBFV.Bnd)
    (hat : AtInstr x msgs n i ρ) (hstep : step x.P.src ρ i = some ρ')
    (hv : ρ' (Trace.dst i) = some v) (hb : refBoundBFV x.P (c.budget n) v.level β i = some b)
    (hdom : domainOK ρ i = true) (hsh : Shape x.P ρ σ) (hlv : Levels x.P ρ)
    (hpp : PartsPos ρ) (hinv : Inv x.P s ρ β σ) (hpt : PtB x β)
    (hodd : FHE.BFV.KSLeveled.KeyOdd ρ) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set (Trace.dst i) (libStep x A rk gk n (zenv ρ) σ i)) i := by
  obtain ⟨hP, hk, hS, hlay, -⟩ := certifyBFV?_paramsOK x c h
  have hlvl : ∀ a xa, ρ a = some xa → levelOf (zenv ρ) a = xa.level := fun a xa hx => by
    rw [levelOf_zenv, levelOf_some hx]
  have ht : 0 < x.P.src.t := by
    have := (hP.plaintext).1
    omega
  -- the operands of a plaintext addition or subtraction
  have hplain : ∀ d a p, (i = .addPlain d a p ∨ i = .subPlain d a p) →
      ∃ xa xp ca c0, ρ a = some xa ∧ ρ p = some xp ∧ σ a = some ca ∧ σ p = some [c0] ∧
        ca.length = xa.parts ∧ 1 ≤ xa.parts ∧ a ≠ p ∧
        normInf (centered (ofInt (x.P.src.modulus xa.level) c0)) ≤
          maxPlainBound x.P x.prog ∧
        (∀ v, ρ' d = some v → v.level = xa.level) ∧
        (c.budget n).plainAdd = plainAddAt x xa.level := by
    intro d a p hi
    have hβ : ∃ bx by', β a = some (.ct bx) ∧ β p = some (.pt by') := by
      rcases hi with rfl | rfl
      · obtain ⟨bx, by', h1, h2, -⟩ := bound_addPlain hb; exact ⟨bx, by', h1, h2⟩
      · obtain ⟨bx, by', h1, h2, -⟩ := bound_subPlain hb; exact ⟨bx, by', h1, h2⟩
    obtain ⟨bx, by', hβa, hβp⟩ := hβ
    have hap : a ≠ p := by
      intro e; rw [e, hβp] at hβa; cases hβa
    rcases hx : ρ a with _ | xa
    · rcases hi with rfl | rfl <;> simp [step, hx] at hstep
    rcases hy : ρ p with _ | xp
    · rcases hi with rfl | rfl <;> simp [step, hx, hy] at hstep
    obtain ⟨hp1, hlev, hdl⟩ := plain_guard hi hstep hx hy
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨cp, hcp, hlp⟩ := hsh p xp hy
    rw [hp1] at hlp
    obtain ⟨c0, rfl⟩ : ∃ c0, cp = [c0] := by
      match cp, hlp with
      | [c0], _ => exact ⟨c0, rfl⟩
    have hsem := operand hinv hβp hy hcp
    obtain ⟨-, m, -, -, hnorm⟩ := plain_iff.mp hsem
    simp only [Trace.phaseAt, List.map, phase] at hnorm
    rw [npoly_mul_zero, npoly_add_zero] at hnorm
    rw [← hlev] at hnorm
    obtain ⟨-, -, -, -, hpa⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
    exact ⟨xa, xp, ca, c0, rfl, rfl, ha, hcp, hla, hpp a xa hx, hap,
      hnorm.trans (hpt p by' hβp), hdl, hpa d a p xa hi hx⟩
  cases i with
  | add d a b' =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    rcases hy : ρ b' with _ | xb
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨cb, hcb, hlb⟩ := hsh b' xb hy
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (Challenge.Source.padZip (· + ·) ((σ a).getD []) ((σ b').getD []))) _
    rw [getD_of ha, getD_of hcb]
    exact Validation.BFV.stepOK_add_padded x.P _ s ρ ρ' σ d a b' xa xb ca cb hstep hx hy ha hcb
      hla hlb
  | sub d a b' =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    rcases hy : ρ b' with _ | xb
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨cb, hcb, hlb⟩ := hsh b' xb hy
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (Challenge.Source.padZip (· - ·) ((σ a).getD []) ((σ b').getD []))) _
    rw [getD_of ha, getD_of hcb]
    exact Validation.BFVMul.stepOK_sub_padded x.P _ s ρ ρ' σ d a b' xa xb ca cb hstep hx hy ha
      hcb hla hlb
  | addPlain d a p =>
    obtain ⟨xa, xp, ca, c0, hx, hy, ha, hcp, hla, h1, hap, hc', hdl, hpa⟩ :=
      hplain d a p (Or.inl rfl)
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (libPlain x (x.P.src.modulus (levelOf (zenv ρ) a)) (· + ·) ((σ a).getD [])
        (((σ p).getD []).headD 0))) _
    rw [getD_of ha, getD_of hcp, hlvl a xa hx]
    have hcc : ∀ v, ρ' d = some v → ofInt (x.P.src.modulus v.level)
        (centered (ofInt (x.P.src.modulus xa.level) c0)) = ofInt (x.P.src.modulus v.level) c0 :=
      fun v hv => by rw [hdl v hv, Validation.Scheme.ofInt_centered]
    have ha' : (σ.set p [centered (ofInt (x.P.src.modulus xa.level) c0)]) a = some ca := by
      simp [Trace.CtEnv.set, hap, ha]
    have hp' : (σ.set p [centered (ofInt (x.P.src.modulus xa.level) c0)]) p =
        some [centered (ofInt (x.P.src.modulus xa.level) c0)] := by simp [Trace.CtEnv.set]
    rcases hpm : x.plainAdd with _ | (_ | _ | _)
    · rw [libPlain_delta (by simp [hpm])]
      exact Validation.BFV.stepOK_addPlain_textbook x.P _ s ρ ρ' σ d a p xa xp ca c0 hstep hx hy
        ha hcp hla
    · rw [libPlain_delta (by simp [hpm])]
      exact Validation.BFV.stepOK_addPlain_textbook x.P _ s ρ ρ' σ d a p xa xp ca c0 hstep hx hy
        ha hcp hla
    · rw [libPlain_rounded hpm]
      refine stepOK_addPlain_transfer x.P _ s ρ ρ' σ d a p hap c0 _ hcp hcc _ ?_
      exact Validation.BFVMul.stepOK_addPlain_rounded x.P hP _ s ρ ρ' _ d a p xa xp ca _ _ hc'
        (le_of_eq (by rw [hpa, plainAddAt_rounded hpm])) hstep hx hy ha' hp' hla h1
    · rw [libPlain_scaled hpm]
      refine stepOK_addPlain_transfer x.P _ s ρ ρ' σ d a p hap c0 _ hcp hcc _ ?_
      exact Validation.BFVMul.stepOK_addPlain_scaled x.P hP ht _ s ρ ρ' _ d a p xa xp ca _ _ _ hc'
        (ceilScale_near _ _ ht _) (le_of_eq (by rw [hpa, plainAddAt_scaled hpm])) hstep hx hy ha'
        hp' hla h1
  | subPlain d a p =>
    obtain ⟨xa, xp, ca, c0, hx, hy, ha, hcp, hla, h1, hap, hc', hdl, hpa⟩ :=
      hplain d a p (Or.inr rfl)
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (libPlain x (x.P.src.modulus (levelOf (zenv ρ) a)) (· - ·) ((σ a).getD [])
        (((σ p).getD []).headD 0))) _
    rw [getD_of ha, getD_of hcp, hlvl a xa hx]
    have hcc : ∀ v, ρ' d = some v → ofInt (x.P.src.modulus v.level)
        (centered (ofInt (x.P.src.modulus xa.level) c0)) = ofInt (x.P.src.modulus v.level) c0 :=
      fun v hv => by rw [hdl v hv, Validation.Scheme.ofInt_centered]
    have ha' : (σ.set p [centered (ofInt (x.P.src.modulus xa.level) c0)]) a = some ca := by
      simp [Trace.CtEnv.set, hap, ha]
    have hp' : (σ.set p [centered (ofInt (x.P.src.modulus xa.level) c0)]) p =
        some [centered (ofInt (x.P.src.modulus xa.level) c0)] := by simp [Trace.CtEnv.set]
    rcases hpm : x.plainAdd with _ | (_ | _ | _)
    · rw [libPlain_delta (by simp [hpm])]
      exact Validation.BFV.stepOK_subPlain_textbook x.P _ s ρ ρ' σ d a p xa xp ca c0 hstep hx hy
        ha hcp hla
    · rw [libPlain_delta (by simp [hpm])]
      exact Validation.BFV.stepOK_subPlain_textbook x.P _ s ρ ρ' σ d a p xa xp ca c0 hstep hx hy
        ha hcp hla
    · rw [libPlain_rounded hpm]
      refine stepOK_subPlain_transfer x.P _ s ρ ρ' σ d a p hap c0 _ hcp hcc _ ?_
      exact Validation.BFVMul.stepOK_subPlain_rounded x.P hP _ s ρ ρ' _ d a p xa xp ca _ _ hc'
        (le_of_eq (by rw [hpa, plainAddAt_rounded hpm])) hstep hx hy ha' hp' hla h1
    · rw [libPlain_scaled hpm]
      refine stepOK_subPlain_transfer x.P _ s ρ ρ' σ d a p hap c0 _ hcp hcc _ ?_
      exact Validation.BFVMul.stepOK_subPlain_scaled x.P hP ht _ s ρ ρ' _ d a p xa xp ca _ _ _ hc'
        (ceilScale_near _ _ ht _) (le_of_eq (by rw [hpa, plainAddAt_scaled hpm])) hstep hx hy ha'
        hp' hla h1
  | mulPlain d a p =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | xp
    · simp [step, hx, hy] at hstep
    have hp1 : xp.parts = 1 := by
      simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
      exact (Validation.Trace.guard_bind_eq_some hstep).1.1
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨cp, hcp, hlp⟩ := hsh p xp hy
    rw [hp1] at hlp
    obtain ⟨c0, rfl⟩ : ∃ c0, cp = [c0] := by
      match cp, hlp with
      | [c0], _ => exact ⟨c0, rfl⟩
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (((σ a).getD []).map ((((σ p).getD []).headD 0) * ·))) _
    rw [getD_of ha, getD_of hcp]
    exact Validation.BFV.stepOK_mulPlain_textbook x.P _ s ρ ρ' σ d a p xa xp ca c0 hstep hx hy ha
      hcp hla
  | mul d a b' =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    rcases hy : ρ b' with _ | xb
    · simp [step, hx, hy] at hstep
    rw [dom_mul, hx, hy] at hdom
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hdom
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨cb, hcb, hlb⟩ := hsh b' xb hy
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (libMul x A n (levelOf (zenv ρ) a) ((σ a).getD []) ((σ b').getD []))) _
    rw [getD_of ha, getD_of hcb, hlvl a xa hx]
    exact lib_mul_ok h hft hA hs hin n d a b' ρ ρ' hat σ xa xb ca cb hstep hx hy ha hcb
      (hla.trans hdom.1) (hlb.trans hdom.2) hdom.1 hdom.2
  | square d a =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    rw [dom_sq, hx] at hdom
    simp only [Option.any_some, beq_iff_eq] at hdom
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (libMul x A n (levelOf (zenv ρ) a) ((σ a).getD []) ((σ a).getD []))) _
    rw [getD_of ha, hlvl a xa hx]
    exact lib_square_ok h hft hA hs hin n d a ρ ρ' hat σ xa ca hstep hx ha (hla.trans hdom) hdom
  | mulConst d a k =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    show TraceBFV.StepOK _ _ _ _ _ _ (σ.set d (((σ a).getD []).map (k • ·))) _
    rw [getD_of ha]
    exact Validation.BFVMul.stepOK_mulConst_textbook x.P _ s ρ ρ' σ d a k xa ca hstep hx ha hla
  | copy d a =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    show TraceBFV.StepOK _ _ _ _ _ _ (σ.set d ((σ a).getD [])) _
    rw [getD_of ha]
    exact Validation.BFV.stepOK_copy_textbook x.P _ s ρ ρ' σ _ d a xa ca (Or.inl rfl) hstep hx ha
      hla
  | toEval d a =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    show TraceBFV.StepOK _ _ _ _ _ _ (σ.set d ((σ a).getD [])) _
    rw [getD_of ha]
    exact Validation.BFV.stepOK_copy_textbook x.P _ s ρ ρ' σ _ d a xa ca (Or.inr (Or.inl rfl))
      hstep hx ha hla
  | toCoeff d a =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    show TraceBFV.StepOK _ _ _ _ _ _ (σ.set d ((σ a).getD [])) _
    rw [getD_of ha]
    exact Validation.BFV.stepOK_copy_textbook x.P _ s ρ ρ' σ _ d a xa ca (Or.inr (Or.inr rfl))
      hstep hx ha hla
  | automorph d a g =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    show TraceBFV.StepOK _ _ _ _ _ _ (σ.set d (((σ a).getD []).map (automorph g))) _
    rw [getD_of ha]
    exact Validation.BFVMul.stepOK_automorph_textbook x.P hP _ s ρ ρ' σ d a g xa ca hstep hx ha
      hla
  | relin d a =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨h1, hL⟩ := hlv a xa hx
    show TraceBFV.StepOK _ _ _ _ _ _ (σ.set d (libKS x A n (levelOf (zenv ρ) a) ((σ a).getD []) rk)) _
    rw [getD_of ha, hlvl a xa hx]
    exact libRelin_aux x c h hks A n (conforms_ks h hft hA (body_at hat) rfl) s hs rk hrk
      msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla h1 hL
  | keySwitch d a =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨h1, hL⟩ := hlv a xa hx
    have hg : ((zenv ρ a).map (·.key)).getD 1 = xa.key := by simp [zenv, zv, hx]
    rw [show Trace.dst (.keySwitch d a) = d from rfl, libStep_keySwitch, getD_of ha, hlvl a xa hx,
      hg]
    have hodd' : xa.key % 2 = 1 := hodd a xa hx
    have hs' := automorph_rotInv x.P.src.N xa.key hP.N_pow2 hodd' s
    exact libKeySwitch_aux x c h hks A n (conforms_ks h hft hA (body_at hat) rfl) s hs msgs
      cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla hodd' h1 hL _ hs' (gk xa.key)
      (hgk xa.key _ hodd' hs')
  | modSwitch d a =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    rw [dom_ms, hx] at hdom
    simp only [Option.any_some, beq_iff_eq] at hdom
    obtain ⟨ca, ha, hla⟩ := hsh a xa hx
    obtain ⟨-, hL⟩ := hlv a xa hx
    obtain ⟨hms, -⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
    show TraceBFV.StepOK _ _ _ _ _ _
      (σ.set d (((σ a).getD []).map (bfvModSwitchComp x.P.src.qs[levelOf (zenv ρ) a - 1]!))) _
    rw [getD_of ha, hlvl a xa hx]
    exact Validation.BFV.stepOK_modSwitch_textbook x.P hP _ (le_of_eq hms.symm) s hs ρ ρ' σ d a xa
      ca hstep hx ha hL hdom (hla.trans hdom)
  | dropLimbs d a k =>
    rcases hx : ρ a with _ | xa
    · simp [step, hx] at hstep
    simp [step, hx, hk, guard] at hstep

end Run

/-! ## The composition -/

section Comp2
open Validation.BFV Validation.BFV.SoundAux Validation.BFV.PerInstrAux
open Validation.Budget.RunAux (Shape Levels levels_step)

variable {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
  (hks : ksDeclOK? x.P x.lay = true)
  (hft : x.floatTol = false →
    (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
    ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
  {A : Spec.Float.Arith} (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
  {s : IntPoly x.P.src.N} (hs : SecretOK x.P.secretBound s)
  {rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N)}
  (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
  {gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)}
  (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
    Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
  {msgs : Var → Msg x.P.src.t x.P.src.N} {cts : Var → List (IntPoly x.P.src.N)}
  (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)

theorem runLibraryAux_cons (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (n : ℕ) (i : Instr)
    (is : List Instr) (ρ ρ' : Env x.P.src) (σ : Trace.CtEnv x.P)
    (hstep : step x.P.src ρ i = some ρ') :
    runLibraryAux x A rk gk n (i :: is) ρ σ =
      runLibraryAux x A rk gk (n + 1) is ρ' (σ.set (Trace.dst i) (libStep x A rk gk n ρ σ i)) := by
  show (match step x.P.src ρ i with
    | some ρ' => runLibraryAux x A rk gk (n + 1) is ρ' (σ.set (Trace.dst i) (libStep x A rk gk n ρ σ i))
    | none => σ) = _
  rw [hstep]

include h hks hft hA hs hrk hgk hin in
/-- **The induction along the body.** -/
theorem lib_run : ∀ (body pre : List Instr) (ρ : Env x.P.src) (σ : Trace.CtEnv x.P)
    (β : Var → Option TraceBFV.Bnd) (r : Env x.P.src × (Var → Option TraceBFV.Bnd)),
    x.prog.body = pre ++ body →
    pre.foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ →
    AllExact ρ → Shape x.P ρ σ → Levels x.P ρ → PartsPos ρ → Inv x.P s ρ β σ → PtB x β →
    FHE.BFV.KSLeveled.KeyOdd ρ →
    refRunBFVAt x.P c.budget pre.length body (zenv ρ) β = some r →
    TraceBFV.RunAt x.P c.budget s pre.length body ρ σ
      (runLibraryAux x A rk gk pre.length body (zenv ρ) σ)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | i :: is, pre, ρ, σ, β, r, hbody, hρf, hρ, hsh, hlv, hpp, hinv, hpt, hodd, hr => by
    obtain ⟨hP, hk, -⟩ := certifyBFV?_paramsOK x c h
    obtain ⟨ρz', vz, b, h1, h2, h3, h4, h5, hdom⟩ := refRunAt_cons_some x.P hr
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    rw [hz] at h1
    obtain ⟨ρ', hstep, rfl⟩ := Option.map_eq_some_iff.mp h1
    simp only [zenv] at h2
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h2
    have h3' : refBoundBFV x.P (c.budget pre.length) v.level β i = some b := h3
    have h4' : bndOK x.P v.level b = true := h4
    rw [domainOK_zenv] at hdom
    have hat : AtInstr x msgs pre.length i ρ := ⟨pre, is, hbody, rfl, hρf⟩
    have hok := lib_stepOK h hks hft hA hs hrk hgk hin pre.length i ρ ρ' σ β v b hat hstep hv h3'
      hdom hsh hlv hpp hinv hpt hodd
    set σ' := σ.set (Trace.dst i) (libStep x A rk gk pre.length (zenv ρ) σ i) with hσ'
    -- the invariant of the soundness proof
    obtain ⟨ct, hσct, hct⟩ := dst_ok hk hP (c.budget pre.length) s hinv h3' hstep hv h4' hok
    obtain ⟨w, hw⟩ := step_set hstep
    have hinv' : Inv x.P s ρ' (fun y => if y = Trace.dst i then some b else β y) σ' := by
      intro y by' hy
      by_cases hyd : y = Trace.dst i
      · subst hyd
        simp only [ite_true, Option.some.injEq] at hy
        subst hy
        refine ⟨v, ct, hv, ?_, hct⟩
        rw [hσct]; simp [Trace.CtEnv.set]
      · simp only [hyd, ite_false] at hy
        obtain ⟨v', ct', h1', h2', h3''⟩ := hinv y by' hy
        refine ⟨v', ct', ?_, ?_, h3''⟩
        · rw [hw]; simp [Env.set, hyd, h1']
        · rw [hσct]; simp [Trace.CtEnv.set, hyd, h2']
    have hpt' : PtB x (fun y => if y = Trace.dst i then some b else β y) := by
      intro y b' hb'
      by_cases hyd : y = Trace.dst i
      · simp only [hyd, ite_true, Option.some.injEq] at hb'
        subst hb'
        obtain ⟨y', hy'⟩ := refBound_pt h3'
        exact hpt y' b' hy'
      · simp only [hyd, ite_false] at hb'
        exact hpt y b' hb'
    have hρf' : (pre ++ [i]).foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ' := by
      rw [List.foldlM_append, hρf]
      simp [hstep]
    have hlen : (pre ++ [i]).length = pre.length + 1 := by simp
    have ih := lib_run is (pre ++ [i]) ρ' σ' _ r (by rw [hbody]; simp) hρf' (hex ρ' hstep)
      (shape_step hsh hstep hok) (levels_step hlv hstep) (partsPos_step hpp hstep) hinv' hpt'
      (FHE.BFV.KSLeveled.step_keyOdd i hstep hodd) (by rw [hlen]; exact h5)
    rw [hlen] at ih
    rw [runLibraryAux_cons x A rk gk pre.length i is (zenv ρ) (zenv ρ') σ (by rw [hz, hstep]; rfl)]
    exact ⟨ρ', σ', hstep, hok, ih⟩

end Comp2

open Validation.BFV Validation.BFV.SoundAux Validation.BFV.PerInstrAux in
theorem library_run_aux (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hks : ksDeclOK? x.P x.lay = true)
    (hft : x.floatTol = false →
      (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
      ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
    (A : Spec.Float.Arith) (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
      Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
      (Trace.initCt x.P x.prog cts) (runLibrary x A rk gk cts) := by
  obtain ⟨hP, -, -, -, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, -, -, -, hB, -⟩ := certifyBFV?_spec x c h
  obtain ⟨hk, hdecl, ρz, βf, hrun, -⟩ := refAnalyzeAt_some hB
  have hfind : ∀ y d, x.prog.inputs.find? (·.name = y) = some d →
      d.name = y ∧ (cts y).length = d.parts := by
    intro y d hd
    have hn : d.name = y := by simpa using List.find?_some hd
    refine ⟨hn, ?_⟩
    have he := hin y d hd
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte] at he
      exact he.1
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, hl, -⟩ := enc_elim hk he
      exact hl
  have hz0 : zenv (initEnv x.P.src x.prog msgs) = initEnv x.P.src x.prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  have hdok : ∀ y v, initEnv x.P.src x.prog msgs y = some v →
      1 ≤ v.parts ∧ 1 ≤ v.level ∧ v.level ≤ x.P.src.qs.length := by
    intro y v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.1, hok.2.1, hok.2.2.1⟩
  have hinv0 : Inv x.P s (initEnv x.P.src x.prog msgs)
      (fun y => (x.prog.inputs.find? (·.name = y)).map fun d =>
        if d.parts = 1 then .pt (TraceBFV.inputBound x.P x.prog d)
        else .ct (TraceBFV.inputBound x.P x.prog d))
      (Trace.initCt x.P x.prog cts) := by
    intro y b hb
    obtain ⟨d, hd, hbe⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨hn, -⟩ := hfind y d hd
    have he := hin y d hd
    have he' : Sem x.P s b (inputVal x.P msgs d) (cts y) := by
      by_cases hp : d.parts = 1
      · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
      · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
    unfold inputVal at he'; rw [hn] at he'
    exact ⟨_, cts y, by simp [initEnv, hd], by simp [Trace.initCt, hd], he'⟩
  have hpt0 : PtB x (fun y => (x.prog.inputs.find? (·.name = y)).map fun d =>
        if d.parts = 1 then .pt (TraceBFV.inputBound x.P x.prog d)
        else .ct (TraceBFV.inputBound x.P x.prog d)) := by
    intro y b hb
    obtain ⟨d, hd, hbe⟩ := Option.map_eq_some_iff.mp hb
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte, TraceBFV.Bnd.pt.injEq] at hbe
      subst hbe
      refine le_foldl_max 0 (List.mem_map.mpr ⟨d, List.mem_filter.mpr
        ⟨List.mem_of_find?_eq_some hd, by simp [hp]⟩, rfl⟩)
    · simp only [hp, ↓reduceIte] at hbe; cases hbe
  have hrunL := lib_run h hks hft hA hs hrk hgk hin x.prog.body [] _ _ _ _ rfl rfl
    (Validation.CertifyBFV.allExact_init hk hin)
    (fun y v hv => by
      simp only [initEnv, Option.map_eq_some_iff] at hv
      obtain ⟨d, hd, rfl⟩ := hv
      exact ⟨cts y, by simp [Trace.initCt, hd], (hfind y d hd).2⟩)
    (fun y v hv => (hdok y v hv).2) (fun y v hv => (hdok y v hv).1) hinv0 hpt0
    (FHE.BFV.KSLeveled.initEnv_keyOdd _ _ _ hdecl) hrun
  unfold runLibrary
  rw [← hz0]
  exact hrunL

theorem library_decrypts_aux (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (hks : ksDeclOK? x.P x.lay = true)
    (hft : x.floatTol = false →
      (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
      ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false)
    (A : Spec.Float.Arith) (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
      Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ ρ, Source.eval x.P.src x.prog msgs = some ρ ∧
      ∀ o ∈ x.prog.outputs, ∃ v ct m B, ρ o = some v ∧ runLibrary x A rk gk cts o = some ct ∧
        c.outputs.lookup o = some B ∧ Encrypts x.P s B v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
        bfvDecrypt x.P.src.t s (ct.map (ofInt (x.P.src.modulus v.level))) = m := by
  obtain ⟨ρ, he, hall⟩ := certifyBFV?_sound x c h s msgs cts hin
  exact ⟨ρ, he, hall _ (library_run_aux x c h hks hft A hA s hs rk hrk gk hgk msgs cts hin)⟩






/-! ## The statements with the hypotheses the checks discharge

`ksDeclOK?` is checked by `certifyBFV?` (item 5b, `Checks.ksDecl`); the idealised budget is recorded
as `idealised` in `c.assumed` (`certifyBFV?_assumed`), so "the budget is the library's" is
`AssumptionBFV.idealised ∉ c.assumed`. -/

theorem mulLevelsAux_nil_of_noMul (Pr : Params) :
    ∀ (body : List Instr) (ρ : Env Pr), body.any isMul = false → mulLevelsAux Pr body ρ = []
  | [], _, _ => rfl
  | i :: is, ρ, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    rw [mulLevelsAux_cons]
    have hlv : lv Pr i ρ = [] := by
      have h1 := h.1
      cases i <;> first | rfl | exact absurd h1 (fun h2 => Bool.noConfusion h2)
    cases step Pr ρ i <;> simp [hlv, mulLevelsAux_nil_of_noMul Pr is _ h.2]

theorem ksDecl_of (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    ksDeclOK? x.P x.lay = true := (checks h).ksDecl

theorem hft_of (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hid : AssumptionBFV.idealised ∉ c.assumed) :
    x.floatTol = false →
      (c.mulLevels = [] ∨ x.mul = some .textbook ∨ ∃ B msk mt, x.mul = some (.behz B msk mt)) ∧
      ∀ Ps, x.mul = some (.leveled Ps) → ksDropped x = false := by
  intro hf
  obtain ⟨-, hI, -, -⟩ := certifyBFV?_assumed x c h
  have hnot := fun hc => hid (hI.mpr ⟨hf, hc⟩)
  obtain ⟨-, -, hML, -⟩ := certifyBFV?_spec x c h
  refine ⟨?_, fun Ps hm => ?_⟩
  · rcases hm : x.mul with _ | m
    · left
      rw [hML, mulLevels_eq]
      have hd := (checks h).mulDecl
      rw [hm] at hd
      have hno : x.prog.body.any isMul = false := by simpa using hd
      rw [mulLevelsAux_nil_of_noMul _ _ _ hno]; rfl
    · cases m with
      | textbook => exact Or.inr (Or.inl rfl)
      | behz B msk mt => exact Or.inr (Or.inr ⟨B, msk, mt, rfl⟩)
      | hps R =>
        left; by_contra hne; exact hnot (Or.inl ⟨hne, Or.inl ⟨R, hm⟩⟩)
      | poverq Ps =>
        left; by_contra hne; exact hnot (Or.inl ⟨hne, Or.inr (Or.inl ⟨Ps, hm⟩)⟩)
      | leveled Ps =>
        left; by_contra hne; exact hnot (Or.inl ⟨hne, Or.inr (Or.inr ⟨Ps, hm⟩)⟩)
  · cases hk : ksDropped x
    · rfl
    · exact absurd (Or.inr ⟨(ksDropped_iff x).mp hk, Ps, hm⟩) hnot

theorem certifyBFV?_libRelin (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (A : Spec.Float.Arith) (n : ℕ)
    (hA : (∃ Ps, x.mul = some (.leveled Ps)) → x.drops.getD n 0 ≠ 0 → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (d a : Var) (ρ ρ' : Env x.P.src)
    (hat : AtInstr x msgs n (.relin d a) ρ) (σ : Trace.CtEnv x.P) (xa : Val x.P.src)
    (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.relin d a) = some ρ') (hx : ρ a = some xa) (ha : σ a = some ca)
    (hla : ca.length = xa.parts) (h1 : 1 ≤ xa.level) (hL : xa.level ≤ x.P.src.qs.length) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ (σ.set d (libKS x A n xa.level ca rk))
      (.relin d a) :=
  libRelin_aux x c h (ksDecl_of x c h) A n hA s hs rk hrk msgs cts hin d a ρ ρ' hat σ xa ca hstep
    hx ha hla h1 hL

theorem certifyBFV?_libKeySwitch (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (A : Spec.Float.Arith) (n : ℕ)
    (hA : (∃ Ps, x.mul = some (.leveled Ps)) → x.drops.getD n 0 ≠ 0 → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (d a : Var) (ρ ρ' : Env x.P.src)
    (hat : AtInstr x msgs n (.keySwitch d a) ρ) (σ : Trace.CtEnv x.P) (xa : Val x.P.src)
    (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some xa) (ha : σ a = some ca)
    (hla : ca.length = xa.parts) (hodd : xa.key % 2 = 1) (h1 : 1 ≤ xa.level)
    (hL : xa.level ≤ x.P.src.qs.length)
    (s' : IntPoly x.P.src.N) (hs' : automorph xa.key s' = s)
    (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hkeys : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois xa.key) s' keys) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (libKeySwitch x A n xa.level xa.key ca keys)) (.keySwitch d a) :=
  libKeySwitch_aux x c h (ksDecl_of x c h) A n hA s hs msgs cts hin d a ρ ρ' hat σ xa ca hstep hx
    ha hla hodd h1 hL s' hs' keys hkeys

theorem certifyBFV?_library_run (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hid : AssumptionBFV.idealised ∉ c.assumed)
    (A : Spec.Float.Arith) (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
      Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
      (Trace.initCt x.P x.prog cts) (runLibrary x A rk gk cts) :=
  library_run_aux x c h (ksDecl_of x c h) (hft_of x c h hid) A hA s hs rk hrk gk hgk msgs cts hin

theorem certifyBFV?_library_decrypts (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (hid : AssumptionBFV.idealised ∉ c.assumed)
    (A : Spec.Float.Arith) (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
      Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ ρ, Source.eval x.P.src x.prog msgs = some ρ ∧
      ∀ o ∈ x.prog.outputs, ∃ v ct m B, ρ o = some v ∧ runLibrary x A rk gk cts o = some ct ∧
        c.outputs.lookup o = some B ∧ Encrypts x.P s B v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
        bfvDecrypt x.P.src.t s (ct.map (ofInt (x.P.src.modulus v.level))) = m :=
  library_decrypts_aux x c h (ksDecl_of x c h) (hft_of x c h hid) A hA s hs rk hrk gk hgk msgs cts
    hin

example := (@certifyBFV?_libRelin : type_of% @Challenge.CertifyBFV.certifyBFV?_libRelin)
example := (@certifyBFV?_libKeySwitch : type_of% @Challenge.CertifyBFV.certifyBFV?_libKeySwitch)
example := (@certifyBFV?_library_run : type_of% @Challenge.CertifyBFV.certifyBFV?_library_run)
example := (@certifyBFV?_library_decrypts :
  type_of% @Challenge.CertifyBFV.certifyBFV?_library_decrypts)

end Validation.CertifyBFV
