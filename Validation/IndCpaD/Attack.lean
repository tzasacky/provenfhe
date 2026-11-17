import Challenge.IndCpaD.Attack
import Validation.IndCpaD.LMBFV
import Validation.IndCpaD.LMAgreeBFV

/-!
# Validation.IndCpaD.Attack — proofs of the pins of `Challenge.IndCpaD.Attack`

The generic part (`attackReduces_of`) instantiates the proved BFV evaluator results of
`Validation.IndCpaD.LMBFV` (`bfvStep_interpOK`, `encOK_bfvKSData`, `correct_bfvEval`,
`bfvKeyGen_keysOK`, `advLM_le`) and the agreement `admLM_fresh_bfvClass` of
`Validation.IndCpaD.LMAgreeBFV`. The closed facts are checked by the kernel (`decide +kernel`).

**Keeping kernel evaluation tractable.** The class runs `Spec.schemeParamsOK?`, whose primality
test `primeOK?` is a trial division in steps of the 2-power part `s` of `q − 1`; evaluated inside
the class term, the step `twoPart q (q − 1)` is passed unevaluated and the check of one 60-bit
prime can take minutes. So: (1) `primeOK_of` proves `primeOK? q` from `twoPart q (q − 1) = s`
and the test at the literal step `s` (seconds per prime); (2) `schemeOK_of` assembles
`schemeParamsOK?`; (3) `adm_fast` rewrites the class, given `schemeParamsOK?`, into `admFast`,
the same Boolean with the parameter guard of `certifyBFVProfile?` removed (`certRest`, a local
copy of the rest of its body, equal by `show`), which the kernel then evaluates. Locked
definitions are read through `show`/`change` only.
-/

namespace Validation.IndCpaDAttack
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM Spec.Encrypt
  Spec.EncryptBFV Challenge.IndCpaDProfile Challenge.IndCpaDLM Challenge.IndCpaDAttack
  Challenge.BFV MeasureTheory

/-! ## Fast forms -/

theorem primeOK_of (q s : ℕ) (hs : twoPart q (q - 1) = s)
    (h : (decide (1 < q) && decide (q % 2 = 1) &&
      (List.range 64).any (fun a => powMod q a ((q - 1) / 2) q == q - 1) &&
      noDivisorFrom q s q (s + 1)) = true) : primeOK? q = true := by
  rw [← hs] at h; exact h

theorem schemeOK_of (P : FullParams) (hqs : P.src.qs.all primeOK? = true)
    (hrest : (decide (P.src.N = 2 ^ Nat.log2 P.src.N) && !P.src.qs.isEmpty && true &&
      decide P.src.qs.Nodup &&
      (decide (2 ≤ P.src.t) && P.src.qs.all fun q => Nat.gcd P.src.t q == 1) &&
      (P.src.kind != .bgv || decide (P.src.t / 2 ≤ P.inputNoise))) = true) :
    schemeParamsOK? P = true := by
  unfold schemeParamsOK?; rw [hqs]; exact hrest

/-- The body of `Challenge.Profile.certifyBFVProfile?` after its parameter guard. -/
def certRest (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    Option (ℕ × List (Var × ℕ)) := do
  guard (P.src.kind = .bfv)
  guard (!prog.outputs.isEmpty)
  guard (Challenge.Profile.inputsDecOK P prog)
  guard (Challenge.CertifyBFV.plainBoundsOK P prog)
  guard (P.src.t - 1 ≤ P.src.qs.headD 0 / 2)
  let B ← refAnalyzeBFVAt P E prog
  guard (Spec.Encrypt.outputsUnderS? P.src prog)
  let outs ← prog.outputs.mapM fun o =>
    (refAnalyzeBFVAt P E { prog with outputs := [o] }).map fun b => (o, b)
  pure (B, outs)

theorem cert_eq (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (h : schemeParamsOK? P = true) :
    Challenge.Profile.certifyBFVProfile? P E prog = certRest P E prog := by
  show (do guard (schemeParamsOK? P); certRest P E prog) = certRest P E prog
  rw [h]; rfl

/-- The class with the parameter guard removed. -/
def admFast (P : FullParams) (C : (cksData P).Circ) : Bool :=
  (certRest (cksData P).Pe (fun _ => cksBudget P) C.1).isSome && (cksData P).inputsFit C &&
    bfvSide (cksData P).Pe cksLayout &&
    bfvNeed (cksData P).Pe cksLayout [] (cksBudget P) C.1.body
      (initEnv P.src C.1 fun _ => .exact 0)

theorem adm_fast (P : FullParams) (h : schemeParamsOK? (cksData P).Pe = true)
    (C : (cksData P).Circ) : admCks P C = admFast P C := by
  show ((Challenge.Profile.certifyBFVProfile? (cksData P).Pe (fun _ => cksBudget P) C.1).isSome &&
      (cksData P).inputsFit C && bfvSide (cksData P).Pe cksLayout &&
      bfvNeed (cksData P).Pe cksLayout [] (cksBudget P) C.1.body
        (initEnv P.src C.1 fun _ => .exact 0)) = admFast P C
  rw [cert_eq _ _ _ h]; rfl

theorem admFast_pt (P : FullParams) (p : Program) (f : List Var) (c c' : Var → M (cksData P)) :
    admFast P (p, f, c) = admFast P (p, f, c') := rfl

theorem admCks_pt (P : FullParams) (p : Program) (f : List Var) (c c' : Var → M (cksData P)) :
    admCks P (mkCks P p f c) = admCks P (mkCks P p f c') := rfl

/-- The class at any plaintext from the class at the zero plaintext, by the fast form. -/
theorem adm_all (P : FullParams) (h : schemeParamsOK? (cksData P).Pe = true) (p : Program)
    (f : List Var) (v : Bool) (h0 : admFast P (p, f, fun _ => 0) = v) (c : Var → M (cksData P)) :
    admCks P (mkCks P p f c) = v :=
  (adm_fast P h _).trans ((admFast_pt P p f c _).trans h0)

/-! ## The oracle on the attack query -/

theorem hmk (P : FullParams) : ∀ p f c, (cksData P).prog (mkCks P p f c) = p ∧
    (cksData P).fresh (mkCks P p f c) = f ∧ (cksData P).pt (mkCks P p f c) = c :=
  fun _ _ _ => ⟨rfl, rfl, rfl⟩

theorem hfd (P : FullParams) (hL : P.src.qs ≠ []) (hN : 1 ≤ P.src.N) :
    ∀ x, (freshDecl (cksData P) x).ok (cksData P).P.src = true := by
  intro x
  have h1 : 1 ≤ P.src.qs.length := List.length_pos_iff.mpr hL
  show decide (1 ≤ 2 ∧ 1 ≤ P.src.qs.length ∧ P.src.qs.length ≤ P.src.qs.length ∧ 1 % 2 = 1 ∧
    1 < 2 * P.src.N) = true
  exact decide_eq_true ⟨by norm_num, h1, le_refl _, rfl, by omega⟩

theorem hdecl (P : FullParams) (K b : ℕ) (c : Var → M (cksData P)) :
    ∀ d ∈ (ptctQ P K b c).1.inputs, d.name ∈ (ptctQ P K b c).2.1 →
      d = freshDecl (cksData P) d.name := by
  intro d hd hn
  have hd' : d ∈ [({ name := "ct_1", parts := 2, level := P.src.qs.length, scale := 0, key := 1 } :
      Decl), { name := "pt_2", parts := 1, level := P.src.qs.length, scale := 0, key := 1 }] := hd
  have hn' : d.name ∈ ["ct_1"] := hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd' hn'
  rcases hd' with rfl | rfl
  · rfl
  · have hne : ("pt_2" : String) ≠ "ct_1" := by decide
    exact absurd hn' hne

theorem hbnd (P : FullParams) (K b : ℕ) (c : Var → M (cksData P)) :
    ∀ x ∈ (ptctQ P K b c).2.1, (ptctQ P K b c).1.boundOf x = none := by
  intro x hx
  have hx' : x ∈ ["ct_1"] := hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  subst hx'
  show (([("pt_2", b)] : List (Var × ℕ)).find? (·.1 = "ct_1")).map (·.2) = none
  simp

/-- The oracle's answer on the attack query is the class's, in every reachable state. -/
theorem admLM_ptct (P : FullParams) (hL : P.src.qs ≠ []) (hN : 1 ≤ P.src.N)
    (hdf : decOK P.src.t (P.src.modulus P.src.qs.length) (cksData P).eps = true) (K b : ℕ)
    (G : Global (cksData P)) (hG : Reach (mkCks P) (admCks P) G) (hfr : "ct_1" ∈ G.fresh)
    (c : Var → M (cksData P))
    (hnew : ∀ x ∈ constNames (ptctQ P K b c) ++ (ptctQ P K b c).1.body.map Trace.dst,
      x ∉ G.names) :
    admLM (mkCks P) (admCks P) G (ptctQ P K b c) [("ct_1", true)] =
      admCks P (mkCks P (ptctProg P.src.qs.length K b) ["ct_1"] c) :=
  Validation.IndCpaDLM.admLM_fresh_bfvClass (cksData P) (mkCks P) (hmk P) cksLayout []
    (cksBudget P) (hfd P hL hN) hdf G hG (ptctQ P K b c) [("ct_1", true)] rfl rfl
    (by intro x hx
        have hx' : x ∈ ["ct_1"] := hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
        exact hx' ▸ hfr)
    hnew (hdecl P K b c) (hbnd P K b c)

/-! ## The generic reduction -/

theorem modulus_ge (P : FullParams) (hL : P.src.qs ≠ []) (hq : ∀ q ∈ P.src.qs, 3 ≤ q) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) : 3 ≤ P.src.modulus ℓ := by
  show 3 ≤ (P.src.qs.take ℓ).prod
  obtain ⟨q, qs, e⟩ := List.exists_cons_of_ne_nil hL
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  rw [e, List.take_succ_cons, List.prod_cons]
  have h3 : 3 ≤ q := hq q (by rw [e]; exact List.mem_cons_self ..)
  have hpos : 0 < (qs.take k).prod := List.prod_pos fun x hx =>
    lt_of_lt_of_le (by norm_num) (hq x (by rw [e]; exact List.mem_cons_of_mem _ (List.mem_of_mem_take hx)))
  calc 3 ≤ q := h3
    _ ≤ q * (qs.take k).prod := Nat.le_mul_of_pos_right q hpos

theorem onesErrL_ok (P : FullParams) (hL : P.src.qs ≠ []) (hq : ∀ q ∈ P.src.qs, 3 ≤ q)
    (hsp : P.store.special = []) (hkn : 1 ≤ P.keyNoise) (ℓ j : ℕ) :
    normInf ((onesErrL P.src.N P.src.qs.length ℓ).getD j 0) ≤ P.keyNoise ∧
      2 * normInf ((onesErrL P.src.N P.src.qs.length ℓ).getD j 0) <
        P.src.modulus ℓ * Budget.specialProd P := by
  have hP : Budget.specialProd P = 1 := by
    show (P.store.special.map (·.q)).prod = 1
    rw [hsp]; rfl
  rw [hP, Nat.mul_one]
  by_cases h0 : ℓ = 0
  · have e : (onesErrL P.src.N P.src.qs.length ℓ).getD j 0 = 0 := by
      show (if ℓ = 0 then [] else _).getD j 0 = 0
      rw [if_pos h0]; rfl
    rw [e, normInf_zero]
    refine ⟨Nat.zero_le _, ?_⟩
    subst h0
    show 2 * 0 < (P.src.qs.take 0).prod
    simp
  · have h1 : normInf ((onesErrL P.src.N P.src.qs.length ℓ).getD j 0) ≤ 1 := by
      have e : (onesErrL P.src.N P.src.qs.length ℓ).getD j 0 =
          if j < P.src.qs.length then (⟨fun _ => 1⟩ : IntPoly P.src.N) else 0 := by
        show (if ℓ = 0 then [] else List.replicate _ _).getD j 0 = _
        rw [if_neg h0, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [e]
      split_ifs
      · rw [normInf_le_iff]; intro i
        show |(1 : ℤ)| ≤ ((1 : ℕ) : ℤ)
        simp
      · rw [normInf_zero]; omega
    have h3 := modulus_ge P hL hq ℓ (by omega)
    exact ⟨h1.trans hkn, by omega⟩

theorem attackReduces_of (P : FullParams) (K b : ℕ) (hk : P.src.kind = .bfv) (ht : 2 ≤ P.src.t)
    (hL : P.src.qs ≠ []) (hN : 1 ≤ P.src.N) (hkn : 1 ≤ P.keyNoise)
    (hsp : P.store.special = []) (hq : ∀ q ∈ P.src.qs, 3 ≤ q)
    (hdec : decOK P.src.t (P.src.modulus P.src.qs.length) (cksData P).eps = true)
    (hmem : admCks P (mkCks P (ptctProg P.src.qs.length K b) ["ct_1"] (fun _ => 0)) = true) :
    AttackReduces P K b := by
  have henc := Validation.IndCpaDLM.encOK_bfvKSData P cksLayout [] 39 1 39 39 ht hdec
  have hC : Correct (freshScheme (cksData P) (admCks P) (evCks P) (cksData P).decBFV) :=
    Validation.IndCpaDLM.correct_bfvEval (cksData P) henc cksLayout [] (cksBudget P) _ _
      (fun _ _ hk => ⟨hk.1, fun ℓ h1 hℓ => hk.2.2.2 ℓ h1 hℓ⟩)
  have hI := Validation.IndCpaDLM.bfvStep_interpOK (cksData P) cksLayout (fun pk => pk.2.2.1)
    (fun pk => pk.2.2.2)
  have hall : ∀ c, admCks P (mkCks P (ptctProg P.src.qs.length K b) ["ct_1"] c) = true :=
    fun c => (admCks_pt P _ _ c _).trans hmem
  refine ⟨hall, fun G hG hfr c hnew => (admLM_ptct P hL hN hdec K b G hG hfr c hnew).trans (hall c),
    henc, hC, ?_, ?_⟩
  · intro s e a hs he ra ga
    exact Validation.IndCpaDLM.bfvKeyGen_keysOK P cksLayout [] 39 1 39 39 hk s e a hs he ra _ ga _
      (onesErrL_ok P hL hq hsp hkn) (fun _ _ => onesErrL_ok P hL hq hsp hkn)
  · intro _ Ω Coins _ μ _ pk sk tape coins A q hq'
    exact Validation.IndCpaDLM.advLM_le (cksData P) (mkCks P) (hmk P) (admCks P)
      (cksData P).decBFV _ hI hC μ pk sk tape coins A q hq'

/-! ## The ciphertext primes (fast primality, `primeOK_of`) -/

theorem prime_1152921504606830593 : primeOK? 1152921504606830593 = true :=
  primeOK_of _ 16384 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504606748673 : primeOK? 1152921504606748673 = true :=
  primeOK_of _ 32768 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504606683137 : primeOK? 1152921504606683137 = true :=
  primeOK_of _ 32768 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504606601217 : primeOK? 1152921504606601217 = true :=
  primeOK_of _ 16384 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504606584833 : primeOK? 1152921504606584833 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504605962241 : primeOK? 1152921504605962241 = true :=
  primeOK_of _ 32768 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504604979201 : primeOK? 1152921504604979201 = true :=
  primeOK_of _ 32768 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504598720513 : primeOK? 1152921504598720513 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504597016577 : primeOK? 1152921504597016577 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504595968001 : primeOK? 1152921504595968001 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504595640321 : primeOK? 1152921504595640321 = true :=
  primeOK_of _ 65536 (by decide +kernel) (by decide +kernel)

theorem prime_1152921504592822273 : primeOK? 1152921504592822273 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

/-! ## The five rows -/

theorem sp_cksN12 : schemeParamsOK? (cksData cksN12).Pe = true :=
  schemeOK_of _
    (by show [1152921504606830593, 1152921504606748673, 1152921504606683137, 1152921504606601217].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606830593, prime_1152921504606748673, prime_1152921504606683137, prime_1152921504606601217, Bool.and_true])
    (by decide +kernel)

theorem sp_cksN12Plus : schemeParamsOK? (cksData cksN12Plus).Pe = true :=
  schemeOK_of _
    (by show [1152921504606830593, 1152921504606748673, 1152921504606683137, 1152921504606601217, 1152921504606584833].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606830593, prime_1152921504606748673, prime_1152921504606683137, prime_1152921504606601217, prime_1152921504606584833, Bool.and_true])
    (by decide +kernel)

theorem refused_cksN12 : AttackRefused cksN12 8 6 786432 := by
  have hdf : decOK cksN12.src.t (cksN12.src.modulus cksN12.src.qs.length) (cksData cksN12).eps =
      true := by decide +kernel
  have hK : ∀ c, admCks cksN12 (mkCks cksN12 (ptctProg cksN12.src.qs.length 8 786432) ["ct_1"] c) =
      false := adm_all _ sp_cksN12 _ _ _ (by decide +kernel)
  exact ⟨by rw [cert_eq _ _ _ sp_cksN12]; decide +kernel, hK, fun G hG hfr c hnew =>
    (admLM_ptct _ (by decide) (by decide) hdf 8 786432 G hG hfr c hnew).trans (hK c),
    adm_all _ sp_cksN12 _ _ _ (by decide +kernel), adm_all _ sp_cksN12 _ _ _ (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem reduces_cksN12Plus : AttackReduces cksN12Plus 8 786432 :=
  attackReduces_of _ 8 786432 rfl (by decide) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide +kernel) (adm_all _ sp_cksN12Plus _ _ _ (by decide +kernel) _)

theorem cks_ptct_n12 :
    AttackRefused cksN12 8 6 786432 ∧ AttackReduces cksN12Plus 8 786432 :=
  ⟨refused_cksN12, reduces_cksN12Plus⟩

theorem sp_cksN13 : schemeParamsOK? (cksData cksN13).Pe = true :=
  schemeOK_of _
    (by show [1152921504606830593, 1152921504606748673, 1152921504606683137, 1152921504606601217].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606830593, prime_1152921504606748673, prime_1152921504606683137, prime_1152921504606601217, Bool.and_true])
    (by decide +kernel)

theorem sp_cksN13Plus : schemeParamsOK? (cksData cksN13Plus).Pe = true :=
  schemeOK_of _
    (by show [1152921504606830593, 1152921504606748673, 1152921504606683137, 1152921504606601217, 1152921504606584833].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606830593, prime_1152921504606748673, prime_1152921504606683137, prime_1152921504606601217, prime_1152921504606584833, Bool.and_true])
    (by decide +kernel)

theorem refused_cksN13 : AttackRefused cksN13 7 5 4194304 := by
  have hdf : decOK cksN13.src.t (cksN13.src.modulus cksN13.src.qs.length) (cksData cksN13).eps =
      true := by decide +kernel
  have hK : ∀ c, admCks cksN13 (mkCks cksN13 (ptctProg cksN13.src.qs.length 7 4194304) ["ct_1"] c) =
      false := adm_all _ sp_cksN13 _ _ _ (by decide +kernel)
  exact ⟨by rw [cert_eq _ _ _ sp_cksN13]; decide +kernel, hK, fun G hG hfr c hnew =>
    (admLM_ptct _ (by decide) (by decide) hdf 7 4194304 G hG hfr c hnew).trans (hK c),
    adm_all _ sp_cksN13 _ _ _ (by decide +kernel), adm_all _ sp_cksN13 _ _ _ (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem reduces_cksN13Plus : AttackReduces cksN13Plus 7 4194304 :=
  attackReduces_of _ 7 4194304 rfl (by decide) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide +kernel) (adm_all _ sp_cksN13Plus _ _ _ (by decide +kernel) _)

theorem cks_ptct_n13 :
    AttackRefused cksN13 7 5 4194304 ∧ AttackReduces cksN13Plus 7 4194304 :=
  ⟨refused_cksN13, reduces_cksN13Plus⟩

theorem sp_cksN14 : schemeParamsOK? (cksData cksN14).Pe = true :=
  schemeOK_of _
    (by show [1152921504606748673, 1152921504606683137, 1152921504606584833, 1152921504605962241].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606748673, prime_1152921504606683137, prime_1152921504606584833, prime_1152921504605962241, Bool.and_true])
    (by decide +kernel)

theorem sp_cksN14Plus : schemeParamsOK? (cksData cksN14Plus).Pe = true :=
  schemeOK_of _
    (by show [1152921504606748673, 1152921504606683137, 1152921504606584833, 1152921504605962241, 1152921504604979201].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606748673, prime_1152921504606683137, prime_1152921504606584833, prime_1152921504605962241, prime_1152921504604979201, Bool.and_true])
    (by decide +kernel)

theorem refused_cksN14 : AttackRefused cksN14 6 4 67108864 := by
  have hdf : decOK cksN14.src.t (cksN14.src.modulus cksN14.src.qs.length) (cksData cksN14).eps =
      true := by decide +kernel
  have hK : ∀ c, admCks cksN14 (mkCks cksN14 (ptctProg cksN14.src.qs.length 6 67108864) ["ct_1"] c) =
      false := adm_all _ sp_cksN14 _ _ _ (by decide +kernel)
  exact ⟨by rw [cert_eq _ _ _ sp_cksN14]; decide +kernel, hK, fun G hG hfr c hnew =>
    (admLM_ptct _ (by decide) (by decide) hdf 6 67108864 G hG hfr c hnew).trans (hK c),
    adm_all _ sp_cksN14 _ _ _ (by decide +kernel), adm_all _ sp_cksN14 _ _ _ (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem reduces_cksN14Plus : AttackReduces cksN14Plus 6 67108864 :=
  attackReduces_of _ 6 67108864 rfl (by decide) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide +kernel) (adm_all _ sp_cksN14Plus _ _ _ (by decide +kernel) _)

theorem cks_ptct_n14 :
    AttackRefused cksN14 6 4 67108864 ∧ AttackReduces cksN14Plus 6 67108864 :=
  ⟨refused_cksN14, reduces_cksN14Plus⟩

theorem sp_cksN15 : schemeParamsOK? (cksData cksN15).Pe = true :=
  schemeOK_of _
    (by show [1152921504606584833, 1152921504598720513, 1152921504597016577, 1152921504595968001].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606584833, prime_1152921504598720513, prime_1152921504597016577, prime_1152921504595968001, Bool.and_true])
    (by decide +kernel)

theorem sp_cksN15Plus : schemeParamsOK? (cksData cksN15Plus).Pe = true :=
  schemeOK_of _
    (by show [1152921504606584833, 1152921504598720513, 1152921504597016577, 1152921504595968001, 1152921504595640321].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606584833, prime_1152921504598720513, prime_1152921504597016577, prime_1152921504595968001, prime_1152921504595640321, Bool.and_true])
    (by decide +kernel)

theorem refused_cksN15 : AttackRefused cksN15 6 4 33423360 := by
  have hdf : decOK cksN15.src.t (cksN15.src.modulus cksN15.src.qs.length) (cksData cksN15).eps =
      true := by decide +kernel
  have hK : ∀ c, admCks cksN15 (mkCks cksN15 (ptctProg cksN15.src.qs.length 6 33423360) ["ct_1"] c) =
      false := adm_all _ sp_cksN15 _ _ _ (by decide +kernel)
  exact ⟨by rw [cert_eq _ _ _ sp_cksN15]; decide +kernel, hK, fun G hG hfr c hnew =>
    (admLM_ptct _ (by decide) (by decide) hdf 6 33423360 G hG hfr c hnew).trans (hK c),
    adm_all _ sp_cksN15 _ _ _ (by decide +kernel), adm_all _ sp_cksN15 _ _ _ (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem reduces_cksN15Plus : AttackReduces cksN15Plus 6 33423360 :=
  attackReduces_of _ 6 33423360 rfl (by decide) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide +kernel) (adm_all _ sp_cksN15Plus _ _ _ (by decide +kernel) _)

theorem cks_ptct_n15 :
    AttackRefused cksN15 6 4 33423360 ∧ AttackReduces cksN15Plus 6 33423360 :=
  ⟨refused_cksN15, reduces_cksN15Plus⟩

theorem sp_cksN16 : schemeParamsOK? (cksData cksN16).Pe = true :=
  schemeOK_of _
    (by show [1152921504606584833, 1152921504598720513, 1152921504597016577, 1152921504595968001].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606584833, prime_1152921504598720513, prime_1152921504597016577, prime_1152921504595968001, Bool.and_true])
    (by decide +kernel)

theorem sp_cksN16Plus : schemeParamsOK? (cksData cksN16Plus).Pe = true :=
  schemeOK_of _
    (by show [1152921504606584833, 1152921504598720513, 1152921504597016577, 1152921504595968001, 1152921504592822273].all primeOK? = true
        simp only [List.all_cons, List.all_nil, prime_1152921504606584833, prime_1152921504598720513, prime_1152921504597016577, prime_1152921504595968001, prime_1152921504592822273, Bool.and_true])
    (by decide +kernel)

theorem refused_cksN16 : AttackRefused cksN16 7 5 1048576 := by
  have hdf : decOK cksN16.src.t (cksN16.src.modulus cksN16.src.qs.length) (cksData cksN16).eps =
      true := by decide +kernel
  have hK : ∀ c, admCks cksN16 (mkCks cksN16 (ptctProg cksN16.src.qs.length 7 1048576) ["ct_1"] c) =
      false := adm_all _ sp_cksN16 _ _ _ (by decide +kernel)
  exact ⟨by rw [cert_eq _ _ _ sp_cksN16]; decide +kernel, hK, fun G hG hfr c hnew =>
    (admLM_ptct _ (by decide) (by decide) hdf 7 1048576 G hG hfr c hnew).trans (hK c),
    adm_all _ sp_cksN16 _ _ _ (by decide +kernel), adm_all _ sp_cksN16 _ _ _ (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem reduces_cksN16Plus : AttackReduces cksN16Plus 7 1048576 :=
  attackReduces_of _ 7 1048576 rfl (by decide) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide +kernel) (adm_all _ sp_cksN16Plus _ _ _ (by decide +kernel) _)

theorem cks_ptct_n16 :
    AttackRefused cksN16 7 5 1048576 ∧ AttackReduces cksN16Plus 7 1048576 :=
  ⟨refused_cksN16, reduces_cksN16Plus⟩

theorem cks_ptct_refused_bounds :
    ptctNoise 4096 786433 (cksN12.src.modulus 4) 786432 (cksData cksN12).eps 7 =
      5251037663091305562219578713906387505284935393317623225167875033404538880 ∧
    ptctNoise 8192 4194305 (cksN13.src.modulus 4) 4194304 (cksData cksN13).eps 6 =
      8645295002261143479853705142650371180946969650113112424994994217025536 ∧
    ptctNoise 16384 67108865 (cksN14.src.modulus 4) 67108864 (cksData cksN14).eps 5 =
      95263556898098926628455582455600851287684774034139372458602464804864 ∧
    ptctNoise 32768 33423361 (cksN15.src.modulus 4) 33423360 (cksData cksN15).eps 5 =
      44020180844967149018074699655908855737692558292007728570408621834240 ∧
    ptctNoise 65536 1048577 (cksN16.src.modulus 4) 1048576 (cksData cksN16).eps 6 =
      659376370918342488325287573605949135222680560990456753709864386295758848 := by
  decide +kernel

example := (@attackReduces_of : type_of% @Challenge.IndCpaDAttack.attackReduces_of)
example := (@cks_ptct_n12 : type_of% @Challenge.IndCpaDAttack.cks_ptct_n12)
example := (@cks_ptct_n13 : type_of% @Challenge.IndCpaDAttack.cks_ptct_n13)
example := (@cks_ptct_n14 : type_of% @Challenge.IndCpaDAttack.cks_ptct_n14)
example := (@cks_ptct_n15 : type_of% @Challenge.IndCpaDAttack.cks_ptct_n15)
example := (@cks_ptct_n16 : type_of% @Challenge.IndCpaDAttack.cks_ptct_n16)
example := (@cks_ptct_refused_bounds : type_of% @Challenge.IndCpaDAttack.cks_ptct_refused_bounds)

/-! ## The squaring circuit -/

/-- The class with the parameter guard removed (squaring data). -/
def admFastL (P : FullParams) (lay : Budget.KSLayout) (C : (sqData P lay).Circ) : Bool :=
  (certRest (sqData P lay).Pe (fun _ => BudgetBFV.certified P lay) C.1).isSome &&
    (sqData P lay).inputsFit C && bfvSide (sqData P lay).Pe lay &&
    bfvNeed (sqData P lay).Pe lay [] (BudgetBFV.certified P lay) C.1.body
      (initEnv P.src C.1 fun _ => .exact 0)

theorem adm_fastL (P : FullParams) (lay : Budget.KSLayout)
    (h : schemeParamsOK? (sqData P lay).Pe = true) (C : (sqData P lay).Circ) :
    admSq P lay C = admFastL P lay C := by
  show ((Challenge.Profile.certifyBFVProfile? (sqData P lay).Pe
      (fun _ => BudgetBFV.certified P lay) C.1).isSome &&
      (sqData P lay).inputsFit C && bfvSide (sqData P lay).Pe lay &&
      bfvNeed (sqData P lay).Pe lay [] (BudgetBFV.certified P lay) C.1.body
        (initEnv P.src C.1 fun _ => .exact 0)) = admFastL P lay C
  rw [cert_eq _ _ _ h]; rfl

theorem admFastL_pt (P : FullParams) (lay : Budget.KSLayout) (p : Program) (f : List Var)
    (c c' : Var → M (sqData P lay)) : admFastL P lay (p, f, c) = admFastL P lay (p, f, c') := rfl

theorem admSq_pt (P : FullParams) (lay : Budget.KSLayout) (p : Program) (f : List Var)
    (c c' : Var → M (sqData P lay)) :
    admSq P lay (mkSq P lay p f c) = admSq P lay (mkSq P lay p f c') := rfl

theorem adm_allL (P : FullParams) (lay : Budget.KSLayout)
    (h : schemeParamsOK? (sqData P lay).Pe = true) (p : Program) (f : List Var) (v : Bool)
    (h0 : admFastL P lay (p, f, fun _ => 0) = v) (c : Var → M (sqData P lay)) :
    admSq P lay (mkSq P lay p f c) = v :=
  (adm_fastL P lay h _).trans ((admFastL_pt P lay p f c _).trans h0)

theorem admLM_sq (P : FullParams) (lay : Budget.KSLayout) (hL : P.src.qs ≠ [])
    (hN : 1 ≤ P.src.N)
    (hdf : decOK P.src.t (P.src.modulus P.src.qs.length) (sqData P lay).eps = true)
    (G : Global (sqData P lay)) (hG : Reach (mkSq P lay) (admSq P lay) G)
    (hfr : ∀ x ∈ sqIns, x ∈ G.fresh) (c : Var → M (sqData P lay))
    (hnew : ∀ x ∈ constNames (sqQ P lay c) ++ (sqQ P lay c).1.body.map Trace.dst,
      x ∉ G.names) :
    admLM (mkSq P lay) (admSq P lay) G (sqQ P lay c) (sqIns.map fun x => (x, true)) =
      admSq P lay (mkSq P lay (sqProg P.src.qs.length 144) sqIns c) := by
  have hfd' : ∀ x, (freshDecl (sqData P lay) x).ok (sqData P lay).P.src = true := by
    intro x
    have h1 : 1 ≤ P.src.qs.length := List.length_pos_iff.mpr hL
    show decide (1 ≤ 2 ∧ 1 ≤ P.src.qs.length ∧ P.src.qs.length ≤ P.src.qs.length ∧ 1 % 2 = 1 ∧
      1 < 2 * P.src.N) = true
    exact decide_eq_true ⟨by norm_num, h1, le_refl _, rfl, by omega⟩
  refine Validation.IndCpaDLM.admLM_fresh_bfvClass (sqData P lay) (mkSq P lay)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) lay [] (BudgetBFV.certified P lay) hfd' hdf G hG
    (sqQ P lay c) (sqIns.map fun x => (x, true)) ?_ ?_ hfr hnew ?_ ?_
  · show sqIns = (sqIns.map fun x => (x, true)).map (·.1)
    rfl
  · show (sqIns.map fun x => (x, true)).all (·.2) = true
    rfl
  · intro d hd _
    have hd' : d ∈ sqIns.map fun x =>
        ({ name := x, parts := 2, level := P.src.qs.length, scale := 0, key := 1 } : Decl) := hd
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd'
    rfl
  · intro x _
    rfl

theorem onesErrL_okS (P : FullParams) (hq : ∀ q ∈ P.src.qs, 3 ≤ q)
    (hsp : 3 ≤ Budget.specialProd P) (hkn : 1 ≤ P.keyNoise) (ℓ j : ℕ) :
    normInf ((onesErrL P.src.N P.src.qs.length ℓ).getD j 0) ≤ P.keyNoise ∧
      2 * normInf ((onesErrL P.src.N P.src.qs.length ℓ).getD j 0) <
        P.src.modulus ℓ * Budget.specialProd P := by
  have h1 : normInf ((onesErrL P.src.N P.src.qs.length ℓ).getD j 0) ≤ 1 := by
    by_cases h0 : ℓ = 0
    · have e : (onesErrL P.src.N P.src.qs.length ℓ).getD j 0 = 0 := by
        show (if ℓ = 0 then [] else _).getD j 0 = 0
        rw [if_pos h0]; rfl
      rw [e, normInf_zero]; omega
    · have e : (onesErrL P.src.N P.src.qs.length ℓ).getD j 0 =
          if j < P.src.qs.length then (⟨fun _ => 1⟩ : IntPoly P.src.N) else 0 := by
        show (if ℓ = 0 then [] else List.replicate _ _).getD j 0 = _
        rw [if_neg h0, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [e]
      split_ifs
      · rw [normInf_le_iff]; intro i
        show |(1 : ℤ)| ≤ ((1 : ℕ) : ℤ)
        simp
      · rw [normInf_zero]; omega
  have hpos : 1 ≤ P.src.modulus ℓ := by
    show 1 ≤ (P.src.qs.take ℓ).prod
    exact List.prod_pos fun x hx => lt_of_lt_of_le (by norm_num) (hq x (List.mem_of_mem_take hx))
  refine ⟨h1.trans hkn, ?_⟩
  calc 2 * normInf ((onesErrL P.src.N P.src.qs.length ℓ).getD j 0) ≤ 2 * 1 :=
        Nat.mul_le_mul_left 2 h1
    _ < 1 * Budget.specialProd P := by omega
    _ ≤ P.src.modulus ℓ * Budget.specialProd P := Nat.mul_le_mul_right _ hpos

theorem sqReduces_of (P : FullParams) (lay : Budget.KSLayout) (hk : P.src.kind = .bfv)
    (ht : 2 ≤ P.src.t) (hL : P.src.qs ≠ []) (hN : 1 ≤ P.src.N) (hkn : 1 ≤ P.keyNoise)
    (hsp : 3 ≤ Budget.specialProd P) (hq : ∀ q ∈ P.src.qs, 3 ≤ q)
    (hdec : decOK P.src.t (P.src.modulus P.src.qs.length) (sqData P lay).eps = true)
    (hmem : admSq P lay (mkSq P lay (sqProg P.src.qs.length 144) sqIns (fun _ => 0)) = true) :
    SqReduces P lay := by
  have henc := Validation.IndCpaDLM.encOK_bfvKSData P lay [] 39 1 39 39 ht hdec
  have hC : Correct (freshScheme (sqData P lay) (admSq P lay) (evSq P lay) (sqData P lay).decBFV) :=
    Validation.IndCpaDLM.correct_bfvEval (sqData P lay) henc lay [] (BudgetBFV.certified P lay)
      _ _ (fun _ _ hk => ⟨hk.1, fun ℓ h1 hℓ => hk.2.2.2 ℓ h1 hℓ⟩)
  have hI := Validation.IndCpaDLM.bfvStep_interpOK (sqData P lay) lay (fun pk => pk.2.2.1)
    (fun pk => pk.2.2.2)
  have hall : ∀ c, admSq P lay (mkSq P lay (sqProg P.src.qs.length 144) sqIns c) = true :=
    fun c => (admSq_pt P lay _ _ c _).trans hmem
  refine ⟨hall, fun G hG hfr c hnew => (admLM_sq P lay hL hN hdec G hG hfr c hnew).trans (hall c),
    henc, hC, ?_, ?_⟩
  · intro s e a hs he ra ga
    exact Validation.IndCpaDLM.bfvKeyGen_keysOK P lay [] 39 1 39 39 hk s e a hs he ra _ ga _
      (onesErrL_okS P hq hsp hkn) (fun _ _ => onesErrL_okS P hq hsp hkn)
  · intro _ Ω Coins _ μ _ pk sk tape coins A q hq'
    exact Validation.IndCpaDLM.advLM_le (sqData P lay) (mkSq P lay) (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
      (admSq P lay) (sqData P lay).decBFV _ hI hC μ pk sk tape coins A q hq'

/-! ## The squaring instance: primes (52 bits) -/

theorem prime_4503599477686273 : primeOK? 4503599477686273 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599479521281 : primeOK? 4503599479521281 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599485812737 : primeOK? 4503599485812737 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599499706369 : primeOK? 4503599499706369 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599503114241 : primeOK? 4503599503114241 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599505211393 : primeOK? 4503599505211393 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599510192129 : primeOK? 4503599510192129 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599511764993 : primeOK? 4503599511764993 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599513075713 : primeOK? 4503599513075713 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599515697153 : primeOK? 4503599515697153 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599517270017 : primeOK? 4503599517270017 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599518842881 : primeOK? 4503599518842881 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599525920769 : primeOK? 4503599525920769 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599526445057 : primeOK? 4503599526445057 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599527231489 : primeOK? 4503599527231489 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599535882241 : primeOK? 4503599535882241 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599536930817 : primeOK? 4503599536930817 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599542960129 : primeOK? 4503599542960129 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599548465153 : primeOK? 4503599548465153 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599550824449 : primeOK? 4503599550824449 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599554756609 : primeOK? 4503599554756609 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599561310209 : primeOK? 4503599561310209 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599563407361 : primeOK? 4503599563407361 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599565766657 : primeOK? 4503599565766657 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599568125953 : primeOK? 4503599568125953 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599571271681 : primeOK? 4503599571271681 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599572320257 : primeOK? 4503599572320257 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599579922433 : primeOK? 4503599579922433 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599583068161 : primeOK? 4503599583068161 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599587000321 : primeOK? 4503599587000321 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599589359617 : primeOK? 4503599589359617 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599592767489 : primeOK? 4503599592767489 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599595257857 : primeOK? 4503599595257857 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599595651073 : primeOK? 4503599595651073 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599597879297 : primeOK? 4503599597879297 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599598665729 : primeOK? 4503599598665729 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599599190017 : primeOK? 4503599599190017 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599600238593 : primeOK? 4503599600238593 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599600762881 : primeOK? 4503599600762881 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599603515393 : primeOK? 4503599603515393 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599603908609 : primeOK? 4503599603908609 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599604170753 : primeOK? 4503599604170753 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599605350401 : primeOK? 4503599605350401 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem prime_4503599606661121 : primeOK? 4503599606661121 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599607840769 : primeOK? 4503599607840769 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599613214721 : primeOK? 4503599613214721 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599615311873 : primeOK? 4503599615311873 = true :=
  primeOK_of _ 524288 (by decide +kernel) (by decide +kernel)

theorem prime_4503599619112961 : primeOK? 4503599619112961 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599621472257 : primeOK? 4503599621472257 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599623045121 : primeOK? 4503599623045121 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599625404417 : primeOK? 4503599625404417 = true :=
  primeOK_of _ 131072 (by decide +kernel) (by decide +kernel)

theorem prime_4503599625535489 : primeOK? 4503599625535489 = true :=
  primeOK_of _ 262144 (by decide +kernel) (by decide +kernel)

theorem prime_4503599626321921 : primeOK? 4503599626321921 = true :=
  primeOK_of _ 1048576 (by decide +kernel) (by decide +kernel)

theorem sp_cksSq257 : schemeParamsOK? (sqData cksSq257 (sqLayout 6)).Pe = true :=
  schemeOK_of _
    (by show [4503599626321921, 4503599625535489, 4503599625404417, 4503599623045121,
          4503599621472257, 4503599619112961, 4503599615311873, 4503599613214721,
          4503599607840769, 4503599606661121, 4503599605350401, 4503599604170753,
          4503599603908609, 4503599603515393, 4503599600762881, 4503599600238593,
          4503599599190017, 4503599598665729, 4503599597879297, 4503599595651073,
          4503599595257857, 4503599592767489, 4503599589359617, 4503599587000321,
          4503599583068161, 4503599579922433].all primeOK? = true
        simp only [List.all_cons, List.all_nil, Bool.and_true,
          prime_4503599626321921, prime_4503599625535489, prime_4503599625404417,
          prime_4503599623045121, prime_4503599621472257, prime_4503599619112961,
          prime_4503599615311873, prime_4503599613214721, prime_4503599607840769,
          prime_4503599606661121, prime_4503599605350401, prime_4503599604170753,
          prime_4503599603908609, prime_4503599603515393, prime_4503599600762881,
          prime_4503599600238593, prime_4503599599190017, prime_4503599598665729,
          prime_4503599597879297, prime_4503599595651073, prime_4503599595257857,
          prime_4503599592767489, prime_4503599589359617, prime_4503599587000321,
          prime_4503599583068161, prime_4503599579922433])
    (by decide +kernel)

theorem sp_cksSq257Cert : schemeParamsOK? (sqData cksSq257Cert (sqLayout 8)).Pe = true :=
  schemeOK_of _
    (by show [4503599626321921, 4503599625535489, 4503599615311873, 4503599613214721,
          4503599606661121, 4503599605350401, 4503599603515393, 4503599595651073,
          4503599592767489, 4503599589359617, 4503599587000321, 4503599583068161,
          4503599579922433, 4503599572320257, 4503599571271681, 4503599568125953,
          4503599565766657, 4503599563407361, 4503599561310209, 4503599554756609,
          4503599550824449, 4503599548465153, 4503599542960129, 4503599536930817,
          4503599535882241, 4503599527231489, 4503599526445057, 4503599525920769,
          4503599518842881, 4503599517270017, 4503599515697153, 4503599513075713,
          4503599511764993, 4503599510192129, 4503599505211393, 4503599503114241,
          4503599499706369, 4503599485812737, 4503599479521281, 4503599477686273].all primeOK? = true
        simp only [List.all_cons, List.all_nil, Bool.and_true,
          prime_4503599626321921, prime_4503599625535489, prime_4503599615311873,
          prime_4503599613214721, prime_4503599606661121, prime_4503599605350401,
          prime_4503599603515393, prime_4503599595651073, prime_4503599592767489,
          prime_4503599589359617, prime_4503599587000321, prime_4503599583068161,
          prime_4503599579922433, prime_4503599572320257, prime_4503599571271681,
          prime_4503599568125953, prime_4503599565766657, prime_4503599563407361,
          prime_4503599561310209, prime_4503599554756609, prime_4503599550824449,
          prime_4503599548465153, prime_4503599542960129, prime_4503599536930817,
          prime_4503599535882241, prime_4503599527231489, prime_4503599526445057,
          prime_4503599525920769, prime_4503599518842881, prime_4503599517270017,
          prime_4503599515697153, prime_4503599513075713, prime_4503599511764993,
          prime_4503599510192129, prime_4503599505211393, prime_4503599503114241,
          prime_4503599499706369, prime_4503599485812737, prime_4503599479521281,
          prime_4503599477686273])
    (by decide +kernel)

theorem refused_cksSq257 : SqRefused cksSq257 (sqLayout 6) 97 := by
  have hdf : decOK cksSq257.src.t (cksSq257.src.modulus cksSq257.src.qs.length)
      (sqData cksSq257 (sqLayout 6)).eps = true := by decide +kernel
  have hK : ∀ c, admSq cksSq257 (sqLayout 6)
      (mkSq cksSq257 (sqLayout 6) (sqProg cksSq257.src.qs.length 144) sqIns c) = false :=
    adm_allL _ _ sp_cksSq257 _ _ _ (by decide +kernel)
  exact ⟨by rw [cert_eq _ _ _ sp_cksSq257]; decide +kernel, hK, fun G hG hfr c hnew =>
    (admLM_sq _ _ (by decide) (by decide) hdf G hG hfr c hnew).trans (hK c),
    adm_allL _ _ sp_cksSq257 _ _ _ (by decide +kernel),
    adm_allL _ _ sp_cksSq257 _ _ _ (by decide +kernel),
    241822531386257379714100197014543414733755274205785085534310686469222400775180064680758544365958898972411816873372905552067183589517685377851143072914131162748757902334098737056492211743912499024404764972766099360724425657049621612418734725453073181843917808589005916404649889505728014840742622400481399852017638145539464204024935260347601224746409060281773758881678300384326489839952734467563,
    by decide +kernel, by decide +kernel⟩

theorem reduces_cksSq257Cert : SqReduces cksSq257Cert (sqLayout 8) :=
  sqReduces_of _ _ rfl (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide) (by decide +kernel) (adm_allL _ _ sp_cksSq257Cert _ _ _ (by decide +kernel) _)

theorem cks_ctct_t257 :
    SqRefused cksSq257 (sqLayout 6) 97 ∧ SqReduces cksSq257Cert (sqLayout 8) :=
  ⟨refused_cksSq257, reduces_cksSq257Cert⟩

example := (@sqReduces_of : type_of% @Challenge.IndCpaDAttack.sqReduces_of)
example := (@cks_ctct_t257 : type_of% @Challenge.IndCpaDAttack.cks_ctct_t257)

theorem cks_eps :
    (cksData cksN12).eps = 889334 ∧ (cksData cksN12Plus).eps = 1097592 ∧
    (cksData cksN13).eps = 2946451 ∧ (cksData cksN13Plus).eps = 2792468 ∧
    (cksData cksN14).eps = 30280324 ∧ (cksData cksN14Plus).eps = 17446959 ∧
    (cksData cksN15).eps = 15245566 ∧ (cksData cksN15Plus).eps = 31996980 ∧
    (cksData cksN16).eps = 5686500 ∧ (cksData cksN16Plus).eps = 5588864 ∧
    (sqData cksSq257 (sqLayout 6)).eps = 5112099 ∧
    (sqData cksSq257Cert (sqLayout 8)).eps = 10223899 := by
  decide +kernel

example := (@cks_eps : type_of% @Challenge.IndCpaDAttack.cks_eps)

end Validation.IndCpaDAttack
