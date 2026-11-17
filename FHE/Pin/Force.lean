import FHE.Pin.Mutants
import Spec.Trace
import Validation.Scheme.Basic
import FHE.Pin.Kron

/-!
# FHE.Pin.Force — memoised ("forced") forms of the trusted BGV definitions, with equality proofs
(UNTRUSTED glue; the theorems are kernel-checked)

`Spec.NPoly R N` is a function `Fin N → R`; nothing is memoised, so a composed trusted expression
such as `Spec.Scheme.phase` costs `N³` ring operations for a two-component ciphertext. The
differential harness `openfhe_pin` therefore keeps data in arrays:

* `ofArr arr` wraps an array as an `NPoly` (at the point of use);
* `toArr K a` evaluates every coefficient of `a` once (in `K` parallel chunks) into an array;
  `ofArr_toArr : ofArr (toArr K a) = a`.

A *forced* function composes the same trusted primitives (`+ - * • ofInt centered automorph`,
`switchDownRev`, `Source.step`, …) along the unfolding of a trusted definition, forcing the
intermediate results. Each `*_spec` theorem below says the forced function, with no mutant
selected (`Mut.none`), equals the trusted definition applied to the wrapped arrays.
-/

namespace FHE.Pin
open Spec Spec.NPoly Spec.Scheme Spec.Source Validation.Scheme

/-! ## Arrays ↔ `NPoly` -/

/-- Wrap an array as a polynomial (coefficients beyond the array are `default`). -/
@[noinline] def ofArr {R : Type} [Inhabited R] {N : ℕ} (arr : Array R) : NPoly R N :=
  ⟨fun i => arr[i.val]!⟩

/-- Evaluate every coefficient once, in `K` chunks, one task per chunk. -/
@[noinline] def toArr {R : Type} [Inhabited R] {N : ℕ} (K : ℕ) (a : NPoly R N) : Array R :=
  let sz := (N + K - 1) / K
  let tasks : Array (Task (Array R)) := Array.ofFn (n := K) fun c => Task.spawn fun _ =>
    Array.ofFn (n := sz) fun j =>
      if h : c.val * sz + j.val < N then a.coeff ⟨c.val * sz + j.val, h⟩ else default
  Array.ofFn (n := N) fun i =>
    match tasks[i.val / sz]? with
    | some t =>
      match t.get[i.val % sz]? with
      | some x => x
      | none => a.coeff i
    | none => a.coeff i

section
variable {R : Type} [Inhabited R] {N : ℕ}

@[simp] theorem toArr_size (K : ℕ) (a : NPoly R N) : (toArr K a).size = N := by
  simp [toArr]

theorem toArr_getElem (K : ℕ) (a : NPoly R N) (i : ℕ) (h : i < N) :
    (toArr K a)[i]'(by simp [h]) = a.coeff ⟨i, h⟩ := by
  unfold toArr
  simp only [Array.getElem_ofFn]
  split
  · rename_i t ht
    split
    · rename_i x hx
      rw [Array.getElem?_ofFn] at ht
      split at ht
      · rename_i hc
        cases ht
        simp only [Task.spawn] at hx
        rw [Array.getElem?_ofFn] at hx
        split at hx
        · rename_i hj
          cases hx
          have e : i / ((N + K - 1) / K) * ((N + K - 1) / K) + i % ((N + K - 1) / K) = i := by
            rw [Nat.mul_comm]; exact Nat.div_add_mod i _
          simp only [e, h, dite_true]
        · cases hx
      · cases ht
    · rfl
  · rfl

@[simp] theorem ofArr_toArr (K : ℕ) (a : NPoly R N) : ofArr (toArr K a) = a := by
  ext i
  simp only [ofArr]
  rw [getElem!_pos _ _ (by simp)]
  exact toArr_getElem K a i.val i.isLt

/-- Forcing is injective: equal arrays come from equal polynomials (this is how an array
comparison in the checker is an equation between the trusted polynomials). -/
theorem toArr_inj {K : ℕ} {a b : NPoly R N} (h : toArr K a = toArr K b) : a = b := by
  rw [← ofArr_toArr K a, h, ofArr_toArr]

/-- An array equal to a forced polynomial wraps to that polynomial. -/
theorem ofArr_eq_of_toArr_eq {K : ℕ} {a : NPoly R N} {arr : Array R} (h : toArr K a = arr) :
    ofArr arr = a := by
  rw [← h, ofArr_toArr]

end

/-! ## Fast forms of the two quadratic primitives

`mulF` is the trusted product as a `Fin.foldl` loop (any ring; quadratic; kept for the closures
where nothing is forced). On the forced paths the product of integer polynomials is `mulArr`
(Kronecker substitution, one GMP product: `Kron.mulNeg`; `ofArr_mulArr`), of `Z_q` polynomials
`mulArrQ` (`ofArr_mulArrQ`), and `autoF` is the linear-time scatter `Kron.autoArr`
(`Kron.autoL_eq`). `mulF_eq`, `autoF_eq`, `mulMF_none`, `ofArr_mulArr` say they are the trusted
operations. -/

section Fast
variable {R : Type} [CommRing R] {N : ℕ}

theorem sum_eq_foldl (f : Fin N → R) :
    ∑ i : Fin N, f i = Fin.foldl N (fun acc i => acc + f i) 0 := by
  rw [Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]
  exact Eq.symm (Fin.foldl_eq_finRange_foldl (fun acc i => acc + f i) 0)

/-- The negacyclic product (`Spec.NPoly`'s `*`) as a loop. -/
def mulF (a b : NPoly R N) : NPoly R N :=
  ⟨fun k => Fin.foldl N (fun acc i => acc +
    (if h : i.val ≤ k.val then
      a.coeff i * b.coeff ⟨k.val - i.val, by have := k.isLt; omega⟩
    else
      -(a.coeff i * b.coeff ⟨N + k.val - i.val, by have := k.isLt; have := i.isLt; omega⟩))) 0⟩

@[simp] theorem mulF_eq (a b : NPoly R N) : mulF a b = a * b := by
  ext k
  exact (sum_eq_foldl _).symm

/-- `Spec.NPoly.automorph` in linear time: each input coefficient scattered to its one destination
(`FHE.Pin.Kron.autoL`, proved equal: `Kron.autoL_eq`). -/
@[inline] def autoF (g : ℕ) (a : NPoly R N) : NPoly R N := Kron.ofArrD (Kron.autoArr g a)

@[simp] theorem autoF_eq (g : ℕ) (a : NPoly R N) : autoF g a = automorph g a :=
  Kron.autoL_eq g a

/-- **Compiled-code discipline.** `NPoly` is a structure with one function field, so the compiler
treats an `NPoly` value as a function: an `NPoly`-valued `let` that is used only inside a
coefficient lambda is moved into it, and a definition or lambda returning an `NPoly` is
eta-expanded with the coefficient index; either way an expensive product would be recomputed for
every coefficient. Arrays are not moved. So the fast products are computed as **arrays**
(`mulArr`, `mulArrM`) and wrapped with `ofArr` only where they are used, and the wrappers below
are `@[inline]`, so that the array is bound at the call site. -/
def mulArr {N : ℕ} (a b : IntPoly N) : Array ℤ := Kron.mulNeg N (toArr 1 a) (toArr 1 b)

/-- **The array product is the trusted product.** -/
@[simp] theorem ofArr_mulArr {N : ℕ} (a b : IntPoly N) : ofArr (mulArr a b) = a * b := by
  have h := Kron.mulNeg_eq N (toArr 1 a) (toArr 1 b)
  have e : ∀ arr : Array ℤ, (ofArr arr : IntPoly N) = Kron.ofArrZ N arr := fun _ => rfl
  rw [mulArr, e, h, ← e, ← e, ofArr_toArr, ofArr_toArr]

/-- The product on the forced path, as an array: `mulArr`, or the cyclic mutant. -/
def mulArrM (m : Mut) {N : ℕ} (a b : IntPoly N) : Array ℤ :=
  if m = .mulCyclic then toArr 1 (Mutants.mulCyclic a b) else mulArr a b

@[simp] theorem ofArr_mulArrM_none {N : ℕ} (a b : IntPoly N) : ofArr (mulArrM .none a b) = a * b := by
  simp [mulArrM]

/-- Coefficientwise sum of two arrays (the first `N` entries). -/
def addArr (N : ℕ) (a b : Array ℤ) : Array ℤ := Array.ofFn (n := N) fun k => a[k.val]! + b[k.val]!

@[simp] theorem ofArr_addArr {N : ℕ} (a b : Array ℤ) :
    ofArr (N := N) (addArr N a b) = ofArr a + ofArr b := by
  ext k
  show (addArr N a b)[k.val]! = a[k.val]! + b[k.val]!
  rw [addArr, getElem!_pos _ _ (by simp), Array.getElem_ofFn]

theorem ofArr_replicate_zero {N : ℕ} : ofArr (N := N) (Array.replicate N (0 : ℤ)) = 0 := by
  ext k
  show (Array.replicate N (0 : ℤ))[k.val]! = 0
  rw [getElem!_pos _ _ (by simp)]
  simp

/-- A sum of array products, accumulated as arrays. -/
theorem ofArr_foldl_addArr {N : ℕ} [NeZero N] (f : ℕ → Array ℤ) (n : ℕ) :
    ofArr (N := N) ((List.range n).foldl (fun acc j => addArr N acc (f j)) (Array.replicate N 0)) =
      ∑ j ∈ Finset.range n, ofArr (N := N) (f j) := by
  induction n with
  | zero => simp [ofArr_replicate_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ofArr_addArr, ih,
      Finset.sum_range_succ]

/-- The product on the forced path (integer polynomials): the Kronecker product (`mulArr`; proved
equal to the trusted `*`: `ofArr_mulArr`), or the cyclic mutant. -/
@[inline] def mulMF (m : Mut) {N : ℕ} (a b : IntPoly N) : IntPoly N := ofArr (mulArrM m a b)

/-- The automorphism on the forced path: the linear-time scatter, or a mutant. -/
@[inline] def autoMF (m : Mut) (g : ℕ) (a : NPoly R N) : NPoly R N :=
  if m = .autoIndex ∨ m = .autoIndexShift ∨ m = .autoSign then m.autoM g a else autoF g a

@[simp] theorem mulMF_none {N : ℕ} (a b : IntPoly N) : mulMF .none a b = a * b := by simp [mulMF]
@[simp] theorem autoMF_none (g : ℕ) (a : NPoly R N) : autoMF .none g a = automorph g a := by
  simp [autoMF]

end Fast

/-- `Spec.Encrypt.encrypt` with loop products (or a mutant). `p` is the stored plaintext
polynomial (any representative of the message). -/
def encryptMF (m : Mut) {N : ℕ} (t : ℕ) (b a p u e₁ e₂ : IntPoly N) : List (IntPoly N) :=
  if m = .none then [ofArr (mulArr b u) + (t : ℤ) • e₁ + p, ofArr (mulArr a u) + (t : ℤ) • e₂]
  else m.encryptM t b a p u e₁ e₂

/-- **`Spec.Encrypt.encrypt`** (the stored-plaintext form: `p` is added as it is). -/
theorem encryptMF_none {N : ℕ} (t : ℕ) (b a p u e₁ e₂ : IntPoly N) :
    encryptMF .none t b a p u e₁ e₂ = Encrypt.encrypt t b a p u e₁ e₂ := by
  simp [encryptMF, Encrypt.encrypt]

/-- `Spec.Encrypt.freshError` with loop products. -/
def freshErrorF {N : ℕ} (s e u e₁ e₂ : IntPoly N) : IntPoly N := mulF e u + e₁ + mulF e₂ s

theorem freshErrorF_eq {N : ℕ} (s e u e₁ e₂ : IntPoly N) :
    freshErrorF s e u e₁ e₂ = Encrypt.freshError s e u e₁ e₂ := by
  simp [freshErrorF, Encrypt.freshError]

/-- `Spec.Encrypt.freshError`, forced, with the array products. -/
def freshErrorA {N : ℕ} (K : ℕ) (s e u e₁ e₂ : IntPoly N) : Array ℤ :=
  toArr K (ofArr (mulArr e u) + e₁ + ofArr (mulArr e₂ s))

theorem freshErrorA_eq {N : ℕ} (K : ℕ) (s e u e₁ e₂ : IntPoly N) :
    ofArr (freshErrorA K s e u e₁ e₂) = Encrypt.freshError s e u e₁ e₂ := by
  simp [freshErrorA, Encrypt.freshError]

/-- `a * 0 = 0` for the negacyclic product (the Horner base case of the phase). -/
theorem npoly_mul_zero {R : Type} [CommRing R] {N : ℕ} (a : NPoly R N) : a * (0 : NPoly R N) = 0 := by
  ext k
  rw [Validation.Ring.coeff_mul']
  apply Finset.sum_eq_zero
  intro i _
  split_ifs <;> simp

/-! ## The phase -/

/-- Forced Horner evaluation of the phase **over the integers** (the secret is small, so no
reduction is needed until the end). -/
def phaseZ (N K : ℕ) (m : Mut) (s : Array ℤ) : List (Array ℤ) → Array ℤ
  | [] => toArr K (0 : IntPoly N)
  | [c] => toArr K (ofArr (N := N) c)
  | c :: c' :: cs => toArr K (ofArr (N := N) c + ofArr (mulArrM m (ofArr (N := N) s) (ofArr (phaseZ N K m s (c' :: cs)))))

/-- **Phase.** The integer phase, reduced modulo any `Q`, is the trusted phase of the reduced
ciphertext under the reduced secret. -/
theorem phaseZ_spec (N K Q : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    ofInt Q (ofArr (N := N) (phaseZ N K .none s ct)) =
      phase (ofInt Q (ofArr s)) (ct.map fun c => ofInt Q (ofArr c)) := by
  induction ct with
  | nil => simp [phaseZ, phase, ofInt_zero]
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [phaseZ, ofArr_toArr, List.map_cons, List.map_nil, phase, npoly_mul_zero]
      ext i; simp
    | cons c' cs' =>
      rw [phaseZ]
      simp only [ofArr_toArr, ofArr_mulArrM_none, List.map_cons, phase, ofInt_add, ofInt_mul]
      rw [ih]
      simp only [List.map_cons, phase]

/-- Forced automorphism of an integer polynomial. -/
def autoA (N K : ℕ) (m : Mut) (g : ℕ) (a : Array ℤ) : Array ℤ :=
  toArr K (autoMF m g (ofArr (N := N) a))

theorem autoA_spec (N K g : ℕ) (a : Array ℤ) :
    ofArr (N := N) (autoA N K .none g a) = automorph g (ofArr a) := by
  simp [autoA]

/-- Forced integer phase under the key `σ_key(s)`; `sK` must be `autoA N K m key s` (the caller
caches it per key). -/
def phaseAtZ (N K : ℕ) (m : Mut) (key : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) : Array ℤ :=
  phaseZ N K m (autoA N K m key s) ct

/-- **`Spec.Trace.phaseAt`.** -/
theorem phaseAtZ_spec (P : FullParams) (K Q key : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    ofInt Q (ofArr (phaseAtZ P.src.N K .none key s ct)) =
      Trace.phaseAt P Q key (ofArr s) (ct.map ofArr) := by
  simp only [phaseAtZ, phaseZ_spec, autoA_spec, Trace.phaseAt, List.map_map]
  rfl

/-- Forced centred lift modulo `Q` of an integer polynomial. -/
def centredA (N K : ℕ) (m : Mut) (Q : ℕ) (z : Array ℤ) : Array ℤ :=
  toArr K (m.centeredM (ofInt Q (ofArr (N := N) z)))

/-- Forced centred phase. -/
def centredPhaseA (N K : ℕ) (m : Mut) (Q : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) : Array ℤ :=
  centredA N K m Q (phaseZ N K m s ct)

/-- **`Spec.Scheme.centeredPhase`.** -/
theorem centredPhaseA_spec (N K Q : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    ofArr (N := N) (centredPhaseA N K .none Q s ct) =
      centeredPhase (ofArr s) (ct.map fun c => ofInt Q (ofArr c)) := by
  simp [centredPhaseA, centredA, centeredPhase, phaseZ_spec]

/-- The centred phase under `σ_key(s)`: `centered (Spec.Trace.phaseAt …)`. -/
theorem centredA_phaseAtZ_spec (P : FullParams) (K Q key : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    ofArr (centredA P.src.N K .none Q (phaseAtZ P.src.N K .none key s ct)) =
      centered (Trace.phaseAt P Q key (ofArr s) (ct.map ofArr)) := by
  simp [centredA, phaseAtZ_spec]

/-! ## Decryption -/

/-- Forced textbook decryption from a forced centred phase `Φ`. -/
def decryptOfPhaseA (N K t : ℕ) (Φ : Array ℤ) : Array (ZMod t) :=
  toArr K (ofInt t (ofArr (N := N) Φ))

/-- Forced `Spec.Scheme.bgvDecrypt`. -/
def decryptA (N K : ℕ) (m : Mut) (t Q : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) : Array (ZMod t) :=
  decryptOfPhaseA N K t (centredPhaseA N K m Q s ct)

/-- **`Spec.Scheme.bgvDecrypt`.** -/
theorem decryptA_spec (N K t Q : ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    ofArr (N := N) (decryptA N K .none t Q s ct) =
      bgvDecrypt t (ofArr s) (ct.map fun c => ofInt Q (ofArr c)) := by
  simp [decryptA, decryptOfPhaseA, bgvDecrypt, centredPhaseA_spec]

/-- Forced switched phase: the centred phase switched down to one limb. -/
def switchedPhaseA (N K : ℕ) (m : Mut) (t : ℕ) (qs : List ℕ) (Φ : Array ℤ) : Array ℤ :=
  toArr K (m.switchDownRevM t qs.reverse (ofArr (N := N) Φ))

/-- Forced `Spec.Decrypt.bgvDecryptSwitched`. -/
def decryptSwitchedA (N K : ℕ) (m : Mut) (t : ℕ) (qs : List ℕ) (s : Array ℤ)
    (ct : List (Array ℤ)) : Array (ZMod t) :=
  decryptOfPhaseA N K t (switchedPhaseA N K m t qs (centredPhaseA N K m qs.prod s ct))

/-- **`Spec.Decrypt.bgvDecryptSwitched`.** -/
theorem decryptSwitchedA_spec (N K t : ℕ) (qs : List ℕ) (s : Array ℤ) (ct : List (Array ℤ)) :
    ofArr (N := N) (decryptSwitchedA N K .none t qs s ct) =
      Decrypt.bgvDecryptSwitched t qs (ofArr s) (ct.map fun c => ofInt qs.prod (ofArr c)) := by
  simp [decryptSwitchedA, decryptOfPhaseA, switchedPhaseA, Decrypt.bgvDecryptSwitched,
    centredPhaseA_spec]

/-! ## Key-switching keys -/

/-- Forced `b + a·s` over the integers (shared by every level). -/
def keyLhsZ (N K : ℕ) (m : Mut) (b a s : Array ℤ) : Array ℤ :=
  toArr K (ofArr (N := N) b + ofArr (mulArrM m (ofArr (N := N) a) (ofArr s)))

/-- Forced target polynomial `target(s)` over the integers. -/
def targetZ (N K : ℕ) (m : Mut) (s : Array ℤ) : KeyTarget → Array ℤ
  | .square => mulArrM m (ofArr (N := N) s) (ofArr s)
  | .galois g => toArr K (autoMF m g (ofArr (N := N) s))

theorem targetZ_spec (N K : ℕ) (s : Array ℤ) (tgt : KeyTarget) :
    ofArr (N := N) (targetZ N K .none s tgt) = tgt.eval (ofArr s) := by
  cases tgt <;> simp [targetZ, KeyTarget.eval]

/-- Forced error of a key for the constant factor `c` modulo `M`, from the forced `b + a·s` and
target. -/
def keyErrA (N K M : ℕ) (c : ZMod M) (lhs tgt : Array ℤ) : Array ℤ :=
  toArr K (centered (ofInt M (ofArr (N := N) lhs) - c • ofInt M (ofArr tgt)))

theorem const_mul_eq_smul {R : Type} [CommRing R] {N : ℕ} (c : R) (a : NPoly R N) :
    const c * a = c • a := by
  ext i; rw [coeff_const_mul]; rfl

/-- **The error of `Spec.Scheme.KeyValid`.** For a requirement whose factor is the constant `c`
(every `Spec.Budget.gadgetReq` is), the forced error is the `e` of `KeyValid`. -/
theorem keyErrA_spec (N K M : ℕ) (c : ZMod M) (tgt : KeyTarget) (b a s : Array ℤ) :
    ofArr (N := N) (keyErrA N K M c (keyLhsZ N K .none b a s) (targetZ N K .none s tgt)) =
      centered (ofInt M (ofArr b) + ofInt M (ofArr a) * ofInt M (ofArr s) -
        (⟨M, const c, tgt⟩ : KeyReq N).factor * ofInt M ((⟨M, const c, tgt⟩ : KeyReq N).target.eval (ofArr s))) := by
  simp only [keyErrA, keyLhsZ, ofArr_toArr, ofArr_mulArrM_none, ofInt_add, ofInt_mul, targetZ_spec,
    const_mul_eq_smul]

/-- Forced decision of `KeyValid .bgv t B` from the forced error. -/
def keyValidOfErr (N t B : ℕ) (e : Array ℤ) : Bool :=
  decide (normInf (ofArr (N := N) e) ≤ B) && decide (∀ i : Fin N, (t : ℤ) ∣ (ofArr (N := N) e).coeff i)

/-- **`Spec.Scheme.KeyValid`** (BGV), for a requirement with a constant factor. -/
theorem keyValid_iff (N K M t B : ℕ) (c : ZMod M) (tgt : KeyTarget) (b a s : Array ℤ) :
    keyValidOfErr N t B (keyErrA N K M c (keyLhsZ N K .none b a s) (targetZ N K .none s tgt)) = true ↔
      KeyValid .bgv t B (ofArr s) (⟨M, const c, tgt⟩ : KeyReq N) (ofInt M (ofArr b)) (ofInt M (ofArr a)) := by
  simp only [keyValidOfErr, keyErrA_spec, KeyValid, Bool.and_eq_true, decide_eq_true_eq, forall_const]

/-! ## Message-level evaluation -/

/-- Replace the message of `d` by its forced copy. `arr` must be `toArr K m` for the message `m`
of `v` (the caller forces it; see `retab_eq`). -/
@[noinline] def retabWith {P : Params} (ρ : Env P) (d : Var) (v : Val P) (arr : Array (ZMod P.t)) :
    Env P :=
  ρ.set d { v with msg := .exact (ofArr arr) }

/-- Re-tabulating a variable does not change the environment. -/
theorem retab_eq {P : Params} (K : ℕ) (ρ : Env P) (d : Var) (v : Val P) (m : Poly P.t P.N)
    (hv : ρ d = some v) (hm : v.msg = .exact m) : retabWith ρ d v (toArr K m) = ρ := by
  funext y
  simp only [retabWith, Env.set, ofArr_toArr]
  split
  · rename_i h; subst h; rw [hv, ← hm]
  · rfl

/-- The trusted product in `Z_t[X]/(X^N+1)` as an array, through integer representatives and the
Kronecker product `mulArr`. -/
def mulArrQ {t N : ℕ} (a b : Poly t N) : Array (ZMod t) :=
  (mulArr (NPoly.map (ZMod.cast : ZMod t → ℤ) a) (NPoly.map (ZMod.cast : ZMod t → ℤ) b)).map
    fun z : ℤ => (z : ZMod t)

theorem mulArr_size {N : ℕ} (a b : IntPoly N) : (mulArr a b).size = N := by
  simp [mulArr, Kron.mulNeg]

theorem ofArr_mulArrQ {t N : ℕ} (a b : Poly t N) : ofArr (mulArrQ a b) = a * b := by
  ext i
  have hs := mulArr_size (NPoly.map (ZMod.cast : ZMod t → ℤ) a) (NPoly.map (ZMod.cast : ZMod t → ℤ) b)
  have h1 : (ofArr (mulArrQ a b) : Poly t N).coeff i =
      (((mulArr (NPoly.map (ZMod.cast : ZMod t → ℤ) a) (NPoly.map (ZMod.cast : ZMod t → ℤ) b))[i.val]! : ℤ)
        : ZMod t) := by
    show (mulArrQ a b)[i.val]! = _
    unfold mulArrQ
    rw [getElem!_pos _ _ (by simp [hs]), Array.getElem_map, getElem!_pos _ _ (by simp [hs])]
  have h2 := congrArg (fun p : IntPoly N => p.coeff i)
    (ofArr_mulArr (NPoly.map (ZMod.cast : ZMod t → ℤ) a) (NPoly.map (ZMod.cast : ZMod t → ℤ) b))
  simp only [ofArr] at h2
  rw [h1, h2]
  have := congrArg (fun p : Poly t N => p.coeff i)
    (Validation.Scheme.ofInt_mul (q := t) (NPoly.map (ZMod.cast : ZMod t → ℤ) a) (NPoly.map (ZMod.cast : ZMod t → ℤ) b))
  simp only [Kron.ofInt_map_cast] at this
  exact this

theorem ofArr_autoArr {t N : ℕ} (g : ℕ) (a : Poly t N) : ofArr (Kron.autoArr g a) = automorph g a := by
  rw [← Kron.autoL_eq]
  ext i
  have hs := (Kron.autoArr_prefix g a N).1
  simp only [ofArr, Kron.autoL, Kron.ofArrD, Kron.autoArr] at hs ⊢
  rw [getElem!_pos _ _ (by simp [hs]), Array.getD, dif_pos (by simp [hs])]
  rfl

/-- The destination's message of `mul`, `square`, `mulPlain` and `automorph`, computed from the
operands' messages as an array (`mulArrQ`: Kronecker product; `Kron.autoArr`: linear scatter);
`none` for every other instruction. -/
def fastMsg {P : Params} (ρ : Env P) : Instr → Option (Array (ZMod P.t))
  | .mul _ a b | .mulPlain _ a b =>
    match ρ a, ρ b with
    | some x, some y => match x.msg, y.msg with
      | .exact mx, .exact my => some (mulArrQ mx my)
    | _, _ => none
  | .square _ a =>
    match ρ a with
    | some x => match x.msg with
      | .exact mx => some (mulArrQ mx mx)
    | none => none
  | .automorph _ a g =>
    match ρ a with
    | some x => match x.msg with
      | .exact mx => some (Kron.autoArr g mx)
    | none => none
  | _ => none

/-- **`fastMsg` is the message `Source.step` stores.** -/
theorem fastMsg_spec {P : Params} (ρ ρ' : Env P) (i : Instr) (v : Val P) (m : Poly P.t P.N)
    (arr : Array (ZMod P.t)) (hs : step P ρ i = some ρ') (hv : ρ' (Trace.dst i) = some v)
    (hm : v.msg = .exact m) (hf : fastMsg ρ i = some arr) : ofArr arr = m := by
  cases i with
  | mul d a b =>
    simp only [fastMsg] at hf
    cases ha : ρ a with
    | none => simp [ha] at hf
    | some x =>
      cases hb : ρ b with
      | none => simp [ha, hb] at hf
      | some y =>
        cases hx : x.msg with
        | exact mx =>
          cases hy : y.msg with
          | exact my =>
            simp only [ha, hb, hx, hy, Option.some.injEq] at hf
            subst hf
            simp [step, ha, hb, hx, hy, Msg.lift₂] at hs
            rw [Option.bind_eq_some_iff] at hs
            obtain ⟨_, _, hs⟩ := hs
            simp only [Option.some.injEq] at hs
            subst hs
            simp [Env.set, Trace.dst] at hv
            subst hv
            simp only at hm
            cases hm
            exact ofArr_mulArrQ mx my
  | mulPlain d a b =>
    simp only [fastMsg] at hf
    cases ha : ρ a with
    | none => simp [ha] at hf
    | some x =>
      cases hb : ρ b with
      | none => simp [ha, hb] at hf
      | some y =>
        cases hx : x.msg with
        | exact mx =>
          cases hy : y.msg with
          | exact my =>
            simp only [ha, hb, hx, hy, Option.some.injEq] at hf
            subst hf
            simp [step, ha, hb, hx, hy, Msg.lift₂] at hs
            rw [Option.bind_eq_some_iff] at hs
            obtain ⟨_, _, hs⟩ := hs
            simp only [Option.some.injEq] at hs
            subst hs
            simp [Env.set, Trace.dst] at hv
            subst hv
            simp only at hm
            cases hm
            exact ofArr_mulArrQ mx my
  | square d a =>
    simp only [fastMsg] at hf
    cases ha : ρ a with
    | none => simp [ha] at hf
    | some x =>
      cases hx : x.msg with
      | exact mx =>
        simp only [ha, hx, Option.some.injEq] at hf
        subst hf
        simp [step, ha, hx, Msg.lift₂] at hs
        rw [Option.bind_eq_some_iff] at hs
        obtain ⟨_, _, hs⟩ := hs
        simp only [Option.some.injEq] at hs
        subst hs
        simp [Env.set, Trace.dst] at hv
        subst hv
        simp only at hm
        cases hm
        exact ofArr_mulArrQ mx mx
  | automorph d a g =>
    simp only [fastMsg] at hf
    cases ha : ρ a with
    | none => simp [ha] at hf
    | some x =>
      cases hx : x.msg with
      | exact mx =>
        simp only [ha, hx, Option.some.injEq] at hf
        subst hf
        simp [step, ha, hx, Msg.lift₁] at hs
        rw [Option.bind_eq_some_iff] at hs
        obtain ⟨_, _, hs⟩ := hs
        simp only [Option.some.injEq] at hs
        subst hs
        simp [Env.set, Trace.dst] at hv
        subst hv
        simp only at hm
        cases hm
        exact ofArr_autoArr g mx
  | _ => simp [fastMsg] at hf

/-- Re-tabulating a variable with any array that wraps to its message does not change the
environment. -/
theorem retab_eq' {P : Params} (ρ : Env P) (d : Var) (v : Val P) (m : Poly P.t P.N)
    (arr : Array (ZMod P.t)) (hv : ρ d = some v) (hm : v.msg = .exact m) (ha : ofArr arr = m) :
    retabWith ρ d v arr = ρ := by
  funext y
  simp only [retabWith, Env.set, ha]
  split
  · rename_i h; subst h; rw [hv, ← hm]
  · rfl

/-- One forced step: `Source.step` (or its mutant), then the destination's message is forced. -/
def stepA (K : ℕ) (mt : Mut) (P : Params) (ρ : Env P) (i : Instr) : Option (Env P) :=
  match mt.stepM P ρ i with
  | none => none
  | some ρ' =>
    match ρ' (Trace.dst i) with
    | some v =>
      match v.msg with
      | .exact m =>
        let arr := match (if mt = .none then fastMsg ρ i else none) with
          | some a => a
          | none => toArr K m
        some (retabWith ρ' (Trace.dst i) v arr)
    | none => some ρ'

/-- **`Spec.Source.step`.** -/
theorem stepA_spec (K : ℕ) (P : Params) (ρ : Env P) (i : Instr) :
    stepA K .none P ρ i = step P ρ i := by
  unfold stepA
  rw [Mut.step_none]
  cases h : step P ρ i with
  | none => rfl
  | some ρ' =>
    simp only
    cases hv : ρ' (Trace.dst i) with
    | none => rfl
    | some v =>
      simp only
      cases hm : v.msg with
      | exact m =>
        simp only [hm, ite_true]
        split
        · rename_i a hf
          exact congrArg some (retab_eq' ρ' _ v m a hv hm (fastMsg_spec ρ ρ' i v m a h hv hm hf))
        · rw [retab_eq K ρ' _ v m hv hm]

/-- **The body of `Spec.Source.eval`.** -/
theorem foldlM_stepA (K : ℕ) (P : Params) (body : List Instr) (ρ : Env P) :
    body.foldlM (stepA K .none P) ρ = body.foldlM (step P) ρ := by
  have : stepA K .none P = step P := by funext ρ i; exact stepA_spec K P ρ i
  rw [this]

/-! ## Witnesses of the approximate phase contracts (`Spec.Trace.StepOK`)

The checker `FHE.Pin.stepCheck` (not proved sound as a whole) uses these witnesses for the
existentials of the `relin`/`keySwitch` and `modSwitch` clauses. The two lemmas say that with
them the equational conjuncts hold by construction, so that only the norm and divisibility
conjuncts remain to be tested on the data. -/

/-- `e := centered (φ − φ_a)` satisfies `φ = φ_a + ofInt Q e`. -/
theorem ks_witness {Q N : ℕ} (φ φa : Poly Q N) : φ = φa + ofInt Q (centered (φ - φa)) := by
  rw [ofInt_centered]; ext i; simp

/-- `δ := q·Φ' − Φ` satisfies `q ∣ Φ + δ` and `(Φ + δ) / q = Φ'`. -/
theorem ms_witness {N : ℕ} (q : ℕ) (hq : q ≠ 0) (Φ Φ' : IntPoly N) :
    (∀ j, (q : ℤ) ∣ Φ.coeff j + ((q : ℤ) • Φ' - Φ).coeff j) ∧
      (⟨fun j => (Φ.coeff j + ((q : ℤ) • Φ' - Φ).coeff j) / q⟩ : IntPoly N) = Φ' := by
  have h : ∀ j, Φ.coeff j + ((q : ℤ) • Φ' - Φ).coeff j = (q : ℤ) * Φ'.coeff j := by
    intro j; simp
  refine ⟨fun j => ⟨Φ'.coeff j, h j⟩, ?_⟩
  ext j
  simp only [h]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hq)

/-! ## Decidability of the trusted predicates (for the literal mode) -/

instance {R : Type} [DecidableEq R] {N : ℕ} : DecidableEq (NPoly R N) := fun a b =>
  decidable_of_iff (∀ i, a.coeff i = b.coeff i) ⟨fun h => NPoly.ext (funext h), fun h _ => h ▸ rfl⟩

instance {N : ℕ} (kind : Kind) (t B : ℕ) (s : IntPoly N) (req : KeyReq N)
    (b a : Poly req.modulus N) : Decidable (KeyValid kind t B s req b a) := by
  unfold KeyValid; infer_instance

instance (P : FullParams) (lay : Budget.KSLayout) (ℓ : ℕ) (tgt : KeyTarget)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    Decidable (Budget.GadgetKeysOK P lay ℓ tgt s keys) := by
  unfold Budget.GadgetKeysOK; infer_instance

instance {N : ℕ} (t Q : ℕ) (s e b a : IntPoly N) : Decidable (Encrypt.PublicKeyOK t Q s e b a) := by
  unfold Encrypt.PublicKeyOK; infer_instance

end FHE.Pin
