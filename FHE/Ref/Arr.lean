import FHE.Pin.Force
import Challenge.Source

/-!
# FHE.Ref.Arr — array forms of the integer-polynomial operations, PROVED equal to the trusted ones
(UNTRUSTED glue; the theorems are kernel-checked)

The reference implementation (`FHE/Ref/*.lean`, executable `provenfhe_ref`) keeps every
polynomial as an `Array ℤ` of its `N` coefficients and never builds a `Spec.NPoly` value on the run
path (`Spec.NPoly` is a structure with one function field: compiled code re-evaluates a composed
`NPoly` for every coefficient where it is read; see `FHE.Pin.mulArr`). An array means the trusted
polynomial `FHE.Pin.ofArr arr` (coefficient `i` is `arr[i]!`); every theorem below says that an
array operation, read through `ofArr`, IS the trusted operation on the wrapped arguments, for all
arrays. Since every polynomial is `ofArr` of an array (`FHE.Pin.ofArr_toArr`), that covers every
input of the trusted operations.

* coefficientwise maps (`mapA`, `zipA`, `addA`, `subA`, `smulA`): definitional;
* the negacyclic product `mulA` = `FHE.Pin.Kron.mulNeg` (Kronecker substitution, one big-integer
  product; `Kron.mulNeg_eq`);
* the automorphism `autoA` = `FHE.Pin.Kron.autoArr` (linear scatter; `Kron.autoL_eq`);
* sums of lists (`sumA`), lists of components (`wC`), key lists (`wK`), the zero-padded
  componentwise operation of `Challenge.Source.padZip` (`padZipA`) and the tensor product
  `Challenge.Source.tensorParts` (`tensorPartsA`) and `Challenge.Source.tensor` (`tensorA`).

Gate convention: no `Challenge.*` definition is named in `simp`/`rw`/`unfold`; their equations are
restated here as `rfl` lemmas in this namespace.
-/

namespace FHE.Ref
open Spec Spec.NPoly FHE.Pin

variable {N : ℕ}

/-! ## Coefficientwise operations -/

/-- The zero polynomial as an array of `N` zeros. -/
def zeroA (N : ℕ) : Array ℤ := Array.replicate N 0

@[simp] theorem ofArr_zeroA : (ofArr (zeroA N) : IntPoly N) = 0 := ofArr_replicate_zero

/-- Evaluate every coefficient of a polynomial once. -/
def force (N : ℕ) {R : Type} (p : NPoly R N) : Array R := Array.ofFn (n := N) fun i => p.coeff i

@[simp] theorem ofArr_force {R : Type} [Inhabited R] (p : NPoly R N) : (ofArr (force N p) : NPoly R N) = p := by
  ext i
  show (force N p)[i.val]! = p.coeff i
  rw [force, getElem!_pos _ _ (by simp), Array.getElem_ofFn]

/-- `f` on every coefficient. -/
def mapA (N : ℕ) {R S : Type} [Inhabited R] (f : R → S) (a : Array R) : Array S :=
  Array.ofFn (n := N) fun k => f a[k.val]!

theorem ofArr_mapA {R S : Type} [Inhabited R] [Inhabited S] (f : R → S) (a : Array R) :
    (ofArr (mapA N f a) : NPoly S N) = ⟨fun i => f ((ofArr a : NPoly R N).coeff i)⟩ := by
  ext i
  show (mapA N f a)[i.val]! = f a[i.val]!
  rw [mapA, getElem!_pos _ _ (by simp), Array.getElem_ofFn]

@[simp] theorem mapA_size {R S : Type} [Inhabited R] (f : R → S) (a : Array R) :
    (mapA N f a).size = N := by simp [mapA]

/-- `f` on every pair of coefficients. -/
def zipA (N : ℕ) (f : ℤ → ℤ → ℤ) (a b : Array ℤ) : Array ℤ :=
  Array.ofFn (n := N) fun k => f a[k.val]! b[k.val]!

theorem ofArr_zipA (f : ℤ → ℤ → ℤ) (a b : Array ℤ) :
    (ofArr (zipA N f a b) : IntPoly N) =
      ⟨fun i => f ((ofArr a : IntPoly N).coeff i) ((ofArr b : IntPoly N).coeff i)⟩ := by
  ext i
  show (zipA N f a b)[i.val]! = f a[i.val]! b[i.val]!
  rw [zipA, getElem!_pos _ _ (by simp), Array.getElem_ofFn]

def addA (N : ℕ) (a b : Array ℤ) : Array ℤ := zipA N (· + ·) a b
def subA (N : ℕ) (a b : Array ℤ) : Array ℤ := zipA N (· - ·) a b
def smulA (N : ℕ) (c : ℤ) (a : Array ℤ) : Array ℤ := mapA N (c * ·) a

@[simp] theorem ofArr_addA (a b : Array ℤ) :
    (ofArr (addA N a b) : IntPoly N) = ofArr a + ofArr b := by
  rw [addA, ofArr_zipA]; rfl

@[simp] theorem ofArr_subA (a b : Array ℤ) :
    (ofArr (subA N a b) : IntPoly N) = ofArr a - ofArr b := by
  rw [subA, ofArr_zipA]; rfl

@[simp] theorem ofArr_smulA (c : ℤ) (a : Array ℤ) :
    (ofArr (smulA N c a) : IntPoly N) = c • ofArr a := by
  rw [smulA, ofArr_mapA]; rfl

/-! ## Product and automorphism -/

/-- **The negacyclic product**: `FHE.Pin.Kron.mulNeg` (Kronecker substitution). -/
def mulA (N : ℕ) (a b : Array ℤ) : Array ℤ := Kron.mulNeg N a b

@[simp] theorem ofArr_mulA (a b : Array ℤ) :
    (ofArr (mulA N a b) : IntPoly N) = ofArr a * ofArr b :=
  Kron.mulNeg_eq N a b

/-- **The automorphism** `X ↦ X^g`: `FHE.Pin.Kron.autoArr` (linear scatter). -/
def autoA (N : ℕ) (g : ℕ) (a : Array ℤ) : Array ℤ := Kron.autoArr g (ofArr a : IntPoly N)

@[simp] theorem ofArr_autoA (g : ℕ) (a : Array ℤ) :
    (ofArr (autoA N g a) : IntPoly N) = automorph g (ofArr a) := by
  rw [← Kron.autoL_eq]
  ext i
  have hs := (Kron.autoArr_prefix g (ofArr a : IntPoly N) N).1
  simp only [ofArr, autoA, Kron.autoL, Kron.ofArrD, Kron.autoArr] at hs ⊢
  rw [getElem!_pos _ _ (by simp [hs]), Array.getD, dif_pos (by simp [hs])]
  rfl

/-! ## Lists -/

/-- The sum of a list of arrays. -/
def sumA (N : ℕ) (l : List (Array ℤ)) : Array ℤ := l.foldr (addA N) (zeroA N)

@[simp] theorem ofArr_sumA (l : List (Array ℤ)) :
    (ofArr (sumA N l) : IntPoly N) = (l.map (ofArr (N := N))).sum := by
  induction l with
  | nil => simp [sumA]
  | cons x xs ih =>
    rw [sumA, List.foldr_cons, ofArr_addA, List.map_cons, List.sum_cons]
    rw [← ih]; rfl

/-- A ciphertext (list of components) read as trusted polynomials. -/
def wC (N : ℕ) (c : List (Array ℤ)) : List (IntPoly N) := c.map ofArr

/-- A list of keys read as trusted polynomials. -/
def wK (N : ℕ) (k : List (Array ℤ × Array ℤ)) : List (IntPoly N × IntPoly N) :=
  k.map fun p => (ofArr p.1, ofArr p.2)

theorem wK_getD (k : List (Array ℤ × Array ℤ)) (j : ℕ) :
    (wK N k).getD j (0, 0) =
      ((ofArr (k.getD j (zeroA N, zeroA N)).1 : IntPoly N), ofArr (k.getD j (zeroA N, zeroA N)).2) := by
  unfold wK
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases k[j]? <;> simp

theorem map_getD (l : List (Array ℤ)) (j : ℕ) :
    (l.map (ofArr (N := N))).getD j 0 = ofArr (l.getD j (zeroA N)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp

theorem wC_headD (l : List (Array ℤ)) : (wC N l).headD 0 = ofArr (l.headD (zeroA N)) := by
  cases l <;> simp [wC]

/-! ## `padZip`, `tensorParts`, `tensor` -/

section
variable (f : IntPoly N → IntPoly N → IntPoly N)

theorem padZip_nil (bs : List (IntPoly N)) : Challenge.Source.padZip f [] bs = bs.map (f 0) := rfl
theorem padZip_cons_nil (a : IntPoly N) (as : List (IntPoly N)) :
    Challenge.Source.padZip f (a :: as) [] = (a :: as).map (fun x => f x 0) := rfl
theorem padZip_cons_cons (a b : IntPoly N) (as bs : List (IntPoly N)) :
    Challenge.Source.padZip f (a :: as) (b :: bs) = f a b :: Challenge.Source.padZip f as bs := rfl
end

/-- `Challenge.Source.padZip` on arrays. -/
def padZipA (N : ℕ) (f : Array ℤ → Array ℤ → Array ℤ) :
    List (Array ℤ) → List (Array ℤ) → List (Array ℤ)
  | [], bs => bs.map (f (zeroA N))
  | a :: as, [] => (a :: as).map (fun x => f x (zeroA N))
  | a :: as, b :: bs => f a b :: padZipA N f as bs

theorem wC_padZipA (fA : Array ℤ → Array ℤ → Array ℤ) (f : IntPoly N → IntPoly N → IntPoly N)
    (hf : ∀ a b, ofArr (fA a b) = f (ofArr a) (ofArr b)) :
    ∀ as bs, wC N (padZipA N fA as bs) = Challenge.Source.padZip f (wC N as) (wC N bs)
  | [], bs => by
    simp only [padZipA, wC, List.map_nil, padZip_nil, List.map_map]
    exact List.map_congr_left fun b _ => by simp [hf]
  | a :: as, [] => by
    simp only [padZipA, wC, List.map_nil, List.map_cons, padZip_cons_nil, List.map_map]
    simp [hf]
  | a :: as, b :: bs => by
    have ih := wC_padZipA fA f hf as bs
    simp only [padZipA, wC, List.map_cons, padZip_cons_cons] at ih ⊢
    rw [hf, ih]

theorem tensorParts_nil (ds : List (IntPoly N)) : Challenge.Source.tensorParts [] ds = [] := rfl
theorem tensorParts_cons (c : IntPoly N) (cs ds : List (IntPoly N)) :
    Challenge.Source.tensorParts (c :: cs) ds =
      Challenge.Source.padZip (· + ·) (ds.map (c * ·)) (0 :: Challenge.Source.tensorParts cs ds) := rfl

/-- `Challenge.Source.tensorParts` on arrays (products by `mulA`). -/
def tensorPartsA (N : ℕ) : List (Array ℤ) → List (Array ℤ) → List (Array ℤ)
  | [], _ => []
  | c :: cs, ds => padZipA N (addA N) (ds.map (mulA N c)) (zeroA N :: tensorPartsA N cs ds)

theorem wC_tensorPartsA : ∀ cs ds : List (Array ℤ),
    wC N (tensorPartsA N cs ds) = Challenge.Source.tensorParts (wC N cs) (wC N ds)
  | [], ds => rfl
  | c :: cs, ds => by
    have ih := wC_tensorPartsA cs ds
    have e : wC N (c :: cs) = ofArr c :: wC N cs := rfl
    rw [e, tensorParts_cons, tensorPartsA, wC_padZipA (addA N) (· + ·) (fun a b => ofArr_addA a b)]
    have e2 : wC N (zeroA N :: tensorPartsA N cs ds) = 0 :: Challenge.Source.tensorParts (wC N cs) (wC N ds) := by
      rw [← ih]; simp [wC]
    rw [e2]
    congr 1
    simp [wC]

/-- `Challenge.Source.tensor` on arrays. -/
def tensorA (N : ℕ) (c d : List (Array ℤ)) : List (Array ℤ) :=
  match c, d with
  | [c₀, c₁], [d₀, d₁] =>
    [mulA N c₀ d₀, addA N (mulA N c₀ d₁) (mulA N c₁ d₀), mulA N c₁ d₁]
  | _, _ => []

theorem wC_tensorA (c d : List (Array ℤ)) :
    wC N (tensorA N c d) = Challenge.Source.tensor (wC N c) (wC N d) := by
  rcases c with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, c⟩⟩⟩ <;>
  rcases d with _ | ⟨d₀, _ | ⟨d₁, _ | ⟨d₂, d⟩⟩⟩ <;>
  first
  | rfl
  | (show [ofArr (mulA N c₀ d₀), ofArr (addA N (mulA N c₀ d₁) (mulA N c₁ d₀)), ofArr (mulA N c₁ d₁)] =
        [ofArr c₀ * ofArr d₀, ofArr c₀ * ofArr d₁ + ofArr c₁ * ofArr d₀, ofArr c₁ * ofArr d₁]
     simp)

end FHE.Ref
