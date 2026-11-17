import Spec.Ring

/-!
# Challenge.Ring — pins for `Spec.NPoly`   (LOCKED statements; proofs live in `Validation/`)

These pin the computable negacyclic operations of `Spec.Ring` to Mathlib's `R[X]/(X^N + 1)`.
They are what makes the ring arithmetic trustworthy no matter who wrote it: `toQuot` is the
one-line canonical map, and these statements say it is a bijective ring homomorphism that turns
`automorph g` into substitution `X ↦ X^g`.
-/

namespace Challenge.Ring
open Spec NPoly

variable {R : Type} [CommRing R] {N : ℕ}

theorem toQuot_zero : toQuot (0 : NPoly R N) = 0 := sorry

theorem toQuot_one (hN : 0 < N) : toQuot (1 : NPoly R N) = 1 := sorry

theorem toQuot_add (a b : NPoly R N) : toQuot (a + b) = toQuot a + toQuot b := sorry

theorem toQuot_neg (a : NPoly R N) : toQuot (-a) = -toQuot a := sorry

theorem toQuot_sub (a b : NPoly R N) : toQuot (a - b) = toQuot a - toQuot b := sorry

theorem toQuot_mul (a b : NPoly R N) : toQuot (a * b) = toQuot a * toQuot b := sorry

theorem toQuot_pow (hN : 0 < N) (a : NPoly R N) (n : ℕ) : toQuot (a ^ n) = toQuot a ^ n := sorry

theorem toQuot_smul (c : R) (a : NPoly R N) :
    toQuot (c • a) = Ideal.Quotient.mk _ (Polynomial.C c) * toQuot a := sorry

theorem toQuot_const (hN : 0 < N) (c : R) :
    toQuot (const c : NPoly R N) = Ideal.Quotient.mk _ (Polynomial.C c) := sorry

theorem toQuot_bijective (hN : 0 < N) : Function.Bijective (toQuot : NPoly R N → Quot R N) := sorry

theorem toQuot_automorph (g : ℕ) (a : NPoly R N) :
    toQuot (automorph g a) = Ideal.Quotient.mk _ ((toPolynomial a).comp (Polynomial.X ^ g)) := sorry

/-- `map f` is coefficient-wise `f` on the anchor representative. Pins `map`, and with it `ofInt`
(which is `map` of the cast `ℤ → ZMod q`). -/
theorem toPolynomial_map {S : Type} [CommRing S] (f : R →+* S) (a : NPoly R N) :
    toPolynomial (map f a) = Polynomial.map f (toPolynomial a) := sorry

theorem ofInt_eq_map (q : ℕ) (a : IntPoly N) : ofInt q a = map (Int.castRingHom (ZMod q)) a := sorry

end Challenge.Ring
