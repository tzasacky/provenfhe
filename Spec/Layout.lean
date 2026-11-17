import Spec.Source

/-!
# Spec.Layout — storage parameters of a scheme instance   (TRUSTED)

A ring element modulo `Q = q₀⋯q_{ℓ-1}` is stored as `ℓ` limbs (its residues mod each `qᵢ`), each
limb a vector of `N` residues. This file records only the per-limb parameters a parameter set
carries besides its modulus chain (`Spec.FullParams.store`): the moduli of the ciphertext limbs
and of the special (key-switching) primes, a `2N`-th root of unity per modulus, and a word size.
The noise certificates read only the moduli of the special primes (`Spec.Budget.specialProd`);
the storage-level clauses of `Spec.ParamsOK` read the rest.
-/

namespace Spec.Layout
open NPoly

/-- Per-modulus storage parameters. -/
structure LimbParams where
  /-- The modulus. -/
  q : ℕ
  /-- The `2N`-th root of unity used for evaluation form modulo `q`. -/
  ψ : ℕ
  deriving Repr

/-- Storage parameters of a scheme instance: word size and per-limb storage parameters for the
ciphertext moduli and the special (key-switching) moduli. -/
structure StoreParams where
  W : ℕ
  /-- Storage parameters for `q₀, …, q_{L-1}`. -/
  limbs : List LimbParams
  /-- Storage parameters for the special moduli `p₀, …` used only by keys. -/
  special : List LimbParams
  deriving Repr

/-- Number of words per limb. -/
def StoreParams.units (S : StoreParams) (N : ℕ) : ℕ := N / S.W

end Spec.Layout
