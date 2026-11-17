import FHE.KeySwitch.Hybrid

/-!
# FHE.KeySwitch.Example — non-vacuity and a kernel-checked run

Tiny BGV parameters: `N = 4`, ciphertext primes `17, 41` (`Q = 697`), one special prime `113`,
`t = 3`, ternary secret `s = 1 − X + X³`, a single digit holding both limbs (so ModUp is a
genuine 2-limb fast base conversion with possible overflow), relinearization keys with nonzero
noise `t·(1, −2, 0, 3)`.

* `example_hyps` — every hypothesis of `keySwitchBGV_spec` holds (kernel `decide`).
* `example_spec` — the main theorem instantiated: the conclusion with bound `ksBound … = 229`
  (`= ⌊(4·9·(2·697) + 3·1·113·5) / 226⌋`; the key-noise term dominates because `P < Q` here).
* `example_run` — kernel-checked execution of the RNS algorithm on one input: the error
  `y₀ + y₁·s − d·s² mod Q` is `(30, −33, 21, 0)`, divisible by `t` and within the bound.
* `example3_hyps`, `example3_run` — the same with three ciphertext primes `17, 41, 97` split into
  two digits `{17, 41}`, `{97}` (so the gadget is a genuine CRT gadget with `dnum = 2`, and digit 0
  has FastBConv overflow): hypotheses hold, the run's error is `(−3, 54, −12, 15)` (bound `245`).
-/

namespace FHE.KeySwitch.Example

open Spec Spec.NPoly Spec.Scheme FHE.RNS FHE.KeySwitch

/-- Ciphertext basis `(17, 41)`. -/
def Cb : Basis 2 := Basis.ofList [17, 41] (by decide) (by decide)
/-- Special basis `(113)`. -/
def Pb : Basis 1 := Basis.ofList [113] (by decide) (by decide)
/-- One digit with both limbs. -/
def Dg : Digits 2 := Digits.single 2

/-- The key modulus `Q·P = 697 · 113`. -/
abbrev M : ℕ := Cb.prod * Pb.prod

def mkP (l : List ℤ) : IntPoly 4 := ⟨fun i => l.getD i.val 0⟩

/-- Ternary secret `1 − X + X³`. -/
def sk : IntPoly 4 := mkP [1, -1, 0, 1]

/-- Key masks. -/
def aK (_ : Fin Dg.dnum) : Poly M 4 := ofInt M (mkP [12345, -7777, 31415, 999])

/-- Key noise, a multiple of `t = 3`. -/
def eK : IntPoly 4 := mkP [3, -6, 0, 9]

/-- `bⱼ = −aⱼ·s + gⱼ·s² + eⱼ (mod Q·P)`. -/
def bK (j : Fin Dg.dnum) : Poly M 4 :=
  -(aK j * ofInt M sk) + const ((gadget Dg Cb Pb.prod j : ℤ) : ZMod M) * ofInt M (sk * sk) +
    ofInt M eK

theorem example_hyps :
    (∀ j, Nat.Coprime 3 (Pb.q j)) ∧ (∀ i, Nat.Coprime Pb.prod (Cb.q i)) ∧ normInf sk ≤ 1 ∧
      ∀ j, KeyValid .bgv 3 9 sk (gadgetReq Dg Cb Pb .square j) (bK j) (aK j) := by
  unfold KeyValid
  decide +kernel

/-- The main theorem at these parameters (all hypotheses discharged). -/
theorem example_spec (a : RNSPoly Cb 4) :
    ∃ y0 y1 e : IntPoly 4,
      keySwitchBGV Dg Cb Pb 3 a bK aK = (Cb.toRNS y0, Cb.toRNS y1) ∧
      ofInt Cb.prod (y0 + y1 * sk) = ofInt Cb.prod (centered (Cb.combine a) * (sk * sk) + e) ∧
      (∀ c, (3 : ℤ) ∣ e.coeff c) ∧ normInf e ≤ 229 := by
  obtain ⟨h1, h2, h3, h4⟩ := example_hyps
  obtain ⟨y0, y1, e, ho, he, hd, hb⟩ := keySwitchBGV_spec Dg Cb Pb h1 h2 sk h3 .square bK aK h4 a
  have : ksBound 4 9 1 3 (1 * Pb.prod) Pb.prod (digitWeight Dg Cb) = 229 := by decide +kernel
  exact ⟨y0, y1, e, ho, he, hd, by rw [this] at hb; exact hb⟩

/-- The input component `d`. -/
def dIn : IntPoly 4 := mkP [123, -321, 222, 7]

/-- The error of one concrete run, computed by the RNS algorithm. -/
def runErr : IntPoly 4 :=
  let out := keySwitchBGV Dg Cb Pb 3 (Cb.toRNS dIn) bK aK
  centered (Cb.combine out.1 + Cb.combine out.2 * ofInt Cb.prod sk -
    ofInt Cb.prod dIn * ofInt Cb.prod (sk * sk))

/-- Kernel-checked run: the algorithm's error on `dIn`. -/
theorem example_run : (runErr.coeff 0, runErr.coeff 1, runErr.coeff 2, runErr.coeff 3) =
    (30, -33, 21, 0) := by
  decide +kernel

/-! ### Two digits, three ciphertext primes -/

/-- Ciphertext basis `(17, 41, 97)`. -/
def C3 : Basis 3 := Basis.ofList [17, 41, 97] (by decide) (by decide)

/-- Digits `{17, 41}` and `{97}`. -/
def D3 : Digits 3 where
  dnum := 2
  size := ![2, 1]
  emb j r := ⟨if j.val = 0 then r.val % 2 else 2, by split <;> omega⟩
  bij := by decide

abbrev M3 : ℕ := C3.prod * Pb.prod

def aK3 (j : Fin D3.dnum) : Poly M3 4 :=
  ofInt M3 (if j.val = 0 then mkP [12345, -7777, 31415, 999] else mkP [-27182, 5555, 4242, -1])

def eK3 (j : Fin D3.dnum) : IntPoly 4 :=
  if j.val = 0 then mkP [3, -6, 0, 9] else mkP [-3, 3, 6, 0]

def bK3 (j : Fin D3.dnum) : Poly M3 4 :=
  -(aK3 j * ofInt M3 sk) + const ((gadget D3 C3 Pb.prod j : ℤ) : ZMod M3) * ofInt M3 (sk * sk) +
    ofInt M3 (eK3 j)

theorem example3_hyps :
    (∀ j, Nat.Coprime 3 (Pb.q j)) ∧ (∀ i, Nat.Coprime Pb.prod (C3.q i)) ∧ normInf sk ≤ 1 ∧
      (∀ j, KeyValid .bgv 3 9 sk (gadgetReq D3 C3 Pb .square j) (bK3 j) (aK3 j)) ∧
      ksBound 4 9 1 3 (1 * Pb.prod) Pb.prod (digitWeight D3 C3) = 245 := by
  unfold KeyValid
  decide +kernel

def dIn3 : IntPoly 4 := mkP [12345, -32100, 2222, 7]

def runErr3 : IntPoly 4 :=
  let out := keySwitchBGV D3 C3 Pb 3 (C3.toRNS dIn3) bK3 aK3
  centered (C3.combine out.1 + C3.combine out.2 * ofInt C3.prod sk -
    ofInt C3.prod dIn3 * ofInt C3.prod (sk * sk))

/-- Kernel-checked two-digit run. -/
theorem example3_run : (runErr3.coeff 0, runErr3.coeff 1, runErr3.coeff 2, runErr3.coeff 3) =
    (-3, 54, -12, 15) := by
  decide +kernel

end FHE.KeySwitch.Example
