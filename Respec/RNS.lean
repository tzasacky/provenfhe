import Respec.Basic

/-!
# Respec.RNS — residue number systems, base conversion, ModDown, hybrid key switching

Sources (primary):
* [BEHZ16] Bajard, Eynard, Hasan, Zucca, *A Full RNS Variant of FV like Somewhat Homomorphic
  Encryption Schemes*, SAC 2016, ePrint 2016/510. §3.1 eq. (2) (fast base conversion), Lemma 2.
* [HPS18] Halevi, Polyakov, Shoup, *An Improved RNS Variant of the BFV Homomorphic Encryption
  Scheme*, CT-RSA 2019, ePrint 2018/117. §2.2 eq. (3) (CRT basis extension with the correction `υ`).
* [CHKKS18] Cheon, Han, Kim, Kim, Song, *A Full RNS Variant of Approximate Homomorphic
  Encryption*, SAC 2018, ePrint 2018/931. §4.1 Alg. 1 (`Conv`), Alg. 2 (`ModUp`), Alg. 3 (`ModDown`).
* [HK19] Han, Ki, *Better Bootstrapping for Approximate Homomorphic Encryption*, CT-RSA 2020,
  ePrint 2019/688. §3.2 (generalized/hybrid key switching, RNS-partition gadget).
* [KPZ21] Kim, Polyakov, Zucca, *Revisiting Homomorphic Encryption Schemes for Finite Fields*,
  ASIACRYPT 2021, ePrint 2021/204. §2.3 / App. B.2.3 (hybrid key switching for BGV, the `t`-corrected
  ModDown).
* OpenFHE v1.2.3: `src/core/include/lattice/hal/default/dcrtpoly-impl.h`
  (`ApproxSwitchCRTBasis` l.910-948, `ApproxModUp` l.951-979, `ApproxModDown` l.982-1021,
  `SwitchCRTBasis` l.1024-1101, `ModReduce` l.758-777, `DropLastElementAndScale` l.715-734) and
  `src/pke/lib/keyswitch/keyswitch-hybrid.cpp` (`KeySwitchGenInternal` l.53-134,
  `EvalKeySwitchPrecomputeCore` l.329-413, `EvalFastKeySwitchCoreExt` l.439-481,
  `EvalFastKeySwitchCore` l.415-437).

## Variants recorded

* **Representative used inside fast base conversion.** BEHZ16 eq. (2) and CHKKS18 Alg. 1 use the
  canonical representative `[0, q_i)` of `y_i = [x_i·(Q/q_i)⁻¹]_{q_i}`, so the integer computed is
  `x + α·Q` with `0 ≤ α ≤ k-1`. HPS18 uses `[-q_i/2, q_i/2)` and gets `|α| ≤ k/2`. OpenFHE's
  `ApproxSwitchCRTBasis` uses the **canonical** representative on the 128-bit code path
  (l.917-936) and the **centred** one (`SwitchModulus`) on the fallback path (l.938-945): the same
  function returns different (both valid) results depending on the build. `Lift` selects.
* **Exact vs approximate.** HPS18 eq. (3) subtracts `υ·Q`, `υ = ⌈Σ y_i/q_i⌋`, and returns the
  *centred* representative of `x` exactly (`exactBConvZ`); OpenFHE `SwitchCRTBasis` l.1072-1081
  computes `υ` in `double`. We formalize the exact rational value; the floating-point
  approximation is outside this specification.
-/

namespace Respec

open Spec

/-- A family of `k` moduli. Source: BEHZ16 §2 ("base `q = {q_1,…,q_k}`"). -/
abbrev Basis (k : ℕ) := Fin k → ℕ

namespace Basis
variable {k : ℕ}

/-- `Q = ∏ q_i`. -/
def prod (q : Basis k) : ℕ := ∏ i, q i

/-- Product of the sub-basis selected by `mask`. -/
def prodM (q : Basis k) (mask : Fin k → Bool) : ℕ := ∏ j, if mask j then q j else 1

/-- `Q_M / q_i`: product of the masked sub-basis without `q_i` (BEHZ16: `q/q_i`; HPS18: `q_i^*`;
OpenFHE: `QHat`). -/
def hatM (q : Basis k) (mask : Fin k → Bool) (i : Fin k) : ℕ :=
  ∏ j, if mask j = true ∧ j ≠ i then q j else 1

/-- The mask selecting the whole basis. -/
def all : Fin k → Bool := fun _ => true

/-- `Q / q_i`. -/
def hat (q : Basis k) (i : Fin k) : ℕ := q.hatM all i

/-- A CRT basis: moduli `> 1`, pairwise coprime. Source: BEHZ16 §2; HPS18 §2.2. -/
def IsCRT (q : Basis k) : Prop := (∀ i, 1 < q i) ∧ ∀ i j, i ≠ j → Nat.Coprime (q i) (q j)

instance (q : Basis k) : Decidable q.IsCRT := by unfold IsCRT; infer_instance

/-- Two bases are jointly a CRT basis. -/
def Coprime {l : ℕ} (q : Basis k) (p : Basis l) : Prop := ∀ i j, Nat.Coprime (q i) (p j)

instance {l : ℕ} (q : Basis k) (p : Basis l) : Decidable (q.Coprime p) := by
  unfold Coprime; infer_instance

/-- Drop the last modulus. -/
abbrev init (q : Basis (k + 1)) : Basis k := fun i => q i.castSucc

/-- The last modulus. -/
abbrev last (q : Basis (k + 1)) : ℕ := q (Fin.last k)

/-- Keep the first `k'` moduli (a lower level of the same chain). -/
abbrev take {k' : ℕ} (q : Basis k) (h : k' ≤ k) : Basis k' := fun i => q (Fin.castLE h i)

end Basis

/-- A residue vector `(x mod q_i)_i`. -/
abbrev Residues {k : ℕ} (q : Basis k) := (i : Fin k) → ZMod (q i)

section Scalar
variable {k : ℕ}

/-- Residues of an integer. -/
def toRes (q : Basis k) (x : ℤ) : Residues q := fun i => (x : ZMod (q i))

/-- `y_i = [x_i · (Q_M/q_i)⁻¹]_{q_i}`. Source: BEHZ16 eq. (2) (`|x_i·(q/q_i)⁻¹|_{q_i}`);
OpenFHE dcrtpoly-impl.h:927 (`xQHatInvModqi`). -/
def bconvY (q : Basis k) (mask : Fin k → Bool) (x : Residues q) (i : Fin k) : ZMod (q i) :=
  x i * ((q.hatM mask i : ℕ) : ZMod (q i))⁻¹

/-- **Fast base conversion, integer value.**
`FastBconv(x, Q_M) = Σ_{i∈M} [x_i·(Q_M/q_i)⁻¹]_{q_i} · (Q_M/q_i)` computed in `ℤ` with the chosen
representative of each `y_i`. The residue of this integer modulo any `m` is the output of the
conversion to `m`.
Source: BEHZ16 §3.1 eq. (2); CHKKS18 Alg. 1 (`Conv_{C→B}`); OpenFHE `ApproxSwitchCRTBasis`
dcrtpoly-impl.h:910-948 (canonical on l.917-936, centred on l.938-945). -/
def fastBConvZ (c : Lift) (q : Basis k) (mask : Fin k → Bool) (x : Residues q) : ℤ :=
  ∑ i, if mask i then c.rep (bconvY q mask x i) * (q.hatM mask i : ℤ) else 0

/-- Fast base conversion to a target modulus `m`. -/
def fastBConv (c : Lift) (q : Basis k) (mask : Fin k → Bool) (x : Residues q) (m : ℕ) : ZMod m :=
  ((fastBConvZ c q mask x : ℤ) : ZMod m)

/-- **The overflow of fast base conversion** (the number `α` with `FastBconv = [x]_Q + α·Q`).
For the canonical convention `α = ⌊Σ y_i/q_i⌋ ∈ [0, k-1]` (BEHZ16 Lemma 2 / the remark after
eq. (2): "`x + α_x·q` with `0 ≤ α_x ≤ k-1`"); for the centred convention the value lies in
`[-kQ/2, kQ/2]`. -/
def fastBConvOverflow (c : Lift) (q : Basis k) (x : ℤ) : ℤ :=
  let v := fastBConvZ c q Basis.all (toRes q x)
  match c with
  | .canonical => (v - nmod x q.prod) / (q.prod : ℤ)
  | .centred => (v - cmod x q.prod) / (q.prod : ℤ)

/-- **Exact statement of the fast-base-conversion overflow** for an integer `x` and a CRT basis
`q` of size `k` with product `Q` (decidable; checked exhaustively at small parameters below).

* canonical: `FastBconv(x) = (x mod Q) + α·Q` with `0 ≤ α ≤ k-1`  (BEHZ16 §3.1);
* centred:  `FastBconv(x) ≡ x (mod Q)` and `2·|FastBconv(x)| ≤ k·Q`   (HPS18 §2.2). -/
def FastBConvSpec (c : Lift) (q : Basis k) (x : ℤ) : Prop :=
  let v := fastBConvZ c q Basis.all (toRes q x)
  match c with
  | .canonical => ∃ α : Fin k, v = nmod x q.prod + (α.val : ℤ) * q.prod
  | .centred => (q.prod : ℤ) ∣ (v - x) ∧ 2 * v.natAbs ≤ k * q.prod

instance (c : Lift) (q : Basis k) (x : ℤ) : Decidable (FastBConvSpec c q x) := by
  unfold FastBConvSpec; cases c <;> simp only <;> infer_instance

/-- **HPS exact CRT basis extension, integer value**: `Σ y_i·(Q/q_i) − υ·Q` with
`υ = ⌈Σ_i y_i/q_i⌋` (`y_i` canonical). Since `Σ y_i/q_i = FastBconv/Q` exactly, `υ = ⌈FastBconv/Q⌋`.
The result is the representative of `x` in `[-Q/2, Q/2)`.
Source: HPS18 §2.2 eq. (3); OpenFHE `SwitchCRTBasis` dcrtpoly-impl.h:1071-1099 (which evaluates
`υ` in floating point: `nu = 0.5 + Σ y_i·(1/q_i)`, `alpha = ⌊nu⌋`). -/
def exactBConvZ (q : Basis k) (mask : Fin k → Bool) (x : Residues q) : ℤ :=
  let v := fastBConvZ .canonical q mask x
  v - rdiv v (q.prodM mask) * (q.prodM mask : ℤ)

/-- Exact base extension to a target modulus. -/
def exactBConv (q : Basis k) (mask : Fin k → Bool) (x : Residues q) (m : ℕ) : ZMod m :=
  ((exactBConvZ q mask x : ℤ) : ZMod m)

/-- CRT reconstruction to `ℤ_Q`. Source: OpenFHE `CRTInterpolate` dcrtpoly-impl.h:779-787
("`V[j] = Σ M(i,j)·(Q/q_i)·[(Q/q_i)⁻¹ mod q_i] mod Q`"). -/
def crt (q : Basis k) (x : Residues q) : ZMod q.prod :=
  ((fastBConvZ .canonical q Basis.all x : ℤ) : ZMod q.prod)

/-- **ModDown on integers (plain)**: `(X − FastBconv_{P→·}([X]_P)) / P`. The division is exact.
With `δ = FastBconv([X]_P) = [X]_P + α·P` the result is `⌊X/P⌋ − α` (canonical) or
`⌊X/P⌉ − α` up to the tie (centred).
Source: CHKKS18 Alg. 3 (`ModDown`); OpenFHE `ApproxModDown` dcrtpoly-impl.h:982-1021 with `t = 0`. -/
def modDownZ {l : ℕ} (c : Lift) (p : Basis l) (X : ℤ) : ℤ :=
  (X - fastBConvZ c p Basis.all (toRes p X)) / (p.prod : ℤ)

/-- **ModDown on integers, BGV `t`-corrected**: `(X − t·FastBconv_{P→·}([X·t⁻¹]_P)) / P`.
The subtracted integer `δ = t·FastBconv([t⁻¹X]_P)` satisfies `δ ≡ X (mod P)` and `δ ≡ 0 (mod t)`,
so the division is exact and `P·result ≡ X (mod t)`.
Source: KPZ21 App. B.2.3; GHS12 (ePrint 2012/099) §3.1-3.2 (the `δ ≡ 0 mod t` trick);
OpenFHE `ApproxModDown` dcrtpoly-impl.h:997-1000 (`partP *= tInvModp`) and l.1014-1018
(`ans = (Q-part − t·partPSwitchedToQ)·PInvModq`). Note the source comment on l.997 says
"`-t^(-1)`" but the code multiplies by `+t⁻¹` and subtracts. -/
def modDownBGVZ {l : ℕ} (c : Lift) (t : ℕ) (p : Basis l) (X : ℤ) : ℤ :=
  let xP : Residues p := fun i => (X : ZMod (p i)) * ((t : ℕ) : ZMod (p i))⁻¹
  (X - (t : ℤ) * fastBConvZ c p Basis.all xP) / (p.prod : ℤ)

end Scalar

/-! ## Polynomials in RNS form -/

/-- A polynomial in RNS ("double-CRT minus NTT") form: one limb per modulus. Source: GHS12 §2.1
(double-CRT); OpenFHE `DCRTPoly`. No NTT is modelled: limbs are in coefficient form.
(A structure rather than a bare function so that compiled code evaluates it once; see
`Respec.Table`.) -/
@[ext]
structure RnsPoly {k : ℕ} (q : Basis k) (N : ℕ) where
  /-- limb `i`, a polynomial modulo `q_i` -/
  limb : (i : Fin k) → Poly (q i) N

instance {k : ℕ} (q : Basis k) (N : ℕ) : CoeFun (RnsPoly q N) fun _ => (i : Fin k) → Poly (q i) N :=
  ⟨RnsPoly.limb⟩

instance {k : ℕ} (q : Basis k) (N : ℕ) : DecidableEq (RnsPoly q N) := fun a b =>
  decidable_of_iff (a.limb = b.limb) ⟨fun h => RnsPoly.ext h, fun h => h ▸ rfl⟩

instance {k : ℕ} (q : Basis k) (N : ℕ) : Inhabited (RnsPoly q N) := ⟨⟨fun _ => 0⟩⟩

section RnsPoly
variable {k l N : ℕ}

/-- The residue vector of coefficient `j`. -/
def RnsPoly.res {q : Basis k} (x : RnsPoly q N) (j : Fin N) : Residues q := fun i => (x i).coeff j

/-- The coefficients of one limb as integers. -/
def limbArr {m : ℕ} (a : Poly m N) : Array ℤ := Array.ofFn fun j : Fin N => ((a.coeff j).cast : ℤ)

/-- All coefficients of an RNS polynomial as a `k × N` array of integers (plain data, hence
evaluated when computed). -/
def rarr {q : Basis k} (x : RnsPoly q N) : Array (Array ℤ) := Array.ofFn fun i : Fin k => limbArr (x i)

/-- Read an RNS polynomial back from a `k × N` array of integers. -/
def rofArr {q : Basis k} (arr : Array (Array ℤ)) : RnsPoly q N :=
  ⟨fun i => ⟨fun j => ((((arr[i.val]?).getD #[])[j.val]?).getD 0 : ℤ)⟩⟩

@[simp] theorem rofArr_rarr {q : Basis k} (x : RnsPoly q N) : rofArr (rarr x) = x := by
  ext i j; simp [rofArr, rarr, limbArr]

/-- Build an RNS polynomial from its limbs, storing the coefficients in an array
(`rmk f = ⟨f⟩`, see `rmk_eq`). -/
def rmk {q : Basis k} (f : (i : Fin k) → Poly (q i) N) : RnsPoly q N :=
  rofArr (Array.ofFn fun i : Fin k => limbArr (f i))

@[simp] theorem rmk_eq {q : Basis k} (f : (i : Fin k) → Poly (q i) N) : rmk f = ⟨f⟩ := by
  ext i j; simp [rmk, rofArr, limbArr]

/-- Tabulate a finite family of RNS polynomials as plain data. (A table whose entries are
themselves closures would not be evaluated: the compiler turns `fun j => f j` with a
function-valued body into a function of more arguments. See `Respec.Table`.) -/
def rtable {d : ℕ} {q : Basis k} (f : Fin d → RnsPoly q N) : Table d (Array (Array ℤ)) :=
  Table.ofFn fun j => rarr (f j)

/-- Read an entry of an `rtable`. -/
def rtableGet {d : ℕ} {q : Basis k} (t : Table d (Array (Array ℤ))) (j : Fin d) : RnsPoly q N :=
  rofArr (t.get j)

@[simp] theorem rtableGet_rtable {d : ℕ} {q : Basis k} (f : Fin d → RnsPoly q N) (j : Fin d) :
    rtableGet (rtable f) j = f j := by
  simp [rtableGet, rtable]

/-- Memoize all limbs (the identity; see `rforce_eq`). -/
def rforce {q : Basis k} (x : RnsPoly q N) : RnsPoly q N := rmk x.limb

@[simp] theorem rforce_eq {q : Basis k} (x : RnsPoly q N) : rforce x = x := by
  simp [rforce]

/-- RNS form of an integer polynomial. -/
def toRns (q : Basis k) (a : IntPoly N) : RnsPoly q N := rmk fun i => NPoly.ofInt (q i) a

/-- RNS form of a polynomial modulo a multiple `M` of every `q_i` (canonical lift, then reduce). -/
def castRns {M : ℕ} (q : Basis k) (a : Poly M N) : RnsPoly q N := toRns q (liftN a)

/-- CRT reconstruction, coefficient-wise. -/
def ofRns (q : Basis k) (x : RnsPoly q N) : Poly q.prod N := force ⟨fun j => crt q (x.res j)⟩

/-- Limb-wise sum (strict). -/
def radd {q : Basis k} (x y : RnsPoly q N) : RnsPoly q N := rmk fun i => x i + y i

/-- Limb-wise product (strict). -/
def rmul {q : Basis k} (x y : RnsPoly q N) : RnsPoly q N := rmk fun i => x i * y i

/-- Integer scalar times RNS polynomial (strict). -/
def rsmul {q : Basis k} (c : ℤ) (x : RnsPoly q N) : RnsPoly q N :=
  rmk fun i => (c : ZMod (q i)) • x i

/-- Limb-wise Galois automorphism (strict). -/
def rautomorph {q : Basis k} (g : ℕ) (x : RnsPoly q N) : RnsPoly q N :=
  rmk fun i => NPoly.automorph g (x i)

@[simp] theorem radd_eq {q : Basis k} (x y : RnsPoly q N) : radd x y = ⟨fun i => x i + y i⟩ :=
  rmk_eq _
@[simp] theorem rmul_eq {q : Basis k} (x y : RnsPoly q N) : rmul x y = ⟨fun i => x i * y i⟩ :=
  rmk_eq _

/-- Fast base conversion of a polynomial to one target modulus. -/
def bconv (c : Lift) (q : Basis k) (mask : Fin k → Bool) (x : RnsPoly q N) (m : ℕ) : Poly m N :=
  force ⟨fun j => fastBConv c q mask (x.res j) m⟩

/-- Fast base conversion of a polynomial to a target basis.
Source: BEHZ16 eq. (2); CHKKS18 Alg. 1; OpenFHE `ApproxSwitchCRTBasis`. -/
def bconvBasis (c : Lift) (q : Basis k) (p : Basis l) (x : RnsPoly q N) : RnsPoly p N :=
  rmk fun i => bconv c q Basis.all x (p i)

/-- Exact (HPS) base extension of a polynomial to a target basis. Source: HPS18 eq. (3). -/
def exactBConvBasis (q : Basis k) (p : Basis l) (x : RnsPoly q N) : RnsPoly p N :=
  rmk fun i => ⟨fun j => exactBConv q Basis.all (x.res j) (p i)⟩

/-- **ModDown (plain)** on limbs: given `X` in basis `Q ∪ P` return
`(X_Q − FastBconv_{P→Q}(X_P))·P⁻¹` in basis `Q`.
Source: CHKKS18 Alg. 3; OpenFHE `ApproxModDown` (dcrtpoly-impl.h:982-1021) with `t = 0`. -/
def modDown (c : Lift) (q : Basis k) (p : Basis l) (xQ : RnsPoly q N) (xP : RnsPoly p N) :
    RnsPoly q N :=
  rmk fun i => ((p.prod : ℕ) : ZMod (q i))⁻¹ ⊡ (xQ i ⊟ bconv c p Basis.all xP (q i))

/-- Multiply every `P`-limb by `t⁻¹ mod p_i` (first step of the BGV ModDown,
OpenFHE dcrtpoly-impl.h:997-1000). -/
def rscaleTInv (t : ℕ) {p : Basis l} (xP : RnsPoly p N) : RnsPoly p N :=
  rmk fun i => ((t : ℕ) : ZMod (p i))⁻¹ • xP i

/-- Second step of the BGV ModDown: `(X_Q − t·FastBconv_{P→Q}(Y_P))·P⁻¹` for an already
`t⁻¹`-scaled `Y_P` (OpenFHE dcrtpoly-impl.h:1003-1019). -/
def modDownBGVCore (c : Lift) (t : ℕ) (q : Basis k) (p : Basis l) (xQ : RnsPoly q N)
    (yP : RnsPoly p N) : RnsPoly q N :=
  rmk fun i => ((p.prod : ℕ) : ZMod (q i))⁻¹ ⊡
    (xQ i ⊟ ((t : ℕ) : ZMod (q i)) ⊡ bconv c p Basis.all yP (q i))

/-- **ModDown, BGV `t`-corrected** on limbs:
`(X_Q − t·FastBconv_{P→Q}([t⁻¹·X_P]_P))·P⁻¹`.
Source: OpenFHE `ApproxModDown` dcrtpoly-impl.h:993-1019 with `t > 0`; KPZ21 App. B.2.3. -/
def modDownBGV (c : Lift) (t : ℕ) (q : Basis k) (p : Basis l) (xQ : RnsPoly q N)
    (xP : RnsPoly p N) : RnsPoly q N :=
  modDownBGVCore c t q p xQ (rscaleTInv t xP)

/-- ModDown with an optional plaintext modulus (`none` = BFV, `some t` = BGV), exactly the
`t == 0 ? … : …` switch of OpenFHE keyswitch-hybrid.cpp:422. -/
def modDownOpt (c : Lift) (t : Option ℕ) (q : Basis k) (p : Basis l) (xQ : RnsPoly q N)
    (xP : RnsPoly p N) : RnsPoly q N :=
  match t with
  | none => modDown c q p xQ xP
  | some t => modDownBGV c t q p xQ xP

/-! ### Dropping the last limb: BGV modulus switching and the BFV level drop in RNS -/

/-- Move a polynomial modulo `q_l` to another modulus through the chosen lift. -/
def switchMod (c : Lift) {q : ℕ} (q' : ℕ) (a : Poly q N) : Poly q' N :=
  force ⟨fun i => ((c.rep (a.coeff i) : ℤ) : ZMod q')⟩

/-- Second step of the BGV modulus switch: `c'_i = (c_i + t·[δ']_{→q_i})·q_l⁻¹`. -/
def modSwitchBGVCore (c : Lift) (t : ℕ) (q : Basis (k + 1)) (x : RnsPoly q N)
    (δ' : Poly q.last N) : RnsPoly q.init N :=
  rmk fun i => ((q.last : ℕ) : ZMod (q.init i))⁻¹ ⊡
    (x i.castSucc ⊞ ((t : ℕ) : ZMod (q.init i)) ⊡ switchMod c (q.init i) δ')

/-- **BGV modulus switching on limbs** (drop the last prime `q_l`):
`δ' = [−c_l·t⁻¹]_{q_l}` (a polynomial mod `q_l`, lifted by `c`), and for each remaining limb
`c'_i = (c_i + t·δ')·q_l⁻¹ mod q_i`.
Source: OpenFHE `DCRTPolyImpl::ModReduce` dcrtpoly-impl.h:758-777 (`delta *= negtInvModq`,
`SwitchModulus` (centred), `m_vectors[i] += tmp*t`, `m_vectors[i] *= qlInvModq[i]`); GHS12 §3.2.
OpenFHE uses `Lift.centred`. -/
def modSwitchBGVRns (c : Lift) (t : ℕ) (q : Basis (k + 1)) (x : RnsPoly q N) : RnsPoly q.init N :=
  modSwitchBGVCore c t q x ((-((t : ℕ) : ZMod q.last)⁻¹) ⊡ x (Fin.last k))

/-- **RNS rescaling / divide-and-round by the last prime** (BFV level drop):
`c'_i = (c_i − [c_l]_{→q_i})·q_l⁻¹ mod q_i`. With the centred lift this is `⌊c/q_l⌉`, with the
canonical lift it is `⌊c/q_l⌋`.
Source: CHKKS18 §4.3 (`RS`: `q_l⁻¹·(c^{(j)} − c^{(l)})`, written with residues in `[0,q)`, i.e.
flooring); OpenFHE `DropLastElementAndScale` dcrtpoly-impl.h:715-734 (centred `SwitchModulus`,
i.e. rounding); SEAL `RNSTool::divide_and_round_q_last_inplace` util/rns.cpp:808-811 ("Add
(qi-1)/2 to change from flooring to rounding"). -/
def rescaleRns (c : Lift) (q : Basis (k + 1)) (x : RnsPoly q N) : RnsPoly q.init N :=
  rmk fun i => ((q.last : ℕ) : ZMod (q.init i))⁻¹ ⊡
    (x i.castSucc ⊟ switchMod c (q.init i) (x (Fin.last k)))

end RnsPoly

/-! ## Hybrid key switching on RNS limbs -/

section Hybrid
variable {k l d N : ℕ}

/-- A hybrid key-switching key in RNS form: `d` digits, each a pair `(b_j, a_j)` over `Q ∪ P`.
Source: OpenFHE `EvalKeyRelinImpl` with `BVector`/`AVector` (keyswitch-hybrid.cpp:96-131);
HK19 §3.2 (`swk = (D_j)`); Lattigo `rlwe.GadgetCiphertext`. -/
structure HybridKey (q : Basis k) (p : Basis l) (d N : ℕ) where
  /-- `b_j` on the `Q` limbs -/
  bQ : Fin d → RnsPoly q N
  /-- `b_j` on the `P` limbs -/
  bP : Fin d → RnsPoly p N
  /-- `a_j` on the `Q` limbs -/
  aQ : Fin d → RnsPoly q N
  /-- `a_j` on the `P` limbs -/
  aP : Fin d → RnsPoly p N

/-- The limbs of digit `j` under a digit assignment `dig : limb ↦ digit`. OpenFHE uses consecutive
blocks of `α = ⌈(L+1)/dnum⌉` limbs: `dig i = ⌊i/α⌋` (rns-cryptoparameters.cpp:77-86,
keyswitch-hybrid.cpp:108-109). -/
def digitMask (dig : Fin k → Fin d) (j : Fin d) : Fin k → Bool := fun i => dig i = j

/-- OpenFHE's block partition: `α` limbs per digit. -/
def blockDigits (α : ℕ) (h : k ≤ α * d) : Fin k → Fin d := fun i =>
  ⟨i.val / α, by
    have := i.isLt
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le this h)⟩

/-- **Hybrid key generation, OpenFHE form.** Switching key *from* `sFrom` *to* `sTo`:
for each digit `j` and each limb,

  `b_j = −a_j·sTo + ns·e_j + [limb ∈ digit j]·(P mod q_i)·sFrom`,

with `ns = t` for BGV and `ns = 1` for BFV, and no `P·sFrom` term on the `P` limbs.
In `ℤ_{QP}` this says `b_j + a_j·sTo = ns·e_j + P·ε_j·sFrom` where
`ε_j = (Q/Q_j)·[(Q/Q_j)⁻¹]_{Q_j}` is the CRT idempotent of digit `j`.
Source: OpenFHE keyswitch-hybrid.cpp:103-127 (`b = -a*sNew + PModq[i]*sOld + ns*e` on the
digit's limbs, `b = -a*sNew + ns*e` elsewhere). OpenFHE's `oldKey` is our `sFrom`.
SEAL (`KeyGenerator::generate_one_kswitch_key`, keygenerator.cpp:319-333) uses the same gadget
with one limb per digit and one special prime, but with the *opposite sign on the error*:
`(−(a·s + t·e) + P·ε_j·s', a)`. HK19 §3.2 instead puts `P·(Q/Q_j)` in the key and
`[(Q/Q_j)⁻¹]_{Q_j}` in the decomposition (see `Respec.BGV.gadgetHK`). -/
def hybridKeyGen (ns : ℕ) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d)
    (sFrom sTo : IntPoly N) (a e : Fin d → IntPoly N) : HybridKey q p d N where
  aQ := rtableGet (rtable fun j => toRns q (a j))
  aP := rtableGet (rtable fun j => toRns p (a j))
  bQ := rtableGet (rtable fun j => rmk fun i =>
    (pneg (red (q i) (a j) ⊠ red (q i) sTo) ⊞ ((ns : ℕ) : ZMod (q i)) ⊡ red (q i) (e j))
      ⊞ (if dig i = j then ((p.prod : ℕ) : ZMod (q i)) ⊡ red (q i) sFrom else 0))
  bP := rtableGet (rtable fun j => rmk fun i =>
    pneg (red (p i) (a j) ⊠ red (p i) sTo) ⊞ ((ns : ℕ) : ZMod (p i)) ⊡ red (p i) (e j))

/-- Restrict a key to a lower level by **dropping limbs** (nothing is recomputed). This works for
the OpenFHE/SEAL/Lattigo gadget because the idempotent `ε_j mod Q_ℓ` is again the idempotent of
the truncated digit. It does *not* work for the HK19 gadget `P·(Q/Q_j)` with a decomposition
constant `[(Q/Q_j)⁻¹]_{Q_j}` fixed at the top level.
Source: OpenFHE keyswitch-hybrid.cpp:461-476 (indexes the key limbs `i < sizeQl` and
`idx = sizeQ + …` for the `P` limbs). -/
def HybridKey.restrict {q : Basis k} {p : Basis l} {k' : ℕ} (h : k' ≤ k)
    (key : HybridKey q p d N) : HybridKey (q.take h) p d N where
  bQ j := ⟨fun i => key.bQ j (Fin.castLE h i)⟩
  bP := key.bP
  aQ j := ⟨fun i => key.aQ j (Fin.castLE h i)⟩
  aP := key.aP

/-- **ModUp of digit `j`**: keep the digit's own limbs, and fill every other limb of `Q ∪ P` with
the fast base conversion from the digit's sub-basis `Q_j`. The integer represented is
`d̃_j = [c]_{Q_j} + α_j·Q_j`.
Source: OpenFHE `EvalKeySwitchPrecomputeCore` keyswitch-hybrid.cpp:383-410 (the decomposition is
*just* "take the limbs of the part", l.375-377, with no multiplication by `(Q/Q_j)⁻¹`);
CHKKS18 Alg. 2 (`ModUp`); HK19 §3.2. -/
def modUp (c : Lift) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d) (j : Fin d)
    (x : RnsPoly q N) : RnsPoly q N × RnsPoly p N :=
  (rmk fun i => if dig i = j then x i else bconv c q (digitMask dig j) x (q i),
   rmk fun i => bconv c q (digitMask dig j) x (p i))

/-- `Σ_j d_j·k_j` limb-wise, for already computed digit extensions. -/
def rdot {m : ℕ} {q : Basis m} (ds : Fin d → RnsPoly q N) (ks : Fin d → RnsPoly q N) :
    RnsPoly q N :=
  rmk fun i => psum ((List.finRange d).map fun j => ds j i ⊠ ks j i)

/-- The inner product for given (memoized) digit extensions. -/
def hybridInnerCore {q : Basis k} {p : Basis l} (key : HybridKey q p d N)
    (dQ : Fin d → RnsPoly q N) (dP : Fin d → RnsPoly p N) :
    (RnsPoly q N × RnsPoly p N) × (RnsPoly q N × RnsPoly p N) :=
  ((rdot dQ key.bQ, rdot dP key.bP), (rdot dQ key.aQ, rdot dP key.aP))

/-- The inner product `Σ_j d̃_j·(b_j, a_j)` in basis `Q ∪ P` (before ModDown).
Source: OpenFHE `EvalFastKeySwitchCoreExt` keyswitch-hybrid.cpp:439-481. -/
def hybridInner (c : Lift) (q : Basis k) (p : Basis l) (dig : Fin k → Fin d)
    (key : HybridKey q p d N) (x : RnsPoly q N) :
    (RnsPoly q N × RnsPoly p N) × (RnsPoly q N × RnsPoly p N) :=
  hybridInnerCore key (rtableGet (rtable fun j => (modUp c q p dig j x).1))
    (rtableGet (rtable fun j => (modUp c q p dig j x).2))

/-- **The hybrid key-switching algorithm on RNS limbs.** Input: one ring element `x` in basis `Q`
(the ciphertext component multiplying `sFrom`) and a key from `sFrom` to `sTo`. Output
`(k₀, k₁)` in basis `Q` with

  `k₀ + k₁·sTo ≡ x·sFrom + E (mod Q)`,  `E` small (and `E ≡ 0 mod t` when `tcorr = some t`).

Steps: (1) split `x` into digits (the limbs of each part); (2) ModUp each digit to `Q ∪ P`;
(3) inner product with the key; (4) ModDown by `P` (BGV-corrected if `tcorr = some t`).
Source: OpenFHE `KeySwitchHYBRID::KeySwitchCore` keyswitch-hybrid.cpp:323-327, composed of
`EvalKeySwitchPrecomputeCore` (l.329-413), `EvalFastKeySwitchCoreExt` (l.439-481) and the two
`ApproxModDown` calls (l.424-434); HK19 §3.2; KPZ21 App. B.2.3. -/
def hybridKeySwitch (c : Lift) (tcorr : Option ℕ) (q : Basis k) (p : Basis l)
    (dig : Fin k → Fin d) (key : HybridKey q p d N) (x : RnsPoly q N) :
    RnsPoly q N × RnsPoly q N :=
  match hybridInner c q p dig key x with
  | ((x0Q, x0P), (x1Q, x1P)) => (modDownOpt c tcorr q p x0Q x0P, modDownOpt c tcorr q p x1Q x1P)

/-- The integer represented by the ModUp of digit `j`, coefficient-wise: `[x]_{Q_j} + α_j·Q_j`.
(Used to state noise bounds.) -/
def modUpZ (c : Lift) (q : Basis k) (dig : Fin k → Fin d) (j : Fin d) (x : RnsPoly q N) :
    IntPoly N :=
  force ⟨fun n => fastBConvZ c q (digitMask dig j) (x.res n)⟩

end Hybrid

/-! ## Sanity tests (tiny parameters) -/

section Tests

/-- Test basis `Q = 97·113·193`. -/
def tq : Basis 3 := ![97, 113, 193]
/-- Test special basis `P = 257·337`. -/
def tp : Basis 2 := ![257, 337]

#guard tq.IsCRT ∧ tp.IsCRT ∧ tq.Coprime tp
#guard tq.prod = 2115473 ∧ tp.prod = 86609 ∧ tq.hat 0 = 113 * 193

-- CRT round trip on a sample of integers.
#guard (List.range 200).all fun n =>
  let x : ℤ := 10007 * n + 3
  (crt tq (toRes tq x)).val = (x % tq.prod).toNat

-- Fast base conversion overflow, exhaustively on a small basis (Q = 3·5·7 = 105) ...
#guard (List.range 105).all fun x => FastBConvSpec .canonical (![3, 5, 7] : Basis 3) x
#guard (List.range 105).all fun x => FastBConvSpec .centred (![3, 5, 7] : Basis 3) x
-- ... the canonical overflow really takes every value 0..k-1 = 0,1,2:
#guard ((List.range 105).map fun x => fastBConvOverflow .canonical (![3, 5, 7] : Basis 3) x).dedup.mergeSort
  = [0, 1, 2]
-- ... and the centred overflow takes negative values too:
#guard ((List.range 105).map fun x => fastBConvOverflow .centred (![3, 5, 7] : Basis 3) x).dedup.mergeSort
  = [-1, 0, 1]
-- and on a sample for the test basis.
#guard (List.range 300).all fun n => FastBConvSpec .canonical tq (7001 * n) ∧
  FastBConvSpec .centred tq (7001 * n)

-- HPS exact extension returns the representative in [-Q/2, Q/2), exhaustively for Q = 105.
#guard (List.range 105).all fun x =>
  exactBConvZ (![3, 5, 7] : Basis 3) Basis.all (toRes _ x) = (if 2 * x ≥ 105 then (x : ℤ) - 105 else x)

-- ModDown on integers: exact division, result within the stated distance of X/P.
#guard (List.range 300).all fun n =>
  let X : ℤ := 104729 * n - 9000000
  let P : ℤ := tp.prod
  let r := modDownZ .canonical tp X
  let rc := modDownZ .centred tp X
  -- canonical: r = ⌊X/P⌋ − α with 0 ≤ α ≤ 1 ;  centred: |rc·P − X| ≤ 2·P/2
  (r = X / P ∨ r = X / P - 1) ∧ (rc * P - X).natAbs ≤ P.natAbs
-- BGV ModDown: P·result ≡ X (mod t) and |P·result − X| ≤ t·(l·P/2) (centred), t = 5.
#guard (List.range 300).all fun n =>
  let X : ℤ := 104729 * n - 9000000
  let P : ℤ := tp.prod
  let r := modDownBGVZ .centred 5 tp X
  (r * P - X) % 5 = 0 ∧ (r * P - X).natAbs ≤ 5 * P.natAbs

-- ModDown on limbs agrees with ModDown on integers.
#guard
  let X : IntPoly 4 := zpoly [123456789012, -98765432101, 5, -77777777777]
  (modDown .centred tq tp (toRns tq X) (toRns tp X) = toRns tq ⟨fun i => modDownZ .centred tp (X.coeff i)⟩)
  ∧ (modDown .canonical tq tp (toRns tq X) (toRns tp X)
      = toRns tq ⟨fun i => modDownZ .canonical tp (X.coeff i)⟩)
  ∧ (modDownBGV .centred 5 tq tp (toRns tq X) (toRns tp X)
      = toRns tq ⟨fun i => modDownBGVZ .centred 5 tp (X.coeff i)⟩)

end Tests

end Respec
