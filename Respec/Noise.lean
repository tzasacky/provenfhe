import Respec.BGV

/-!
# Respec.Noise — worst-case noise rules for BGV

## Conventions (stated once, used in every rule)

* The **noise of a ciphertext** is `‖v‖∞` where `v = [⟨ct,(1,s,s²,…)⟩]_Q` is the *centred*
  critical quantity (`Respec.BGV.crit`), an integer polynomial, and `‖·‖∞` is the largest absolute
  value of a coefficient (coefficient embedding, *not* the canonical embedding used by
  GHS12 App. D / HElib / Costache–Smart; the two differ by the ring constant `c_m` and by
  `√N`-type factors, and a formalization must not mix them).
* **Ring expansion factor**: in `ℤ[X]/(X^N+1)`, `‖a·b‖∞ ≤ N·‖a‖∞·‖b‖∞` (`δ_R = N`; FV12 §2;
  KPZ21 §2.1). Sharper: `‖a·b‖∞ ≤ ‖a‖₁·‖b‖∞`.
* **Worst case**, not average case: an error polynomial is bounded by `B_e` (e.g. `6σ`, or the
  tail-cut of the sampler), the secret by `B_s` (1 for ternary), the encryption randomness by
  `B_u`. KPZ21 and OpenFHE's parameter generation use *average-case* (CLT, `√N`-type) estimates
  instead; those are not theorems.
* **Representatives**: every fast base conversion inside key switching and every lift inside
  modulus switching is parametrised by `Lift`. Centred lifts give the constants `1/2`; canonical
  lifts give `1` (twice as large). OpenFHE's 128-bit path of `ApproxSwitchCRTBasis` is canonical,
  its `ModReduce` is centred.
* Every rule has a **no-wrap side condition** `2·B_out < Q`: the rule describes integer identities
  that hold only while the right-hand side stays inside `(-Q/2, Q/2)`.

Sources: GHS12 App. D; KPZ21 §4 and App. B (BGV noise, hybrid key switching); HK19 §3.2 Lemma 3
(hybrid key-switching error); BGV12 Lemmas 4-8; own derivations where indicated.
-/

namespace Respec.Noise

open Spec Respec Respec.BGV

variable {N : ℕ}

/-- Worst-case size of a lifted plaintext coefficient: `⌊t/2⌋` (centred) or `t − 1` (canonical). -/
def msgBound (ml : Lift) (t : ℕ) : ℕ :=
  match ml with
  | .centred => t / 2
  | .canonical => t - 1

/-- **Fresh public-key encryption, worst case.** The critical quantity is
`v = m̃ + t·(e·u + e₀ + e₁·s)` (`BGV.freshCrit`; `−e·u` for the HES18/SEAL key), hence

  `‖v‖∞ ≤ ‖m̃‖∞ + t·(N·B_e·B_u + B_e + N·B_e·B_s)`,

which for ternary `s, u` is `‖m̃‖∞ + t·B_e·(2N + 1)`.
Source: derivation from OpenFHE rns-pke.cpp:169-193 & base-pke.cpp:82; KPZ21 §2.2 / App. B.1
(there with average-case constants); GHS12 App. D.1. -/
def freshBound (ml : Lift) (N t Bs Be Bu : ℕ) : ℕ :=
  msgBound ml t + t * (N * Be * Bu + Be + N * Be * Bs)

/-- Secret-key fresh encryption `(a·s + t·e + m, −a)`: `v = m̃ + t·e`, `‖v‖∞ ≤ ‖m̃‖∞ + t·B_e`. -/
def freshSymBound (ml : Lift) (t Be : ℕ) : ℕ := msgBound ml t + t * Be

/-- **Addition**: `v = v₁ + v₂`, `‖v‖∞ ≤ B₁ + B₂`. Source: BGV12 §4; KPZ21 App. B. -/
def addBound (B1 B2 : ℕ) : ℕ := B1 + B2

/-- Multiplication by an integer constant `c`: `‖v‖∞ ≤ |c|·B`. (With the centred representative of
a constant mod `t` this is `≤ (t/2)·B`.) -/
def mulConstBound (c : ℤ) (B : ℕ) : ℕ := c.natAbs * B

/-- **Tensor multiplication**: `v = v₁·v₂`, `‖v‖∞ ≤ N·B₁·B₂`.
Source: BGV12 Lemma 8 (with `γ_R`); KPZ21 §2.1 (`δ_R = N`). -/
def mulBound (N B1 B2 : ℕ) : ℕ := N * B1 * B2

/-- Twice the worst-case absolute value of a fast base conversion from the basis `qs`:
`2·|Σ_i y_i·(Q/q_i)| ≤ Σ_i bound2(q_i)·(Q/q_i)`, i.e. `k·Q` for centred residues and
`2·(k·Q − Σ_i Q/q_i)` for canonical ones. -/
def bconvBound2 (c : Lift) (qs : List ℕ) : ℕ :=
  lsum (qs.zipIdx.map fun qi => c.bound2 qi.1 * (qs.eraseIdx qi.2).prod)

/-- **Hybrid key switching: the additive error (own derivation).**

Setting: level-`ℓ` element `x ∈ R_{Q_ℓ}` in RNS form; digits `Q_ℓ = ∏_j Q_j` (digit `j` has the
limbs listed in `digits[j]`); special basis `ps` with product `P`; key
`b_j + a_j·s = P·ε_j·s' + t·e_j (mod Q P)` with `‖e_j‖∞ ≤ B_e`; `‖s‖∞ ≤ B_s`.

1. *ModUp.* `d̃_j = Σ_{i∈digit j} y_i·(Q_j/q_i)` with `y_i = [x_i (Q_j/q_i)⁻¹]_{q_i}` lifted by
   `c`. So `d̃_j ≡ x (mod Q_j)` and `2‖d̃_j‖∞ ≤ bconvBound2 c digits[j]`.
2. *Inner product.* `X₀ + X₁·s ≡ Σ_j d̃_j·(b_j + a_j s) ≡ P·x·s' + t·E (mod Q_ℓ P)` with
   `E = Σ_j d̃_j·e_j`, `‖E‖∞ ≤ N·B_e·Σ_j‖d̃_j‖∞` (using `Σ_j d̃_j ε_j ≡ x mod Q_ℓ`).
3. *ModDown.* `k_i = (X_i − δ_i)/P` with `δ_i = t·FastBconv_P([t⁻¹X_i]_P)`, so `δ_i ≡ X_i (mod P)`,
   `δ_i ≡ 0 (mod t)` and `2‖δ_i‖∞ ≤ t·bconvBound2 c ps`.
4. Hence `k₀ + k₁·s ≡ x·s' + A (mod Q_ℓ)` with `A = (t·E − δ₀ − δ₁·s)/P` (an exact division),
   `A ≡ 0 (mod t)` and

   `‖A‖∞ ≤ ( t·N·B_e·Σ_j bconvBound2 c digits[j] + t·bconvBound2 c ps·(1 + N·B_s) ) / (2P)`.

   For centred lifts and `d` digits of `α` limbs each of size `≈ q`, `|ps| = l`:
   `‖A‖∞ ≤ t·( N·B_e·d·α·q^α/(2P) + (l/2)·(1 + N·B_s) )`; canonical lifts double both terms.

This is the bound the function returns (a rational number). The first term is the reason
`P ≳ max_j Q_j` is required; the second is the "rounding" term, independent of `P`.
Compare: HK19 Lemma 3 / KPZ21 App. B.2.3 give the same two terms with average-case constants
and without the fast-base-conversion factors `α` and `l` (they analyse exact digits). -/
def ksAddedBound (c : Lift) (N t Bs Be : ℕ) (digits : List (List ℕ)) (ps : List ℕ) : ℚ :=
  let D2 : ℕ := lsum (digits.map (bconvBound2 c))
  ((t * N * Be * D2 + t * bconvBound2 c ps * (1 + N * Bs) : ℕ) : ℚ) / (2 * ps.prod : ℕ)

/-- Key switching / relinearization: `B_out = B_in + ‖A‖∞`. -/
def keySwitchBound (c : Lift) (N t Bs Be : ℕ) (digits : List (List ℕ)) (ps : List ℕ) (B : ℕ) : ℚ :=
  B + ksAddedBound c N t Bs Be digits ps

/-- Twice the worst-case `‖δ‖∞` of one component in a modulus switch by `q_ℓ`:
`t·q_ℓ` for the GHS/OpenFHE centred correction, `2t(q_ℓ−1)` for a canonical lift,
`2(t·q_ℓ − 1)` for SEAL's correction, `t·q_ℓ` for BGV12's. -/
def msDeltaBound2 (v : MSVariant) (t ql : ℕ) : ℕ :=
  match v with
  | .ghs c => t * c.bound2 ql
  | .seal => 2 * (t * ql - 1)
  | .bgv12 => t * ql

/-- **Modulus switching** from `Q = Q'·q_ℓ` to `Q'` of a ciphertext with `D + 1` components:
`v' = (v + Σ_i δ_i·s^i)/q_ℓ`, hence

  `‖v'‖∞ ≤ ( B + ‖δ‖∞·Σ_{i=0}^{D} (N·B_s)^i ) / q_ℓ`,

i.e. for `D = 1`, centred: `B/q_ℓ + (t/2)·(1 + N·B_s)`.
Source: BGV12 Lemma 4 (`‖·‖ ≤ (p/q)‖·‖ + (r/2)·√d·γ_R·ℓ₁(s)` in their norms); GHS12 §3.2 /
App. D.2; KPZ21 App. B.2.2. -/
def modSwitchBound (v : MSVariant) (N t Bs ql D B : ℕ) : ℚ :=
  ((B : ℚ) + (msDeltaBound2 v t ql : ℚ) / 2 * (lsum ((List.range (D + 1)).map fun i => (N * Bs) ^ i) : ℕ))
    / ql

/-! ## The rules as propositions

These are the statements a careful cryptographer would assert. They are **not proved here** (they
are `Prop`-valued definitions, to be proved or compared later); each is exercised
numerically in `Respec/BGVTest.lean`. -/

/-- Fresh encryption rule (OpenFHE key and encryption equations). -/
def FreshRule (ml : Lift) (N t Q : ℕ) : Prop :=
  ∀ (s a e u e0 e1 : IntPoly N) (m : Poly t N) (Bs Be Bu : ℕ),
    0 < t → 0 < N →
    NPoly.normInf s ≤ Bs → NPoly.normInf e ≤ Be → NPoly.normInf e0 ≤ Be → NPoly.normInf e1 ≤ Be →
    NPoly.normInf u ≤ Bu → 2 * freshBound ml N t Bs Be Bu < Q →
    crit s (encrypt (Q := Q) ml (pkGen t s a e) m u e0 e1) = freshCrit ml m s e u e0 e1 ∧
      Encrypts t s (encrypt (Q := Q) ml (pkGen t s a e) m u e0 e1) m (freshBound ml N t Bs Be Bu)

/-- Addition rule. -/
def AddRule (N t Q : ℕ) : Prop :=
  ∀ (s : IntPoly N) (c1 c2 : Ct Q N) (m1 m2 : Poly t N) (B1 B2 : ℕ),
    Encrypts t s c1 m1 B1 → Encrypts t s c2 m2 B2 → 2 * addBound B1 B2 < Q →
    Encrypts t s (BGV.add c1 c2) (m1 + m2) (addBound B1 B2)

/-- Tensor-multiplication rule. -/
def MulRule (N t Q : ℕ) : Prop :=
  ∀ (s : IntPoly N) (c1 c2 : Ct Q N) (m1 m2 : Poly t N) (B1 B2 : ℕ),
    Encrypts t s c1 m1 B1 → Encrypts t s c2 m2 B2 → 2 * mulBound N B1 B2 < Q →
    Encrypts t s (mulTensor c1 c2) (m1 * m2) (mulBound N B1 B2)

/-- Modulus-switching rule for a two-component ciphertext and the GHS/OpenFHE correction: the
message is multiplied by `q_ℓ⁻¹ mod t`. The no-wrap condition is on the *numerator*
`B + ‖δ‖∞(1 + N·B_s)` against `Q/2`. -/
def ModSwitchRule (c : Lift) (N t ql Q' : ℕ) : Prop :=
  ∀ (s : IntPoly N) (c0 c1 : Poly (Q' * ql) N) (m : Poly t N) (Bs B : ℕ),
    Nat.Coprime t ql → 1 < t → 1 < ql → 0 < N →
    NPoly.normInf s ≤ Bs → Encrypts t s [c0, c1] m B →
    2 * B + msDeltaBound2 (.ghs c) t ql * (1 + N * Bs) < Q' * ql →
    ∃ B' : ℕ, (B' : ℚ) ≤ modSwitchBound (.ghs c) N t Bs ql 1 B ∧
      Encrypts t s (modSwitch (.ghs c) t ql Q' [c0, c1]) ((((ql : ℕ) : ZMod t)⁻¹) • m) B'

/-- Hybrid key-switching rule (RNS algorithm, OpenFHE key form): for every input limb vector `x`
the output `(k₀, k₁)` satisfies `k₀ + k₁·sTo = x·sFrom + A (mod Q)` with `t ∣ A` and `‖A‖∞`
bounded by `ksAddedBound`. No no-wrap condition is needed: the statement is modulo `Q`. -/
def KeySwitchRule (c : Lift) {k l d : ℕ} (N t : ℕ) (q : Basis k) (p : Basis l)
    (dig : Fin k → Fin d) : Prop :=
  ∀ (sFrom sTo : IntPoly N) (a e : Fin d → IntPoly N) (x : RnsPoly q N) (Bs Be : ℕ),
    q.IsCRT → p.IsCRT → q.Coprime p → (∀ i, Nat.Coprime t (q i)) → (∀ i, Nat.Coprime t (p i)) →
    0 < N → NPoly.normInf sTo ≤ Bs → (∀ j, NPoly.normInf (e j) ≤ Be) →
    let ks := hybridKeySwitch c (some t) q p dig (hybridKeyGen t q p dig sFrom sTo a e) x
    ∃ A : IntPoly N,
      ofRns q ks.1 + ofRns q ks.2 * NPoly.ofInt q.prod sTo
        = ofRns q x * NPoly.ofInt q.prod sFrom + NPoly.ofInt q.prod A ∧
      DivisibleBy t A ∧
      (NPoly.normInf A : ℚ) ≤ ksAddedBound c N t Bs Be
        ((List.finRange d).map fun j => (List.finRange k).filterMap fun i =>
          if dig i = j then some (q i) else none)
        (List.ofFn p)

end Respec.Noise
