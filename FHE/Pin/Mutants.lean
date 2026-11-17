import Spec.Budget
import Spec.Encrypt
import Spec.Decrypt
import Spec.Trace

/-!
# FHE.Pin.Mutants — deliberately WRONG copies of trusted definitions   (UNTRUSTED, test-only)

The differential harness `openfhe_pin` executes the trusted BGV definitions on data dumped from
OpenFHE. To show that the harness has teeth, `--mutate NAME` replaces one trusted operation on the
*forced* execution path by one of the wrong copies below; the suite must then fail
(`harness/openfhe-pin/lean/mutation.sh`). Nothing here is used when `Mut.none` is selected: every
selector reduces to the trusted definition by `rfl` (the `*_none` lemmas), and the equality
theorems of `FHE.Pin.Force` are stated at `Mut.none`.
-/

namespace FHE.Pin
open Spec Spec.NPoly Spec.Scheme Spec.Source

/-- Which mutant is active. -/
inductive Mut
  | none
  /-- canonical lift `[0, q)` instead of the centred lift, in the phase / decryption -/
  | centring
  /-- canonical instead of centred representative inside `switchPhase` -/
  | switchCentring
  /-- `X ↦ X^(g⁻¹ mod 2N)` instead of `X ↦ X^g` -/
  | autoIndex
  /-- `X ↦ X^(g+2)` instead of `X ↦ X^g` -/
  | autoIndexShift
  /-- no minus sign on wrap-around in the automorphism -/
  | autoSign
  /-- gadget factor without the `[Q̂ⱼ⁻¹]` term -/
  | gadgetFactor
  /-- gadget factor of the next digit -/
  | gadgetDigit
  /-- message scale of `modSwitch`: `q` instead of `q⁻¹` -/
  | scaleStep
  /-- `decScale` without the inverse -/
  | scaleDec
  /-- cyclic instead of negacyclic product -/
  | mulCyclic
  /-- `encrypt` adds the centred lift of the message `p mod t` instead of the stored plaintext
  polynomial `p` -/
  | lift
  /-- public key / key-switching key components swapped -/
  | keyOrder
  /-- the modulus-switching budget of a 2-component ciphertext for every operand with more than
  one component (the rule before `Spec.Trace.Budget.modSwitchAt`) -/
  | msParts
  deriving DecidableEq, Repr, Inhabited

def Mut.all : List (String × Mut) :=
  [("centring", .centring), ("switch-centring", .switchCentring), ("automorph-index", .autoIndex),
   ("automorph-shift", .autoIndexShift), ("automorph-sign", .autoSign),
   ("gadget-factor", .gadgetFactor), ("gadget-digit", .gadgetDigit), ("scale-step", .scaleStep),
   ("scale-dec", .scaleDec), ("mul-negacyclic", .mulCyclic), ("lift", .lift),
   ("key-order", .keyOrder), ("ms-parts", .msParts)]

def Mut.ofString? (s : String) : Option Mut :=
  if s == "none" then some .none else (Mut.all.find? (·.1 == s)).map (·.2)

namespace Mutants
variable {R : Type} [CommRing R] {N : ℕ}

/-- WRONG: cyclic convolution (`X^N = 1`). -/
def mulCyclic (a b : NPoly R N) : NPoly R N :=
  ⟨fun k => ∑ i : Fin N,
    if h : i.val ≤ k.val then
      a.coeff i * b.coeff ⟨k.val - i.val, by have := k.isLt; omega⟩
    else
      a.coeff i * b.coeff ⟨N + k.val - i.val, by have := k.isLt; have := i.isLt; omega⟩⟩

/-- WRONG: the automorphism without the sign of `X^N = -1`. -/
def automorphNoSign (g : ℕ) (a : NPoly R N) : NPoly R N :=
  ⟨fun k => ∑ i : Fin N,
    if (i.val * g) % (2 * N) = k.val then a.coeff i
    else if (i.val * g) % (2 * N) = k.val + N then a.coeff i
    else 0⟩

/-- `g⁻¹ mod 2N` by search (`g` itself if there is none). -/
def invIndex (N g : ℕ) : ℕ :=
  ((List.range (2 * N)).find? fun h => (g * h) % (2 * N) = 1).getD g

/-- WRONG: canonical lift where the centred one is meant. -/
def canonicalLift {q : ℕ} (a : Poly q N) : IntPoly N := ⟨fun i => ((a.coeff i).val : ℤ)⟩

/-- WRONG: `switchPhase` with the canonical representative of the correction. -/
def switchPhaseCanon (t q : ℕ) (c : IntPoly N) : IntPoly N :=
  ⟨fun i => (c.coeff i + (t : ℤ) * ((((-(c.coeff i) : ℤ) : ZMod q) * (t : ZMod q)⁻¹).val : ℤ)) / q⟩

/-- WRONG: gadget factor without `[Q̂ⱼ⁻¹]_{Qⱼ}`. -/
def gadgetFactorNoInv (Pm : ℕ) (Qs : List ℕ) (j : ℕ) : ℕ := Pm * (Qs.eraseIdx j).prod

/-- WRONG: the gadget factor of the next digit (cyclically). -/
def gadgetFactorNext (Pm : ℕ) (Qs : List ℕ) (j : ℕ) : ℕ :=
  Budget.gadgetFactor Pm Qs ((j + 1) % Qs.length)

/-- WRONG: `decScale` without the inverse. -/
def decScaleNoInv (P : Params) (ℓ : ℕ) : ZMod P.t := ((((P.qs.take ℓ).drop 1).prod : ℕ) : ZMod P.t)

/-- WRONG: `encrypt` adding the centred lift of the message `p mod t` instead of the stored
plaintext polynomial `p` itself (they differ whenever `p` is not centred modulo `t`, e.g. for a
packed plaintext with a coefficient above `t/2`). -/
def encryptCentred (t : ℕ) (b a p u e₁ e₂ : IntPoly N) : List (IntPoly N) :=
  [b * u + (t : ℤ) • e₁ + centered (ofInt t p), a * u + (t : ℤ) • e₂]

end Mutants

/-! ### Selectors: the trusted operation unless the corresponding mutant is active -/

section Sel
variable {R : Type} [CommRing R] {N : ℕ}

def Mut.mulM (m : Mut) (a b : NPoly R N) : NPoly R N :=
  if m = .mulCyclic then Mutants.mulCyclic a b else a * b

def Mut.autoM (m : Mut) (g : ℕ) (a : NPoly R N) : NPoly R N :=
  if m = .autoIndex then automorph (Mutants.invIndex N g) a
  else if m = .autoIndexShift then automorph (g + 2) a
  else if m = .autoSign then Mutants.automorphNoSign g a
  else automorph g a

def Mut.centeredM (m : Mut) {q : ℕ} (a : Poly q N) : IntPoly N :=
  if m = .centring then Mutants.canonicalLift a else NPoly.centered a

def Mut.switchPhaseM (m : Mut) (t q : ℕ) (c : IntPoly N) : IntPoly N :=
  if m = .switchCentring then Mutants.switchPhaseCanon t q c else Decrypt.switchPhase t q c

/-- `Spec.Decrypt.switchDownRev` over the selected `switchPhase`. -/
def Mut.switchDownRevM (m : Mut) (t : ℕ) : List ℕ → IntPoly N → IntPoly N
  | [], c => c
  | [_], c => c
  | q :: rest, c => Mut.switchDownRevM m t rest (NPoly.centered (ofInt rest.prod (m.switchPhaseM t q c)))

def Mut.gadgetFactorM (m : Mut) (Pm : ℕ) (Qs : List ℕ) (j : ℕ) : ℕ :=
  if m = .gadgetFactor then Mutants.gadgetFactorNoInv Pm Qs j
  else if m = .gadgetDigit then Mutants.gadgetFactorNext Pm Qs j
  else Budget.gadgetFactor Pm Qs j

def Mut.decScaleM (m : Mut) (P : Params) (ℓ : ℕ) : ZMod P.t :=
  if m = .scaleDec then Mutants.decScaleNoInv P ℓ else Decrypt.decScale P ℓ

def Mut.encryptM (m : Mut) (t : ℕ) (b a p u e₁ e₂ : IntPoly N) : List (IntPoly N) :=
  if m = .lift then Mutants.encryptCentred t b a p u e₁ e₂
  else if m = .keyOrder then Encrypt.encrypt t a b p u e₁ e₂
  else Encrypt.encrypt t b a p u e₁ e₂

/-- `Spec.Source.step`, with the `modSwitch` message scale or the automorphism replaced when the
corresponding mutant is active. -/
def Mut.stepM (m : Mut) (P : Params) (ρ : Env P) (i : Instr) : Option (Env P) :=
  if m = .scaleStep then
    match i with
    | .modSwitch d a => do
      let x ← ρ a
      guard (2 ≤ x.level)
      let qLast ← P.qs[x.level - 1]?
      pure (ρ.set d { x with msg := x.msg.lift₁ (((qLast : ZMod P.t)) • ·), level := x.level - 1 })
    | i => step P ρ i
  else if m = .autoIndex ∨ m = .autoIndexShift ∨ m = .autoSign then
    match i with
    | .automorph d a g => do
      let x ← ρ a
      guard (g % 2 = 1)
      pure (ρ.set d { x with msg := x.msg.lift₁ (m.autoM g),
                             key := (x.key * g) % (2 * P.N) })
    | i => step P ρ i
  else step P ρ i

/-- The modulus-switching budget for an operand with `k` components: `E.modSwitchAt k`, or (WRONG,
mutant `msParts`) the 2-component budget for every `k ≥ 2`. -/
def Mut.msBudgetM (m : Mut) (E : Trace.Budget) (k : ℕ) : ℕ :=
  if m = .msParts then (if k = 1 then E.modSwitchOne else E.modSwitch) else E.modSwitchAt k

@[simp] theorem Mut.msBudget_none (E : Trace.Budget) (k : ℕ) :
    Mut.none.msBudgetM E k = E.modSwitchAt k := rfl

@[simp] theorem Mut.mul_none (a b : NPoly R N) : Mut.none.mulM a b = a * b := rfl
@[simp] theorem Mut.auto_none (g : ℕ) (a : NPoly R N) : Mut.none.autoM g a = automorph g a := rfl
@[simp] theorem Mut.centered_none {q : ℕ} (a : Poly q N) : Mut.none.centeredM a = NPoly.centered a := rfl
@[simp] theorem Mut.switchPhase_none (t q : ℕ) (c : IntPoly N) :
    Mut.none.switchPhaseM t q c = Decrypt.switchPhase t q c := rfl
@[simp] theorem Mut.switchDownRev_none (t : ℕ) (qs : List ℕ) (c : IntPoly N) :
    Mut.none.switchDownRevM t qs c = Decrypt.switchDownRev t qs c := by
  induction qs generalizing c with
  | nil => rfl
  | cons q rest ih =>
    cases rest with
    | nil => rfl
    | cons r rest' => simp only [Mut.switchDownRevM, Decrypt.switchDownRev, Mut.switchPhase_none, ih]
@[simp] theorem Mut.gadgetFactor_none (Pm : ℕ) (Qs : List ℕ) (j : ℕ) :
    Mut.none.gadgetFactorM Pm Qs j = Budget.gadgetFactor Pm Qs j := rfl
@[simp] theorem Mut.decScale_none (P : Params) (ℓ : ℕ) : Mut.none.decScaleM P ℓ = Decrypt.decScale P ℓ := rfl
@[simp] theorem Mut.encrypt_none (t : ℕ) (b a p u e₁ e₂ : IntPoly N) :
    Mut.none.encryptM t b a p u e₁ e₂ = Encrypt.encrypt t b a p u e₁ e₂ := rfl
@[simp] theorem Mut.step_none (P : Params) (ρ : Env P) (i : Instr) :
    Mut.none.stepM P ρ i = step P ρ i := rfl

end Sel
end FHE.Pin
