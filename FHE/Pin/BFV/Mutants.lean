import FHE.Pin.BFV.Sound
import Challenge.CertifyBFV.Defs

/-!
# FHE.Pin.BFV.Mutants — deliberately WRONG copies of trusted BFV definitions   (UNTRUSTED, test-only)

`openfhe_pin --mutate NAME` on a BFV case replaces ONE trusted definition (or one number of the
budget `Challenge.CertifyBFV.budgetBFV`) by a wrong copy; the suite must then fail
(`harness/openfhe-pin/lean/mutation_bfv.sh`). A mutant is a record of overrides (`BMut`); the
default record is the trusted configuration, and with it every selector below returns the trusted
function itself (`*_none` lemmas, by `rfl`). With a mutant the literal mode is off.

A budget mutant that survives is a measurement, not a defect of the harness: it says that the
recorded executions stay below the perturbed number (the table of `mutation_bfv.sh` prints how
far).
-/

namespace FHE.Pin.BFV
open Spec Spec.NPoly Spec.Scheme Spec.Source FHE.Pin
open Spec.TraceBFV (Bnd)
open Spec.CertifyBFV (InputBFV Technique)

/-- The overrides of one mutant. -/
structure BMut where
  name : String := "none"
  /-- What it perturbs (printed by `--help` and by the mutation table). -/
  what : String := ""
  /-- Hooks of the step decision `FHE.Pin.BFV.stepOKb`. -/
  hooks : Hooks := {}
  /-- A mutant of the shared forced primitives (`FHE.Pin.Mut`: product, automorphism). -/
  bgv : Mut := .none
  /-- `Δ` of the noise definition `Spec.Scheme.BFVEncrypts` (trusted: `Q / t`). -/
  delta : Option (ℕ → ℕ → ℕ) := none
  /-- The library model of the encoding predicts `⌊Q·p/t⌋` instead of `⌈Q·p/t⌉`. -/
  encFloor : Bool := false
  /-- Applied to the decoded input before `budgetBFV` (technique, `floatTol`). -/
  input : InputBFV → InputBFV := id
  /-- Applied to the budget of every instruction (`x` is the unmodified input). -/
  budget : InputBFV → TraceBFV.Budget → TraceBFV.Budget := fun _ E => E
  /-- The input bound is divided by this. -/
  freshDiv : ℕ := 1
  /-- `bfvDecrypt` with `⌊t·Φ/Q⌋` instead of `⌊t·Φ/Q⌉`. -/
  decFloor : Bool := false
  /-- `refBoundBFV` without the carry terms `Q mod t`. -/
  boundNoCarry : Bool := false
  /-- `refBoundBFV` with `mulBound` at `E.mulLift := 0`. -/
  boundMulK0 : Bool := false

def BMut.isNone (m : BMut) : Bool := m.name == "none"

namespace Mutants

/-- WRONG: cyclic product over `ℤ`. -/
def mulCyclicZ {N : ℕ} (a b : IntPoly N) : IntPoly N := FHE.Pin.Mutants.mulCyclic a b

/-- WRONG (when `floor`): BFV decryption with `⌊t·Φ/Q⌋`. -/
def decryptFloorA (N K t Q : ℕ) (Φ : Array ℤ) : Array (ZMod t) :=
  toArr K (⟨fun i => (((t : ℤ) * (ofArr (N := N) Φ).coeff i / (Q : ℤ) : ℤ) : ZMod t)⟩ : Poly t N)

/-- `mulBound` with the carry `r` and the lift number as parameters (a copy of
`Challenge.BFV.mulBound`, which is `mulBoundR (Q % t)`). -/
def mulBoundR (r N t Q K R B₁ B₂ : ℕ) : ℕ :=
  let M := t - 1
  let K₁ := K + 1
  N * (B₁ + B₂) * (t * K₁ + M) + r * N * M * (2 * K₁ + 1) +
    (Q * R + 2 * N * (r * (Q / t) * M * M + r * M * (B₁ + B₂) + t * B₁ * B₂)) / (2 * Q)

/-- A copy of `Challenge.BFV.refBoundBFV` with the carry `r ℓ` and the lift number `K` of the
product rule as parameters (WRONG unless `r ℓ = Q_ℓ mod t` and `K = E.mulLift`). -/
def refBoundR (r : ℕ → ℕ) (K : ℕ) (P : FullParams) (E : TraceBFV.Budget) (ℓ : ℕ)
    (β : Var → Option Bnd) : Instr → Option Bnd
  | .add _ a b | .sub _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) => some (.ct (x + y + r ℓ))
    | _, _ => none
  | .addPlain _ a p | .subPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) =>
      some (.ct (x + r ℓ * ((y + P.src.t - 1) / P.src.t) + E.plainAdd))
    | _, _ => none
  | .mulPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) => some (.ct (P.src.N * y * (x + r ℓ)))
    | _, _ => none
  | .mul _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) =>
      some (.ct (mulBoundR (r ℓ) P.src.N P.src.t (P.src.modulus ℓ) K E.mulRound x y))
    | _, _ => none
  | .square _ a =>
    match β a with
    | some (.ct x) =>
      some (.ct (mulBoundR (r ℓ) P.src.N P.src.t (P.src.modulus ℓ) K E.mulRound x x))
    | _ => none
  | .mulConst _ a c =>
    match β a with
    | some (.ct x) => some (.ct (c.natAbs * (x + r ℓ)))
    | _ => none
  | .copy _ a | .toEval _ a | .toCoeff _ a => β a
  | .automorph _ a _ =>
    match β a with
    | some (.ct x) => some (.ct (x + r ℓ))
    | _ => none
  | .relin _ a | .keySwitch _ a =>
    match β a with
    | some (.ct x) => some (.ct (x + E.keySwitch))
    | _ => none
  | .modSwitch _ a =>
    match β a, P.src.qs[ℓ]? with
    | some (.ct x), some q => some (.ct (x / q + E.modSwitch + r ℓ))
    | _, _ => none
  | .dropLimbs _ _ _ => none

end Mutants

/-- The bound rule on the checked path: the trusted `Challenge.BFV.refBoundBFV`, or a wrong
copy. -/
def BMut.refBound (m : BMut) (P : FullParams) (E : TraceBFV.Budget) (ℓ : ℕ)
    (β : Var → Option Bnd) (i : Instr) : Option Bnd :=
  if m.boundNoCarry then Mutants.refBoundR (fun _ => 0) E.mulLift P E ℓ β i
  else if m.boundMulK0 then Mutants.refBoundR (fun ℓ => P.src.modulus ℓ % P.src.t) 0 P E ℓ β i
  else Challenge.BFV.refBoundBFV P E ℓ β i

/-- BFV decryption from a forced centred phase: the forced `Spec.Scheme.bfvDecrypt`
(`decryptBFVOfPhaseA`), or the flooring mutant. -/
def BMut.decryptOfPhase (m : BMut) (N K t Q : ℕ) (Φ : Array ℤ) : Array (ZMod t) :=
  if m.decFloor then Mutants.decryptFloorA N K t Q Φ else decryptBFVOfPhaseA N K t Q Φ

/-- The noise polynomial `[Z − Δ·m]_Q` for a given `Δ`. -/
def noisePolyD (N K t Q Δ : ℕ) (Z : Array ℤ) (m : Array (ZMod t)) : Array ℤ :=
  toArr K (centered (ofInt Q (ofArr (N := N) Z) -
    ofInt Q ⟨fun i => ((Δ * ((ofArr (N := N) m).coeff i).val : ℕ) : ℤ)⟩))

/-- The noise polynomial of `Spec.Scheme.BFVEncrypts` (`Δ = Q / t`), or with the mutant's `Δ`. -/
def BMut.noisePoly (m : BMut) (N K t Q : ℕ) (Z : Array ℤ) (msg : Array (ZMod t)) : Array ℤ :=
  noisePolyD N K t Q ((m.delta.getD fun Q t => Q / t) Q t) Z msg

/-- The measured noise: `FHE.Pin.BFV.noiseA` (= the noise of `BFVEncrypts`, `noiseA_spec`), or
the norm of the mutant's noise polynomial. -/
def BMut.noise (m : BMut) (N K t Q : ℕ) (Z : Array ℤ) (msg : Array (ZMod t)) : ℕ :=
  match m.delta with
  | none => noiseA N K t Q Z msg
  | some δ => normA N (noisePolyD N K t Q (δ Q t) Z msg)

/-- The norm of the trusted noise polynomial is `noiseA`. -/
theorem noisePolyD_norm (N K t Q : ℕ) (Z : Array ℤ) (m : Array (ZMod t)) :
    normA N (noisePolyD N K t Q (Q / t) Z m) = noiseA N K t Q Z m := by
  simp [noisePolyD, noiseA, normA]

/-- The input decision: `FHE.Pin.BFV.inputOKb` (sound: `inputOKb_sound`), or, with a mutant of
`Δ`, of decryption or of the bound, the same two conjuncts on the mutated functions. -/
def BMut.inputOK (m : BMut) (P : FullParams) (K B parts : ℕ) (ph : Ph)
    (msg : Array (ZMod P.src.t)) : Bool :=
  if m.delta.isNone && !m.decFloor then inputOKb P K B parts ph msg
  else if parts = 1 then inputPtOKb P K B ph msg
  else
    let Q := P.src.modulus ph.level
    (m.decryptOfPhase P.src.N K P.src.t Q ph.Φ == msg) &&
      decide (m.noise P.src.N K P.src.t Q ph.Z msg ≤ B)

@[simp] theorem BMut.refBound_none (P : FullParams) (E : TraceBFV.Budget) (ℓ : ℕ)
    (β : Var → Option Bnd) (i : Instr) :
    ({} : BMut).refBound P E ℓ β i = Challenge.BFV.refBoundBFV P E ℓ β i := rfl
@[simp] theorem BMut.decryptOfPhase_none (N K t Q : ℕ) (Φ : Array ℤ) :
    ({} : BMut).decryptOfPhase N K t Q Φ = decryptBFVOfPhaseA N K t Q Φ := rfl
@[simp] theorem BMut.noise_none (N K t Q : ℕ) (Z : Array ℤ) (msg : Array (ZMod t)) :
    ({} : BMut).noise N K t Q Z msg = noiseA N K t Q Z msg := rfl
@[simp] theorem BMut.inputOK_none (P : FullParams) (K B parts : ℕ) (ph : Ph)
    (msg : Array (ZMod P.src.t)) :
    ({} : BMut).inputOK P K B parts ph msg = inputOKb P K B parts ph msg := rfl

/-! ### The table -/

/-- The other technique whose slack `wrong-technique` charges: BEHZ for an HPS run (base = the
auxiliary basis without its last modulus, `m_sk` = that modulus, `m̃ = 2¹⁶`), HPS for a BEHZ or
P-over-Q run (auxiliary basis = the run's). -/
def swapTechnique : Technique → Technique
  | .textbook => .textbook
  | .hps R => .behz R.dropLast (R.getLastD 0) 65536
  | .poverq Ps => .hps Ps
  | .leveled Ps => .hps Ps
  | .behz B msk _ => .hps (B ++ [msk])

def setKS (f : InputBFV → ℕ → ℕ) : InputBFV → TraceBFV.Budget → TraceBFV.Budget :=
  fun x E => { E with keySwitch := f x E.keySwitch }

def BMut.all : List BMut :=
  [ { name := "delta-round", what := "Δ = ⌊Q/t⌉ in the noise definition and in addPlain/subPlain",
      delta := some fun Q t => (2 * Q + t) / (2 * t), hooks := { delta := fun Q t => (2 * Q + t) / (2 * t) } },
    { name := "delta-ceil", what := "Δ = ⌈Q/t⌉ in the noise definition and in addPlain/subPlain",
      delta := some fun Q t => (Q + t - 1) / t, hooks := { delta := fun Q t => (Q + t - 1) / t } },
    { name := "enc-floor", what := "the predicted encoding of Encrypt is ⌊Q·p/t⌋ instead of ⌈Q·p/t⌉",
      encFloor := true },
    { name := "mul-no-t", what := "the product contract without the factor t", hooks := { tfac := fun _ => 1 } },
    { name := "mulround-half", what := "E.mulRound halved",
      budget := fun _ E => { E with mulRound := E.mulRound / 2 } },
    { name := "mulround-textbook", what := "E.mulRound := Spec.BudgetBFV.mulRound P (ρ = 1: float tolerance and technique slack dropped)",
      budget := fun x E => { E with mulRound := BudgetBFV.mulRound x.P } },
    { name := "mulround-zero", what := "E.mulRound := 0", budget := fun _ E => { E with mulRound := 0 } },
    { name := "mullift-zero", what := "E.mulLift := 0", budget := fun _ E => { E with mulLift := 0 } },
    { name := "mullift-half", what := "E.mulLift halved",
      budget := fun _ E => { E with mulLift := E.mulLift / 2 } },
    { name := "ks-half", what := "E.keySwitch halved", budget := setKS fun _ k => k / 2 },
    { name := "ks-zero", what := "E.keySwitch := 0", budget := setKS fun _ _ => 0 },
    { name := "ks-noleveled", what := "E.keySwitch capped at Spec.BudgetBFV.ksBudget P lay (the ksLeveled term of an internal drop dropped)",
      budget := setKS fun x k => min k (BudgetBFV.ksBudget x.P x.lay) },
    { name := "ms-half", what := "E.modSwitch halved",
      budget := fun _ E => { E with modSwitch := E.modSwitch / 2 } },
    { name := "ms-zero", what := "E.modSwitch := 0", budget := fun _ E => { E with modSwitch := 0 } },
    { name := "plainadd-zero", what := "E.plainAdd := 0 (the declared `scaled` deviation dropped)",
      budget := fun _ E => { E with plainAdd := 0 } },
    { name := "plainadd-rounded", what := "E.plainAdd := plainAddRounded (the library rounds up)",
      budget := fun x E =>
        let pa := BudgetBFV.plainAddRounded x.P (Challenge.CertifyBFV.maxPlainBound x.P x.prog)
        { E with plainAdd := pa } },
    { name := "wrong-technique", what := "the slacks of another technique (HPS ↔ BEHZ, P-over-Q → HPS)",
      input := fun x => { x with mul := x.mul.map swapTechnique } },
    { name := "slack-idealised", what := "floatTol := false (the slacks of the exact algorithms)",
      input := fun x => { x with floatTol := false } },
    { name := "fresh-half", what := "the input bound halved", freshDiv := 2 },
    { name := "decrypt-floor", what := "bfvDecrypt with ⌊t·Φ/Q⌋", decFloor := true },
    { name := "automorph-index", what := "X ↦ X^(g⁻¹) instead of X ↦ X^g", bgv := .autoIndex },
    { name := "mul-cyclic", what := "cyclic instead of negacyclic product",
      bgv := .mulCyclic, hooks := { mul := fun a b => toArr 1 (Mutants.mulCyclicZ a b) } },
    { name := "bound-no-carry", what := "refBoundBFV without the Q mod t terms", boundNoCarry := true },
    { name := "bound-mul-k0", what := "refBoundBFV's mulBound with E.mulLift := 0", boundMulK0 := true } ]

def BMut.ofString? (s : String) : Option BMut :=
  if s == "none" then some {} else BMut.all.find? (·.name == s)

end FHE.Pin.BFV
