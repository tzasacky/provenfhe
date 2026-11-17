import FHE.Pin.Force
import Challenge.BFVMul.Float
import Challenge.BFVMul.BEHZ

/-!
# FHE.Pin.BFV.Stage — the locked BFV multiplications with their intermediate polynomials forced
(UNTRUSTED glue; the equalities are proved)

The locked definitions `Challenge.BFVMul.Fl.hpsMul`, `Fl.poverqMul`, `Fl.leveledMul`,
`Challenge.BFVMul.behzMul` are compositions of functions on `IntPoly N` (closures): executed as
written, every coefficient of the result re-evaluates the whole chain below it. Here the same
compositions are written with every intermediate polynomial **forced** to an array once
(`frc K p = ofArr (toArr K p)`, the identity: `frc_eq`) and the negacyclic products as
`FHE.Pin.mulArr` (Kronecker substitution, `ofArr_mulArr`). Each forced pipeline is proved equal to the locked definition
(`hpsForced_eq`, `poverqForced_eq`, `leveledForced_eq`, `behzForced_eq`); the per-coefficient
functions it calls (`Fl.switch1`, `Fl.scale1`, `POverQ.approx1`, `BEHZ.smmrq1`, `BEHZ.floor1`,
`BEHZ.sk1`, `HPS.reconstruct`) are the locked ones, unchanged. Cost: quadratic in `N` (the
products) with large constants (the locked scalar functions recompute their tables at every
coefficient), so this tier is run at medium `N` only.
-/

namespace FHE.Pin.BFV
open Spec Spec.NPoly Challenge.BFVMul FHE.Pin

variable {N : ℕ}

/-- Evaluate every coefficient once (the identity: `frc_eq`). -/
@[noinline] def frc (K : ℕ) (p : IntPoly N) : IntPoly N := ofArr (toArr K p)

@[simp] theorem frc_eq (K : ℕ) (p : IntPoly N) : frc K p = p := ofArr_toArr K p

/-- Force every polynomial of a list. -/
def frcL (K : ℕ) (x : List (IntPoly N)) : List (IntPoly N) := x.map (frc K)

@[simp] theorem frcL_eq (K : ℕ) (x : List (IntPoly N)) : frcL K x = x := by
  have h : (frc K : IntPoly N → IntPoly N) = id := funext (frc_eq K)
  simp [frcL, h]

/-- One limb product of `HPS.mulLimbs` as an array: the Kronecker product (`FHE.Pin.mulArr`), each
coefficient reduced `% m`. -/
def mulLimbArr (m : ℕ) (a b : IntPoly N) : Array ℤ := (mulArr a b).map fun z => z % (m : ℤ)

theorem ofArr_mulLimbArr (m : ℕ) (a b : IntPoly N) :
    ofArr (mulLimbArr m a b) = (⟨fun i => (a * b).coeff i % (m : ℤ)⟩ : IntPoly N) := by
  ext i
  have hs : (mulArr a b).size = N := by simp [mulArr, Kron.mulNeg]
  have h := congrArg (fun p : IntPoly N => p.coeff i) (ofArr_mulArr a b)
  simp only [ofArr] at h ⊢
  unfold mulLimbArr
  rw [getElem!_pos _ _ (by simp [hs]), Array.getElem_map, ← getElem!_pos, h]

/-- `HPS.mulLimbs` with the Kronecker product, forced (the limb products are arrays: an
`NPoly`-valued product would be re-evaluated per coefficient by the compiled code). -/
def mulLimbsF (K : ℕ) (ms : List ℕ) (a b : List (IntPoly N)) : List (IntPoly N) :=
  frcL K ((List.zipWith (fun (m : ℕ) ab => mulLimbArr m ab.1 ab.2) ms (a.zip b)).map ofArr)

@[simp] theorem mulLimbsF_eq (K : ℕ) (ms : List ℕ) (a b : List (IntPoly N)) :
    mulLimbsF K ms a b = HPS.mulLimbs ms a b := by
  delta HPS.mulLimbs
  simp only [mulLimbsF, frcL_eq, List.map_zipWith, ofArr_mulLimbArr]

/-- `HPS.tensor` with every product and the result forced. -/
def tensorForced (K : ℕ) (ms : List ℕ) (c d : List (List (IntPoly N))) : List (List (IntPoly N)) :=
  match c, d with
  | [c₀, c₁], [d₀, d₁] =>
    [mulLimbsF K ms c₀ d₀,
     frcL K (HPS.addLimbs ms (mulLimbsF K ms c₀ d₁) (mulLimbsF K ms c₁ d₀)),
     mulLimbsF K ms c₁ d₁]
  | _, _ => []

@[simp] theorem tensorForced_eq (K : ℕ) (ms : List ℕ) (c d : List (List (IntPoly N))) :
    tensorForced K ms c d = HPS.tensor ms c d := by
  match c, d with
  | [c₀, c₁], [d₀, d₁] =>
    change _ = [HPS.mulLimbs ms c₀ d₀, HPS.addLimbs ms (HPS.mulLimbs ms c₀ d₁) (HPS.mulLimbs ms c₁ d₀),
      HPS.mulLimbs ms c₁ d₁]
    simp only [tensorForced, mulLimbsF_eq, frcL_eq]
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _ :: _, _ => rfl
  | [_, _], [] => rfl
  | [_, _], [_] => rfl
  | [_, _], _ :: _ :: _ :: _ => rfl

/-- `Fl.hpsMul` with every intermediate forced. -/
def hpsForced (K : ℕ) (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) :
    List (IntPoly N) :=
  let ext := fun a : IntPoly N => frcL K (Fl.expand S qs ps (HPS.toLimbs qs a))
  (tensorForced K (qs ++ ps) (c.map ext) (d.map ext)).map fun x =>
    frc K (HPS.reconstruct qs
      (frcL K (Fl.switchBasis S ps qs (frcL K (Fl.scaleRound S t qs ps x)))))

/-- **The forced HPS pipeline is the locked definition.** -/
theorem hpsForced_eq (K : ℕ) (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) :
    hpsForced K S t qs ps c d = Fl.hpsMul S t qs ps c d := by
  simp only [hpsForced, tensorForced_eq, frcL_eq, frc_eq]
  rfl

/-- `Fl.poverqMul` with every intermediate forced. -/
def poverqForced (K : ℕ) (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) :
    List (IntPoly N) :=
  let a := c.map fun x => frcL K (Fl.expand S qs ps (HPS.toLimbs qs x))
  let b := d.map fun x => frcL K (Fl.fastExpand S qs ps qs (HPS.toLimbs qs x))
  (tensorForced K (qs ++ ps) a b).map fun x =>
    frc K (HPS.reconstruct qs
      (frcL K (Fl.scaleRoundOut S t ps qs (x.drop qs.length) (x.take qs.length))))

/-- **The forced P-over-Q pipeline is the locked definition.** -/
theorem poverqForced_eq (K : ℕ) (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) :
    poverqForced K S t qs ps c d = Fl.poverqMul S t qs ps c d := by
  simp only [poverqForced, tensorForced_eq, frcL_eq, frc_eq]
  rfl

/-- `Fl.leveledMul` with every intermediate forced. -/
def leveledForced (K : ℕ) (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (drop : ℕ)
    (c d : List (IntPoly N)) : List (IntPoly N) :=
  let l := qs.length - drop
  let ql := qs.take l
  let pl := ps.take l
  let a := c.map fun x =>
    let xl := HPS.toLimbs qs x
    frcL K (Fl.expand S ql pl (frcL K (Fl.scaleRoundOut S 1 (qs.drop l) ql (xl.drop l) (xl.take l))))
  let b := d.map fun x => frcL K (Fl.fastExpand S qs pl ql (HPS.toLimbs qs x))
  (tensorForced K (ql ++ pl) a b).map fun x =>
    frc K (HPS.reconstruct qs
      (POverQ.expandQlHat qs ql
        (frcL K (Fl.scaleRoundOut S t pl ql (x.drop ql.length) (x.take ql.length)))))

/-- **The forced leveled P-over-Q pipeline is the locked definition.** -/
theorem leveledForced_eq (K : ℕ) (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (drop : ℕ)
    (c d : List (IntPoly N)) :
    leveledForced K S t qs ps drop c d = Fl.leveledMul S t qs ps drop c d := by
  simp only [leveledForced, tensorForced_eq, frcL_eq, frc_eq]
  rfl

/-- `behzMul` with every intermediate forced. -/
def behzForced (K : ℕ) (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ) (c d : List (IntPoly N)) :
    List (IntPoly N) :=
  let bsk := bs ++ [msk]
  let ext := fun a : IntPoly N => frcL K (BEHZ.extend qs bsk mt (HPS.toLimbs qs a))
  (tensorForced K (qs ++ bsk) (c.map ext) (d.map ext)).map fun x =>
    frc K (HPS.reconstruct qs
      (frcL K (BEHZ.convSK qs bs msk (frcL K (BEHZ.floorq t qs bsk x)))))

/-- **The forced BEHZ pipeline is the locked definition.** -/
theorem behzForced_eq (K : ℕ) (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ) (c d : List (IntPoly N)) :
    behzForced K t qs bs msk mt c d = behzMul t qs bs msk mt c d := by
  simp only [behzForced, tensorForced_eq, frcL_eq, frc_eq]
  rfl

end FHE.Pin.BFV
