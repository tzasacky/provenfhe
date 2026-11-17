import FHE.Ref.Arr
import Challenge.Realize.OpenFHEBFV

/-!
# FHE.Ref.KeySwitch — the locked key-switching transcriptions on arrays, PROVED equal
(UNTRUSTED glue; the theorems are kernel-checked)

Array forms of `Challenge.Realize.ksOpenFHE` (hybrid key switching of one component: ModUp of the
digits, inner products with the stored keys over `ℤ`, BGV ModDown by the special modulus) and of
the BGV relinearization / two-component key switch `relinOpenFHE`, `keySwitchOpenFHE`; and of the
BFV `Challenge.RealizeBFV.ksBFV` (both branches: BV digits without special primes, HYBRID =
`ksOpenFHE` at plaintext modulus 1 with them), `relinBFV`, `keySwitchBFV`. The products are the
Kronecker product `mulA`; the ModUp digits are computed once and shared by both inner products.
Every function returns the SAME INTEGERS as the locked definition (no reduction is added).
-/

namespace FHE.Ref
open Spec Spec.NPoly FHE.Pin Spec.Budget Challenge.Realize

variable (P : FullParams) (lay : KSLayout) (ℓ : ℕ)

/-- ModUp digit `j` of `d` (`Challenge.Realize.modUpDigit`), coefficient by coefficient. -/
def modUpA (d : Array ℤ) (j : ℕ) : Array ℤ :=
  mapA P.src.N (fun z => fbc (digitMods P lay ℓ j) (fun m => (z : ZMod m))) d

theorem ofArr_modUpA (d : Array ℤ) (j : ℕ) :
    (ofArr (modUpA P lay ℓ d j) : IntPoly P.src.N) = modUpDigit P lay ℓ (ofArr d) j := by
  rw [modUpA, ofArr_mapA]; rfl

/-- BGV ModDown (`Challenge.Realize.modDownBGV`), coefficient by coefficient. -/
def modDownA (X : Array ℤ) : Array ℤ :=
  mapA P.src.N (fun z => (z - (P.src.t : ℤ) *
      fbc (specialMods P) (fun p => (z : ZMod p) * (P.src.t : ZMod p)⁻¹)) /
    (specialProd P : ℤ)) X

theorem ofArr_modDownA (X : Array ℤ) :
    (ofArr (modDownA P X) : IntPoly P.src.N) = modDownBGV P (ofArr X) := by
  rw [modDownA, ofArr_mapA]; rfl

/-- The inner product `Σⱼ Dⱼ · kⱼ` from the ModUp digits `ups`. -/
def innerA (ups : Array (Array ℤ)) (k : ℕ → Array ℤ) : Array ℤ :=
  sumA P.src.N (List.ofFn fun j : Fin (lay.sizes ℓ).length => mulA P.src.N ups[j.val]! (k j))

theorem innerKey_def (d : IntPoly P.src.N) (k : ℕ → IntPoly P.src.N) :
    innerKey P lay ℓ d k =
      (List.ofFn fun j : Fin (lay.sizes ℓ).length => modUpDigit P lay ℓ d j * k j).sum := rfl

theorem ofArr_innerA (d : Array ℤ) (k : ℕ → Array ℤ) :
    (ofArr (innerA P lay ℓ (Array.ofFn (n := (lay.sizes ℓ).length) fun j => modUpA P lay ℓ d j) k)
        : IntPoly P.src.N) = innerKey P lay ℓ (ofArr d) (fun j => ofArr (k j)) := by
  rw [innerA, ofArr_sumA, innerKey_def, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  simp only [Function.comp, ofArr_mulA]
  rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn, ofArr_modUpA]

/-- **Hybrid key switching of one component** (`Challenge.Realize.ksOpenFHE`) on arrays. -/
def ksA (d : Array ℤ) (keys : List (Array ℤ × Array ℤ)) : Array ℤ × Array ℤ :=
  let ups := Array.ofFn (n := (lay.sizes ℓ).length) fun j => modUpA P lay ℓ d j
  (modDownA P (innerA P lay ℓ ups fun j => (keys.getD j (zeroA P.src.N, zeroA P.src.N)).1),
   modDownA P (innerA P lay ℓ ups fun j => (keys.getD j (zeroA P.src.N, zeroA P.src.N)).2))

theorem ksOpenFHE_def (d : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksOpenFHE P lay ℓ d keys =
      (modDownBGV P (innerKey P lay ℓ d fun j => (keys.getD j (0, 0)).1),
       modDownBGV P (innerKey P lay ℓ d fun j => (keys.getD j (0, 0)).2)) := rfl

/-- **`ksA` is `Challenge.Realize.ksOpenFHE`**, for all arrays and keys. -/
theorem ksA_eq (d : Array ℤ) (keys : List (Array ℤ × Array ℤ)) :
    ((ofArr (ksA P lay ℓ d keys).1 : IntPoly P.src.N), (ofArr (ksA P lay ℓ d keys).2 : IntPoly P.src.N)) =
      ksOpenFHE P lay ℓ (ofArr d) (wK P.src.N keys) := by
  rw [ksOpenFHE_def]
  simp only [ksA, ofArr_modDownA, ofArr_innerA, wK_getD]

/-- BGV relinearization (`Challenge.Realize.relinOpenFHE`) on arrays. -/
def relinA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) : List (Array ℤ) :=
  match ca with
  | [c0, c1, c2] =>
    let r := ksA P lay ℓ c2 keys
    [addA P.src.N c0 r.1, addA P.src.N c1 r.2]
  | _ => []

/-- BGV key switch of two components (`Challenge.Realize.keySwitchOpenFHE`) on arrays. -/
def keySwitchA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) : List (Array ℤ) :=
  match ca with
  | [c0, c1] =>
    let r := ksA P lay ℓ c1 keys
    [addA P.src.N c0 r.1, r.2]
  | _ => []

theorem wC_relinA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) :
    wC P.src.N (relinA P lay ℓ ca keys) = relinOpenFHE P lay ℓ (wC P.src.N ca) (wK P.src.N keys) := by
  have h := ksA_eq P lay ℓ
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, ca⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · show [ofArr (addA P.src.N c0 (ksA P lay ℓ c2 keys).1), ofArr (addA P.src.N c1 (ksA P lay ℓ c2 keys).2)] =
      [ofArr c0 + (ksOpenFHE P lay ℓ (ofArr c2) (wK P.src.N keys)).1,
       ofArr c1 + (ksOpenFHE P lay ℓ (ofArr c2) (wK P.src.N keys)).2]
    rw [← h]; simp
  · rfl

theorem wC_keySwitchA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) :
    wC P.src.N (keySwitchA P lay ℓ ca keys) =
      keySwitchOpenFHE P lay ℓ (wC P.src.N ca) (wK P.src.N keys) := by
  have h := ksA_eq P lay ℓ
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, ca⟩⟩⟩
  · rfl
  · rfl
  · show [ofArr (addA P.src.N c0 (ksA P lay ℓ c1 keys).1), ofArr (ksA P lay ℓ c1 keys).2] =
      [ofArr c0 + (ksOpenFHE P lay ℓ (ofArr c1) (wK P.src.N keys)).1,
       (ksOpenFHE P lay ℓ (ofArr c1) (wK P.src.N keys)).2]
    rw [← h]; simp
  · rfl

/-! ## BFV -/

open Challenge.RealizeBFV

/-- The centred residue modulo `q` (`Challenge.RealizeBFV.crtDigit`). -/
def crtDigitA (N : ℕ) (q : ℕ) (d : Array ℤ) : Array ℤ := mapA N (fun z : ℤ => ((z : ZMod q)).valMinAbs) d

theorem ofArr_crtDigitA {N : ℕ} (q : ℕ) (d : Array ℤ) :
    (ofArr (crtDigitA N q d) : IntPoly N) = crtDigit q (ofArr d) := by
  rw [crtDigitA, ofArr_mapA]; rfl

/-- BV key switching, digit size 0 (`Challenge.RealizeBFV.ksBV`), on arrays. -/
def ksBVA (d : Array ℤ) (keys : List (Array ℤ × Array ℤ)) : Array ℤ × Array ℤ :=
  let digs := Array.ofFn (n := ℓ) fun i => crtDigitA P.src.N (P.src.qs.getD i 0) d
  (sumA P.src.N (List.ofFn fun i : Fin ℓ =>
      mulA P.src.N digs[i.val]! (keys.getD i (zeroA P.src.N, zeroA P.src.N)).1),
   sumA P.src.N (List.ofFn fun i : Fin ℓ =>
      mulA P.src.N digs[i.val]! (keys.getD i (zeroA P.src.N, zeroA P.src.N)).2))

theorem ksBV_def (d : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksBV P ℓ d keys =
      ((List.ofFn fun i : Fin ℓ => crtDigit (P.src.qs.getD i 0) d * (keys.getD i (0, 0)).1).sum,
       (List.ofFn fun i : Fin ℓ => crtDigit (P.src.qs.getD i 0) d * (keys.getD i (0, 0)).2).sum) := rfl

theorem ksBVA_eq (d : Array ℤ) (keys : List (Array ℤ × Array ℤ)) :
    ((ofArr (ksBVA P ℓ d keys).1 : IntPoly P.src.N), (ofArr (ksBVA P ℓ d keys).2 : IntPoly P.src.N)) =
      ksBV P ℓ (ofArr d) (wK P.src.N keys) := by
  rw [ksBV_def]
  simp only [ksBVA, ofArr_sumA, List.map_ofFn, wK_getD]
  congr 2 <;>
  · apply List.ofFn_inj.mpr
    funext i
    simp only [Function.comp, ofArr_mulA]
    rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn, ofArr_crtDigitA]

/-- **OpenFHE's BFV key switching of one component** (`Challenge.RealizeBFV.ksBFV`) on arrays:
BV without special primes, HYBRID (`ksA` at plaintext modulus 1) with them. -/
def ksBFVA (d : Array ℤ) (keys : List (Array ℤ × Array ℤ)) : Array ℤ × Array ℤ :=
  if P.store.special = [] then ksBVA P ℓ d keys else ksA (BudgetBFV.unitPlain P) lay ℓ d keys

theorem ksBFV_def (d : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksBFV P lay ℓ d keys =
      if P.store.special = [] then ksBV P ℓ d keys
      else ksOpenFHE (BudgetBFV.unitPlain P) lay ℓ d keys := rfl

theorem ksBFVA_eq (d : Array ℤ) (keys : List (Array ℤ × Array ℤ)) :
    ((ofArr (ksBFVA P lay ℓ d keys).1 : IntPoly P.src.N), (ofArr (ksBFVA P lay ℓ d keys).2 : IntPoly P.src.N)) =
      ksBFV P lay ℓ (ofArr d) (wK P.src.N keys) := by
  rw [ksBFV_def]
  by_cases h : P.store.special = []
  · simp only [ksBFVA, h, ↓reduceIte]; exact ksBVA_eq P ℓ d keys
  · simp only [ksBFVA, h, ↓reduceIte]; exact ksA_eq (BudgetBFV.unitPlain P) lay ℓ d keys

/-- BFV relinearization (`Challenge.RealizeBFV.relinBFV`) on arrays. -/
def relinBFVA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) : List (Array ℤ) :=
  match ca with
  | [c0, c1, c2] =>
    let r := ksBFVA P lay ℓ c2 keys
    [addA P.src.N c0 r.1, addA P.src.N c1 r.2]
  | _ => []

/-- BFV key switch of two components (`Challenge.RealizeBFV.keySwitchBFV`) on arrays. -/
def keySwitchBFVA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) : List (Array ℤ) :=
  match ca with
  | [c0, c1] =>
    let r := ksBFVA P lay ℓ c1 keys
    [addA P.src.N c0 r.1, r.2]
  | _ => []

theorem wC_relinBFVA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) :
    wC P.src.N (relinBFVA P lay ℓ ca keys) = relinBFV P lay ℓ (wC P.src.N ca) (wK P.src.N keys) := by
  have h := ksBFVA_eq P lay ℓ
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, ca⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · show [ofArr (addA P.src.N c0 (ksBFVA P lay ℓ c2 keys).1), ofArr (addA P.src.N c1 (ksBFVA P lay ℓ c2 keys).2)] =
      [ofArr c0 + (ksBFV P lay ℓ (ofArr c2) (wK P.src.N keys)).1,
       ofArr c1 + (ksBFV P lay ℓ (ofArr c2) (wK P.src.N keys)).2]
    rw [← h]; simp
  · rfl

theorem wC_keySwitchBFVA (ca : List (Array ℤ)) (keys : List (Array ℤ × Array ℤ)) :
    wC P.src.N (keySwitchBFVA P lay ℓ ca keys) =
      keySwitchBFV P lay ℓ (wC P.src.N ca) (wK P.src.N keys) := by
  have h := ksBFVA_eq P lay ℓ
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, ca⟩⟩⟩
  · rfl
  · rfl
  · show [ofArr (addA P.src.N c0 (ksBFVA P lay ℓ c1 keys).1), ofArr (ksBFVA P lay ℓ c1 keys).2] =
      [ofArr c0 + (ksBFV P lay ℓ (ofArr c1) (wK P.src.N keys)).1,
       (ksBFV P lay ℓ (ofArr c1) (wK P.src.N keys)).2]
    rw [← h]; simp
  · rfl

end FHE.Ref
