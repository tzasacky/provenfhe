import FHE.Pin.BFV.Fast

/-!
# FHE.Pin.BFV.NTT — OpenFHE's evaluation representation   (UNTRUSTED glue)

OpenFHE keeps a polynomial either in coefficient or in evaluation representation
(`Format::COEFFICIENT` / `EVALUATION`); the dumps hold coefficient vectors only. The evaluation
representation is needed here for one purpose: to reproduce what the library computes when it
adds (or multiplies) vectors held in *different* representations, which v1.6.1's BFV does for the
components of an un-relinearised product (`FHE.Pin.BFV.Algo`, "mixed representations").

`nttF ψ q a` is the vector `j ↦ a(ψ^{2·brv(j)+1})` (`brv`: bit reversal on `log₂ N` bits) with `ψ`
the **minimum** primitive `2N`-th root of unity modulo `q` (`minRoot`; OpenFHE `RootOfUnity`,
`core/include/math/nbtheory-impl.h:190-236`). That this is OpenFHE's ordering is an observation
confirmed by the data (the mixed sums are reproduced bit for bit), not a reading of its NTT code.
-/

namespace FHE.Pin.BFV

def powModN (b e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := b % m
  let mut e := e
  for _ in [0:256] do
    if e == 0 then break
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

def bitRev (bits x : Nat) : Nat := (List.range bits).foldl (fun acc i => acc * 2 + ((x >>> i) % 2)) 0

/-- The minimum primitive `2N`-th root of unity modulo `q` (`0` if none is found). -/
def minRoot (N q : Nat) : Nat := Id.run do
  if N == 0 || q < 3 || (q - 1) % (2 * N) != 0 then return 0
  let mut r := 0
  for g in [2:400] do
    let c := powModN g ((q - 1) / (2 * N)) q
    if powModN c N q == q - 1 then
      r := c
      break
  if r == 0 then return 0
  let r2 := r * r % q
  let mut x := r
  let mut best := r
  for _ in [1:N] do
    x := x * r2 % q
    if x < best then best := x
  return best

/-- `ψ^{brv(k)}` for `k < N`. -/
def psiTable (psi q N : Nat) : Array Nat := Id.run do
  let lg := Nat.log2 N
  let mut pw := Array.mkEmpty N
  let mut x := 1 % q
  for _ in [0:N] do
    pw := pw.push x
    x := x * psi % q
  return (Array.range N).map fun k => pw[bitRev lg k]!

/-- Forward negacyclic transform: `j ↦ a(ψ^{2·brv(j)+1})`. -/
def nttF (psi q : Nat) (a : Limb) : Limb := Id.run do
  let N := a.size
  let lg := Nat.log2 N
  let tab := psiTable psi q N
  let mut a := a
  let mut t := N
  let mut m := 1
  for _ in [0:lg] do
    t := t / 2
    for i in [0:m] do
      let j1 := 2 * i * t
      let S := tab[m + i]!
      for j in [j1:j1 + t] do
        let U := a[j]!
        let V := a[j + t]! * S % q
        a := a.set! j ((U + V) % q)
        a := a.set! (j + t) ((U + q - V) % q)
    m := m * 2
  return a

/-- Inverse of `nttF`. -/
def inttF (psi q : Nat) (a : Limb) : Limb := Id.run do
  let N := a.size
  let lg := Nat.log2 N
  let tab := psiTable (inv psi q) q N
  let mut a := a
  let mut t := 1
  let mut m := N
  for _ in [0:lg] do
    let h := m / 2
    for i in [0:h] do
      let j1 := 2 * i * t
      let S := tab[h + i]!
      for j in [j1:j1 + t] do
        let U := a[j]!
        let V := a[j + t]!
        a := a.set! j ((U + V) % q)
        a := a.set! (j + t) ((U + q - V) * S % q)
    t := t * 2
    m := h
  let ni := inv N q
  return a.map fun v => v * ni % q

/-- The transform by its definition (reference for `nttF`). -/
def nttNaive (psi q : Nat) (a : Limb) : Limb :=
  let N := a.size
  let lg := Nat.log2 N
  (Array.range N).map fun j =>
    let x := powModN psi (2 * bitRev lg j + 1) q
    (Array.range N).foldl (fun acc i => (acc + a[i]! * powModN x i q) % q) 0

-- N = 8, q = 17 (ψ = 3 is the minimum primitive 16th root), q = 97
#guard minRoot 8 17 == 3 && minRoot 8 97 == 8
#guard nttF 3 17 #[1, 2, 3, 4, 5, 6, 7, 8] == nttNaive 3 17 #[1, 2, 3, 4, 5, 6, 7, 8]
#guard inttF 3 17 (nttF 3 17 #[1, 2, 3, 4, 5, 6, 7, 8]) == #[1, 2, 3, 4, 5, 6, 7, 8]
#guard nttF 8 97 #[5, 0, 96, 1, 2, 3, 50, 7] == nttNaive 8 97 #[5, 0, 96, 1, 2, 3, 50, 7]
#guard inttF 8 97 (nttF 8 97 #[5, 0, 96, 1, 2, 3, 50, 7]) == #[5, 0, 96, 1, 2, 3, 50, 7]
-- the transform is multiplicative for the negacyclic product
#guard nttF 8 97 (mulNegSchool 97 #[5, 0, 96, 1, 2, 3, 50, 7] #[9, 8, 7, 6, 5, 4, 3, 2])
  == (Array.zipWith (fun x y => x * y % 97) (nttF 8 97 #[5, 0, 96, 1, 2, 3, 50, 7]) (nttF 8 97 #[9, 8, 7, 6, 5, 4, 3, 2]))
#guard mulNeg 97 #[5, 0, 96, 1, 2, 3, 50, 7] #[9, 8, 7, 6, 5, 4, 3, 2]
  == mulNegSchool 97 #[5, 0, 96, 1, 2, 3, 50, 7] #[9, 8, 7, 6, 5, 4, 3, 2]

end FHE.Pin.BFV
