import FHE.Check.Decode
import Spec.Encrypt

set_option autoImplicit false

/-!
# FHE.Check.Security — the security table, and moving a program to another ring dimension   (UNTRUSTED glue)

Shared by the report of a plain check (`FHE.Check.Report`: the security note, and the "smallest
fix" at `2N`) and by `fhe_check recommend` (`FHE.Check.Recommend`). Nothing here decides a
verdict:

* the security table is an INPUT ASSUMPTION (this project proves nothing about lattice security),
  printed as a note next to the verdict, never part of it;
* the input noise and the Galois elements at another ring dimension are UNVERIFIED GLUE used only
  by searches (suggestions, recommendations), whose results are re-checked or labelled.
-/

namespace FHE.Check
open Lean Spec Spec.Source

/-! ## The security table (INPUT ASSUMPTION, not proved here) -/

/-- Maximum `log₂ q` for the ternary secret distribution {−1, 0, 1}, classical security,
`(N, 128-bit, 192-bit, 256-bit)`. Source: the HomomorphicEncryption.org Security Standard
(M. Albrecht et al., "Homomorphic Encryption Security Standard", HomomorphicEncryption.org,
Toronto, November 2018), table for the ternary distribution, rows N = 1024 … 32768, as
transcribed in OpenFHE v1.3.1 `src/core/lib/lattice/stdlatticeparms.cpp:169-186`. The rows
N = 65536 and 131072 are NOT in the 2018 standard; they are OpenFHE's extension
(`stdlatticeparms.cpp:187-192`). This table is an input assumption: this project proves nothing
about lattice security. The cap is applied to `Q·P` (the largest modulus key switching uses), as
OpenFHE does (`bgvrns-parametergeneration.cpp:465-474`). -/
def secTable : List (Nat × Nat × Nat × Nat) :=
  [(1024, 27, 19, 14), (2048, 54, 37, 29), (4096, 109, 75, 58), (8192, 218, 152, 118),
   (16384, 438, 305, 237), (32768, 881, 611, 476),
   (65536, 1747, 1199, 929), (131072, 3523, 2411, 1866)]

/-- `true` for the rows taken from OpenFHE's extension rather than the 2018 standard. -/
def secRowIsExtension (N : Nat) : Bool := N ≥ 65536

def capOf (sec N : Nat) : Option Nat :=
  (secTable.find? (·.1 = N)).bind fun (_, a, b, c) =>
    if sec = 128 then some a else if sec = 192 then some b else if sec = 256 then some c else none

/-- HEIR's own 128-bit table (from ia.cr/2024/463; HEIR's `lib/Parameters/
RLWESecurityParams.cpp:11-14`). Printed for information only: HEIR does not apply it to a
`bgv.schemeParam` the user supplies (`GenerateParamBGV.cpp:146-149` returns early). -/
def heirTable128 : List (Nat × Nat) :=
  [(1024, 26), (2048, 53), (4096, 106), (8192, 214), (16384, 430), (32768, 868),
   (65536, 1747), (131072, 3523)]

/-- The citation printed with every security statement. -/
def secCitation : String :=
  "HomomorphicEncryption.org Security Standard (Albrecht et al., November 2018), ternary secret, classical security; as transcribed in OpenFHE stdlatticeparms.cpp"

/-- `Q·P`: every ciphertext limb (including an extra limb such as FLEXIBLEAUTOEXT's) and every
special prime. -/
def qpOf (P : FullParams) : Nat := P.src.qs.prod * (P.store.special.map (·.q)).prod

/-- Why the table has no row for `N`, or `none` if it has one. -/
def secNoEntry (N : Nat) : Option String :=
  if secTable.any (·.1 = N) then none
  else if N ≠ 2 ^ Nat.log2 N then
    some s!"no entry: N = {N} is not a power of two, and the standard tabulates only N = 1024 ... 32768 (OpenFHE's extension: 65536, 131072); no security level is stated for it"
  else if N < 1024 then
    some s!"no entry: N = {N} is below the standard's smallest ring dimension (1024); NOT secure per the standard (a toy or test parameter set)"
  else
    some s!"no entry: N = {N} is above the largest ring dimension tabulated (32768 in the 2018 standard, 131072 in OpenFHE's extension); no security level is stated for it"

/-- `log₂(Q·P)` against the 128-bit cap at `N`, in words (used by the "smallest fix"). -/
def capText128 (N qp : Nat) : String :=
  match capOf 128 N with
  | some cap =>
    if qp < 2 ^ cap then s!"log2(Q*P) = {fmt2 (log2F qp)} <= {cap}, the 128-bit cap at N = {N}{if secRowIsExtension N then " (OpenFHE's extension row)" else ""}"
    else s!"log2(Q*P) = {fmt2 (log2F qp)} > {cap}, ABOVE the 128-bit cap at N = {N}{if secRowIsExtension N then " (OpenFHE's extension row)" else ""}"
  | none => s!"log2(Q*P) = {fmt2 (log2F qp)}; the security table has {(secNoEntry N).getD "no entry"}"

/-! ## Rotations at another ring dimension (UNVERIFIED GLUE) -/

/-- `b^e mod m` by square-and-multiply. -/
def powModF (b e m : Nat) : Nat := Id.run do
  if m ≤ 1 then return 0
  let mut r := 1
  let mut x := b % m
  let mut k := e
  while k > 0 do
    if k % 2 == 1 then r := r * x % m
    x := x * x % m
    k := k / 2
  return r

/-- `(negated, e)` with `g ≡ ±5^e (mod 2N)`, `e < N/2` (the rotation group of `X^N + 1`). -/
def dlog5 (g N : Nat) : Option (Bool × Nat) := Id.run do
  let m := 2 * N
  let gm := g % m
  let mut x := 1
  for e in [0:N / 2 + 1] do
    if x == gm then return some (false, e)
    if (m - x) % m == gm then return some (true, e)
    x := x * 5 % m
  return none

/-- The Galois element of the same rotation at ring dimension `N'`: `±5^e mod 2N ↦ ±5^e mod 2N'`
(exact when `N' ≤ N`; when `N' > N` the smallest such `e` is used). UNVERIFIED GLUE: the
certificate is about the remapped program; the round trip re-extracts the library's own. -/
def remapG (g N N' : Nat) : Option Nat :=
  if N = N' then some g else
  (dlog5 g N).map fun (neg, e) =>
    let x := powModF 5 e (2 * N')
    if neg then (2 * N' - x) % (2 * N') else x

def remapInstr (N N' : Nat) : Instr → Option Instr
  | .automorph d a g => (remapG g N N').map (.automorph d a ·)
  | i => some i

def remapProg (prog : Program) (N N' : Nat) : Option Program := do
  let body ← prog.body.mapM (remapInstr N N')
  let inputs ← prog.inputs.mapM fun d => (remapG d.key N N').map fun k => { d with key := k }
  pure { prog with body, inputs }

/-! ## Input noise at another ring dimension (UNVERIFIED GLUE) -/

/-- The frontend's input noise moved to ring dimension `N'`, for a file that describes its fresh
encryptions (`freshEncryption`): `Spec.Encrypt.freshNoise t (Spec.Encrypt.worstError N' …)` from
the file's own sampler bounds (verified functions; the formula is the OpenFHE extractor's), plus
the excess of the file's value over that formula at its own `N`, if any. `none` without a
`freshEncryption` section. -/
def freshNoiseAt (inp : Input) (N' : Nat) : Option Nat := do
  let P := inp.P
  if N' = P.src.N then return P.inputNoise
  let fm ← inp.fresh
  let w := fun (N : Nat) => Encrypt.freshNoise P.src.t (fm.bp P.src.t) (Encrypt.worstError N P.secretBound fm.keyError fm.u fm.e1 fm.e2)
  return w N' + (P.inputNoise - w P.src.N)

end FHE.Check
