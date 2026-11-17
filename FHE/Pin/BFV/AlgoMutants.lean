import FHE.Pin.BFV.Fast

/-!
# FHE.Pin.BFV.AlgoMutants — convention mutants of the BFV algorithm-level comparison
(UNTRUSTED, test-only)

Each mutant perturbs **one** convention of the mirrored BFV routines; the comparison with
OpenFHE's recorded outputs must then fail (`harness/openfhe-pin/algo/mutation_bfv.sh`). The
key-switching mutants shared with BGV (`FHE.Pin.Algo.AMut`: `modup-centred`, `moddown-centred`,
`moddown-add`, `ks-all-centred`, `digit-boundary`, `automorph-first`) apply to BFV's HYBRID key
switch unchanged and are selected by the same names.
-/

namespace FHE.Pin.BFV

/-- How the plaintext is scaled by `Q/t`. -/
inductive QOverT
  /-- OpenFHE `TimesQovert`: `⌈Q·p/t⌉` -/
  | ceil
  /-- `⌊Q·p/t⌉` (`Challenge.BFVMul.scaleUp`) -/
  | round
  /-- `⌊Q·p/t⌋` -/
  | floor
  /-- `⌊Q/t⌋·p` (`Challenge.BFV.bfvAddPlain`) -/
  | delta
  deriving DecidableEq, Inhabited

/-- The active mutant. -/
structure AlgoMut where
  name : String := "none"
  /-- the other contraction choice for `s += a * b` -/
  flipFma : Bool := false
  exactSw : Bool := false
  exactSr : Bool := false
  swNoHalf : Bool := false
  srNoHalf : Bool := false
  fastCentred : Bool := false
  behzNoMont : Bool := false
  behzNoSK : Bool := false
  behzSKCanon : Bool := false
  /-- the auxiliary primes in reverse order -/
  auxReversed : Bool := false
  /-- P-over-Q: the operand expanded exactly and the one scaled by `P/Q` exchanged -/
  rolesSwapped : Bool := false
  /-- HPSPOVERQLEVELED: the internal drop of the multiplication ignored -/
  mulDropIgnored : Bool := false
  /-- HPSPOVERQLEVELED: the internal drop of the key switch ignored -/
  ksDropIgnored : Bool := false
  /-- HYBRID ModDown with BGV's `t`-correction (the plaintext modulus instead of 1) -/
  ksWithT : Bool := false
  /-- the automorphism over `Q·P` before ModDown (BGV's order in v1.6.1) -/
  autoBeforeModDown : Bool := false
  /-- BV: the RNS digits lifted canonically, not centred -/
  bvCanon : Bool := false
  /-- BV with `digitSizeBV > 0`: plain unsigned windows instead of balanced digits -/
  bvUnbalanced : Bool := false
  qovert : QOverT := .ceil
  /-- `DropLastElementAndScale` with the canonical last limb (floor instead of round) -/
  compressFloor : Bool := false
  /-- Decryption after `Compress`: `MultiplyAndRound` exact instead of in `double` -/
  decryptExactScale : Bool := false
  deriving Inhabited

def AlgoMut.all : List AlgoMut :=
  [{ name := "float-fma-flipped", flipFma := true },
   { name := "sw-exact", exactSw := true },
   { name := "sr-exact", exactSr := true },
   { name := "sw-no-half", swNoHalf := true },
   { name := "sr-floor", srNoHalf := true },
   { name := "poverq-centred-digits", fastCentred := true },
   { name := "behz-no-montgomery", behzNoMont := true },
   { name := "behz-no-sk", behzNoSK := true },
   { name := "behz-sk-canonical", behzSKCanon := true },
   { name := "aux-order", auxReversed := true },
   { name := "poverq-roles", rolesSwapped := true },
   { name := "leveled-mul-drop-ignored", mulDropIgnored := true },
   { name := "leveled-ks-drop-ignored", ksDropIgnored := true },
   { name := "ks-moddown-t", ksWithT := true },
   { name := "automorph-before-moddown", autoBeforeModDown := true },
   { name := "bv-digits-canonical", bvCanon := true },
   { name := "bv-digits-unbalanced", bvUnbalanced := true },
   { name := "timesqovert-round", qovert := .round },
   { name := "timesqovert-floor", qovert := .floor },
   { name := "timesqovert-delta", qovert := .delta },
   { name := "compress-floor", compressFloor := true },
   { name := "decrypt-small-exact-scale", decryptExactScale := true }]

def AlgoMut.ofString? (s : String) : Option AlgoMut :=
  if s == "none" then some {} else AlgoMut.all.find? (·.name == s)

def AlgoMut.isNone (m : AlgoMut) : Bool := m.name == "none"

/-- The conventions of the float routines under the mutant, for a build with contraction
`fmaBuild`. -/
def AlgoMut.cv (m : AlgoMut) (fmaBuild : Bool) : Conv :=
  { fma := if m.flipFma then !fmaBuild else fmaBuild
    exactSw := m.exactSw, exactSr := m.exactSr, swNoHalf := m.swNoHalf, srNoHalf := m.srNoHalf
    fastCentred := m.fastCentred, behzNoMont := m.behzNoMont, behzNoSK := m.behzNoSK
    behzSKCanon := m.behzSKCanon }

end FHE.Pin.BFV
