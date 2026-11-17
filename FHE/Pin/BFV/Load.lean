import FHE.Pin.Core
import FHE.Pin.BFV.Mutants
import FHE.Pin.BFV.Keys
import FHE.Check.BFVReport

/-!
# FHE.Pin.BFV.Load — a BFV case of `openfhe_pin`: decoding and the per-case context
(UNTRUSTED glue)

A case whose `pin.json` has `"scheme": "BFV"` (`harness/openfhe-pin/FORMAT.md`, "BFV cases"). The
case directory is read by the shared loader `FHE.Pin.loadCase`; `prog.fhecheck.json` is decoded
here by `FHE.Check.BFV.decode`, the decoder of `fhe_check`, and turned into the input of the
locked decision by `FHE.Check.BFV.inputBFV`, exactly as `fhe_check` does
(`FHE.Check.BFV.runCheck`).
-/

namespace FHE.Pin.BFV
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source FHE.Pin

/-- The documented support bound of OpenFHE's error sampler (the extractor's `errorBound`). -/
def gaussBound : Nat := 39

/-- Decode `prog.fhecheck.json` of a BFV case (`Json.null`: the shared loader could not parse
it). -/
def decodeProg (c : Case) : Except String FHE.Check.BFV.Input :=
  if c.progJson.isNull then .error "prog.fhecheck.json is missing or malformed"
  else if (jStr? c.progJson "error").isSome then .error "extractor refusal"
  else if !FHE.Check.BFV.isBFV c.progJson then .error "prog.fhecheck.json: params.scheme is not BFV"
  else
    match FHE.Check.BFV.decode c.progJson with
    | .error e => .error s!"prog.fhecheck.json: {e}"
    | .ok (.unsupported what idx why) => .error s!"prog.fhecheck.json: unsupported {what} {idx}: {why}"
    | .ok (.ok inp) => .ok inp

/-- Per-case context of the BFV checks. `x` is the shared context (forced phases, objects); its
mutant is the shared-primitive part of `mu`. -/
structure BX where
  x : Cx
  mu : BMut
  /-- `pin.json: bfv.mult`, `bfv.ks`, `bfv.enc`. -/
  mult : String
  ks : String
  enc : String
  inp : Except String FHE.Check.BFV.Input
  /-- Whether the parameters come from the program file (`false`: extractor refusal, the
  fallback parameters with the extractor's documented `inputNoise` formula). -/
  declared : Bool
  /-- Failures of `e.step`, `f.bound`, `c.input` (for `f.certified-consistent`). -/
  stepFail : IO.Ref Nat
  boundFail : IO.Ref Nat
  inputFail : IO.Ref Nat
  /-- The measured noise of an object for the message the program computes (set by the program
  replay for every variable under `s` that has an object; read by `a.decrypt`). -/
  objNoise : IO.Ref (Std.HashMap String Nat)

namespace BX

abbrev c (b : BX) : Case := b.x.c
abbrev P (b : BX) : FullParams := b.x.P
abbrev N (b : BX) : Nat := b.x.P.src.N
abbrev t (b : BX) : Nat := b.x.P.src.t
def K (b : BX) : Nat := b.x.o.K
def s (b : BX) : Array Int := b.x.s
def want (b : BX) (g : String) : Bool := b.x.want g
def bfvJ (b : BX) : Json := (jObj? b.c.pin "bfv").getD Json.null

/-- Whether the library's secret distribution (`pin.json: bfv.secretKeyDist`) is ternary
(`UNIFORM_TERNARY`, `SPARSE_TERNARY`, or not recorded); otherwise it is `GAUSSIAN`. -/
def ternarySecret (b : BX) : Bool :=
  match jStr? b.bfvJ "secretKeyDist" with
  | some d => d != "GAUSSIAN"
  | none => true

/-- The declared bound of the samples of the secret-key distribution: the secret itself and the
ephemeral `u` of an encryption (`1` ternary; the Gaussian bound for a `GAUSSIAN` secret, for which
the library also draws `u` from the Gaussian sampler, `rns-pke.cpp:152-200`). -/
def secretDistBound (b : BX) : Nat := if b.ternarySecret then 1 else gaussBound

/-- Append a result line; every BFV line carries the scheme, the two techniques and `N`. -/
def emit (b : BX) (check id op : String) (ok : Option Bool) (impl : String)
    (extra : List (String × Json) := []) : IO Unit := do
  let base : List (String × Json) :=
    [("case", Json.str b.c.name), ("check", Json.str check), ("id", Json.str id),
     ("op", Json.str op), ("ok", optBoolJ ok), ("impl", Json.str impl),
     ("scheme", Json.str "BFV"), ("mult", Json.str b.mult), ("ks", Json.str b.ks),
     ("enc", Json.str b.enc), ("N", Json.num b.c.N), ("suite", Json.str b.c.generator),
     ("arbitrary", Json.bool (jBool b.c.pin "inputsArbitrary"))]
  let base := if b.mu.isNone then base else base ++ [("mutate", Json.str b.mu.name)]
  b.x.out.modify (·.push (Json.mkObj (base ++ extra)))

/-- OpenFHE's raw `Decrypt` output: a line with modulus `t` (residues), or an exact (modulus-0)
line with values in `[0, t]` (`"rawReduced": false`: BEHZ may return `t` itself). Returns the
values reduced modulo `t` and the number of coefficients equal to `t`. -/
def rawDec (b : BX) (nm : String) : IO (Array Int × Nat) := do
  let t := b.P.src.t
  let some e := b.c.polys[nm]? | throw (IO.userError s!"polys.txt has no entry {nm}")
  if e.moduli != #[t] && e.moduli != #[0] then
    throw (IO.userError s!"{nm}: modulus {e.moduli.toList} is neither [{t}] nor [0]")
  let v := e.limbs[0]!
  if v.any fun x => x < 0 || x > (t : Int) then
    throw (IO.userError s!"{nm}: a value outside [0, t]")
  return (v.map (· % (t : Int)), v.foldl (fun n x => if x == (t : Int) then n + 1 else n) 0)

/-- Whether the literal trusted definitions are also run (never with a mutant). -/
def literal (b : BX) (parts : Nat) : Bool := b.mu.isNone && b.x.literal parts

end BX

/-- A JSON number for a float at full precision (`null` if not finite). -/
def floatJ (f : Float) : Json :=
  match JsonNumber.fromFloat? f with
  | .inr n => Json.num n
  | .inl _ => Json.null

/-- `⌈a / b⌉` for printing. -/
def cdiv (a b : Nat) : Nat := if b = 0 then 0 else (a + b - 1) / b

/-- `log₂(bound / measured)` (bits of slack; `null` if `measured = 0`). -/
def slackJ (measured bound : Nat) : Json :=
  if measured = 0 || bound = 0 then Json.null
  else FHE.Check.jsonF (FHE.Check.log2F bound - FHE.Check.log2F measured)

def measuredBound (measured bound : Nat) : List (String × Json) :=
  [("measured", natJ measured), ("bound", natJ bound), ("measuredBits", bitsJ measured),
   ("boundBits", bitsJ bound), ("slackBits", slackJ measured bound)]

/-- The extractor's documented `inputNoise` (`harness/frontend/README.md`, "BFV extraction";
`extract_bfv.py: noise_inputs`), for a case it refused: STANDARD
`Be·(1 + 2N) + max_ℓ ⌈(Q_ℓ mod t)(t−1)/t⌉`; EXTENDED
`⌊max_ℓ (Q_ℓ mod t)(t−1)/t + (t−1)/(t·p) + Be(1+2N)/p + (p−1)(1+N)/(2p)⌋`, `ℓ` over the given
numbers of limbs. -/
def extractorInputNoise (N t : Nat) (qs : List Nat) (levels : List Nat) (extPrime : Nat) : Nat :=
  let Be := gaussBound
  let E := Be * (1 + 2 * N)
  let rs := levels.map fun ℓ => (qs.take ℓ).prod % t
  let rmax := rs.foldl max 0
  if extPrime ≤ 1 then E + cdiv (rmax * (t - 1)) t
  else
    let p := extPrime
    (2 * p * rmax * (t - 1) + 2 * (t - 1) + 2 * t * E + t * (p - 1) * (1 + N)) / (2 * t * p)

/-- The stored plaintext polynomial of a plaintext object: the centred lift over its own limbs,
and its message (that polynomial modulo `t`). -/
def storedPlain (b : BX) (ptId : String) : IO (Array Int × Array (ZMod b.P.src.t) × Nat) := do
  let some pj := b.c.object? ptId | throw (IO.userError s!"pin.json has no object {ptId}")
  let some pn := jStr? pj "poly" | throw (IO.userError s!"{ptId}: poly")
  let (pm, v) ← liftExcept (b.c.rnsPolyAny pn)
  let vc := centredA b.N b.K .none (pm.foldl (· * ·) 1) v
  pure (vc, toArr b.K (ofInt b.P.src.t (ofArr (N := b.P.src.N) vc)), pm.length)

end FHE.Pin.BFV
