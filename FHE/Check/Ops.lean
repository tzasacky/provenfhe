import FHE.Check.Basic
import Spec.Source

/-!
# FHE.Check.Ops — the operation table of the neutral format   (UNTRUSTED glue)

**SWITCH-OVER POINT 2 (operation table).** This file is the only place that maps an operation
name of the `fhe-check/v1` format to a `Spec.Source.Instr`. Operations `Spec.Source` does not
have are decoded to `.unsupported`, so the tool answers UNSUPPORTED with the operation named
instead of guessing a meaning. (`addPlain`, `subPlain`, `mulPlain`, `dropLimbs` were switched
over when `Spec/Source.lean` gained them; their plaintext bounds go to `Program.bounds`,
SWITCH-OVER POINT 2b in `FHE.Check.Decode`.)

A wrong entry here can only make `fhe_check` certify a different program than the frontend
meant; the certificate is always about the decoded `Source.Program`, which `--dump-program`
prints.
-/

namespace FHE.Check
open Lean Spec.Source

/-- Result of decoding one instruction. -/
inductive OpDecode
  | ok (i : Instr)
  /-- A known or unknown operation outside the certified operation set. -/
  | unsupported (op why : String)

/-- The operations `fhe_check` certifies today, for `--help` and the report. -/
def supportedOps : List String :=
  ["add", "sub", "mul", "square", "mulConst", "negate", "copy", "toEval", "toCoeff", "relin",
   "keySwitch", "automorph", "modSwitch", "addPlain", "subPlain", "mulPlain", "dropLimbs"]

/-- Operations of the format that are not (yet) `Source` operations. -/
def pendingOps : List String := []

/-- Decode one body instruction (`ctx` is its JSON path, for error messages). Malformed fields
are errors; unknown or uncertified operation names are `.unsupported`. -/
def decodeInstr (ctx : String) (j : Json) : DecodeM OpDecode := do
  let op ← strField ctx j "op"
  let dst ← strField ctx j "dst"
  let a ← strField ctx j "a"
  let b := fun (_ : Unit) => strField ctx j "b"
  match op with
  | "add" => return .ok (.add dst a (← b ()))
  | "sub" => return .ok (.sub dst a (← b ()))
  | "mul" => return .ok (.mul dst a (← b ()))
  | "square" => return .ok (.square dst a)
  | "mulConst" => return .ok (.mulConst dst a (← asInt s!"{ctx}.c" (← field ctx j "c")))
  | "negate" => return .ok (.mulConst dst a (-1))
  | "copy" => return .ok (.copy dst a)
  | "toEval" => return .ok (.toEval dst a)
  | "toCoeff" => return .ok (.toCoeff dst a)
  | "relin" => return .ok (.relin dst a)
  | "keySwitch" => return .ok (.keySwitch dst a)
  | "automorph" => return .ok (.automorph dst a (← natField ctx j "g"))
  | "modSwitch" => return .ok (.modSwitch dst a)
  -- SWITCH-OVER POINT 2 (done): plaintext operations and dropLimbs are `Source` operations.
  | "addPlain" => return .ok (.addPlain dst a (← strField ctx j "p"))
  | "subPlain" => return .ok (.subPlain dst a (← strField ctx j "p"))
  | "mulPlain" => return .ok (.mulPlain dst a (← strField ctx j "p"))
  | "dropLimbs" => return .ok (.dropLimbs dst a (← natField ctx j "k"))
  | "rescale" => return .unsupported op "rescale is not an operation of the BGV or BFV programs this tool covers"
  | _ => return .unsupported op "unknown operation"

end FHE.Check
