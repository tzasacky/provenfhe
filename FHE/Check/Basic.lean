import Lean.Data.Json

set_option autoImplicit false

/-!
# FHE.Check.Basic — number formatting and JSON field access for `fhe_check`   (UNTRUSTED glue)

Nothing here decides a verdict. `log2` is for *printing* margins; every comparison the verdict
depends on is done by the verified definitions on exact natural numbers.
-/

namespace FHE.Check
open Lean

/-- `log₂ x` as a float, accurate for arbitrarily large `x` (no overflow past `2^1024`): the top
53 bits through `Float`, the rest as an exponent. `-inf` for `0`. -/
def log2F (x : Nat) : Float :=
  if x = 0 then -(1.0 / 0.0) else
  let n := Nat.log2 x
  if n < 53 then (Float.ofNat x).log2
  else (Float.ofNat (x >>> (n - 52))).log2 + Float.ofNat (n - 52)

/-- A float with two decimals (`inf`, `-inf` spelled out). -/
def fmt2 (f : Float) : String :=
  if f.isNaN then "nan" else if f.isInf then (if f > 0 then "inf" else "-inf") else
  let r := (f * 100).round
  let neg := r < 0
  let a := (if neg then -r else r).toUInt64.toNat
  let s := s!"{a / 100}.{if a % 100 < 10 then "0" else ""}{a % 100}"
  if neg && a ≠ 0 then "-" ++ s else s

/-- The declared input bounds as the report prints them: all of them up to 20; beyond that the
first 20 and how many more (a program with 10^5 plaintext inputs would otherwise print a line of
megabytes). The bounds themselves are in the input file; the certificate covers all of them. -/
def boundsList (bounds : List (String × Nat)) : String :=
  let shown := (bounds.take 20).map fun (x, b) => s!"{x} <= {b}"
  if bounds.length ≤ 20 then String.intercalate ", " shown
  else String.intercalate ", " shown ++ s!", and {bounds.length - 20} more, as declared in the input file"

/-- `2^x.xx` for a natural number (`0` for zero). -/
def pow2 (x : Nat) : String := if x = 0 then "0" else s!"2^{fmt2 (log2F x)}"

/-- A JSON number for a float rounded to two decimals (`null` if not finite). -/
def jsonF (f : Float) : Json :=
  if f.isNaN || f.isInf then Json.null else
  match JsonNumber.fromFloat? ((f * 100).round / 100) with
  | .inr n => Json.num n
  | .inl _ => Json.null

/-! ### Field access with error paths -/

abbrev DecodeM := Except String

/-- Largest input file read (bytes): checked on the file's size before it is read, and again by
`lexCheck`. Decoding is linear: the 615 MB extraction of a 2.18M-instruction OpenFHE program
(about 280 bytes per instruction) decodes in about 60 s with 4.5 GB resident memory, after which
the instruction limit (`FHE.Check.defaultMaxInstructions`) answers UNSUPPORTED with an estimate (a resource guard: the check is near-linear);
so files up to 1 GB get that informative answer instead of a refusal on size. -/
def maxInputBytes : Nat := 1024 * 1024 * 1024

/-- Longest number accepted, in characters (JSON number token) or digits (decimal string):
enough for any modulus, bound or product of this format (`10^400 > 2^1328`). -/
def maxNumberChars : Nat := 400

/-- Deepest nesting of arrays and objects accepted. -/
def maxDepth : Nat := 64

/-- A lexical scan of the raw input *before* it is given to the JSON parser, so that no input
can make the tool compute for long or exhaust the stack: number tokens are at most
`maxNumberChars` characters and have no positive exponent (the JSON parser would otherwise
evaluate `1e400000` as a big integer, and would hand `2e5` to the decoder as the integer 200000);
a negative exponent (a small float in a printed-only field) has at most 3 digits; and the
nesting depth is at most `maxDepth`. It does not
validate JSON; the parser does. -/
def lexCheck (text : String) : Except String Unit :=
  let bytes := text.toUTF8
  if bytes.size > maxInputBytes then
    .error s!"the input is larger than {maxInputBytes} bytes"
  else lexLoop bytes 0 false false 0 0 false false 0
where
  /-- The scan, one byte at a time, as a tail-recursive loop over unboxed state (a `for` loop with
  this many mutable variables allocates per byte: 18 MB took 5 s). -/
  lexLoop (bytes : ByteArray) (i : Nat) (inStr esc : Bool) (depth numLen : Nat) (inExp expNeg : Bool)
      (expDigits : Nat) : Except String Unit :=
    if h : i < bytes.size then
      let b := bytes[i]
      if inStr then
        if esc then lexLoop bytes (i + 1) true false depth numLen inExp expNeg expDigits
        else if b == 92 then lexLoop bytes (i + 1) true true depth numLen inExp expNeg expDigits   -- backslash
        else if b == 34 then lexLoop bytes (i + 1) false false depth numLen inExp expNeg expDigits -- closing quote
        else lexLoop bytes (i + 1) true false depth numLen inExp expNeg expDigits
      else
        let isDigit := 48 ≤ b && b ≤ 57
        let isNum := isDigit || b == 43 || b == 45 || b == 46 || b == 69 || b == 101  -- + - . E e
        if isNum then
          let numLen := numLen + 1
          let isE := b == 69 || b == 101
          let inExp' := inExp || isE
          let expNeg' := if !isE && inExp && b == 45 then true else expNeg
          let expDigit := !isE && !(inExp && b == 45) && inExp && (isDigit || b == 43)
          if expDigit && !expNeg then
            .error "a number is written with an exponent (integers must be written out in full; big integers as decimal strings)"
          else
          let expDigits := if expDigit then expDigits + 1 else expDigits
          if numLen > maxNumberChars then
            .error s!"a number token is longer than {maxNumberChars} characters (big integers are decimal strings of at most {maxNumberChars} digits)"
          else if expDigits > 3 then
            .error "a number has a negative exponent of more than 3 digits"
          else lexLoop bytes (i + 1) false esc depth numLen inExp' expNeg' expDigits
        else
          if b == 34 then lexLoop bytes (i + 1) true esc depth 0 false false 0
          else if b == 91 || b == 123 then          -- [ {
            if depth + 1 > maxDepth then .error s!"arrays/objects are nested more than {maxDepth} deep"
            else lexLoop bytes (i + 1) false esc (depth + 1) 0 false false 0
          else if b == 93 || b == 125 then lexLoop bytes (i + 1) false esc (depth - 1) 0 false false 0
          else lexLoop bytes (i + 1) false esc depth 0 false false 0
    else .ok ()
  termination_by bytes.size - i

def field (ctx : String) (j : Json) (k : String) : DecodeM Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"{ctx}: missing field \"{k}\""

def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok Json.null => none
  | .ok v => some v
  | .error _ => none

def asStr (ctx : String) (j : Json) : DecodeM String :=
  match j with
  | .str s => pure s
  | _ => throw s!"{ctx}: expected a string"

/-- A natural number given as a decimal string (`"123"`) or as a non-negative JSON integer. Big
integers must be strings in the format; small ones may be numbers. -/
def asNat (ctx : String) (j : Json) : DecodeM Nat :=
  match j with
  | .str s =>
    if s.length > maxNumberChars then
      throw s!"{ctx}: a number of {s.length} characters (at most {maxNumberChars} digits are accepted)"
    else if !s.isEmpty && s.all Char.isDigit then pure s.toNat! else
      throw s!"{ctx}: \"{s}\" is not a decimal natural number"
  | .num n =>
    if n.exponent = 0 && n.mantissa ≥ 0 then pure n.mantissa.toNat else
      throw s!"{ctx}: {n} is not a natural number"
  | _ => throw s!"{ctx}: expected a natural number (decimal string)"

/-- An integer given as a decimal string (optionally signed) or a JSON integer. -/
def asInt (ctx : String) (j : Json) : DecodeM Int :=
  match j with
  | .str s =>
    let (neg, d) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
    if s.length > maxNumberChars + 1 then
      throw s!"{ctx}: a number of {s.length} characters (at most {maxNumberChars} digits are accepted)"
    else if !d.isEmpty && d.all Char.isDigit then pure (if neg then -(d.toNat! : Int) else d.toNat!)
    else throw s!"{ctx}: \"{s}\" is not a decimal integer"
  | .num n =>
    if n.exponent = 0 then pure n.mantissa else throw s!"{ctx}: {n} is not an integer"
  | _ => throw s!"{ctx}: expected an integer"

def asArr (ctx : String) (j : Json) : DecodeM (Array Json) :=
  match j with
  | .arr a => pure a
  | _ => throw s!"{ctx}: expected an array"

def natField (ctx : String) (j : Json) (k : String) : DecodeM Nat := do
  asNat s!"{ctx}.{k}" (← field ctx j k)

def strField (ctx : String) (j : Json) (k : String) : DecodeM String := do
  asStr s!"{ctx}.{k}" (← field ctx j k)

end FHE.Check
