import Spec.Correct

/-!
# Spec.Decrypt — BGV decryption as the libraries do it: switch the phase to one limb   (TRUSTED)

`Spec.Scheme.bgvDecrypt` is textbook decryption at the ciphertext's own level: `[[⟨ct, s⟩]_Q]_t`.
OpenFHE's `PKEBGVRNS::Decrypt` (`src/pke/lib/scheme/bgvrns/bgvrns-pke.cpp:44-99`, the branch taken
after any homomorphic operation) does something else: it computes the phase `b = ⟨ct, s⟩ mod Q_ℓ`,
then modulus-switches the *phase polynomial* down to one limb (`DCRTPoly::ModReduce`, the
t-corrected switch: `δ = t·[−b·t⁻¹]_{q_last}` with the centred representative, then
`(b + δ)/q_last`), and reads the centred residue modulo `q₀` modulo `t`. Each switch multiplies
the message by `q_last⁻¹ mod t`, which the library tracks in the ciphertext's scaling factor.

This file defines that decryption (`bgvDecryptSwitched`), the factor (`decScale`), and a bound on
the switched phase computed from a bound on the phase at the output's level (`decBound`). The
phase is one polynomial: its switch adds at most `t·⌊q/2⌋/q ≤ t/2` per dropped limb and has no
secret-dependent term. `Challenge.Decrypt` pins that whenever `decryptOK?` holds, the switched
decryption of a ciphertext that `Encrypts` a message returns that message times `decScale`.
-/

namespace Spec.Decrypt
open NPoly Scheme Source

variable {N : ℕ}

/-- One t-corrected modulus switch of an integer polynomial by the prime `q`: `(c + δ) / q` with
`δ = t·[−c·t⁻¹]_q`, the bracket being the centred representative, so that `q ∣ c + δ` and
`t ∣ δ`. -/
def switchPhase (t q : ℕ) (c : IntPoly N) : IntPoly N :=
  ⟨fun i => (c.coeff i + (t : ℤ) * (((-(c.coeff i) : ℤ) : ZMod q) * (t : ZMod q)⁻¹).valMinAbs) / q⟩

/-- Switch a phase down to one limb. The argument lists the limbs still in use, *last limb
first*; `c` is the centred representative of the phase modulo their product. Each round switches
by the last limb and takes the centred representative modulo the product of the remaining ones
(the library holds residues, not integers). -/
def switchDownRev (t : ℕ) : List ℕ → IntPoly N → IntPoly N
  | [], c => c
  | [_], c => c
  | q :: rest, c => switchDownRev t rest (centered (ofInt rest.prod (switchPhase t q c)))

/-- BGV decryption with the phase switched to one limb (OpenFHE's `Decrypt`): the centred phase
modulo `Q = qs.prod` under `s`, switched down to `q₀`, reduced modulo `t`. With one limb this is
`bgvDecrypt`. -/
def bgvDecryptSwitched (t : ℕ) (qs : List ℕ) (s : IntPoly N) (ct : List (Poly qs.prod N)) :
    Poly t N :=
  ofInt t (switchDownRev t qs.reverse (centeredPhase s ct))

/-- Bound on the switched phase, from a bound `B` on the phase before the switches: each round
maps `B` to `⌊(B + t·⌊q/2⌋) / q⌋` (the correction is at most `t·⌊q/2⌋`, the division is exact).
The list is the limbs in use, last limb first. -/
def decBoundRev (t : ℕ) : List ℕ → ℕ → ℕ
  | [], B => B
  | [_], B => B
  | q :: rest, B => decBoundRev t rest ((B + t * (q / 2)) / q)

/-- Bound on the phase after switching from level `ℓ` to one limb, if it was at most `B`. -/
def decBound (P : Params) (ℓ B : ℕ) : ℕ := decBoundRev P.t (P.qs.take ℓ).reverse B

/-- The factor the switches put on the message: `(q₁ ⋯ q_{ℓ-1})⁻¹ mod t`. -/
def decScale (P : Params) (ℓ : ℕ) : ZMod P.t := ((((P.qs.take ℓ).drop 1).prod : ℕ) : ZMod P.t)⁻¹

/-- The switched decryption of a ciphertext at level `ℓ` with phase at most `B` is exact: the
switched phase stays below `q₀ / 2`. -/
def decryptOK? (P : Params) (ℓ B : ℕ) : Bool := decide (2 * decBound P ℓ B < P.qs.headD 0)

/-- The level at which the program leaves output `o` (it does not depend on the messages:
`Challenge.Decrypt.outputLevel?_eq`), computed on all-zero messages. -/
def outputLevel? (P : Params) (prog : Program) (o : Var) : Option ℕ := do
  let ρ ← eval P prog fun _ => .exact 0
  let v ← ρ o
  pure v.level

/-- Every output of the program, if its phase is at most `B` at its own level, decrypts exactly
by the switched decryption. -/
def decryptAllOK? (P : Params) (prog : Program) (B : ℕ) : Bool :=
  prog.outputs.all fun o =>
    match outputLevel? P prog o with
    | some ℓ => decryptOK? P ℓ B
    | none => false

end Spec.Decrypt
