import Obj.Basic

/-
  Base64 decoding, as specified (no C involved).

  The C runtime decodes in two stages: `tg3__b64_decode_char` maps one
  character to its 6-bit value (or `-1`), and `tg3__b64_decode_into` streams
  characters through a 32-bit accumulator emitting one byte whenever at least
  8 bits are available. `B64.charValue` and `B64.step` specify those two
  stages; `decode` is the composition.
-/
namespace Obj.B64

open Obj

/-- Value of one base64 character; `-1` for characters outside the alphabet. -/
def charValue (c : UInt8) : Int32 :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then (n - 65).toInt32
  else if 97 ≤ n ∧ n ≤ 122 then (n - 97 + 26).toInt32
  else if 48 ≤ n ∧ n ≤ 57 then (n - 48 + 52).toInt32
  else if n = 43 then 62
  else if n = 47 then 63
  else -1

/-- The value the C runtime actually returns, as a `u32` representation:
    `4294967295` is the encoding of `-1`. -/
def charValueU (c : UInt8) : Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then n - 65
  else if 97 ≤ n ∧ n ≤ 122 then n - 97 + 26
  else if 48 ≤ n ∧ n ≤ 57 then n - 48 + 52
  else if n = 43 then 62
  else if n = 47 then 63
  else 4294967295

/-- Stream state: `(accumulator, bit count, output so far)`, with the
    accumulator reduced modulo `2^32` as in the C code. -/
structure St where
  accum : Nat := 0
  bits : Nat := 0
  out : List UInt8 := []
  deriving DecidableEq, Repr

/-- One character, folded into the state. -/
def step (st : St) (c : UInt8) : St :=
  if charValue c < 0 then st
  else
    let accum := (st.accum * 64 + Obj.wrap32 (charValue c)) % 4294967296
    let bits := st.bits + 6
    if 8 ≤ bits then
      { accum := accum, bits := bits - 8,
        out := st.out ++ [(((accum / 2 ^ (bits - 8)) % 256)).toUInt8] }
    else { accum := accum, bits := bits, out := st.out }

/-- Decode a whole base64 character string. -/
def decode (cs : List UInt8) : List UInt8 :=
  (cs.foldl step {}).out

/-- Length of the decoded output: `n * 3 / 4`. -/
def decodedLen (n : Nat) : Nat := n * 3 / 4

end Obj.B64
