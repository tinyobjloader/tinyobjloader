/-
  Basic types shared by the glTF formalization.

  Scalars use the exact C types of `tiny_gltf_v3.h` (`Int32`, `UInt32`,
  `UInt64`), so wrap-around and signedness match the C runtime. Doubles are
  modelled by their IEEE-754 bit pattern (`F64`) with comparison operators
  defined on the bits, so every predicate is decidable and provable (Lean's
  builtin `Float` is opaque to the kernel).
-/
namespace Obj

/-- Byte strings (`tg3_str`). C compares them bytewise, so do we. -/
abbrev Bytes := List UInt8

/-- ASCII/UTF-8-free literal helper; only used for ASCII constants. -/
def str (s : String) : Bytes := s.toList.map (fun c => c.toNat.toUInt8)

/-! ## IEEE-754 binary64, as bit patterns -/

/-- An IEEE-754 binary64 value, represented by its bit pattern. -/
structure F64 where
  bits : UInt64
  deriving DecidableEq, Repr, Inhabited

namespace F64

def zero : F64 := ⟨0⟩
def one : F64 := ⟨0x3FF0000000000000⟩
def half : F64 := ⟨0x3FE0000000000000⟩
def two : F64 := ⟨0x4000000000000000⟩
def negOne : F64 := ⟨0xBFF0000000000000⟩
def nan : F64 := ⟨0x7FF8000000000000⟩
def inf : F64 := ⟨0x7FF0000000000000⟩

def expBits (x : F64) : UInt64 := (x.bits >>> 52) &&& 0x7FF
def fracBits (x : F64) : UInt64 := x.bits &&& 0xFFFFFFFFFFFFF
def signBit (x : F64) : Bool := (x.bits >>> 63) == 1

def isNaN (x : F64) : Bool := x.expBits == 0x7FF && x.fracBits != 0

/-- Order key: sign-magnitude mapped onto `Int`. Monotone in the real value
    for all non-NaN inputs (including ±∞), and `+0`/`-0` share key `0`. -/
def key (x : F64) : Int :=
  let m : Int := (x.bits &&& 0x7FFFFFFFFFFFFFFF).toNat
  if x.signBit then -m else m

/-- C `a < b` on doubles. -/
def lt (a b : F64) : Bool := !a.isNaN && !b.isNaN && decide (a.key < b.key)
/-- C `a <= b` on doubles. -/
def le (a b : F64) : Bool := !a.isNaN && !b.isNaN && decide (a.key ≤ b.key)
/-- C `a == b` on doubles (`+0 == -0`, `NaN != NaN`). -/
def eq (a b : F64) : Bool := !a.isNaN && !b.isNaN && decide (a.key = b.key)
/-- C `a != b` on doubles (true whenever either side is NaN). -/
def ne (a b : F64) : Bool := !(eq a b)

/-- `0 <= x && x <= 1`, as written in the C runtime. -/
def unitInterval (x : F64) : Bool := le zero x && le x one

end F64

/-- Two's-complement representation of a signed 32-bit value, as stored in
    `Val.int IntTy.i32`. -/
def wrap32 (x : Int32) : Nat := x.toBitVec.toNat

/-! ## Helpers on C-style indices -/

/-- `idx < 0 || (uint32_t)idx >= n` is false, i.e. `idx` is a valid index. -/
def validIdx (idx : Int32) (n : Nat) : Bool :=
  decide (0 ≤ idx.toInt) && decide (idx.toInt < n)

/-- Optional index: `-1` means absent. -/
def validOptIdx (idx : Int32) (n : Nat) : Bool :=
  idx == -1 || validIdx idx n

/-- Safe list access by an index already known to be valid. -/
def getIdx? {α} (l : List α) (idx : Int32) : Option α :=
  if 0 ≤ idx.toInt then l[idx.toInt.toNat]? else none

/-- `2^64`: the C runtime's overflow checks reject any `uint64_t` result that
    does not fit, so specifications are phrased in `Nat` with this bound. -/
def u64Bound : Nat := 2 ^ 64

end Obj
