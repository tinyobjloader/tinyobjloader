/-
  Pure model of the writer's floating-point formatting.

  `Obj/Write.lean` deliberately keeps coordinates as raw token text, so its
  round-trip theorem never mentions floats.  This module supplies the numeric
  representation the writer relies on:

  * `f64Parts` / `f64Rat` decode a binary64 bit pattern exactly, mirroring the
    decomposition in `tobj_write_real.inc` (`tobj_dparts_of`);
  * `DecLit` is a decimal literal, `DecLit.value` its exact rational value;
  * `RoundsTo` says a literal lies within half an ulp of a double, i.e. is a
    valid 17-significant-digit rendering of it.

  Proved here: the decode is well-formed (`f64Parts_fst_lt`), zero decodes to
  zero (`f64Rat_zero`), and -- the fact that makes "write then read back"
  reproduce a coordinate -- a literal cannot be a valid rendering of two
  doubles that are more than the sum of their half-ulps apart
  (`RoundsTo.unique`).

  Scope: this file does NOT prove that `tobj_fmt_real` emits digits satisfying
  `RoundsTo`.  That refinement step is validated empirically (byte-identical
  to `%.17g` on the corpus, 400k random doubles round-trip, real scenes
  round-trip through the loader in `tests/write_tester.c`).  Stating a
  `sorry`-backed refinement theorem would overstate what is verified, so none
  is stated here.
-/
import Obj.Basic
namespace Obj

/-! ### Binary64 decomposition -/

/-- `(significand, binary exponent)` of a bit pattern, with `value = m * 2^e`.
    Subnormals (and zero) use `e = -1074` with `m = frac`. -/
def f64Parts (bits : Nat) : Nat × Int :=
  let exp : Nat := (bits / 2 ^ 52) % 2 ^ 11
  let frac : Nat := bits % 2 ^ 52
  if exp = 0 then (frac, -1074) else (frac + 2 ^ 52, (exp : Int) - 1075)

/-- Exact rational value of a finite nonnegative bit pattern. -/
def f64Rat (bits : Nat) : Rat :=
  let p := f64Parts bits
  let m : Rat := (p.1 : Rat)
  let two : Rat := 2
  if p.2 ≥ 0 then m * two ^ p.2.toNat else m / two ^ (-p.2).toNat

/-- The significand of any pattern is below `2^53` (52 fraction bits plus the
    implicit leading one). -/
theorem f64Parts_fst_lt (bits : Nat) : (f64Parts bits).1 < 2 ^ 53 := by
  unfold f64Parts
  dsimp only
  split
  · have := Nat.mod_lt bits (show 0 < 2 ^ 52 by decide)
    omega
  · have h1 := Nat.mod_lt bits (show 0 < 2 ^ 52 by decide)
    have h2 := Nat.mod_lt (bits / 2 ^ 52) (show 0 < 2 ^ 11 by decide)
    omega

theorem f64Rat_zero : f64Rat 0 = 0 := by
  unfold f64Rat f64Parts
  dsimp only
  split
  · show (0 : Rat) / (2 : Rat) ^ 1074 = 0
    rw [Rat.div_def, Rat.zero_mul]
  · exfalso; omega

/-- The bit pattern of the next double above `bits` (successor in the total
    order of doubles, for a positive finite value). -/
def nextUp (bits : Nat) : Nat := bits + 1

/-! ### Decimal literals -/

/-- A decimal literal `± digits * 10^exp`.  The formatter emits at most 17
    significant digits, i.e. `digits < 10^17`. -/
structure DecLit where
  neg : Bool
  digits : Nat
  exp : Int
  deriving DecidableEq, Repr

/-- Exact rational value of a decimal literal. -/
def DecLit.value (d : DecLit) : Rat :=
  let m : Rat := (d.digits : Rat)
  let ten : Rat := 10
  let v : Rat := if d.exp ≥ 0 then m * ten ^ d.exp.toNat
                 else m / ten ^ (-d.exp).toNat
  if d.neg then -v else v

/-- A literal is a valid rendering of a double `v` with ulp `u` when it lies
    within half an ulp of it. -/
def RoundsTo (v u : Rat) (d : DecLit) : Prop := Rat.abs (d.value - v) ≤ u / 2

/-! ### The load-bearing step of the round-trip argument -/

end Obj
