import Tess.C.Gen
import Obj.C.Logic
namespace Tess.C
open Obj.C

/-- Four 32-bit limbs cannot overflow the uint64 multiply-add helper.
C counterpart: tess_limb_madd in lib/tess/src/exact_core.c.
Fixtures: exact oracle and the maximum-limb kernel test below. -/
theorem limb_madd_bound (a b c d : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) (hd : d < 2^32) :
    a*b+c+d < 2^64 := by
  have hp : a*b ≤ 4294967295*4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

private theorem cast_limb (a : Nat) (ha : a < 2^32) :
    evalCast IntTy.u64 (.int IntTy.u32 a) = .ok (.int IntTy.u64 a) := by
  simp [evalCast, IntTy.u32, IntTy.u64, IntTy.modulus,
    Nat.mod_eq_of_lt (show a < 18446744073709551616 by omega)]

private theorem add_u64 (a b : Nat) (h : a+b < 2^64) :
    evalBin .add (some IntTy.u64) (.int IntTy.u64 a) (.int IntTy.u64 b) =
    .ok (.int IntTy.u64 (a+b)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64,
    IntTy.modulus, Nat.mod_eq_of_lt h]

private theorem mul_u64 (a b : Nat) (h : a*b < 2^64) :
    evalBin .mul (some IntTy.u64) (.int IntTy.u64 a) (.int IntTy.u64 b) =
    .ok (.int IntTy.u64 (a*b)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64,
    IntTy.modulus, Nat.mod_eq_of_lt h]

/-- Symbolic refinement of the actual translated helper, for every limb tuple,
with arbitrary memory and local frame. It returns the mathematical integer
multiply-add without wraparound, UB, or memory modification. -/
theorem limb_madd_refines (s : State) (a b c d : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) (hd : d < 2^32)
    (l0 : s.locals 0 = some (.int IntTy.u32 a))
    (l1 : s.locals 1 = some (.int IntTy.u32 b))
    (l2 : s.locals 2 = some (.int IntTy.u32 c))
    (l3 : s.locals 3 = some (.int IntTy.u32 d)) :
    ExS Gen.prog s Gen.tess_limb_madd.body
      (.ret (some (.int IntTy.u64 (a*b+c+d)))) s := by
  have bound := limb_madd_bound a b c d ha hb hc hd
  have ea := EvE.cast (EvE.var (p := Gen.prog) l0) (cast_limb a ha)
  have eb := EvE.cast (EvE.var (p := Gen.prog) l1) (cast_limb b hb)
  have ec := EvE.cast (EvE.var (p := Gen.prog) l2) (cast_limb c hc)
  have ed := EvE.cast (EvE.var (p := Gen.prog) l3) (cast_limb d hd)
  have ep := EvE.bin ea eb (mul_u64 a b (by omega))
  have es := EvE.bin ep ec (add_u64 (a*b) c (by omega))
  exact ExS.ret (EvE.bin es ed (add_u64 (a*b+c) d bound))

/-- The low/high uint32 digits used by schoolbook multiplication reconstruct
exactly the helper result, with neither digit overflowing its limb width. -/
theorem limb_madd_digits (a b c d : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) (hd : d < 2^32) :
    let result := a*b+c+d
    result % 2^32 < 2^32 ∧ result / 2^32 < 2^32 ∧
      result % 2^32 + 2^32 * (result / 2^32) = result := by
  have bound := limb_madd_bound a b c d ha hb hc hd
  dsimp
  refine ⟨Nat.mod_lt _ (by decide),?_,Nat.mod_add_div _ _⟩
  omega

#print axioms limb_madd_digits

#print axioms limb_madd_refines
end Tess.C
