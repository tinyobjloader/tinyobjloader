import Tess.C.Arithmetic
import Obj.C.Proofs.ObjFixIndex
namespace Tess.C
open Obj.C

/-- Reuse the loader's signed decoding lemma, including INT64_MIN. -/
theorem magnitude_signed_decode (a : Int)
    (range : -(2^63) ≤ a ∧ a < 2^63) :
    IntTy.toInt IntTy.i64 (IntTy.wrap IntTy.i64 a) = a := by
  exact Obj.C.Proofs.toInt_i64_wrap a (by constructor <;> omega)

private theorem wrap_unsigned_nonnegative (a : Int) (lo : 0 ≤ a) (hi : a < 2^64) :
    IntTy.wrap IntTy.u64 a = a.toNat := by
  simp only [IntTy.wrap, IntTy.modulus, IntTy.u64]
  change (a % (18446744073709551616 : Int)).toNat = a.toNat
  rw [Int.emod_eq_of_lt lo (show a < 18446744073709551616 by omega)]

/-- Symbolic refinement of the actual translated `tess_mag` for every signed
64-bit value and arbitrary state. Increment-before-negate handles INT64_MIN
without signed overflow; the function preserves all locals and memory. -/
theorem magnitude_refines (state : State) (a : Int)
    (range : -(2^63) ≤ a ∧ a < 2^63)
    (inputLocal : state.locals 0 = some (.int IntTy.i64 (IntTy.wrap IntTy.i64 a))) :
    ExS Gen.prog state Gen.tess_mag.body
      (.ret (some (.int IntTy.u64 a.natAbs))) state := by
  have decode := magnitude_signed_decode a range
  have zeroCast : evalCast IntTy.i64 (.int IntTy.i32 0)=.ok (.int IntTy.i64 0) := by rfl
  have oneCast : evalCast IntTy.i64 (.int IntTy.i32 1)=.ok (.int IntTy.i64 1) := by rfl
  have test := EvE.bin (p := Gen.prog) (EvE.var inputLocal)
    (EvE.cast (EvE.const (.int IntTy.i32 0)) zeroCast)
    (show evalBin .lt (some IntTy.i64) (.int IntTy.i64 (IntTy.wrap IntTy.i64 a))
      (.int IntTy.i64 0)=.ok (boolVal (decide (a<0))) by
      change Res.ok (boolVal (decide (IntTy.i64.toInt (IntTy.wrap IntTy.i64 a)<0)))=_
      rw [decode])
  apply ExS.ret
  apply EvE.cond test
    (show truthy (boolVal (decide (a<0)))=.ok (decide (a<0)) by
      by_cases neg : a<0 <;> simp [neg, truthy, boolVal])
  by_cases negative : a<0
  · simp only [negative, decide_true, ite_true]
    have addRange : IntTy.inRange IntTy.i64 (a+1)=true := by
      simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i64]; omega
    have negRange : IntTy.inRange IntTy.i64 (-(a+1))=true := by
      simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i64]; omega
    have decodeAdd := magnitude_signed_decode (a+1) (by constructor <;> omega)
    have decodeNeg := magnitude_signed_decode (-(a+1)) (by constructor <;> omega)
    have added := EvE.bin (p := Gen.prog) (EvE.var inputLocal)
      (EvE.cast (EvE.const (.int IntTy.i32 1)) oneCast)
      (show evalBin .add (some IntTy.i64) (.int IntTy.i64 (IntTy.wrap IntTy.i64 a))
        (.int IntTy.i64 1)=.ok (.int IntTy.i64 (IntTy.wrap IntTy.i64 (a+1))) by
        change arith IntTy.i64 (IntTy.i64.toInt (IntTy.wrap IntTy.i64 a)+1)=_
        rw [decode]
        simp [arith, addRange])
    have negated := EvE.un added
      (show evalUn .neg IntTy.i64 (.int IntTy.i64 (IntTy.wrap IntTy.i64 (a+1)))=
        .ok (.int IntTy.i64 (IntTy.wrap IntTy.i64 (-(a+1)))) by
        change arith IntTy.i64 (-(IntTy.i64.toInt (IntTy.wrap IntTy.i64 (a+1))))=_
        rw [decodeAdd]
        simp [arith, negRange])
    have casted := EvE.cast negated
      (show evalCast IntTy.u64 (.int IntTy.i64 (IntTy.wrap IntTy.i64 (-(a+1))))=
        .ok (.int IntTy.u64 (-(a+1)).toNat) by
        change Res.ok (Val.int IntTy.u64 (IntTy.wrap IntTy.u64
          (IntTy.i64.toInt (IntTy.wrap IntTy.i64 (-(a+1))))))=_
        rw [decodeNeg, wrap_unsigned_nonnegative (-(a+1)) (by omega) (by omega)])
    have magnitude : (-(a+1)).toNat+1=a.natAbs := by omega
    refine EvE.bin casted (EvE.const (.int IntTy.u64 1)) ?_
    have fits : a.natAbs < 18446744073709551616 := by omega
    change Res.ok (Val.int IntTy.u64 (((-(a+1)).toNat+1)%18446744073709551616))=_
    rw [magnitude,Nat.mod_eq_of_lt fits]
  · simp only [negative, decide_false]
    have magnitude : a.toNat=a.natAbs := by omega
    exact EvE.cast (EvE.var inputLocal) (by
      change Res.ok (Val.int IntTy.u64 (IntTy.wrap IntTy.u64
        (IntTy.i64.toInt (IntTy.wrap IntTy.i64 a))))=_
      rw [decode,wrap_unsigned_nonnegative a (by omega) (by omega),magnitude])

#print axioms magnitude_refines
end Tess.C
