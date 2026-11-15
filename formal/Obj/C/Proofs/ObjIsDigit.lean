/-
  Invariant proofs for `tobj_is_digit` (tinyobjloader verified core).

  For input characters in i8 range the translated function returns 1 iff
  c is between '0' (48) and '9' (57) inclusive, 0 otherwise.
-/
import Obj.C.Semantics
import Obj.C.Gen
import Obj.C.Logic
import Obj.C.Proofs.ObjIsSpace

namespace Obj.C.Proofs
open Obj.C

set_option linter.unusedSimpArgs false

/-- `tobj_is_digit` on a digit character ('0'..'9'). -/
theorem tobj_is_digit_ge (loc : Locals) (m : Mem) (c : Int) {ro : Bool}
    (hrange : IntTy.inRange IntTy.i8 c = true)
    (h48 : 48 ≤ c) (h57 : c ≤ 57)
    (h : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c))) :
    ExS Gen.prog ⟨loc, m, ro⟩ Gen.tobj_is_digit.body
      (.ret (some (.int IntTy.u8 1))) ⟨loc, m, ro⟩ := by
  have hbnd : -128 ≤ c ∧ c ≤ 127 := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8] at hrange
    exact hrange
  have hcast := evCast_i8_i32 (m := m) (ro := ro) hbnd h
  have hconv : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) c) = c :=
    toInt_i32_wrap_i8 c hbnd
  have h48to : IntTy.toInt (⟨32, true⟩ : IntTy) 48 = 48 := by rfl
  have h57to : IntTy.toInt (⟨32, true⟩ : IntTy) 57 = 57 := by rfl
  have hge : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
      (boolVal true) := by
    refine EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 48)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, h48, hconv, h48to, isPtr, intOf]
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hle : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57)))
      (boolVal true) := by
    refine EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 57)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, h57, hconv, h57to, isPtr, intOf]
  have hland : EvE Gen.prog ⟨loc, m, ro⟩
      (.land (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
             (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57))))
      (boolVal true) := EvE.land_true (ha := hge) (ht := ht) (hb := hle) (hbb := ht)
  have hbc : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, ro⟩
      (if true then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 1) :=
    EvE.const (.int IntTy.u8 1)
  have hexpr : EvE Gen.prog ⟨loc, m, ro⟩
      (.cond (.land (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
                  (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 1) :=
    EvE.cond (hc := hland) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

/-- `tobj_is_digit` on a character below '0'. -/
theorem tobj_is_digit_lo (loc : Locals) (m : Mem) (c : Int) {ro : Bool}
    (hrange : IntTy.inRange IntTy.i8 c = true)
    (hlo : c < 48)
    (h : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c))) :
    ExS Gen.prog ⟨loc, m, ro⟩ Gen.tobj_is_digit.body
      (.ret (some (.int IntTy.u8 0))) ⟨loc, m, ro⟩ := by
  have hbnd : -128 ≤ c ∧ c ≤ 127 := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8] at hrange
    exact hrange
  have h48lt : ¬ (48 ≤ c) := by omega
  have hcast := evCast_i8_i32 (m := m) (ro := ro) hbnd h
  have hconv : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) c) = c :=
    toInt_i32_wrap_i8 c hbnd
  have h48to : IntTy.toInt (⟨32, true⟩ : IntTy) 48 = 48 := by rfl
  have hge : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
      (boolVal false) := by
    refine EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 48)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, h48lt, hconv, h48to, isPtr, intOf]
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hland : EvE Gen.prog ⟨loc, m, ro⟩
      (.land (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
             (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57))))
      (boolVal false) := EvE.land_false (ha := hge) (hf := hf)
  have hbc : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, ro⟩
      (if false then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 0) :=
    EvE.const (.int IntTy.u8 0)
  have hexpr : EvE Gen.prog ⟨loc, m, ro⟩
      (.cond (.land (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
                  (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 0) :=
    EvE.cond (hc := hland) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

/-- `tobj_is_digit` on a character above '9'. -/
theorem tobj_is_digit_hi (loc : Locals) (m : Mem) (c : Int) {ro : Bool}
    (hrange : IntTy.inRange IntTy.i8 c = true)
    (hhi : 57 < c)
    (h : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c))) :
    ExS Gen.prog ⟨loc, m, ro⟩ Gen.tobj_is_digit.body
      (.ret (some (.int IntTy.u8 0))) ⟨loc, m, ro⟩ := by
  have hbnd : -128 ≤ c ∧ c ≤ 127 := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8] at hrange
    exact hrange
  have hcast := evCast_i8_i32 (m := m) (ro := ro) hbnd h
  have hconv : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) c) = c :=
    toInt_i32_wrap_i8 c hbnd
  have h48to : IntTy.toInt (⟨32, true⟩ : IntTy) 48 = 48 := by rfl
  have h57to : IntTy.toInt (⟨32, true⟩ : IntTy) 57 = 57 := by rfl
  have h48le : 48 ≤ c := by omega
  have h57lt : ¬ (c ≤ 57) := by omega
  have hge : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
      (boolVal true) := by
    refine EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 48)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, h48le, hconv, h48to, isPtr, intOf]
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hle : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57)))
      (boolVal false) := by
    refine EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 57)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, h57lt, hconv, h57to, isPtr, intOf]
  have hbb : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hland : EvE Gen.prog ⟨loc, m, ro⟩
      (.land (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
             (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57))))
      (boolVal false) := EvE.land_true (ha := hge) (ht := ht) (hb := hle) (hbb := hbb)
  have hbc : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, ro⟩
      (if false then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 0) :=
    EvE.const (.int IntTy.u8 0)
  have hexpr : EvE Gen.prog ⟨loc, m, ro⟩
      (.cond (.land (.bin .ge (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 48)))
                  (.bin .le (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 57))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 0) :=
    EvE.cond (hc := hland) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

end Obj.C.Proofs
