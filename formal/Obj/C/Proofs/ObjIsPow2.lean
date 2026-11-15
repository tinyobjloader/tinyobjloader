/-
  Invariant proofs for `tobj_is_pow2` (tinyobjloader verified core).

  The translated function is `v && !(v & (v - 1))` on a u64 argument.
-/
import Obj.C.Semantics
import Obj.C.Gen
import Obj.C.Logic

namespace Obj.C.Proofs
open Obj.C

set_option linter.unusedSimpArgs false

/-- `tobj_is_pow2` on zero: returns 0 (`v && ...` short-circuits). -/
theorem tobj_is_pow2_zero (loc : Locals) (m : Mem)
    (h : loc 0 = some (.int IntTy.u64 0)) :
    ExS Gen.prog ⟨loc, m, false⟩ Gen.tobj_is_pow2.body
      (.ret (some (.int IntTy.u8 0))) ⟨loc, m, false⟩ := by
  have hf : truthy (.int IntTy.u64 0) = .ok false := by simp [truthy]
  have hland : EvE Gen.prog ⟨loc, m, false⟩
      (.land (.var 0)
             (.bin .eq (some ⟨64, false⟩) (.bin .band (some ⟨64, false⟩) (.var 0)
               (.bin .sub (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))))
               (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      (boolVal false) := EvE.land_false (ha := EvE.var h) (hf := hf)
  have hbc : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, false⟩
      (if false then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 0) :=
    EvE.const (.int IntTy.u8 0)
  have hexpr : EvE Gen.prog ⟨loc, m, false⟩
      (.cond (.land (.var 0)
                    (.bin .eq (some ⟨64, false⟩) (.bin .band (some ⟨64, false⟩) (.var 0)
                      (.bin .sub (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))))
                      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 0) :=
    EvE.cond (hc := hland) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

/-- `tobj_is_pow2` on 8 (a power of two): returns 1. -/
theorem tobj_is_pow2_eight (loc : Locals) (m : Mem)
    (h : loc 0 = some (.int IntTy.u64 8)) :
    ExS Gen.prog ⟨loc, m, false⟩ Gen.tobj_is_pow2.body
      (.ret (some (.int IntTy.u8 1))) ⟨loc, m, false⟩ := by
  have ht : truthy (.int IntTy.u64 8) = .ok true := by simp [truthy]
  have hcast1 : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.u64 (.const (.int IntTy.u32 1))) (.int IntTy.u64 1) :=
    EvE.cast (ha := EvE.const (.int IntTy.u32 1)) (by rfl)
  have hsub : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.sub (some IntTy.u64) (.var 0) (.cast IntTy.u64 (.const (.int IntTy.u32 1))))
      (.int IntTy.u64 7) :=
    EvE.bin (ha := EvE.var h) (hb := hcast1) (by rfl)
  have hband : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.band (some IntTy.u64) (.var 0)
        (.bin BinOp.sub (some IntTy.u64) (.var 0) (.cast IntTy.u64 (.const (.int IntTy.u32 1)))))
      (.int IntTy.u64 0) :=
    EvE.bin (ha := EvE.var h) (hb := hsub) (by rfl)
  have hcast0 : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.u64 (.const (.int IntTy.i32 0))) (.int IntTy.u64 0) :=
    EvE.cast (ha := EvE.const (.int IntTy.i32 0)) (by rfl)
  have heq : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.eq (some IntTy.u64) (.bin BinOp.band (some IntTy.u64) (.var 0)
          (.bin BinOp.sub (some IntTy.u64) (.var 0) (.cast IntTy.u64 (.const (.int IntTy.u32 1)))))
          (.cast IntTy.u64 (.const (.int IntTy.i32 0))))
      (boolVal true) :=
    EvE.bin (ha := hband) (hb := hcast0) (by rfl)
  have ht2 : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hland : EvE Gen.prog ⟨loc, m, false⟩
      (.land (.var 0)
             (.bin .eq (some ⟨64, false⟩) (.bin .band (some ⟨64, false⟩) (.var 0)
               (.bin .sub (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))))
               (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      (boolVal true) := EvE.land_true (ha := EvE.var h) (ht := ht) (hb := heq) (hbb := ht2)
  have hbc : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, false⟩
      (if true then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 1) :=
    EvE.const (.int IntTy.u8 1)
  have hexpr : EvE Gen.prog ⟨loc, m, false⟩
      (.cond (.land (.var 0)
                    (.bin .eq (some ⟨64, false⟩) (.bin .band (some ⟨64, false⟩) (.var 0)
                      (.bin .sub (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))))
                      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 1) :=
    EvE.cond (hc := hland) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

/-- `tobj_is_pow2` on 6 (not a power of two): returns 0. -/
theorem tobj_is_pow2_six (loc : Locals) (m : Mem)
    (h : loc 0 = some (.int IntTy.u64 6)) :
    ExS Gen.prog ⟨loc, m, false⟩ Gen.tobj_is_pow2.body
      (.ret (some (.int IntTy.u8 0))) ⟨loc, m, false⟩ := by
  have ht : truthy (.int IntTy.u64 6) = .ok true := by simp [truthy]
  have hcast1 : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.u64 (.const (.int IntTy.u32 1))) (.int IntTy.u64 1) :=
    EvE.cast (ha := EvE.const (.int IntTy.u32 1)) (by rfl)
  have hsub : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.sub (some IntTy.u64) (.var 0) (.cast IntTy.u64 (.const (.int IntTy.u32 1))))
      (.int IntTy.u64 5) :=
    EvE.bin (ha := EvE.var h) (hb := hcast1) (by rfl)
  have hband : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.band (some IntTy.u64) (.var 0)
        (.bin BinOp.sub (some IntTy.u64) (.var 0) (.cast IntTy.u64 (.const (.int IntTy.u32 1)))))
      (.int IntTy.u64 4) :=
    EvE.bin (ha := EvE.var h) (hb := hsub) (by rfl)
  have hcast0 : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.u64 (.const (.int IntTy.i32 0))) (.int IntTy.u64 0) :=
    EvE.cast (ha := EvE.const (.int IntTy.i32 0)) (by rfl)
  have heq : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.eq (some IntTy.u64) (.bin BinOp.band (some IntTy.u64) (.var 0)
          (.bin BinOp.sub (some IntTy.u64) (.var 0) (.cast IntTy.u64 (.const (.int IntTy.u32 1)))))
          (.cast IntTy.u64 (.const (.int IntTy.i32 0))))
      (boolVal false) :=
    EvE.bin (ha := hband) (hb := hcast0) (by rfl)
  have ht2 : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hland : EvE Gen.prog ⟨loc, m, false⟩
      (.land (.var 0)
             (.bin .eq (some ⟨64, false⟩) (.bin .band (some ⟨64, false⟩) (.var 0)
               (.bin .sub (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))))
               (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      (boolVal false) := EvE.land_true (ha := EvE.var h) (ht := ht) (hb := heq) (hbb := ht2)
  have hbc : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, false⟩
      (if false then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 0) :=
    EvE.const (.int IntTy.u8 0)
  have hexpr : EvE Gen.prog ⟨loc, m, false⟩
      (.cond (.land (.var 0)
                    (.bin .eq (some ⟨64, false⟩) (.bin .band (some ⟨64, false⟩) (.var 0)
                      (.bin .sub (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))))
                      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 0) :=
    EvE.cond (hc := hland) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

end Obj.C.Proofs
