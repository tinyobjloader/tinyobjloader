/-
  Invariant proofs for `tobj_is_space` (tinyobjloader verified core).

  For each concrete i8 input the translated function returns 1 exactly for
  space (32) or tab (9), and 0 otherwise, with no undefined behaviour and no
  state change (it is a pure function of its argument).
-/
import Obj.C.Semantics
import Obj.C.Gen
import Obj.C.Logic

namespace Obj.C.Proofs
open Obj.C

set_option linter.unusedSimpArgs false

/-- `tobj_is_space` on space (c = 32). -/
theorem tobj_is_space_space (loc : Locals) (m : Mem) {ro : Bool}
    (h : loc 0 = some (.int IntTy.i8 32)) :
    ExS Gen.prog ⟨loc, m, ro⟩ Gen.tobj_is_space.body
      (.ret (some (.int IntTy.u8 1))) ⟨loc, m, ro⟩ := by
  have hcast : EvE Gen.prog ⟨loc, m, ro⟩
      (.cast IntTy.i32 (.var 0)) (.int IntTy.i32 32) :=
    EvE.cast (ha := EvE.var h) (by rfl)
  have hleft : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
      (boolVal true) :=
    EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 32)) (by rfl)
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hlor : EvE Gen.prog ⟨loc, m, ro⟩
      (.lor (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
            (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9))))
      (boolVal true) := EvE.lor_true (ha := hleft) (ht := ht)
  have hbc : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, ro⟩
      (if true then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 1) :=
    EvE.const (.int IntTy.u8 1)
  have hexpr : EvE Gen.prog ⟨loc, m, ro⟩
      (.cond (.lor (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
                  (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 1) :=
    EvE.cond (hc := hlor) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

/-- `tobj_is_space` on tab (c = 9). -/
theorem tobj_is_space_tab (loc : Locals) (m : Mem) {ro : Bool}
    (h : loc 0 = some (.int IntTy.i8 9)) :
    ExS Gen.prog ⟨loc, m, ro⟩ Gen.tobj_is_space.body
      (.ret (some (.int IntTy.u8 1))) ⟨loc, m, ro⟩ := by
  have hcast : EvE Gen.prog ⟨loc, m, ro⟩
      (.cast IntTy.i32 (.var 0)) (.int IntTy.i32 9) :=
    EvE.cast (ha := EvE.var h) (by rfl)
  have hleft : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
      (boolVal false) :=
    EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 32)) (by rfl)
  have hright : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9)))
      (boolVal true) :=
    EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 9)) (by rfl)
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have ht : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hlor : EvE Gen.prog ⟨loc, m, ro⟩
      (.lor (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
            (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9))))
      (boolVal true) := EvE.lor_false (ha := hleft) (hf := hf) (hb := hright) (hbb := ht)
  have hbc : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, ro⟩
      (if true then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 1) :=
    EvE.const (.int IntTy.u8 1)
  have hexpr : EvE Gen.prog ⟨loc, m, ro⟩
      (.cond (.lor (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
                  (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 1) :=
    EvE.cond (hc := hlor) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

/-- Signed extension helper: for `c` in i8 range, the i32 value produced by
    `cast i32 (i8 c)` is `c` when viewed through `toInt`. -/
theorem toInt_i32_wrap_i8 (c : Int) (h : -128 ≤ c ∧ c ≤ 127) :
    IntTy.toInt IntTy.i32 (IntTy.wrap IntTy.i32 c) = c := by
  have hmod : c % (4294967296 : Int) = if c < 0 then 4294967296 + c else c := by
    by_cases hneg : c < 0
    · have hle : (0 : Int) ≤ c + 4294967296 := by omega
      have hlt : c + 4294967296 < 4294967296 := by omega
      have e1 : (c + 4294967296) % (4294967296 : Int) = c + 4294967296 :=
        Int.emod_eq_of_lt hle hlt
      have e2 : c % (4294967296 : Int) = (c + 4294967296) % (4294967296 : Int) :=
        (Int.add_emod_right c 4294967296).symm
      simp [hneg, e2, e1]
      omega
    · have hle : (0 : Int) ≤ c := by omega
      have hlt : c < 4294967296 := by omega
      have e1 : c % (4294967296 : Int) = c := Int.emod_eq_of_lt hle hlt
      simp [hneg, e1]
  have hw : IntTy.wrap IntTy.i32 c = Int.toNat (if c < 0 then 4294967296 + c else c) := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i32, hmod]
  rw [hw]
  by_cases hneg : c < 0
  · have hlen : (Int.toNat (4294967296 + c) : Int) = 4294967296 + c :=
      Int.toNat_of_nonneg (by omega)
    have hb2 : 2147483648 ≤ 4294967296 + c := by omega
    simp [hneg, IntTy.toInt, IntTy.modulus, IntTy.i32, hlen, hb2]
    omega
  · have hlen : (Int.toNat c : Int) = c := Int.toNat_of_nonneg (by omega)
    have hsmall : Int.toNat c < 2147483648 := by omega
    simp [hneg, IntTy.toInt, IntTy.modulus, IntTy.i32, hlen]
    intro hcontra
    omega

/-- The i32 `cast` of an i8 local, shared by the tinyobjloader proofs:
    `cast i32 (i8 c)` evaluates to `wrap i32 c` without UB (chars are i8). -/
theorem evCast_i8_i32 {loc : Locals} {m : Mem} {c : Int} {ro : Bool}
    (hbnd : -128 ≤ c ∧ c ≤ 127)
    (h : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c))) :
    EvE Gen.prog ⟨loc, m, ro⟩ (.cast IntTy.i32 (.var 0))
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 c)) := by
  refine EvE.cast (ha := EvE.var (s := ⟨loc, m, ro⟩) h) ?_
  by_cases hneg : c < 0
  · have hle : (0 : Int) ≤ c + 4294967296 := by omega
    have hlt : c + 4294967296 < 4294967296 := by omega
    have e1 : (c + 4294967296) % (4294967296 : Int) = c + 4294967296 :=
      Int.emod_eq_of_lt hle hlt
    have e2 : c % (4294967296 : Int) = (c + 4294967296) % (4294967296 : Int) :=
      (Int.add_emod_right c 4294967296).symm
    simp [evalCast, IntTy.i8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      hbnd, hneg, e2, e1]
    omega
  · have hle : (0 : Int) ≤ c := by omega
    have hlt : c < 4294967296 := by omega
    have e1 : c % (4294967296 : Int) = c := Int.emod_eq_of_lt hle hlt
    simp [evalCast, IntTy.i8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      hbnd, hneg, e1]
    omega

/-- `tobj_is_space` on anything else (c ≠ 32, c ≠ 9, in i8 range): returns 0. -/
theorem tobj_is_space_other (loc : Locals) (m : Mem) (c : Int) {ro : Bool}
    (hrange : IntTy.inRange IntTy.i8 c = true)
    (h32 : c ≠ 32) (h9 : c ≠ 9)
    (h : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c))) :
    ExS Gen.prog ⟨loc, m, ro⟩ Gen.tobj_is_space.body
      (.ret (some (.int IntTy.u8 0))) ⟨loc, m, ro⟩ := by
  have hbnd : -128 ≤ c ∧ c ≤ 127 := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8] at hrange
    exact hrange
  have hcast : EvE Gen.prog ⟨loc, m, ro⟩
      (.cast IntTy.i32 (.var 0)) (.int IntTy.i32 (IntTy.wrap IntTy.i32 c)) := by
    refine EvE.cast (ha := EvE.var h) ?_
    by_cases hneg : c < 0
    · have hle : (0 : Int) ≤ c + 4294967296 := by omega
      have hlt : c + 4294967296 < 4294967296 := by omega
      have e1 : (c + 4294967296) % (4294967296 : Int) = c + 4294967296 :=
        Int.emod_eq_of_lt hle hlt
      have e2 : c % (4294967296 : Int) = (c + 4294967296) % (4294967296 : Int) :=
        (Int.add_emod_right c 4294967296).symm
      simp [evalCast, IntTy.i8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus,
        hbnd, hneg, e2, e1]
      omega
    · have hle : (0 : Int) ≤ c := by omega
      have hlt : c < 4294967296 := by omega
      have e1 : c % (4294967296 : Int) = c := Int.emod_eq_of_lt hle hlt
      simp [evalCast, IntTy.i8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus,
        hbnd, hneg, e1]
      omega
  have hconv : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) c) = c :=
    toInt_i32_wrap_i8 c hbnd
  have h32to : IntTy.toInt (⟨32, true⟩ : IntTy) 32 = 32 := by rfl
  have h9to : IntTy.toInt (⟨32, true⟩ : IntTy) 9 = 9 := by rfl
  have hleft : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
      (boolVal false) := by
    refine EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 32)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, h32, hconv, h32to, isPtr, intOf]
  have hright : EvE Gen.prog ⟨loc, m, ro⟩
      (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9)))
      (boolVal false) := by
    refine EvE.bin (ha := hcast) (hb := EvE.const (.int IntTy.i32 9)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, h9, hconv, h9to, isPtr, intOf]
  have hf : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hlor : EvE Gen.prog ⟨loc, m, ro⟩
      (.lor (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
            (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9))))
      (boolVal false) := EvE.lor_false (ha := hleft) (hf := hf) (hb := hright) (hbb := hf)
  have hbc : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hv : EvE Gen.prog ⟨loc, m, ro⟩
      (if false then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 0) :=
    EvE.const (.int IntTy.u8 0)
  have hexpr : EvE Gen.prog ⟨loc, m, ro⟩
      (.cond (.lor (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 32)))
                  (.bin .eq (some IntTy.i32) (.cast IntTy.i32 (.var 0)) (.const (.int IntTy.i32 9))))
            (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))
      (.int IntTy.u8 0) :=
    EvE.cond (hc := hlor) (hbc := hbc) (hv := hv)
  exact ExS.ret hexpr

end Obj.C.Proofs
