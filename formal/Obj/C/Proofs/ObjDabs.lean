import Obj.C.Proofs.ObjOrient2d
namespace Obj.C.Proofs
open Obj.C Obj

/-! ### Bit-level model of `tobj_dabs` -/

/-- `x < 0.0 ? -x : x`, in the bit-level model.  Note `-0.0` is *not* less than
    `0.0` (they share an ordering key), so `dabs(-0.0) = -0.0`, matching IEEE
    comparison semantics. -/
def dabsBits (a : Nat) : Nat :=
  if (!f64IsNaN a && !f64IsNaN 0 && decide (f64Key a < f64Key 0)) then
    F64.negBits a
  else
    a

theorem evalBin_f64_lt_zero (a : Nat) :
    evalBin .lt none (.f64 a) (.f64 0) =
      .ok (boolVal (!f64IsNaN a && !f64IsNaN 0 && decide (f64Key a < f64Key 0))) := by
  simp [evalBin, isPtr, evalBinInt, binF64]

theorem truthy_boolVal (b : Bool) : truthy (boolVal b) = .ok b := by
  cases b <;> simp [truthy, boolVal]

/-- **`tobj_dabs` refines `dabsBits`.**  The translated body
    `x < 0.0 ? -x : x` returns exactly the pure bit-level absolute value,
    including the `-0.0` case (which stays `-0.0`, as IEEE comparison
    dictates). -/
theorem tobj_dabs_refines (m : Mem) (a : Nat) (ro : Bool) :
    ExS Gen.prog
      ⟨frameLocals Gen.tobj_dabs.params [.f64 a], m, ro⟩
      Gen.tobj_dabs.body (.ret (some (.f64 (dabsBits a))))
      ⟨frameLocals Gen.tobj_dabs.params [.f64 a], m, ro⟩ := by
  let s0 : State := ⟨frameLocals Gen.tobj_dabs.params [.f64 a], m, ro⟩
  have l0 : s0.locals 0 = some (.f64 a) := by
    simp [s0, frameLocals, Gen.tobj_dabs, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hv0 : EvE Gen.prog s0 (.var 0) (.f64 a) := EvE.var l0
  have hlt : EvE Gen.prog s0 (.bin .lt none (.var 0) (.const (.f64 0)))
      (boolVal (!f64IsNaN a && !f64IsNaN 0 && decide (f64Key a < f64Key 0))) :=
    EvE.bin hv0 (EvE.const _) (evalBin_f64_lt_zero a)
  have hbody : Gen.tobj_dabs.body =
      .ret (some (.cond (.bin .lt none (.var 0) (.const (.f64 0)))
        (.un .neg ⟨64, false⟩ (.var 0)) (.var 0))) := rfl
  by_cases h : (!f64IsNaN a && !f64IsNaN 0 && decide (f64Key a < f64Key 0)) = true
  · -- negative branch: -x
    have hneg : EvE Gen.prog s0 (.un .neg ⟨64, false⟩ (.var 0)) (.f64 (F64.negBits a)) :=
      EvE.un hv0 (evalUn_f64_neg a)
    have hcond : EvE Gen.prog s0
        (.cond (.bin .lt none (.var 0) (.const (.f64 0)))
          (.un .neg ⟨64, false⟩ (.var 0)) (.var 0)) (.f64 (F64.negBits a)) := by
      rw [show (!f64IsNaN a && !f64IsNaN 0 && decide (f64Key a < f64Key 0)) = true from h] at hlt
      exact EvE.cond hlt (truthy_boolVal true) hneg
    have : dabsBits a = F64.negBits a := by simp [dabsBits, h]
    rw [this]
    rw [hbody]
    exact ExS.ret hcond
  · -- non-negative branch: x
    have hf : (!f64IsNaN a && !f64IsNaN 0 && decide (f64Key a < f64Key 0)) = false := by
      simpa using h
    have hcond : EvE Gen.prog s0
        (.cond (.bin .lt none (.var 0) (.const (.f64 0)))
          (.un .neg ⟨64, false⟩ (.var 0)) (.var 0)) (.f64 a) := by
      rw [show (!f64IsNaN a && !f64IsNaN 0 && decide (f64Key a < f64Key 0)) = false from hf] at hlt
      exact EvE.cond hlt (truthy_boolVal false) hv0
    have : dabsBits a = a := by simp [dabsBits, hf]
    rw [this]
    rw [hbody]
    exact ExS.ret hcond

end Obj.C.Proofs
