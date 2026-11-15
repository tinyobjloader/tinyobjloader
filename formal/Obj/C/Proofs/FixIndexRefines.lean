/-
  `fix_index_f` (the translated C `fix_index`) refines the OBJ index
  specification `Obj.resolveIndex` / `Obj.storedIndex`, for every
  i32 index and every element count below 2^31:

    * the function returns 1 exactly when the index resolves,
    * it stores `storedIndex idx n` (little-endian i32) at `*out`,
    * it never hits undefined behaviour and always terminates.
-/
import Obj.C.Proofs.ObjFixIndex
import Obj.Spec

namespace Obj.C.Proofs
open Obj.C Obj

theorem fix_index_f_refines (loc : Locals) (m : Mem) (b o : Nat) (blk : Block)
    (idx : Int) (n : Nat)
    (hrange : IntTy.inRange IntTy.i32 idx = true)
    (hn : n < 2147483648)
    (hm : m b = some blk)
    (hblk : o + 4 ≤ blk.length)
    (h0 : loc 0 = some (.int IntTy.i32 (IntTy.wrap IntTy.i32 idx)))
    (h1 : loc 1 = some (.int IntTy.u64 n))
    (h2 : loc 2 = some (.ptr b o)) :
    ∃ s', ExS Gen.prog ⟨loc, m, false⟩ Gen.fix_index_f.body
        (.ret (some (.int IntTy.u8 (if (resolveIndex idx n).isSome then 1 else 0)))) s' ∧
      s'.mem = m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (storedIndex idx n)))) := by
  rcases (show idx < 0 ∨ idx = 0 ∨ 0 < idx by omega) with hlt | heq | hgt
  · by_cases hin : 0 ≤ (n : Int) + idx
    · have hres : (if (resolveIndex idx n).isSome then 1 else 0) = (1 : Nat) := by
        simp [resolveIndex_neg_in hlt hin]
      rw [hres]
      refine ⟨_, fix_index_f_neg loc m b o blk idx n (by omega) hrange hlt hin hm hblk h0 h1 h2, ?_⟩
      simp [resolveIndex_neg_in hlt hin, storedIndex]
    · have hneg : (n : Int) + idx < 0 := by omega
      have hres : (if (resolveIndex idx n).isSome then 1 else 0) = (0 : Nat) := by
        simp [resolveIndex_neg_out hlt hneg]
      rw [hres]
      refine ⟨_, fix_index_f_oob loc m b o blk idx n (by omega) hrange hlt hneg hm hblk h0 h1 h2, ?_⟩
      simp [resolveIndex_neg_out hlt hneg, storedIndex]
  · subst heq
    have hres : (if (resolveIndex 0 n).isSome then 1 else 0) = (0 : Nat) := by
      simp [resolveIndex_zero]
    rw [hres]
    refine ⟨_, fix_index_f_zero loc m b o blk ?_ h2 hm hblk, ?_⟩
    · simpa using h0
    · simp [resolveIndex_zero, storedIndex]
  · have hres : (if (resolveIndex idx n).isSome then 1 else 0) = (1 : Nat) := by
      simp [resolveIndex_pos hgt]
    rw [hres]
    refine ⟨_, fix_index_f_pos loc m b o blk idx (n : Int) hrange hgt hm hblk h0 ?_ h2, ?_⟩
    · have hw : IntTy.wrap IntTy.u64 (n : Int) = n := by
        have hmod : (n : Int) % (IntTy.u64.modulus : Int) = n :=
          Int.emod_eq_of_lt (by omega) (by simp [IntTy.u64, IntTy.modulus]; omega)
        simp [IntTy.wrap, hmod]
      rw [hw] at *
      simpa [hw] using h1
    · simp [resolveIndex_pos hgt, storedIndex]

end Obj.C.Proofs
