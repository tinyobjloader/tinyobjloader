/-
  Invariant proof for `fix_index_f` (tinyobjloader verified core).

  For an OBJ index `idx > 0`, the translated function stores `idx - 1`
  at `*out` (little-endian i32), never hits UB, and returns 1.
-/
import Obj.C.Semantics
import Obj.C.Gen
import Obj.C.Logic
import Obj.C.Splice

namespace Obj.C.Proofs
open Obj.C

set_option linter.unusedSimpArgs false

/-- Signed extension helper for i32: the toInt of wrap is the input itself. -/
theorem toInt_i32_wrap (c : Int) (h : -2147483648 ≤ c ∧ c ≤ 2147483647) :
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
    simp [hneg, IntTy.toInt, IntTy.modulus, IntTy.i32, hlen, hsmall]
    intro hcontra
    omega


/-- `fix_index_f` on a positive index: `*out = idx - 1`, returns 1. -/
theorem fix_index_f_pos (loc : Locals) (m : Mem)
    (b o : Nat) (blk : Block)
    (idx n : Int)
    (hrange : IntTy.inRange IntTy.i32 idx = true)
    (hpos : 0 < idx)
    (hm : m b = some blk)
    (hblk : o + 4 ≤ blk.length)
    (h0 : loc 0 = some (.int IntTy.i32 (IntTy.wrap IntTy.i32 idx)))
    (h1 : loc 1 = some (.int IntTy.u64 (IntTy.wrap IntTy.u64 n)))
    (h2 : loc 2 = some (.ptr b o)) :
    ExS Gen.prog ⟨loc, m, false⟩ Gen.fix_index_f.body
      (.ret (some (.int IntTy.u8 1)))
      ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1)))), false⟩ := by
  have hbnd : -2147483648 ≤ idx ∧ idx ≤ 2147483647 := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i32] at hrange
    exact hrange
  have hconv : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) idx) = idx :=
    toInt_i32_wrap idx hbnd
  have h1to : IntTy.toInt (⟨32, true⟩ : IntTy) 1 = 1 := by rfl
  have h0to : IntTy.toInt (⟨32, true⟩ : IntTy) 0 = 0 := by rfl
  have hsub_ok : (⟨32, true⟩ : IntTy).inRange (idx - 1) = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal]; omega
  -- `idx - 1` as an i32 value
  have hsub : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.sub (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 1)))
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 (idx - 1))) := by
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 1)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, hconv, h1to, hrange, hsub_ok, arith]
  -- address of `out`
  have haddr : EvE Gen.prog ⟨loc, m, false⟩ (.var 2) (.ptr b o) := EvE.var h2
  -- the store succeeds in this memory
  have hstore : store m (.int IntTy.i32) (.ptr b o)
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 (idx - 1)))
      = .ok (m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1))))) := by
    have hlen : (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1))).length = 4 := by
      simp [encodeLE, IntTy.wrap]
    simp [store, writeBytes, splice, hm, hblk, encodeLE, IntTy.i32, IntTy.bytes, hlen]
  have hms : ExS Gen.prog ⟨loc, m, false⟩
      (.store (.int IntTy.i32) (.var 2)
        (.bin BinOp.sub (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 1))))
      .normal ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1)))), false⟩ :=
    ExS.store haddr hsub (by simp) hstore
  -- `return 1`
  have hbc1 : truthy (.int IntTy.i32 1) = .ok true := by simp [truthy]
  have hv : EvE Gen.prog ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1)))), false⟩
      (if true then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 1) :=
    EvE.const (.int IntTy.u8 1)
  have hret : ExS Gen.prog ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1)))), false⟩
      (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))))
      (.ret (some (.int IntTy.u8 1))) ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1)))), false⟩ :=
    ExS.ret (EvE.cond (hc := EvE.const (.int IntTy.i32 1)) (hbc := hbc1) (hv := hv))
  have hseq : ExS Gen.prog ⟨loc, m, false⟩
      (.seq (.store (.int IntTy.i32) (.var 2)
        (.bin BinOp.sub (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 1))))
        (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
      (.ret (some (.int IntTy.u8 1))) ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1)))), false⟩ :=
    ExS.seq hms hret
  -- the first `if (idx > 0)` condition
  have hgt : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
      (boolVal true) := by
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 0)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, hconv, h0to, hpos, hrange]
  have hbc : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hite : ExS Gen.prog ⟨loc, m, false⟩
      (.ite (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2)
              (.bin BinOp.sub (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
            .skip)
      (.ret (some (.int IntTy.u8 1))) ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (idx - 1)))), false⟩ :=
    ExS.ite hgt hbc hseq
  -- the rest of the body never executes
  exact ExS.seq_ret hite


/-- Signed extension helper for i64: the toInt of wrap is the input itself. -/
theorem toInt_i64_wrap (c : Int) (h : -9223372036854775808 ≤ c ∧ c ≤ 9223372036854775807) :
    IntTy.toInt IntTy.i64 (IntTy.wrap IntTy.i64 c) = c := by
  have hmod : c % (18446744073709551616 : Int) = if c < 0 then 18446744073709551616 + c else c := by
    by_cases hneg : c < 0
    · have e1 : (c + 18446744073709551616) % (18446744073709551616 : Int) = c + 18446744073709551616 :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have e2 : c % (18446744073709551616 : Int) = (c + 18446744073709551616) % (18446744073709551616 : Int) :=
        (Int.add_emod_right c 18446744073709551616).symm
      simp [hneg, e2, e1]
      omega
    · have e1 : c % (18446744073709551616 : Int) = c := Int.emod_eq_of_lt (by omega) (by omega)
      simp [hneg, e1]
  have hw : IntTy.wrap IntTy.i64 c = Int.toNat (if c < 0 then 18446744073709551616 + c else c) := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i64, hmod]
  rw [hw]
  by_cases hneg : c < 0
  · have hlen : (Int.toNat (18446744073709551616 + c) : Int) = 18446744073709551616 + c :=
      Int.toNat_of_nonneg (by omega)
    have hb2 : 9223372036854775808 ≤ 18446744073709551616 + c := by omega
    simp [hneg, IntTy.toInt, IntTy.modulus, IntTy.i64, hlen, hb2]
    omega
  · have hlen : (Int.toNat c : Int) = c := Int.toNat_of_nonneg (by omega)
    have hsmall : Int.toNat c < 9223372036854775808 := by omega
    simp [hneg, IntTy.toInt, IntTy.modulus, IntTy.i64, hlen, hsmall]
    intro hcontra
    omega

/-- Signed extension helper for u64 → i64 (non-negative inputs below 2^31). -/
theorem toInt_i64_wrap_u64 (n : Nat) (hn_small : n < 2147483648) :
    IntTy.toInt IntTy.i64 (IntTy.wrap IntTy.i64 (n : Int)) = n := by
  have hmod : (n : Int) % (18446744073709551616 : Int) = n := by
    apply Int.emod_eq_of_lt (by omega) (by omega)
  have hw : IntTy.wrap IntTy.i64 (n : Int) = Int.toNat (n : Int) := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i64, hmod]
  rw [hw]
  have hlen : (Int.toNat (n : Int) : Int) = n := Int.toNat_of_nonneg (by omega)
  have hsmall : Int.toNat (n : Int) < 9223372036854775808 := by omega
  simp [IntTy.toInt, IntTy.modulus, IntTy.i64, hlen, hsmall]
  intro hcontra
  omega




/-- `fix_index_f` on a negative OBJ index (relative to the end of the vertex
    array): given `n + idx >= 0` (and vertex counts below 2^31), the
    translated function stores `n + idx` at `*out` and returns 1. -/
theorem fix_index_f_neg (loc : Locals) (m : Mem)
    (b o : Nat) (blk : Block)
    (idx : Int) (k : Nat)
    (hk_small : k < 2147483648)
    (hrange : IntTy.inRange IntTy.i32 idx = true)
    (hneg : idx < 0)
    (hnonneg : 0 ≤ (k : Int) + idx)
    (hm : m b = some blk)
    (hblk : o + 4 ≤ blk.length)
    (h0 : loc 0 = some (.int IntTy.i32 (IntTy.wrap IntTy.i32 idx)))
    (h1 : loc 1 = some (.int IntTy.u64 k))
    (h2 : loc 2 = some (.ptr b o)) :
    ExS Gen.prog ⟨loc, m, false⟩ Gen.fix_index_f.body
      (.ret (some (.int IntTy.u8 1)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
       m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))),
       false⟩ := by
  have hbnd : -2147483648 ≤ idx ∧ idx ≤ 2147483647 := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i32] at hrange
    exact hrange
  have hconv_i32 : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) idx) = idx :=
    toInt_i32_wrap idx hbnd
  have hi64_lo : IntTy.toInt (⟨64, true⟩ : IntTy) (IntTy.wrap (⟨64, true⟩ : IntTy) idx) = idx :=
    toInt_i64_wrap idx (by omega)
  have h1to0 : IntTy.toInt (⟨32, true⟩ : IntTy) 0 = 0 := by rfl
  have hi64_sum : IntTy.toInt (⟨64, true⟩ : IntTy) (IntTy.wrap (⟨64, true⟩ : IntTy) ((k : Int) + idx)) = (k : Int) + idx :=
    toInt_i64_wrap ((k : Int) + idx) (by omega)
  have hsum_ok : (⟨64, true⟩ : IntTy).inRange ((k : Int) + idx) = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal]; omega
  have hnok64 : ¬ (k ≥ 9223372036854775808) := by omega
  have hcast_n_toInt : IntTy.toInt (⟨64, true⟩ : IntTy) k = k := by
    simp [IntTy.toInt, IntTy.modulus, IntTy.i64, hnok64]
  have hw_k : IntTy.toInt (⟨64, true⟩ : IntTy) (IntTy.wrap (⟨64, true⟩ : IntTy) (k : Int)) = k :=
    toInt_i64_wrap_u64 k (by omega)
  have hsum_nonneg : 0 ≤ (k : Int) + idx := hnonneg
  have hsum_small : (k : Int) + idx < 2147483648 := by omega
  have hsum_i32_ok : IntTy.inRange IntTy.i32 ((k : Int) + idx) = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i32]; omega

  -- first `if (idx > 0)` is false, so branch is skipped
  have hgt_false : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
      (boolVal false) := by
    have hng : ¬ (0 < idx) := by omega
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 0)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, hconv_i32, h1to0, hng]
  have hbcF : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hA : ExS Gen.prog ⟨loc, m, false⟩
      (.ite (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2)
              (.bin BinOp.sub (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
            .skip)
      .normal ⟨loc, m, false⟩ :=
    ExS.ite hgt_false hbcF ExS.skip

  -- second `if (idx == 0)` is false, so skipped
  have heq_false : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.eq (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
      (boolVal false) := by
    have hng : idx ≠ 0 := by omega
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 0)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, hconv_i32, h1to0, hng]
  have hB : ExS Gen.prog ⟨loc, m, false⟩
      (.ite (.bin BinOp.eq (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un UnOp.neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
            .skip)
      .normal ⟨loc, m, false⟩ :=
    ExS.ite heq_false hbcF ExS.skip

  -- the rest: set r = n + idx
  have hcast_n : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.i64 (.var 1)) (.int IntTy.i64 k) := by
    refine EvE.cast (ha := EvE.var h1) ?_
    have hmod : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
    simp [evalCast, IntTy.i64, IntTy.u64, IntTy.modulus, hmod]
  have hcast_idx : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.i64 (.var 0)) (.int IntTy.i64 (IntTy.wrap IntTy.i64 idx)) := by
    refine EvE.cast (ha := EvE.var h0) ?_
    simp [evalCast, IntTy.i64, IntTy.i32, hconv_i32]
  have hadd : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.add (some IntTy.i64) (.cast IntTy.i64 (.var 1)) (.cast IntTy.i64 (.var 0)))
      (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))) := by
    refine EvE.bin (ha := hcast_n) (hb := hcast_idx) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i64, isPtr, intOf, hw_k, hi64_lo, hcast_n_toInt, hsum_ok, arith]

  have hset : ExS Gen.prog ⟨loc, m, false⟩
      (.set 3 (.bin BinOp.add (some IntTy.i64) (.cast IntTy.i64 (.var 1)) (.cast IntTy.i64 (.var 0))))
      .normal ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩ :=
    ExS.set hadd

  -- after `set r = n + idx`, `r >= 0`, so `if (r < 0)` is skipped
  set_option linter.unusedSimpArgs false in
  have hv3 : (loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx)))) 3 =
      some (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))) := by
    simp [Locals.upd]
  have h0to64 : IntTy.toInt (⟨64, true⟩ : IntTy) 0 = 0 := by rfl
  have h0to64w : IntTy.toInt (⟨64, true⟩ : IntTy) ((⟨64, true⟩ : IntTy).wrap (IntTy.i32.toInt 0)) = 0 := by rfl
  have hlt_false : EvE Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.bin BinOp.lt (some IntTy.i64) (.var 3) (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
      (boolVal false) := by
    have hng : ¬ ((k : Int) + idx < 0) := by omega
    refine EvE.bin (ha := EvE.var hv3) (hb := EvE.cast (ha := EvE.const (.int IntTy.i32 0)) (by rfl)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i64, isPtr, intOf, h0to64, h0to64w, hi64_sum, hng]
  have hC : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.ite (.bin BinOp.lt (some IntTy.i64) (.var 3) (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un UnOp.neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
            .skip)
      .normal ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩ :=
    ExS.ite hlt_false hbcF ExS.skip

  -- the final stores and returns 1
  have hcastI32 : EvE Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.cast IntTy.i32 (.var 3)) (.int IntTy.i32 (IntTy.wrap IntTy.i32 ((k : Int) + idx))) := by
    have hv3 : (loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx)))) 3 =
        some (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))) := by
      simp [Locals.upd]
    refine EvE.cast (ha := EvE.var hv3) ?_
    have hsum_i32_ok' : IntTy.inRange IntTy.i32 ((k : Int) + idx) = true := by omega
    have hsum_i32_to : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) ((k : Int) + idx)) = (k : Int) + idx :=
      toInt_i32_wrap ((k : Int) + idx) (by omega)
    simp [evalCast, IntTy.i64, IntTy.i32, hi64_sum, hsum_i32_to, hsum_i32_ok']
  have hstore : store m (.int IntTy.i32) (.ptr b o)
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))
      = .ok (m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx))))) := by
    have hlen : (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx))).length = 4 := by
      simp [encodeLE, IntTy.wrap]
    simp [store, writeBytes, splice, hm, hblk, encodeLE, IntTy.i32, IntTy.bytes, hlen]
  have haddr : EvE Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.var 2) (.ptr b o) := by
    have hv2 : (loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx)))) 2 = some (.ptr b o) := by
      simp [Locals.upd, h2]
    exact EvE.var hv2
  have hms : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.store (.int IntTy.i32) (.var 2) (.cast IntTy.i32 (.var 3)))
      .normal ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
                m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩ :=
    ExS.store haddr hcastI32 (by simp) hstore
  have hbc1 : truthy (.int IntTy.i32 1) = .ok true := by simp [truthy]
  have hv : EvE Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
      m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩
      (if true then (.const (.int IntTy.u8 1)) else (.const (.int IntTy.u8 0))) (.int IntTy.u8 1) :=
    EvE.const (.int IntTy.u8 1)
  have hret : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
      m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩
      (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))))
      (.ret (some (.int IntTy.u8 1)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
       m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩ :=
    ExS.ret (EvE.cond (hc := EvE.const (.int IntTy.i32 1)) (hbc := hbc1) (hv := hv))
  have hDE : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.seq (.store (.int IntTy.i32) (.var 2) (.cast IntTy.i32 (.var 3)))
        (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
      (.ret (some (.int IntTy.u8 1)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
       m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩ :=
    ExS.seq hms hret
  have hCD : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.seq (.ite (.bin BinOp.lt (some IntTy.i64) (.var 3) (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un UnOp.neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
            .skip)
        (.seq (.store (.int IntTy.i32) (.var 2) (.cast IntTy.i32 (.var 3)))
          (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))))))
      (.ret (some (.int IntTy.u8 1)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
       m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩ :=
    ExS.seq hC hDE
  have hsetAll : ExS Gen.prog ⟨loc, m, false⟩
      (.seq (.set 3 (.bin BinOp.add (some IntTy.i64) (.cast IntTy.i64 (.var 1)) (.cast IntTy.i64 (.var 0))))
        (.seq (.ite (.bin BinOp.lt (some IntTy.i64) (.var 3) (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un UnOp.neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
            .skip)
          (.seq (.store (.int IntTy.i32) (.var 2) (.cast IntTy.i32 (.var 3)))
            (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))))
      (.ret (some (.int IntTy.u8 1)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
       m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩ :=
    ExS.seq hset hCD
  -- assemble through the two skipped preamble branches
  have hBset : ExS Gen.prog ⟨loc, m, false⟩
      (.seq (.ite (.bin BinOp.eq (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un UnOp.neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
            .skip)
        (.seq (.set 3 (.bin BinOp.add (some IntTy.i64) (.cast IntTy.i64 (.var 1)) (.cast IntTy.i64 (.var 0))))
          (.seq (.ite (.bin BinOp.lt (some IntTy.i64) (.var 3) (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
              (.seq (.store (.int IntTy.i32) (.var 2) (.un UnOp.neg IntTy.i32 (.const (.int IntTy.i32 1))))
                (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0))))))
              .skip)
            (.seq (.store (.int IntTy.i32) (.var 2) (.cast IntTy.i32 (.var 3)))
              (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1)) (.const (.int IntTy.u8 0)))))))))
      (.ret (some (.int IntTy.u8 1)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
       m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 ((k : Int) + idx)))), false⟩ :=
    ExS.seq hB hsetAll
  exact ExS.seq hA hBset

/-- `fix_index_f` on the zero index: invalid per the OBJ spec. Stores `-1`
    at `*out` and returns 0. -/
theorem fix_index_f_zero (loc : Locals) (m : Mem) (b o : Nat) (blk : Block)
    (h0 : loc 0 = some (.int IntTy.i32 0))
    (h2 : loc 2 = some (.ptr b o))
    (hm : m b = some blk)
    (hblk : o + 4 ≤ blk.length) :
    ExS Gen.prog ⟨loc, m, false⟩ Gen.fix_index_f.body
      (.ret (some (.int IntTy.u8 0)))
      ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ := by
  have hgt : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
      (boolVal false) := by
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 0)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, IntTy.toInt, IntTy.modulus]
  have hbcF : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hA : ExS Gen.prog ⟨loc, m, false⟩
      (.ite (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2)
              (.bin BinOp.sub (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1))
                (.const (.int IntTy.u8 0))))))
            .skip)
      .normal ⟨loc, m, false⟩ :=
    ExS.ite hgt hbcF ExS.skip
  have heq : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.eq (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
      (boolVal true) := by
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 0)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, IntTy.toInt, IntTy.modulus]
  have htT : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hneg : EvE Gen.prog ⟨loc, m, false⟩
      (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 (-1))) := by
    refine EvE.un (ha := EvE.const (.int IntTy.i32 1)) ?_
    rfl
  have hstore : store m (.int IntTy.i32) (.ptr b o)
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 (-1)))
      = .ok (m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1))))) := by
    have hlen : (encodeLE 4 (IntTy.wrap IntTy.i32 (-1))).length = 4 := by
      simp [encodeLE, IntTy.wrap]
    simp [store, writeBytes, splice, hm, hblk, encodeLE, IntTy.i32, IntTy.bytes, hlen]
  have hst : ExS Gen.prog ⟨loc, m, false⟩
      (.store (.int IntTy.i32) (.var 2) (.un .neg IntTy.i32 (.const (.int IntTy.i32 1))))
      .normal ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ :=
    ExS.store (EvE.var h2) hneg (by simp) hstore
  have hz : truthy (.int IntTy.i32 0) = .ok false := by simp [truthy]
  have hret : ExS Gen.prog ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩
      (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1))
        (.const (.int IntTy.u8 0)))))
      (.ret (some (.int IntTy.u8 0)))
      ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ :=
    ExS.ret (EvE.cond (hc := EvE.const (.int IntTy.i32 0)) (hbc := hz)
      (hv := EvE.const (.int IntTy.u8 0)))
  have hB : ExS Gen.prog ⟨loc, m, false⟩
      (.ite (.bin BinOp.eq (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un .neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1))
                (.const (.int IntTy.u8 0))))))
            .skip)
      (.ret (some (.int IntTy.u8 0)))
      ⟨loc, m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ :=
    ExS.ite heq htT (ExS.seq hst hret)
  exact ExS.seq hA (ExS.seq_ret hB)


set_option linter.unusedSimpArgs false

/-- `fix_index_f` on a negative index whose relative position falls before the
    start of the array (`n + idx < 0`): invalid per the OBJ spec. Stores `-1`
    at `*out` and returns 0. -/
theorem fix_index_f_oob (loc : Locals) (m : Mem) (b o : Nat) (blk : Block)
    (idx : Int) (k : Nat)
    (hk_small : k < 2147483648)
    (hrange : IntTy.inRange IntTy.i32 idx = true)
    (hneg : idx < 0)
    (hsum : (k : Int) + idx < 0)
    (hm : m b = some blk)
    (hblk : o + 4 ≤ blk.length)
    (h0 : loc 0 = some (.int IntTy.i32 (IntTy.wrap IntTy.i32 idx)))
    (h1 : loc 1 = some (.int IntTy.u64 k))
    (h2 : loc 2 = some (.ptr b o)) :
    ExS Gen.prog ⟨loc, m, false⟩ Gen.fix_index_f.body
      (.ret (some (.int IntTy.u8 0)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
       m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ := by
  have hbnd : -2147483648 ≤ idx ∧ idx ≤ 2147483647 := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i32] at hrange
    exact hrange
  have hconv_i32 : IntTy.toInt (⟨32, true⟩ : IntTy) (IntTy.wrap (⟨32, true⟩ : IntTy) idx) = idx :=
    toInt_i32_wrap idx hbnd
  have hi64_lo : IntTy.toInt (⟨64, true⟩ : IntTy) (IntTy.wrap (⟨64, true⟩ : IntTy) idx) = idx :=
    toInt_i64_wrap idx (by omega)
  have hi64_sum : IntTy.toInt (⟨64, true⟩ : IntTy) (IntTy.wrap (⟨64, true⟩ : IntTy) ((k : Int) + idx)) = (k : Int) + idx :=
    toInt_i64_wrap ((k : Int) + idx) (by omega)
  have hsum_ok : (⟨64, true⟩ : IntTy).inRange ((k : Int) + idx) = true := by
    simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal]; omega
  have hnok64 : ¬ (k ≥ 9223372036854775808) := by omega
  have hcast_n_toInt : IntTy.toInt (⟨64, true⟩ : IntTy) k = k := by
    simp [IntTy.toInt, IntTy.modulus, IntTy.i64, hnok64]
  have hw_k : IntTy.toInt (⟨64, true⟩ : IntTy) (IntTy.wrap (⟨64, true⟩ : IntTy) (k : Int)) = k :=
    toInt_i64_wrap_u64 k (by omega)
  have h1to0 : IntTy.toInt (⟨32, true⟩ : IntTy) 0 = 0 := by rfl
  have h0to64w : IntTy.toInt (⟨64, true⟩ : IntTy) ((⟨64, true⟩ : IntTy).wrap (IntTy.i32.toInt 0)) = 0 := by rfl
  -- `if (idx > 0)` is false
  have hgt : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
      (boolVal false) := by
    have hng : ¬ (0 < idx) := by omega
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 0)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, hconv_i32, h1to0, hng]
  have hbcF : truthy (boolVal false) = .ok false := by simp [truthy, boolVal]
  have hA : ExS Gen.prog ⟨loc, m, false⟩
      (.ite (.bin BinOp.gt (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2)
              (.bin BinOp.sub (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 1)) (.const (.int IntTy.u8 1))
                (.const (.int IntTy.u8 0))))))
            .skip)
      .normal ⟨loc, m, false⟩ :=
    ExS.ite hgt hbcF ExS.skip
  -- `if (idx == 0)` is false
  have heq : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.eq (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
      (boolVal false) := by
    have hne : idx ≠ 0 := by omega
    refine EvE.bin (ha := EvE.var h0) (hb := EvE.const (.int IntTy.i32 0)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i32, isPtr, intOf, hconv_i32, h1to0, hne]
  have hB : ExS Gen.prog ⟨loc, m, false⟩
      (.ite (.bin BinOp.eq (some IntTy.i32) (.var 0) (.const (.int IntTy.i32 0)))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un .neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1))
                (.const (.int IntTy.u8 0))))))
            .skip)
      .normal ⟨loc, m, false⟩ :=
    ExS.ite heq hbcF ExS.skip
  -- `r = (i64)n + (i64)idx`
  have hcast_n : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.i64 (.var 1)) (.int IntTy.i64 k) := by
    refine EvE.cast (ha := EvE.var h1) ?_
    have hmod : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
    simp [evalCast, IntTy.i64, IntTy.u64, IntTy.modulus, hmod]
  have hcast_idx : EvE Gen.prog ⟨loc, m, false⟩
      (.cast IntTy.i64 (.var 0)) (.int IntTy.i64 (IntTy.wrap IntTy.i64 idx)) := by
    refine EvE.cast (ha := EvE.var h0) ?_
    simp [evalCast, IntTy.i64, IntTy.i32, hconv_i32]
  have hadd : EvE Gen.prog ⟨loc, m, false⟩
      (.bin BinOp.add (some IntTy.i64) (.cast IntTy.i64 (.var 1)) (.cast IntTy.i64 (.var 0)))
      (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))) := by
    refine EvE.bin (ha := hcast_n) (hb := hcast_idx) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i64, isPtr, intOf, hw_k, hi64_lo, hcast_n_toInt,
      hsum_ok, arith]
  have hset : ExS Gen.prog ⟨loc, m, false⟩
      (.set 3 (.bin BinOp.add (some IntTy.i64) (.cast IntTy.i64 (.var 1)) (.cast IntTy.i64 (.var 0))))
      .normal ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩ :=
    ExS.set hadd
  -- `if (r < 0)` holds: store -1 and return 0
  have hv3 : (loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx)))) 3 =
      some (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))) := by
    simp [Locals.upd]
  have hlt : EvE Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.bin BinOp.lt (some IntTy.i64) (.var 3) (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
      (boolVal true) := by
    refine EvE.bin (ha := EvE.var hv3)
      (hb := EvE.cast (ha := EvE.const (.int IntTy.i32 0)) (by rfl)) ?_
    simp [evalBin, evalBinInt, binInt, IntTy.i64, isPtr, intOf, hi64_sum, h0to64w, hsum]
  have htT : truthy (boolVal true) = .ok true := by simp [truthy, boolVal]
  have hneg1 : EvE Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.un .neg IntTy.i32 (.const (.int IntTy.i32 1)))
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 (-1))) :=
    EvE.un (ha := EvE.const (.int IntTy.i32 1)) rfl
  have hstore : store m (.int IntTy.i32) (.ptr b o)
      (.int IntTy.i32 (IntTy.wrap IntTy.i32 (-1)))
      = .ok (m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1))))) := by
    have hlen : (encodeLE 4 (IntTy.wrap IntTy.i32 (-1))).length = 4 := by
      simp [encodeLE, IntTy.wrap]
    simp [store, writeBytes, splice, hm, hblk, encodeLE, IntTy.i32, IntTy.bytes, hlen]
  have haddr : EvE Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.var 2) (.ptr b o) := by
    have hv2 : (loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx)))) 2 = some (.ptr b o) := by
      simp [Locals.upd, h2]
    exact EvE.var hv2
  have hst : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.store (.int IntTy.i32) (.var 2) (.un .neg IntTy.i32 (.const (.int IntTy.i32 1))))
      .normal ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
        m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ :=
    ExS.store haddr hneg1 (by simp) hstore
  have hret : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
      m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩
      (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1))
        (.const (.int IntTy.u8 0)))))
      (.ret (some (.int IntTy.u8 0)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
        m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ := by
    have hz : truthy (.int IntTy.i32 0) = .ok false := by simp [truthy]
    exact ExS.ret (EvE.cond (hc := EvE.const (.int IntTy.i32 0)) (hbc := hz)
      (hv := EvE.const (.int IntTy.u8 0)))
  have hC : ExS Gen.prog ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))), m, false⟩
      (.ite (.bin BinOp.lt (some IntTy.i64) (.var 3) (.cast IntTy.i64 (.const (.int IntTy.i32 0))))
            (.seq (.store (.int IntTy.i32) (.var 2) (.un .neg IntTy.i32 (.const (.int IntTy.i32 1))))
              (.ret (some (.cond (.const (.int IntTy.i32 0)) (.const (.int IntTy.u8 1))
                (.const (.int IntTy.u8 0))))))
            .skip)
      (.ret (some (.int IntTy.u8 0)))
      ⟨loc.upd 3 (.int IntTy.i64 (IntTy.wrap IntTy.i64 ((k : Int) + idx))),
        m.upd b (splice blk o (encodeLE 4 (IntTy.wrap IntTy.i32 (-1)))), false⟩ :=
    ExS.ite hlt htT (ExS.seq hst hret)
  exact ExS.seq hA (ExS.seq hB (ExS.seq hset (ExS.seq_ret hC)))

end Obj.C.Proofs
