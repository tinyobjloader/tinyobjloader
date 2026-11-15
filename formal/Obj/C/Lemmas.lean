/-
  Lemmas for symbolic execution of MiniC programs.
-/
import Obj.C.Semantics
import Obj.Glb

namespace Obj.C

theorem decodeLE_take_one_drop (d : List UInt8) (o : Nat) (h : o < d.length) :
    decodeLE (List.take 1 (List.drop o d)) = Glb.byteAt d o := by
  unfold Glb.byteAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  have : List.drop o d = d[o] :: List.drop (o + 1) d := by
    rw [List.drop_eq_getElem_cons h]
  rw [this, List.take_succ_cons, List.take_zero]
  simp only [decodeLE]; omega

theorem byteAt_lt (d : List UInt8) (o : Nat) : Glb.byteAt d o < 256 := by
  unfold Glb.byteAt; exact UInt8.toNat_lt _

/-- `a ||| b * 2^k = a + b * 2^k` when `a < 2^k`. -/
theorem or_mul_two_pow {a b k : Nat} (h : a < 2 ^ k) : a ||| b * 2 ^ k = a + b * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h]; omega

theorem rd32_lt (d : List UInt8) (o : Nat) : Glb.rd32 d o < 2 ^ 32 := by
  unfold Glb.rd32
  have := byteAt_lt d o; have := byteAt_lt d (o + 1)
  have := byteAt_lt d (o + 2); have := byteAt_lt d (o + 3)
  omega

theorem rd64_lt (d : List UInt8) (o : Nat) : Glb.rd64 d o < 2 ^ 64 := by
  unfold Glb.rd64
  have := rd32_lt d o; have := rd32_lt d (o + 4)
  omega

/-- The value computed by `tg3__rd_u32le`'s expression tree. -/
theorem rd32_or (d : List UInt8) (o : Nat) :
    Glb.byteAt d o ||| Glb.byteAt d (o + 1) * 256 % 4294967296 |||
      Glb.byteAt d (o + 2) * 65536 % 4294967296 |||
      Glb.byteAt d (o + 3) * 16777216 % 4294967296 = Glb.rd32 d o := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  have b2 := byteAt_lt d (o + 2); have b3 := byteAt_lt d (o + 3)
  rw [Nat.mod_eq_of_lt (by omega : Glb.byteAt d (o + 1) * 256 < 4294967296),
      Nat.mod_eq_of_lt (by omega : Glb.byteAt d (o + 2) * 65536 < 4294967296),
      Nat.mod_eq_of_lt (by omega : Glb.byteAt d (o + 3) * 16777216 < 4294967296)]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, or_mul_two_pow (by omega)]
  rw [show (65536 : Nat) = 2 ^ 16 by rfl, or_mul_two_pow (by omega)]
  rw [show (16777216 : Nat) = 2 ^ 24 by rfl, or_mul_two_pow (by omega)]
  unfold Glb.rd32; omega

theorem rd64_or (d : List UInt8) (o : Nat) :
    Glb.rd32 d o ||| Glb.rd32 d (o + 4) * 4294967296 % 18446744073709551616 = Glb.rd64 d o := by
  have := rd32_lt d o; have := rd32_lt d (o + 4)
  rw [Nat.mod_eq_of_lt (by omega : Glb.rd32 d (o + 4) * 4294967296 < 18446744073709551616)]
  rw [show (4294967296 : Nat) = 2 ^ 32 by rfl, or_mul_two_pow (by omega)]
  unfold Glb.rd64; omega

end Obj.C

namespace Obj.C

@[simp] theorem byteAt_mod32 (d : List UInt8) (o : Nat) :
    Glb.byteAt d o % 4294967296 = Glb.byteAt d o :=
  Nat.mod_eq_of_lt (by have := byteAt_lt d o; omega)

@[simp] theorem encodeLE_length (k n : Nat) : (encodeLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [encodeLE, ih]

theorem decodeLE_encodeLE (k n : Nat) : decodeLE (encodeLE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [encodeLE, decodeLE, Nat.mod_one]
  | succ k ih =>
    simp only [encodeLE, decodeLE, ih]
    have h1 : ((n % 256).toUInt8).toNat = n % 256 := by
      simp [Nat.toUInt8, UInt8.toNat_ofNat]
    rw [h1, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

end Obj.C

namespace Obj.C
@[simp] theorem rd32_mod64 (d : List UInt8) (o : Nat) :
    Glb.rd32 d o % 18446744073709551616 = Glb.rd32 d o :=
  Nat.mod_eq_of_lt (by have := rd32_lt d o; omega)
@[simp] theorem rd32_mod32 (d : List UInt8) (o : Nat) :
    Glb.rd32 d o % 4294967296 = Glb.rd32 d o :=
  Nat.mod_eq_of_lt (by have := rd32_lt d o; omega)
@[simp] theorem rd64_mod64 (d : List UInt8) (o : Nat) :
    Glb.rd64 d o % 18446744073709551616 = Glb.rd64 d o :=
  Nat.mod_eq_of_lt (by have := rd64_lt d o; omega)
end Obj.C

namespace Obj.C
@[simp] theorem Mem.upd_same (m : Mem) (b : Nat) (x : Block) : (m.upd b x) b = some x := by
  simp [Mem.upd]
@[simp] theorem Mem.upd_ne (m : Mem) {b b' : Nat} (x : Block) (h : b' ≠ b) : (m.upd b x) b' = m b' := by
  simp [Mem.upd, h]
@[simp] theorem Mem.upd_upd (m : Mem) (b : Nat) (x y : Block) : (m.upd b x).upd b y = m.upd b y := by
  funext b'; simp only [Mem.upd]; split <;> rfl
@[simp] theorem Locals.upd_same (l : Locals) (i : Nat) (v : Val) : (l.upd i v) i = some v := by
  simp [Locals.upd]
@[simp] theorem Locals.upd_ne (l : Locals) {i j : Nat} (v : Val) (h : j ≠ i) : (l.upd i v) j = l j := by
  simp [Locals.upd, h]
@[simp] theorem Locals.upd_upd (l : Locals) (i : Nat) (v w : Val) : (l.upd i v).upd i w = l.upd i w := by
  funext j; simp only [Locals.upd]; split <;> rfl
@[simp] theorem frameLocals_apply (ps : List Nat) (vs : List Val) (i : Nat) :
    frameLocals ps vs i = (match ps.idxOf? i with | some k => vs[k]? | none => none) := rfl
@[simp] theorem wrap_zero (t : IntTy) : t.wrap 0 = 0 := by simp [IntTy.wrap]
@[simp] theorem wrap_ofNat (t : IntTy) (n : Nat) : t.wrap (n : Int) = n % t.modulus := by
  simp only [IntTy.wrap]; omega
end Obj.C

namespace Obj.C
@[simp] theorem and_three (x : Nat) : x &&& 3 = x % 4 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 2
  simpa using this
end Obj.C

namespace Obj.C
@[simp] theorem mod4_le4 (x : Nat) : x % 4 ≤ 4 := Nat.le_of_lt (Nat.mod_lt _ (by decide))
end Obj.C

namespace Obj.C
theorem decodeLE_take_one (d : List UInt8) (h : 0 < d.length) :
    decodeLE (List.take 1 d) = Glb.byteAt d 0 := by
  have := decodeLE_take_one_drop d 0 h
  simpa using this
end Obj.C

namespace Obj.C
theorem decodeLE_take_one_tail (d : List UInt8) (h : 1 < d.length) :
    decodeLE (List.take 1 d.tail) = Glb.byteAt d 1 := by
  have := decodeLE_take_one_drop d 1 h
  simpa using this
end Obj.C
