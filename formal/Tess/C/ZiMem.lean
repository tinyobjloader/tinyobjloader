/-
  Shared memory models for the MiniC limb kernels in `Tess/C/LimbGen.lean`.

  A `zi` value lives in one block whose layout is the C struct: the 8-byte
  `v` pointer at offset 0, the 8-byte `n` at offset 8 and the 4-byte sign
  at offset 16, followed by 4 bytes of padding (the kernels never read the
  sign or the padding). The `v` pointer targets a block holding `n`
  little-endian 32-bit limbs.

  All theorems here are about the translated memory model, not about the C
  implementation. They assume nothing about how the blocks were allocated,
  except their existence and their contents.
-/
import Obj.C.Semantics
import Obj.C.Splice

namespace Tess.C
open Obj.C

def u32 : IntTy := ⟨32, false⟩
def u64 : IntTy := ⟨64, false⟩

/-- Layout of `struct zi` in little-endian memory: `v` pointer, `n`, `sign`,
4 bytes of padding. The kernels read only the pointer and `n`. -/
def ziBlock (vblk : Nat) (n : Nat) (sign : Int) : Block :=
  encodeLE 8 (ptrPack (.ptr vblk 0)) ++ encodeLE 8 n ++
    encodeLE 4 (IntTy.wrap IntTy.i32 sign) ++ [0, 0, 0, 0]

theorem ziBlock_length (vblk : Nat) (n : Nat) (sign : Int) :
    (ziBlock vblk n sign).length = 24 := by
  simp [ziBlock]

theorem encodeLE_length (k n : Nat) : (encodeLE k n).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [encodeLE, ih]

theorem pos_pow_256 (k : Nat) : 0 < 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih (by simp)

theorem decodeLE_encodeLE (n k : Nat) : decodeLE (encodeLE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one, encodeLE, decodeLE]
  | succ k ih =>
      simp only [encodeLE, decodeLE, ih, Nat.pow_succ]
      have hbyte : (n % 256).toUInt8.toNat = n % 256 := by
        simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
        show (n % 256) % 256 = n % 256
        exact Nat.mod_eq_of_lt (Nat.mod_lt n (by simp))
      rw [hbyte]
      have hk : 0 < 256 ^ k := pos_pow_256 k
      have hsk : n / 256 % 256 ^ k < 256 ^ k := Nat.mod_lt _ hk
      have hr : n % 256 < 256 := Nat.mod_lt _ (by simp)
      have hle : 256 * (n / 256 % 256 ^ k) + n % 256 < 256 ^ k * 256 := by omega
      have hd' := Nat.div_add_mod (n / 256) (256 ^ k)
      have step1 : n = 256 ^ k * 256 * (n / 256 / 256 ^ k) + (256 * (n / 256 % 256 ^ k) + n % 256) :=
        calc n = 256 * (n / 256) + n % 256 := (Nat.div_add_mod n 256).symm
          _ = 256 * (256 ^ k * (n / 256 / 256 ^ k) + n / 256 % 256 ^ k) + n % 256 := by rw [hd']
          _ = 256 * (256 ^ k * (n / 256 / 256 ^ k)) + 256 * (n / 256 % 256 ^ k) + n % 256 := by
              rw [Nat.mul_add, Nat.add_assoc]
          _ = 256 ^ k * 256 * (n / 256 / 256 ^ k) + (256 * (n / 256 % 256 ^ k) + n % 256) := by
              rw [← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ k), Nat.add_assoc]
      conv => rhs; rw [step1, Nat.add_comm (256 ^ k * 256 * (n / 256 / 256 ^ k)) (256 * (n / 256 % 256 ^ k) + n % 256),
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hle]
      exact Nat.add_comm _ _

/-- Pack/unpack round trip for in-range pointers (offset < 2^32). -/
theorem ptrUnpack_ptrPack (b o : Nat) (ho : o < 4294967296) :
    ptrUnpack (ptrPack (.ptr b o)) = .ptr b o := by
  have hne : ptrPack (.ptr b o) ≠ 0 := by
    simp only [ptrPack]
    omega
  unfold ptrUnpack
  rw [if_neg hne]
  simp only [ptrPack]
  have hdiv : (1 + b * 4294967296 + o - 1) / 4294967296 = b := by
    rw [show 1 + b * 4294967296 + o - 1 = 4294967296 * b + o from by omega,
        Nat.mul_add_div (by omega : (4294967296:Nat) > 0), Nat.div_eq_of_lt ho]
    simp
  have hmod : (1 + b * 4294967296 + o - 1) % 4294967296 = o := by
    rw [show 1 + b * 4294967296 + o - 1 = 4294967296 * b + o from by omega,
        Nat.mul_add_mod, Nat.mod_eq_of_lt ho]
  rw [hdiv, hmod]

theorem load_ptr_packed (m : Mem) (blk : Block) (b o : Nat) (p : Nat)
    (hm : m b = some blk) (hoff : o + 8 ≤ blk.length)
    (hp : p < 18446744073709551616)
    (hpre : (blk.drop o).take 8 = encodeLE 8 p) :
    load m .ptr (.ptr b o) = .ok (ptrUnpack p) := by
  have hrb : readBytes m b o 8 = .ok (encodeLE 8 p) := by
    simp only [readBytes, hm, if_pos hoff, hpre]
  have hsize : Ty.size .ptr = 8 := rfl
  simp only [load, hsize, hrb, Res.bind_eq, Res.bind_ok]
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt hp]
  rfl

theorem load_u32_at (m : Mem) (vb : Nat) (blk : Block) (o n : Nat)
    (hm : m vb = some blk) (hoff : o + 4 ≤ blk.length)
    (hpre : (blk.drop o).take 4 = encodeLE 4 n) :
    load m (.int u32) (.ptr vb o) = .ok (.int u32 (n % 2 ^ 32)) := by
  have hrb : readBytes m vb o 4 = .ok (encodeLE 4 n) := by
    simp only [readBytes, hm, if_pos hoff, hpre]
  have hsize : Ty.size (.int u32) = 4 := rfl
  simp only [load, hsize, hrb, Res.bind_eq, Res.bind_ok]
  rw [decodeLE_encodeLE, show (256 : Nat) ^ 4 = 2 ^ 32 from rfl]
  rfl

theorem load_u64_at (m : Mem) (vb : Nat) (blk : Block) (o n : Nat)
    (hm : m vb = some blk) (hoff : o + 8 ≤ blk.length)
    (hpre : (blk.drop o).take 8 = encodeLE 8 n) :
    load m (.int u64) (.ptr vb o) = .ok (.int u64 (n % 2 ^ 64)) := by
  have hrb : readBytes m vb o 8 = .ok (encodeLE 8 n) := by
    simp only [readBytes, hm, if_pos hoff, hpre]
  have hsize : Ty.size (.int u64) = 8 := rfl
  simp only [load, hsize, hrb, Res.bind_eq, Res.bind_ok]
  rw [decodeLE_encodeLE, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]
  rfl

theorem load_ziBlock_v (m : Mem) (zb vblk : Nat) (n : Nat) (sign : Int)
    (hm : m zb = some (ziBlock vblk n sign)) (hb : vblk < 4294967296) :
    load m .ptr (.ptr zb 0) = .ok (.ptr vblk 0) := by
  have hpre : ((ziBlock vblk n sign).drop 0).take 8 = encodeLE 8 (ptrPack (.ptr vblk 0)) := by
    simp [ziBlock, encodeLE_length]
  have hp : ptrPack (.ptr vblk 0) < 18446744073709551616 := by
    simp only [ptrPack]
    omega
  rw [load_ptr_packed m (ziBlock vblk n sign) zb 0 _ hm (by simp [ziBlock_length]) hp hpre,
    ptrUnpack_ptrPack vblk 0 (by omega)]

theorem load_ziBlock_n (m : Mem) (zb vblk : Nat) (n : Nat) (sign : Int)
    (hm : m zb = some (ziBlock vblk n sign)) :
    load m (.int u64) (.ptr zb 8) = .ok (.int u64 (n % 2 ^ 64)) := by
  have hpre : ((ziBlock vblk n sign).drop 8).take 8 = encodeLE 8 n := by
    simp [ziBlock, encodeLE_length]
  rw [load_u64_at m zb (ziBlock vblk n sign) 8 n hm (by simp [ziBlock_length]) hpre]

/-- Limb arrays are stored as consecutive little-endian 32-bit words. -/
def limbBytes (limbs : List Nat) : Block := limbs.flatMap (encodeLE 4)

theorem limbBytes_length (limbs : List Nat) :
    (limbBytes limbs).length = 4 * limbs.length := by
  induction limbs with
  | nil => rfl
  | cons x xs ih =>
      have hlen : (limbBytes (x :: xs)).length = 4 + (limbBytes xs).length := by
        rw [limbBytes, List.flatMap_cons, List.length_append, encodeLE_length]
        rfl
      rw [hlen, ih, List.length_cons]
      omega

theorem limbBytes_drop (limbs : List Nat) (i : Nat) :
    (limbBytes limbs).drop (4 * i) = limbBytes (limbs.drop i) := by
  induction limbs generalizing i with
  | nil => simp [limbBytes]
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [limbBytes, List.flatMap_cons]
          rw [show 4 * (i + 1) = 4 + 4 * i from by omega, List.drop_append,
            List.drop_eq_nil_of_le (by rw [encodeLE_length]; omega :
              (encodeLE 4 x).length ≤ 4 + 4 * i),
            List.nil_append]
          rw [show 4 + 4 * i - (encodeLE 4 x).length = 4 * i from by
            rw [encodeLE_length]; omega]
          rw [show List.drop (i + 1) (x :: xs) = List.drop i xs from rfl]
          exact ih i

/-- The encoding of limb `i` is exposed after the 4-byte prefix. -/
theorem limbBytes_take (limbs : List Nat) (i : Nat) (hi : i < limbs.length) :
    (limbBytes limbs).drop (4 * i) =
      encodeLE 4 (limbs[i]'hi) ++ limbBytes (limbs.drop (i + 1)) := by
  rw [limbBytes_drop, List.drop_eq_getElem_cons hi]
  show limbBytes (limbs[i]'hi :: limbs.drop (i + 1)) = _
  rfl

theorem load_limb (m : Mem) (vb : Nat) (limbs : List Nat) (i : Nat)
    (hm : m vb = some (limbBytes limbs)) (hi : i < limbs.length) :
    load m (.int u32) (.ptr vb (4 * i)) = .ok (.int u32 (limbs[i]'hi % 2 ^ 32)) := by
  have hlen : (limbBytes limbs).length = 4 * limbs.length := limbBytes_length limbs
  have hoff : 4 * i + 4 ≤ (limbBytes limbs).length := by omega
  have hpre : ((limbBytes limbs).drop (4 * i)).take 4 = encodeLE 4 (limbs[i]'hi) := by
    rw [limbBytes_take limbs i hi,
      List.take_append_of_le_length (Nat.le_of_eq (encodeLE_length 4 (limbs[i]'hi))),
      List.take_of_length_le (Nat.le_of_eq (encodeLE_length 4 (limbs[i]'hi)))]
  have hsize : Ty.size (.int u32) = 4 := rfl
  exact load_u32_at m vb (limbBytes limbs) (4 * i) _ hm hoff hpre

/-- Splicing after a leading block is splicing inside the tail. -/
theorem splice_append_left (l₁ l₂ bs : Block) (i : Nat)
    (h : i ≥ l₁.length) (_hlt : l₁.length + i ≤ l₁.length + l₂.length) :
    splice (l₁ ++ l₂) i bs = l₁ ++ splice l₂ (i - l₁.length) bs := by
  have hdrop : i + bs.length - l₁.length = i - l₁.length + bs.length := by omega
  simp only [splice]
  rw [List.take_append, List.take_of_length_le (by omega : l₁.length ≤ i),
    List.drop_append, List.drop_eq_nil_of_le (show l₁.length ≤ i + bs.length by omega),
    List.nil_append, hdrop]
  simp [List.append_assoc]

theorem limbBytes_set (limbs : List Nat) (i : Nat) (hi : i < limbs.length) (v : Nat) :
    limbBytes (limbs.set i v) = splice (limbBytes limbs) (4 * i) (encodeLE 4 v) := by
  induction limbs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          show limbBytes (v :: xs) = splice (encodeLE 4 x ++ limbBytes xs) 0 (encodeLE 4 v)
          simp [limbBytes, splice]
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          have hx := ih i hi'
          show encodeLE 4 x ++ limbBytes (xs.set i v) =
            splice (encodeLE 4 x ++ limbBytes xs) (4 * (i + 1)) (encodeLE 4 v)
          rw [show 4 * (i + 1) = 4 + 4 * i from by omega,
            splice_append_left (encodeLE 4 x) (limbBytes xs) (encodeLE 4 v)
              (4 + 4 * i) (by rw [encodeLE_length]; omega)
              (by rw [encodeLE_length, limbBytes_length]; omega),
            encodeLE_length, Nat.add_sub_cancel_left, hx]

theorem store_limb (m : Mem) (vb : Nat) (limbs : List Nat) (i : Nat) (v : Nat)
    (hm : m vb = some (limbBytes limbs)) (hi : i < limbs.length) :
    store m (.int u32) (.ptr vb (4 * i)) (.int u32 v) =
      .ok (m.upd vb (limbBytes (limbs.set i v))) := by
  rw [limbBytes_set limbs i hi v]
  have hoff : 4 * i + (encodeLE 4 v).length ≤ (limbBytes limbs).length := by
    rw [encodeLE_length, limbBytes_length]; omega
  simp only [store, splice, writeBytes, hm]
  rw [show IntTy.bytes u32 = 4 from rfl, if_pos hoff]
  rfl
end Tess.C
