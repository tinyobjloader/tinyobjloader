/-
  Refinement proofs for `tobj_skip_space` and `tobj_next_token` (tiny_obj_c.c)
  in the *cursor-struct layout* used by the loader: the cursor `{p, end}` is a
  16-byte block `cc` holding two packed pointers into the input block `bb`,
  and the token outputs are two 8-byte blocks.

  * `skip_space_exs`: `*pp` ends at `skipStop bytes pos` (the first non-space/tab
    byte), with the other blocks untouched.
  * `next_token_none` / `next_token_some`: the translated function returns 0 or 1,
    stores the token start and length, and leaves the cursor at the token end.
  * `nextToken_eq` identifies these offsets with the pure specification
    `Obj.nextToken` (`Obj/Spec.lean`), so the pair of theorems is a full
    refinement of `nextToken` for arbitrary byte buffers and start offsets.
  * The cursor end is an arbitrary `e ≤ bytes.length` (the token slice length)
    and the pure side reads `(bytes.take e)`, so tokens that live inside a
    larger input block are covered; `e = bytes.length` is the whole-buffer case.
  * Reusable pieces: `isSpace_call` (the whitespace predicate as an expression
    call on any byte, including bytes ≥ 128), `load_ptr_*`/`store_ptr_*` for
    packed pointer cells, `tw_inside`/`tw_boundary` for `takeWhile`.
-/
import Obj.C.Proofs.ObjMemcpy
import Obj.C.Proofs.ObjIsSpace
import Obj.Spec
namespace Obj.C.Proofs
open Obj.C Obj

theorem load_i8_at (m : Mem) (b o : Nat) (blk : Block) (hm : m b = some blk) (h : o < blk.length) :
    load m (.int ⟨8, true⟩) (.ptr b o) = .ok (.int ⟨8, true⟩ (blk[o]'h).toNat) := by
  have hd : blk.drop o = blk[o] :: blk.drop (o + 1) := List.drop_eq_getElem_cons h
  have hrb : readBytes m b o 1 = .ok [blk[o]] := by
    simp only [readBytes, hm]
    rw [if_pos (by omega), hd]
    rfl
  have : Ty.size (.int ⟨8, true⟩) = 1 := rfl
  simp only [load, this, hrb, Res.bind_eq, Res.bind_ok]
  simp [decodeLE]


theorem isSpace_body_false (byte : UInt8) (hnotspace : scanSpace byte.toNat = false) (m : Mem) :
    ExS Gen.prog ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], m, true⟩ Gen.tobj_is_space.body
      (.ret (some (.int IntTy.u8 0))) ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], m, true⟩ := by
  let c : Int := IntTy.toInt IntTy.i8 byte.toNat
  have hbyteRange : byte.toNat < 256 := by
    have h := UInt8.toNat_lt byte
    omega
  have hrange : IntTy.inRange IntTy.i8 c = true := by
    by_cases hhigh : 128 ≤ byte.toNat
    · simp [c, IntTy.toInt, IntTy.modulus, IntTy.inRange, IntTy.minVal,
        IntTy.maxVal, IntTy.i8, hhigh]
      omega
    · have hlow : byte.toNat < 128 := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.inRange, IntTy.minVal,
        IntTy.maxVal, IntTy.i8, hlow, hhigh]
      omega
  have hwrap : IntTy.wrap IntTy.i8 c = byte.toNat := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      simp
    · have hc : c = (byte.toNat : Int) - 256 := by
        have hhigh : 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      change (((byte.toNat : Int) - 256) % (256 : Int)).toNat = byte.toNat
      have hmod : ((byte.toNat : Int) - 256) % (256 : Int) = byte.toNat := by
        have hmod := Int.emod_add_emod (-256) (256 : Int) (byte.toNat : Int)
        have hz : (-256 : Int) % 256 = 0 := by decide
        have hlt : 0 ≤ (byte.toNat : Int) := by omega
        have hlt2 : (byte.toNat : Int) < 256 := by omega
        have hnat : (byte.toNat : Int) % 256 = byte.toNat :=
          Int.emod_eq_of_lt hlt hlt2
        rw [hz] at hmod
        have hleft : (0 + (byte.toNat : Int)) % 256 = byte.toNat := by
          simpa using hnat
        rw [hleft] at hmod
        simpa [Int.sub_eq_add_neg, Int.add_comm] using hmod.symm
      rw [hmod]
      simp
  have h32 : c ≠ 32 := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      intro heq
      have hraw : byte.toNat = 32 := by omega
      simp [scanSpace, hraw] at hnotspace
    · have hhigh : 128 ≤ byte.toNat := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      omega
  have h9 : c ≠ 9 := by
    by_cases hsmall : byte.toNat < 128
    · have hc : c = byte.toNat := by
        have hnohigh : ¬ 128 ≤ byte.toNat := by omega
        simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hnohigh]
      intro heq
      have hraw : byte.toNat = 9 := by omega
      simp [scanSpace, hraw] at hnotspace
    · have hhigh : 128 ≤ byte.toNat := by omega
      simp [c, IntTy.toInt, IntTy.modulus, IntTy.i8, hhigh]
      omega
  let loc := frameLocals [0] [.int IntTy.i8 byte.toNat]
  have hlocal : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 c)) := by
    simp [loc, frameLocals, hwrap]
  exact Obj.C.Proofs.tobj_is_space_other loc m c (ro := true) hrange h32 h9 hlocal

theorem isSpace_body_true (byte : UInt8) (hspace : scanSpace byte.toNat = true) (m : Mem) :
    ExS Gen.prog ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], m, true⟩ Gen.tobj_is_space.body
      (.ret (some (.int IntTy.u8 1))) ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], m, true⟩ := by
  have hs : byte.toNat = 9 ∨ byte.toNat = 32 := by
    simp [scanSpace] at hspace
    omega
  let loc := frameLocals [0] [.int IntTy.i8 byte.toNat]
  have hwrap : IntTy.wrap IntTy.i8 (byte.toNat : Int) = byte.toNat := by
    rcases hs with h | h <;> simp [IntTy.wrap, IntTy.modulus, IntTy.i8, h]
  have hlocal : loc 0 = some (.int IntTy.i8 (IntTy.wrap IntTy.i8 (byte.toNat : Int))) := by
    simp [loc, frameLocals, hwrap]
  rw [hwrap] at hlocal
  rcases hs with h | h
  · exact Obj.C.Proofs.tobj_is_space_tab loc m (ro := true) (by simpa [h] using hlocal)
  · exact Obj.C.Proofs.tobj_is_space_space loc m (ro := true) (by simpa [h] using hlocal)

/-- Evaluating `(int)tobj_is_space(*e)` for a pointer expression `e` into a byte block. -/
theorem isSpace_call (s : State) (e : Expr) (b o : Nat) (blk : Block) (byte : UInt8)
    (he : EvE Gen.prog s e (.ptr b o)) (hm : s.mem b = some blk) (hlt : o < blk.length)
    (ho : blk[o]? = some byte) :
    EvE Gen.prog s (.cast ⟨32, true⟩ (.call 6 [.load (.int ⟨8, true⟩) e]))
      (.int ⟨32, true⟩ (if scanSpace byte.toNat then 1 else 0)) := by
  have hbyte : blk[o]'hlt = byte := by
    have := List.getElem?_eq_getElem hlt
    rw [this] at ho; exact Option.some.inj ho
  have hload : EvE Gen.prog s (.load (.int ⟨8, true⟩) e) (.int ⟨8, true⟩ byte.toNat) := by
    apply EvE.load he
    have := load_i8_at s.mem b o blk hm hlt
    rw [hbyte] at this; exact this
  have hargs : EvArgs Gen.prog s [.load (.int ⟨8, true⟩) e] [.int ⟨8, true⟩ byte.toNat] :=
    EvArgs.cons hload EvArgs.nil
  by_cases hsp : scanSpace byte.toNat = true
  · have hcall : EvE Gen.prog s (.call 6 [.load (.int ⟨8, true⟩) e]) (.int IntTy.u8 1) := by
      have := EvE.call hargs (f := 6) (fn := Gen.tobj_is_space) (by rfl) (by rfl)
        (isSpace_body_true byte hsp s.mem)
      simpa using this
    have hcast : evalCast ⟨32, true⟩ (.int IntTy.u8 1) = .ok (.int ⟨32, true⟩ 1) := by
      simp [evalCast, IntTy.u8, IntTy.modulus]
    simpa [hsp] using EvE.cast hcall hcast
  · have hsp' : scanSpace byte.toNat = false := by simpa using hsp
    have hcall : EvE Gen.prog s (.call 6 [.load (.int ⟨8, true⟩ ) e]) (.int IntTy.u8 0) := by
      have := EvE.call hargs (f := 6) (fn := Gen.tobj_is_space) (by rfl) (by rfl)
        (isSpace_body_false byte hsp' s.mem)
      simpa using this
    have hcast : evalCast ⟨32, true⟩ (.int IntTy.u8 0) = .ok (.int ⟨32, true⟩ 0) := by
      simp [evalCast, IntTy.u8, IntTy.modulus]
    simpa [hsp'] using EvE.cast hcall hcast


theorem tw_inside {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (hk : k < (l.takeWhile p).length) : ∃ x, l[k]? = some x ∧ p x = true := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    by_cases ha : p a = true
    · simp only [List.takeWhile_cons, ha, if_true, List.length_cons] at hk
      cases k with
      | zero => exact ⟨a, rfl, ha⟩
      | succ k => simpa using ih k (by omega)
    · simp [List.takeWhile_cons, ha] at hk

theorem tw_boundary {α : Type} (p : α → Bool) (l : List α)
    (h : (l.takeWhile p).length < l.length) :
    ∃ x, l[(l.takeWhile p).length]? = some x ∧ p x = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : p a = true
    · simp only [List.takeWhile_cons, ha, if_true, List.length_cons] at h ⊢
      simpa using ih (by omega)
    · simp [List.takeWhile_cons, ha]

def ssBody : Stmt :=
  (.ite (.land (.bin .lt (some IntTy.u64) (.var 2) (.var 1))
      (.cast ⟨32, true⟩ (.call 6 [.load (.int ⟨8, true⟩) (.var 2)])))
    (.set 2 (.index (.var 2) (.const (.int ⟨64, true⟩ 1)) 1)) .brk)

/-- Get an element of the first-`e` slice of `bytes` dropped by `pos`; the
    slice agrees with `bytes` at every in-slice offset. -/
theorem take_drop_getElem? (bytes : Block) (e pos k : Nat) (hk : k < e - pos) :
    ((bytes.take e).drop pos)[k]? = bytes[pos + k]? := by
  rw [List.drop_take, List.getElem?_take_of_lt hk, List.getElem?_drop]

theorem ss_ast : Gen.tobj_skip_space_loop0 = .loop ssBody .skip := rfl

/-- Absolute stop offset of the whitespace skip. -/
def skipStop (bytes : Block) (pos : Nat) : Nat :=
  pos + ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length

theorem skipStop_le (bytes : Block) (pos : Nat) (hpos : pos ≤ bytes.length) :
    skipStop bytes pos ≤ bytes.length := by
  unfold skipStop
  have := (List.takeWhile_prefix (fun b : UInt8 => scanSpace b.toNat)
    (l := bytes.drop pos)).length_le
  simp at this; omega


theorem state_upd_self (s : State) (i : Nat) (v : Val) (h : s.locals i = some v) :
    ({ s with locals := s.locals.upd i v } : State) = s := by
  cases s with
  | mk l m r =>
    simp only at h
    simp only [State.mk.injEq, and_true]
    funext k
    by_cases hk : k = i
    · subst hk; simp [Locals.upd, h]
    · simp [Locals.upd, hk]

theorem ss_loop (bb : Nat) (bytes : Block) (pos e : Nat) (hpos : pos ≤ e)
    (he : e ≤ bytes.length) (s : State)
    (l1 : s.locals 1 = some (.ptr bb e)) (l2 : s.locals 2 = some (.ptr bb pos))
    (hm : s.mem bb = some bytes) :
    ∃ sf, ExS Gen.prog s (.loop ssBody .skip) .normal sf ∧
      sf = { s with locals := s.locals.upd 2 (.ptr bb (skipStop (bytes.take e) pos)) } := by
  let stop := skipStop (bytes.take e) pos
  have hseLen : (bytes.take e).length = e := by simp [List.length_take, he]
  have hstopLe : stop ≤ e := by
    have hsl : (bytes.take e).length = e := by simp [List.length_take, he]
    have := skipStop_le (bytes.take e) pos (by simpa [hsl] using hpos)
    rwa [hsl] at this
  have hstopLe' : stop ≤ bytes.length := by omega
  have hposStop : pos ≤ stop := by simp [stop, skipStop]
  let P : Nat → State → Prop := fun j st => ∃ q, q + j = stop ∧ pos ≤ q ∧
    st = { s with locals := s.locals.upd 2 (.ptr bb q) }
  have hget : ∀ i, i < e - pos → ((bytes.take e).drop pos)[i]? = bytes[pos + i]? := by
    intro i hi
    rw [List.drop_take, List.getElem?_take, if_pos hi, List.getElem?_drop]
  have hstep : ∀ j st, P (j + 1) st → ∃ s1 s2, ExS Gen.prog st ssBody .normal s1 ∧
      ExS Gen.prog s1 .skip .normal s2 ∧ P j s2 := by
    intro j st ⟨q, hq, hpq, hst⟩
    subst hst
    have hqlt : q < stop := by omega
    have hqlen : q < e := by omega
    have hqlen' : q < bytes.length := by omega
    obtain ⟨byte, hb, hsp⟩ := tw_inside (fun b : UInt8 => scanSpace b.toNat) ((bytes.take e).drop pos)
      (q - pos) (by simp only [stop, skipStop] at hqlt; omega)
    have hbyte : bytes[q]? = some byte := by
      have hi : q - pos < e - pos := by omega
      rw [hget (q - pos) hi] at hb
      have : pos + (q - pos) = q := by omega
      rwa [this] at hb
    let st : State := { s with locals := s.locals.upd 2 (.ptr bb q) }
    have hv2 : EvE Gen.prog st (.var 2) (.ptr bb q) := EvE.var (by simp [st, Locals.upd])
    have hv1 : EvE Gen.prog st (.var 1) (.ptr bb e) :=
      EvE.var (by simpa [st, Locals.upd] using l1)
    have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.var 2) (.var 1)) (boolVal true) := by
      apply EvE.bin hv2 hv1
      simp [evalBin, isPtr, boolVal, hqlen]
    have hcall := isSpace_call st (.var 2) bb q bytes byte hv2 (by simpa [st] using hm) hqlen' hbyte
    rw [if_pos hsp] at hcall
    have hland : EvE Gen.prog st (.land (.bin .lt (some IntTy.u64) (.var 2) (.var 1))
        (.cast ⟨32, true⟩ (.call 6 [.load (.int ⟨8, true⟩) (.var 2)]))) (boolVal true) :=
      EvE.land_true hlt (by simp [truthy, boolVal]) hcall (by simp [truthy])
    have hidx : EvE Gen.prog st (.index (.var 2) (.const (.int ⟨64, true⟩ 1)) 1) (.ptr bb (q + 1)) := by
      apply EvE.index hv2 (EvE.const _)
      have h1 : IntTy.toInt ⟨64, true⟩ 1 = 1 := by simp [IntTy.toInt, IntTy.modulus]
      simp [IntTy.signed, ptrAdd, hm, st, h1]
      omega
    have hset := ExS.set (p := Gen.prog) (i := 2) hidx
    refine ⟨{ st with locals := st.locals.upd 2 (.ptr bb (q + 1)) }, _, ?_, ExS.skip, q + 1, by omega, by omega, ?_⟩
    · unfold ssBody
      exact ExS.ite hland (bc := true) (by simp [truthy, boolVal]) (by simpa using hset)
    · simp [st, Locals.upd_upd]
  have hexit : ∀ st, P 0 st → ∃ s1, ExS Gen.prog st ssBody .brk s1 ∧ P 0 s1 := by
    intro st ⟨q, hq, hpq, hst⟩
    subst hst
    have hqs : q = stop := by omega
    have hqs' : q = pos + (((bytes.take e).drop pos).takeWhile (fun b => scanSpace b.toNat)).length := hqs
    let st : State := { s with locals := s.locals.upd 2 (.ptr bb q) }
    have hv2 : EvE Gen.prog st (.var 2) (.ptr bb q) := EvE.var (by simp [st, Locals.upd])
    have hv1 : EvE Gen.prog st (.var 1) (.ptr bb e) :=
      EvE.var (by simpa [st, Locals.upd] using l1)
    refine ⟨st, ?_, ⟨q, by omega, hpq, rfl⟩⟩
    unfold ssBody
    by_cases hend : q = e
    · have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.var 2) (.var 1)) (boolVal false) := by
        apply EvE.bin hv2 hv1
        simp [evalBin, isPtr, boolVal, hend]
      have hland : EvE Gen.prog st (.land (.bin .lt (some IntTy.u64) (.var 2) (.var 1))
          (.cast ⟨32, true⟩ (.call 6 [.load (.int ⟨8, true⟩) (.var 2)]))) (boolVal false) :=
        EvE.land_false hlt (by simp [truthy, boolVal])
      exact ExS.ite hland (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.brk (p := Gen.prog) (s := st)))
    · have hqe : q < e := by omega
      have hqlen' : q < bytes.length := by omega
      have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.var 2) (.var 1)) (boolVal true) := by
        apply EvE.bin hv2 hv1
        simp [evalBin, isPtr, boolVal, hqe]
      have hbd : ((((bytes.take e).drop pos).takeWhile (fun b => scanSpace b.toNat))).length <
          ((bytes.take e).drop pos).length := by
        simp only [List.length_drop, hseLen]
        omega
      obtain ⟨byte, hb, hns⟩ := tw_boundary (fun b : UInt8 => scanSpace b.toNat) ((bytes.take e).drop pos) hbd
      have hbyte : bytes[q]? = some byte := by
        have hsbLen : ((bytes.take e).drop pos).length = e - pos := by
          simp [List.length_drop, hseLen]
        have hsLen : (((bytes.take e).drop pos).takeWhile (fun b => scanSpace b.toNat)).length < e - pos := by
          omega
        have h1 : ((bytes.take e).drop pos)[(((bytes.take e).drop pos).takeWhile (fun b => scanSpace b.toNat)).length]? =
            bytes[q]? := by
          rw [take_drop_getElem? bytes e pos _ hsLen]
          rw [hqs']
        rwa [h1] at hb
      have hcall := isSpace_call st (.var 2) bb q bytes byte hv2 (by simpa [st] using hm) hqlen' hbyte
      have hns' : scanSpace byte.toNat = false := by simpa using hns
      rw [hns'] at hcall
      simp only [Bool.false_eq_true, if_false] at hcall
      have hland : EvE Gen.prog st (.land (.bin .lt (some IntTy.u64) (.var 2) (.var 1))
          (.cast ⟨32, true⟩ (.call 6 [.load (.int ⟨8, true⟩) (.var 2)]))) (boolVal false) :=
        EvE.land_true hlt (by simp [truthy, boolVal]) hcall (by simp [truthy])
      exact ExS.ite hland (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.brk (p := Gen.prog) (s := st)))
  have hinit : P (stop - pos) s := ⟨pos, by omega, Nat.le_refl _, (state_upd_self s 2 _ l2).symm⟩
  obtain ⟨sf, hl, q, hq, hpq, hsf⟩ := ExS.loop_decreasing_post (p := Gen.prog) (P := P)
    (Q := fun st => ∃ q, q + 0 = stop ∧ pos ≤ q ∧
      st = { s with locals := s.locals.upd 2 (.ptr bb q) })
    (n := stop - pos) (s := s) hinit hstep hexit
  refine ⟨sf, hl, ?_⟩
  have : q = stop := by omega
  subst this
  exact hsf


theorem ptrUnpack_pack (b o : Nat) (ho : o < 4294967296) :
    ptrUnpack (ptrPack (.ptr b o)) = .ptr b o := by
  have hne : ptrPack (.ptr b o) ≠ 0 := by simp [ptrPack]
  have h1 : (ptrPack (.ptr b o) - 1) / 4294967296 = b := by simp only [ptrPack]; omega
  have h2 : (ptrPack (.ptr b o) - 1) % 4294967296 = o := by simp only [ptrPack]; omega
  unfold ptrUnpack
  rw [if_neg hne, h1, h2]

theorem ptrPack_lt (b o : Nat) (hb : b < 4294967295) (ho : o < 4294967296) :
    ptrPack (.ptr b o) < 256 ^ 8 := by
  have : (256 : Nat) ^ 8 = 4294967296 * 4294967296 := by decide
  rw [this]; simp only [ptrPack]; omega

/-- A pointer stored in the first 8 bytes of a block reloads as itself. -/
theorem load_ptr_cell (m : Mem) (cb b o : Nat) (tail : Block)
    (hm : m cb = some (encodeLE 8 (ptrPack (.ptr b o)) ++ tail))
    (hb : b < 4294967295) (ho : o < 4294967296) :
    load m .ptr (.ptr cb 0) = .ok (.ptr b o) := by
  have hlen : (encodeLE 8 (ptrPack (.ptr b o))).length = 8 := encodeLE_length 8 _
  have hrb : readBytes m cb 0 8 = .ok (encodeLE 8 (ptrPack (.ptr b o))) := by
    simp only [readBytes, hm]
    rw [if_pos (by simp [hlen])]
    simp [List.take_append_of_le_length, hlen]
  have hsz : Ty.size .ptr = 8 := rfl
  simp only [load, hsz, hrb, Res.bind_eq, Res.bind_ok]
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt (ptrPack_lt b o hb ho), ptrUnpack_pack b o ho]
  rfl

theorem store_ptr_cell (m : Mem) (cb b o b' o' : Nat) (tail : Block)
    (hm : m cb = some (encodeLE 8 (ptrPack (.ptr b o)) ++ tail)) :
    store m .ptr (.ptr cb 0) (.ptr b' o') =
      .ok (m.upd cb (encodeLE 8 (ptrPack (.ptr b' o')) ++ tail)) := by
  have hlen : (encodeLE 8 (ptrPack (.ptr b o))).length = 8 := encodeLE_length 8 _
  have hlen' : (encodeLE 8 (ptrPack (.ptr b' o'))).length = 8 := encodeLE_length 8 _
  simp only [store, writeBytes, hm, hlen']
  rw [if_pos (by simp [hlen])]
  congr 2


/-- **`tobj_skip_space` refines `skipStop`** for a cursor cell that lives in its own
    block `cb` (first 8 bytes) and input bytes in block `bb`. The cursor end is
    `e` (the length of the token slice), which may be smaller than the block. -/
theorem skip_space_exs (m : Mem) (cb bb : Nat) (bytes : Block) (pos e : Nat) (tail : Block)
    (hne : cb ≠ bb) (hbb : m bb = some bytes)
    (hcb : m cb = some (encodeLE 8 (ptrPack (.ptr bb pos)) ++ tail))
    (hpos : pos ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.tobj_skip_space.params [.ptr cb 0, .ptr bb e], m, false⟩
      Gen.tobj_skip_space.body .normal s' ∧
      s'.mem = m.upd cb (encodeLE 8 (ptrPack (.ptr bb (skipStop (bytes.take e) pos))) ++ tail) := by
  let s0 : State := ⟨frameLocals Gen.tobj_skip_space.params [.ptr cb 0, .ptr bb e],
    m, false⟩
  have l0 : s0.locals 0 = some (.ptr cb 0) := by
    simp [s0, frameLocals, Gen.tobj_skip_space, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr bb e) := by
    simp [s0, frameLocals, Gen.tobj_skip_space, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hld : EvE Gen.prog s0 (.load .ptr (.var 0)) (.ptr bb pos) :=
    EvE.load (EvE.var l0) (load_ptr_cell m cb bb pos tail hcb hb32 (by omega))
  have hset := ExS.set (p := Gen.prog) (i := 2) hld
  let s1 : State := { s0 with locals := s0.locals.upd 2 (.ptr bb pos) }
  obtain ⟨sf, hl, hsf⟩ := ss_loop bb bytes pos e hpos he s1
    (by simpa [s1, Locals.upd] using l1) (by simp [s1, Locals.upd]) hbb
  have hv0 : EvE Gen.prog sf (.var 0) (.ptr cb 0) := EvE.var (by
    rw [hsf]; simpa [s1, Locals.upd] using l0)
  have hv2 : EvE Gen.prog sf (.var 2) (.ptr bb (skipStop (bytes.take e) pos)) := EvE.var (by
    rw [hsf]; simp [s1, Locals.upd])
  have hstore := store_ptr_cell m cb bb pos bb (skipStop (bytes.take e) pos) tail hcb
  have hsm : sf.mem = m := by rw [hsf]
  have hfin := ExS.store (p := Gen.prog) (s := sf) (ty := .ptr) (a := .var 0) (e := .var 2)
    hv0 hv2 (by rw [hsf]) (by rw [hsm]; exact hstore)
  refine ⟨{ sf with mem := m.upd cb (encodeLE 8 (ptrPack (.ptr bb (skipStop (bytes.take e) pos))) ++ tail) }, ?_, rfl⟩
  · have hbody : Gen.tobj_skip_space.body = .seq (.set 2 (.load .ptr (.var 0)))
        (.seq (.loop ssBody .skip) (.store .ptr (.var 0) (.var 2))) := rfl
    rw [hbody]
    exact ExS.seq hset (ExS.seq hl hfin)


theorem load_ptr_at (m : Mem) (cb b o : Nat) (pre tail : Block)
    (hm : m cb = some (pre ++ encodeLE 8 (ptrPack (.ptr b o)) ++ tail))
    (hb : b < 4294967295) (ho : o < 4294967296) :
    load m .ptr (.ptr cb pre.length) = .ok (.ptr b o) := by
  have hlen : (encodeLE 8 (ptrPack (.ptr b o))).length = 8 := encodeLE_length 8 _
  have hrb : readBytes m cb pre.length 8 = .ok (encodeLE 8 (ptrPack (.ptr b o))) := by
    simp only [readBytes, hm]
    rw [if_pos (by simp [hlen])]
    simp [List.drop_append, hlen]
  have hsz : Ty.size .ptr = 8 := rfl
  simp only [load, hsz, hrb, Res.bind_eq, Res.bind_ok]
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt (ptrPack_lt b o hb ho), ptrUnpack_pack b o ho]
  rfl

theorem store_ptr_at (m : Mem) (cb b o b' o' : Nat) (pre tail : Block)
    (hm : m cb = some (pre ++ encodeLE 8 (ptrPack (.ptr b o)) ++ tail)) :
    store m .ptr (.ptr cb pre.length) (.ptr b' o') =
      .ok (m.upd cb (pre ++ encodeLE 8 (ptrPack (.ptr b' o')) ++ tail)) := by
  have hlen : (encodeLE 8 (ptrPack (.ptr b o))).length = 8 := encodeLE_length 8 _
  have hlen' : (encodeLE 8 (ptrPack (.ptr b' o'))).length = 8 := encodeLE_length 8 _
  simp only [store, writeBytes, hm, hlen']
  rw [if_pos (by simp [hlen])]
  congr 2
  simp [List.take_append, List.drop_append, hlen]

theorem isSpace_call_raw (s : State) (e : Expr) (b o : Nat) (blk : Block) (byte : UInt8)
    (he : EvE Gen.prog s e (.ptr b o)) (hm : s.mem b = some blk) (hlt : o < blk.length)
    (ho : blk[o]? = some byte) :
    EvE Gen.prog s (.call 6 [.load (.int ⟨8, true⟩) e])
      (.int IntTy.u8 (if scanSpace byte.toNat then 1 else 0)) := by
  have hbyte : blk[o]'hlt = byte := by
    have := List.getElem?_eq_getElem hlt
    rw [this] at ho; exact Option.some.inj ho
  have hload : EvE Gen.prog s (.load (.int ⟨8, true⟩) e) (.int ⟨8, true⟩ byte.toNat) := by
    apply EvE.load he
    have := load_i8_at s.mem b o blk hm hlt
    rw [hbyte] at this; exact this
  have hargs : EvArgs Gen.prog s [.load (.int ⟨8, true⟩) e] [.int ⟨8, true⟩ byte.toNat] :=
    EvArgs.cons hload EvArgs.nil
  by_cases hsp : scanSpace byte.toNat = true
  · have := EvE.call hargs (f := 6) (fn := Gen.tobj_is_space) (by rfl) (by rfl)
      (isSpace_body_true byte hsp s.mem)
    simpa [hsp] using this
  · have hsp' : scanSpace byte.toNat = false := by simpa using hsp
    have := EvE.call hargs (f := 6) (fn := Gen.tobj_is_space) (by rfl) (by rfl)
      (isSpace_body_false byte hsp' s.mem)
    simpa [hsp'] using this


/-- The cursor struct: `p` then `end`, both pointers into block `bb`. -/
def curCell (bb len q : Nat) : Block :=
  encodeLE 8 (ptrPack (.ptr bb q)) ++ encodeLE 8 (ptrPack (.ptr bb len))

theorem cur_p_eval (st : State) (cc bb len q : Nat)
    (hl0 : st.locals 0 = some (.ptr cc 0)) (hm : st.mem cc = some (curCell bb len q))
    (hb : bb < 4294967295) (hq : q < 4294967296) :
    EvE Gen.prog st (.load .ptr (.field (.var 0) 0)) (.ptr bb q) := by
  have hlen : (curCell bb len q).length = 16 := by simp [curCell, encodeLE_length]
  refine EvE.load (EvE.field (r := .ptr cc 0) (EvE.var hl0) (by simp [ptrAddN, hm, hlen])) ?_
  exact load_ptr_cell st.mem cc bb q _ hm hb hq

theorem cur_end_eval (st : State) (cc bb len q : Nat)
    (hl0 : st.locals 0 = some (.ptr cc 0)) (hm : st.mem cc = some (curCell bb len q))
    (hb : bb < 4294967295) (hlen : len < 4294967296) :
    EvE Gen.prog st (.load .ptr (.field (.var 0) 8)) (.ptr bb len) := by
  have hl : (curCell bb len q).length = 16 := by simp [curCell, encodeLE_length]
  refine EvE.load (EvE.field (r := .ptr cc 8) (EvE.var hl0) (by simp [ptrAddN, hm, hl])) ?_
  have := load_ptr_at st.mem cc bb len (encodeLE 8 (ptrPack (.ptr bb q))) [] (by
    rw [hm]; simp [curCell]) hb hlen
  simpa [encodeLE_length] using this

theorem upd_self_mem (m : Mem) (b : Nat) (blk : Block) (h : m b = some blk) :
    m.upd b blk = m := by
  funext x
  by_cases hx : x = b
  · subst hx; simp [Mem.upd, h]
  · simp [Mem.upd, hx]

def tkBody : Stmt :=
  (.ite (.land (.bin .lt (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
      (.load .ptr (.field (.var 0) 8)))
    (.un .lnot ⟨32, true⟩ (.call 6 [(.load (.int ⟨8, true⟩) (.load .ptr (.field (.var 0) 0)))])))
    (.store .ptr (.field (.var 0) 0) (.index (.load .ptr (.field (.var 0) 0))
      (.const (.int ⟨64, true⟩ 1)) 1)) .brk)

theorem tk_ast : Gen.tobj_next_token_loop0 = .loop tkBody .skip := rfl

/-- Absolute end of the token that starts at `stop`. -/
def tokEnd (bytes : Block) (stop : Nat) : Nat :=
  stop + ((bytes.drop stop).takeWhile (fun b => !scanSpace b.toNat)).length

theorem tokEnd_le (bytes : Block) (stop : Nat) (hstop : stop ≤ bytes.length) :
    tokEnd bytes stop ≤ bytes.length := by
  unfold tokEnd
  have := (List.takeWhile_prefix (fun b : UInt8 => !scanSpace b.toNat)
    (l := bytes.drop stop)).length_le
  simp at this; omega


theorem tk_loop (cc bb : Nat) (bytes : Block) (stop e : Nat) (hstop : stop ≤ e)
    (he : e ≤ bytes.length)
    (hb : bb < 4294967295) (hlen32 : e < 4294967296) (hne : cc ≠ bb) (s : State)
    (l0 : s.locals 0 = some (.ptr cc 0)) (hcc : s.mem cc = some (curCell bb e stop))
    (hbb : s.mem bb = some bytes) (hro : s.ro = false) :
    ∃ sf, ExS Gen.prog s (.loop tkBody .skip) .normal sf ∧
      sf = { s with mem := s.mem.upd cc (curCell bb e (tokEnd (bytes.take e) stop)) } := by
  let te := tokEnd (bytes.take e) stop
  have hteLe : te ≤ e := by
    have hsl : (bytes.take e).length = e := by simp [List.length_take, he]
    have := tokEnd_le (bytes.take e) stop (by rwa [hsl])
    rwa [hsl] at this
  have hteLe' : te ≤ bytes.length := by omega
  have hstopTe : stop ≤ te := by simp [te, tokEnd]
  let P : Nat → State → Prop := fun j st => ∃ q, q + j = te ∧ stop ≤ q ∧
    st = { s with mem := s.mem.upd cc (curCell bb e q) }
  have hget : ∀ i, i < ((bytes.take e).drop stop).length → ((bytes.take e).drop stop)[i]? = bytes[stop + i]? := by
    intro i hi
    have hsl : (bytes.take e).length = e := by simp [List.length_take, he]
    have hie : i < e - stop := by
      have hd : ((bytes.take e).drop stop).length = e - stop := by simp [List.length_drop, hsl]
      omega
    rw [List.drop_take, List.getElem?_take, if_pos hie, List.getElem?_drop]
  have hbbm : ∀ q, ({ s with mem := s.mem.upd cc (curCell bb e q) } : State).mem bb
      = some bytes := by
    intro q; show (s.mem.upd cc _) bb = _
    rw [Mem.upd_ne _ _ (Ne.symm hne)]; exact hbb
  have hccm : ∀ q, ({ s with mem := s.mem.upd cc (curCell bb e q) } : State).mem cc
      = some (curCell bb e q) := by
    intro q; exact Mem.upd_same _ _ _
  have hstep : ∀ j st, P (j + 1) st → ∃ s1 s2, ExS Gen.prog st tkBody .normal s1 ∧
      ExS Gen.prog s1 .skip .normal s2 ∧ P j s2 := by
    intro j st ⟨q, hq, hpq, hst⟩
    subst hst
    have hqlt : q < te := by omega
    have hqlen : q < e := by omega
    have hqlen' : q < bytes.length := by omega
    obtain ⟨byte, hb', hsp⟩ := tw_inside (fun b : UInt8 => !scanSpace b.toNat) ((bytes.take e).drop stop)
      (q - stop) (by simp only [te, tokEnd] at hqlt; omega)
    have hbyte : bytes[q]? = some byte := by
      have hi : q - stop < ((bytes.take e).drop stop).length := by
        have hsl : (bytes.take e).length = e := by simp [List.length_take, he]
        simp [List.length_drop, hsl]
        omega
      rw [hget (q - stop) hi] at hb'
      have : stop + (q - stop) = q := by omega
      rwa [this] at hb'
    have hns : scanSpace byte.toNat = false := by simpa using hsp
    let st : State := { s with mem := s.mem.upd cc (curCell bb e q) }
    have hl0' : st.locals 0 = some (.ptr cc 0) := l0
    have hbst : st.mem bb = some bytes := hbbm q
    have hcst : st.mem cc = some (curCell bb e q) := hccm q
    have hp := cur_p_eval st cc bb e q hl0' (hccm q) hb (by omega)
    have hend_ev := cur_end_eval st cc bb e q hl0' (hccm q) hb hlen32
    have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
        (.load .ptr (.field (.var 0) 8))) (boolVal true) := by
      apply EvE.bin hp hend_ev
      simp [evalBin, isPtr, boolVal, hqlen]
    have hcall := isSpace_call_raw st (.load .ptr (.field (.var 0) 0)) bb q bytes byte hp
      hbst hqlen' hbyte
    rw [hns] at hcall
    simp only [Bool.false_eq_true, if_false] at hcall
    have hnot : EvE Gen.prog st (.un .lnot ⟨32, true⟩ (.call 6 [(.load (.int ⟨8, true⟩)
        (.load .ptr (.field (.var 0) 0)))])) (boolVal true) :=
      EvE.un hcall (by simp [evalUn, truthy, boolVal])
    have hland := EvE.land_true (bb := true) hlt (by simp [truthy, boolVal]) hnot (by simp [truthy, boolVal])
    have haddr : EvE Gen.prog st (.field (.var 0) 0) (.ptr cc 0) :=
      EvE.field (r := .ptr cc 0) (EvE.var hl0') (by simp [ptrAddN, hcst])
    have hidx : EvE Gen.prog st (.index (.load .ptr (.field (.var 0) 0))
        (.const (.int ⟨64, true⟩ 1)) 1) (.ptr bb (q + 1)) := by
      apply EvE.index hp (EvE.const _)
      have h1 : IntTy.toInt ⟨64, true⟩ 1 = 1 := by simp [IntTy.toInt, IntTy.modulus]
      simp [IntTy.signed, ptrAdd, hbst, h1]
      omega
    have hstore := store_ptr_cell st.mem cc bb q bb (q + 1) (encodeLE 8 (ptrPack (.ptr bb e)))
      (hccm q)
    have hexs := ExS.store (p := Gen.prog) (s := st) (ty := .ptr) haddr hidx hro hstore
    refine ⟨{ st with mem := st.mem.upd cc (curCell bb e (q + 1)) }, _, ?_, ExS.skip,
      q + 1, by omega, by omega, ?_⟩
    · unfold tkBody
      exact ExS.ite hland (bc := true) (by simp [truthy, boolVal]) (by exact hexs)
    · simp [st, Mem.upd_upd]
  have hexit : ∀ st, P 0 st → ∃ s1, ExS Gen.prog st tkBody .brk s1 ∧ P 0 s1 := by
    intro st ⟨q, hq, hpq, hst⟩
    subst hst
    have hqs : q = te := by omega
    have hqs' : q = stop + (((bytes.take e).drop stop).takeWhile (fun b => !scanSpace b.toNat)).length := hqs
    let st : State := { s with mem := s.mem.upd cc (curCell bb e q) }
    have hl0' : st.locals 0 = some (.ptr cc 0) := l0
    have hbst : st.mem bb = some bytes := hbbm q
    have hcst : st.mem cc = some (curCell bb e q) := hccm q
    have hp := cur_p_eval st cc bb e q hl0' (hccm q) hb (by omega)
    have hend_ev := cur_end_eval st cc bb e q hl0' (hccm q) hb hlen32
    refine ⟨st, ?_, ⟨q, by omega, hpq, rfl⟩⟩
    unfold tkBody
    by_cases hend : q = e
    · have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
          (.load .ptr (.field (.var 0) 8))) (boolVal false) := by
        apply EvE.bin hp hend_ev
        simp [evalBin, isPtr, boolVal, hend]
      have hland := EvE.land_false (b := (.un .lnot ⟨32, true⟩ (.call 6 [(.load (.int ⟨8, true⟩)
        (.load .ptr (.field (.var 0) 0)))]))) hlt (by simp [truthy, boolVal])
      exact ExS.ite hland (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.brk (p := Gen.prog) (s := st)))
    · have hqe : q < e := by omega
      have hqlen' : q < bytes.length := by omega
      have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
          (.load .ptr (.field (.var 0) 8))) (boolVal true) := by
        apply EvE.bin hp hend_ev
        simp [evalBin, isPtr, boolVal, hqe]
      have hbd : (((bytes.take e).drop stop).takeWhile (fun b => !scanSpace b.toNat)).length <
          ((bytes.take e).drop stop).length := by
        have hse : (bytes.take e).length = e := by simp [List.length_take, he]
        simp only [List.length_drop, hse]
        omega
      obtain ⟨byte, hb', hns⟩ := tw_boundary (fun b : UInt8 => !scanSpace b.toNat)
        ((bytes.take e).drop stop) hbd
      have hbyte : bytes[q]? = some byte := by
        have hse : (bytes.take e).length = e := by simp [List.length_take, he]
        have hsdLen : ((bytes.take e).drop stop).length = e - stop := by
          simp [List.length_drop, hse]
        have hsLen : (((bytes.take e).drop stop).takeWhile (fun b => !scanSpace b.toNat)).length < e - stop := by
          omega
        have h1 : ((bytes.take e).drop stop)[(((bytes.take e).drop stop).takeWhile (fun b => !scanSpace b.toNat)).length]? =
            bytes[q]? := by
          rw [take_drop_getElem? bytes e stop _ hsLen]
          rw [hqs']
        rwa [h1] at hb'
      have hsp : scanSpace byte.toNat = true := by simpa using hns
      have hcall := isSpace_call_raw st (.load .ptr (.field (.var 0) 0)) bb q bytes byte hp
        hbst hqlen' hbyte
      rw [hsp] at hcall
      simp only [if_true] at hcall
      have hnot : EvE Gen.prog st (.un .lnot ⟨32, true⟩ (.call 6 [(.load (.int ⟨8, true⟩)
          (.load .ptr (.field (.var 0) 0)))])) (boolVal false) :=
        EvE.un hcall (by simp [evalUn, truthy, boolVal])
      have hland := EvE.land_true (bb := false) hlt (by simp [truthy, boolVal]) hnot (by simp [truthy, boolVal])
      exact ExS.ite hland (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.brk (p := Gen.prog) (s := st)))
  have hinit : P (te - stop) s := ⟨stop, by omega, Nat.le_refl _, by
    rw [upd_self_mem s.mem cc _ hcc]⟩
  obtain ⟨sf, hl, q, hq, hpq, hsf⟩ := ExS.loop_decreasing_post (p := Gen.prog) (P := P)
    (Q := fun st => ∃ q, q + 0 = te ∧ stop ≤ q ∧
      st = { s with mem := s.mem.upd cc (curCell bb e q) })
    (n := te - stop) (s := s) hinit hstep hexit
  refine ⟨sf, hl, ?_⟩
  have : q = te := by omega
  subst this
  exact hsf


/-- Prefix of `tobj_next_token`: the whitespace skip through the cursor struct. -/
theorem nt_prefix (m : Mem) (cc bb tb lb : Nat) (bytes : Block) (pos e : Nat)
    (hne : cc ≠ bb) (hbb : m bb = some bytes) (hcc : m cc = some (curCell bb e pos))
    (hpos : pos ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296) :
    let s0 : State := ⟨frameLocals Gen.tobj_next_token.params
        [.ptr cc 0, .ptr tb 0, .ptr lb 0], m, false⟩
    ∃ s1 : State, ExS Gen.prog s0 (.call none 23 [(.field (.var 0) 0),
        (.load .ptr (.field (.var 0) 8))]) .normal s1 ∧ s1.locals = s0.locals ∧ s1.ro = false ∧
      s1.mem = m.upd cc (curCell bb e (skipStop (bytes.take e) pos)) := by
  intro s0
  have l0 : s0.locals 0 = some (.ptr cc 0) := by
    simp [s0, frameLocals, Gen.tobj_next_token, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hp := cur_p_eval s0 cc bb e pos l0 hcc hb32 (by omega)
  have hend_ev := cur_end_eval s0 cc bb e pos l0 hcc hb32 hlen32
  have hl : (curCell bb e pos).length = 16 := by simp [curCell, encodeLE_length]
  have hf0 : EvE Gen.prog s0 (.field (.var 0) 0) (.ptr cc 0) :=
    EvE.field (r := .ptr cc 0) (EvE.var l0) (by simp [ptrAddN, s0, hcc, hl])
  have hargs := EvArgs.cons hf0 (EvArgs.cons hend_ev EvArgs.nil)
  obtain ⟨sk, hbody, hmem⟩ := skip_space_exs m cc bb bytes pos e
    (encodeLE 8 (ptrPack (.ptr bb e))) hne hbb (by simpa [curCell] using hcc)
    hpos he hb32 (by omega)
  have hcall := ExS.call (p := Gen.prog) (s := s0) (f := 23) (fn := Gen.tobj_skip_space)
    (vs := [.ptr cc 0, .ptr bb e]) (o := .normal) (s' := sk) hargs (by rfl) (by rfl)
    hbody (Or.inl rfl)
  exact ⟨{ s0 with mem := sk.mem }, hcall, rfl, rfl, by simpa [curCell] using hmem⟩


theorem store_ptr_blk8 (m : Mem) (b b' o' : Nat) (blk : Block) (h : m b = some blk)
    (hl : blk.length = 8) :
    store m .ptr (.ptr b 0) (.ptr b' o') = .ok (m.upd b (encodeLE 8 (ptrPack (.ptr b' o')))) := by
  have hlen' : (encodeLE 8 (ptrPack (.ptr b' o'))).length = 8 := encodeLE_length 8 _
  simp only [store, writeBytes, h, hlen']
  rw [if_pos (by omega)]
  congr 2
  rw [List.take_zero, List.drop_eq_nil_of_le (by omega)]
  simp

theorem store_u64_blk8 (m : Mem) (b : Nat) (blk : Block) (v : Nat) (h : m b = some blk)
    (hl : blk.length = 8) :
    store m (.int ⟨64, false⟩) (.ptr b 0) (.int ⟨64, false⟩ v) = .ok (m.upd b (encodeLE 8 v)) := by
  have hlen' : (encodeLE 8 v).length = 8 := encodeLE_length 8 _
  have hw : writeBytes m b 0 (encodeLE 8 v) = .ok (m.upd b (encodeLE 8 v)) := by
    simp only [writeBytes, h]
    rw [if_pos (by omega)]
    congr 2
    rw [List.take_zero, List.drop_eq_nil_of_le (by omega)]
    simp
  simpa [store, IntTy.bytes] using hw

/-- `tobj_next_token` when only whitespace remains: returns 0 and leaves the cursor
    after the whitespace; the token outputs are untouched. -/
theorem next_token_none (m : Mem) (cc bb tb lb : Nat) (bytes : Block) (pos e : Nat)
    (hne : cc ≠ bb) (hbb : m bb = some bytes) (hcc : m cc = some (curCell bb e pos))
    (hpos : pos ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296)
    (hend : skipStop (bytes.take e) pos = e) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_next_token.params
        [.ptr cc 0, .ptr tb 0, .ptr lb 0], m, false⟩ Gen.tobj_next_token.body
        (.ret (some (.int ⟨8, false⟩ 0))) s' ∧
      s'.mem = m.upd cc (curCell bb e e) := by
  obtain ⟨s1, hcall, hl1, hro1, hm1⟩ := nt_prefix m cc bb tb lb bytes pos e hne hbb hcc hpos he
    hb32 hlen32
  have l0 : s1.locals 0 = some (.ptr cc 0) := by
    rw [hl1]; simp [frameLocals, Gen.tobj_next_token, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hccm : s1.mem cc = some (curCell bb e (skipStop (bytes.take e) pos)) := by
    rw [hm1]; exact Mem.upd_same _ _ _
  have hp := cur_p_eval s1 cc bb e _ l0 hccm hb32 (by have := skipStop_le (bytes.take e) pos (by simpa [List.length_take, he] using hpos); omega)
  have hend_ev := cur_end_eval s1 cc bb e _ l0 hccm hb32 hlen32
  have hge : EvE Gen.prog s1 (.bin .ge (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
      (.load .ptr (.field (.var 0) 8))) (boolVal true) := by
    apply EvE.bin hp hend_ev
    simp [evalBin, isPtr, boolVal, hend]
  have hret : EvE Gen.prog s1 (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
      (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 0) :=
    EvE.cond (EvE.const _) (bc := false) (by simp [truthy]) (EvE.const _)
  have hite : ExS Gen.prog s1 (.ite (.bin .ge (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
      (.load .ptr (.field (.var 0) 8))) (.ret (some (.cond (.const (.int ⟨32, true⟩ 0))
        (.const (.int ⟨8, false⟩ 1)) (.const (.int ⟨8, false⟩ 0))))) .skip)
      (.ret (some (.int ⟨8, false⟩ 0))) s1 :=
    ExS.ite hge (bc := true) (by simp [truthy, boolVal]) (ExS.ret hret)
  refine ⟨s1, ?_, by rw [hm1, hend]⟩
  exact ExS.seq hcall (ExS.seq_ret hite)


/-- `tobj_next_token` when a token follows the whitespace: returns 1, stores the
    token start and length, and leaves the cursor at the token end. -/
theorem next_token_some (m : Mem) (cc bb tb lb : Nat) (bytes : Block) (pos e : Nat)
    (tokblk lenblk : Block)
    (hne : cc ≠ bb) (hnt : tb ≠ cc) (hnt2 : tb ≠ bb) (hnl : lb ≠ cc) (hnl2 : lb ≠ bb)
    (hntl : lb ≠ tb)
    (hbb : m bb = some bytes) (hcc : m cc = some (curCell bb e pos))
    (htb : m tb = some tokblk) (hlb : m lb = some lenblk)
    (htl : tokblk.length = 8) (hll : lenblk.length = 8)
    (hpos : pos ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296)
    (hlt : skipStop (bytes.take e) pos < e) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_next_token.params
        [.ptr cc 0, .ptr tb 0, .ptr lb 0], m, false⟩ Gen.tobj_next_token.body
        (.ret (some (.int ⟨8, false⟩ 1))) s' ∧
      s'.mem = ((m.upd cc (curCell bb e (tokEnd (bytes.take e) (skipStop (bytes.take e) pos)))).upd tb
        (encodeLE 8 (ptrPack (.ptr bb (skipStop (bytes.take e) pos))))).upd lb
        (encodeLE 8 (tokEnd (bytes.take e) (skipStop (bytes.take e) pos) - skipStop (bytes.take e) pos)) := by
  have hsl : (bytes.take e).length = e := by simp [List.length_take, he]
  obtain ⟨s1, hcall, hl1, hro1, hm1⟩ := nt_prefix m cc bb tb lb bytes pos e hne hbb hcc hpos he
    hb32 hlen32
  let stop := skipStop (bytes.take e) pos
  let te := tokEnd (bytes.take e) stop
  have hstopLe : stop ≤ e := by
    have := skipStop_le (bytes.take e) pos (by simpa [hsl] using hpos)
    rwa [hsl] at this
  have hteLe : te ≤ e := by
    have := tokEnd_le (bytes.take e) stop (by rwa [hsl])
    rwa [hsl] at this
  have hstopTe : stop ≤ te := by simp [te, tokEnd]
  have lc : ∀ i, (s1.locals i = (frameLocals Gen.tobj_next_token.params
      [.ptr cc 0, .ptr tb 0, .ptr lb 0]) i) := fun i => congrFun hl1 i
  have l0 : s1.locals 0 = some (.ptr cc 0) := by
    rw [lc]; simp [frameLocals, Gen.tobj_next_token, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s1.locals 1 = some (.ptr tb 0) := by
    rw [lc]; simp [frameLocals, Gen.tobj_next_token, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s1.locals 2 = some (.ptr lb 0) := by
    rw [lc]; simp [frameLocals, Gen.tobj_next_token, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hccm : s1.mem cc = some (curCell bb e stop) := by
    rw [hm1]; exact Mem.upd_same _ _ _
  have hbbm : s1.mem bb = some bytes := by
    rw [hm1]; show (m.upd cc _) bb = _
    rw [Mem.upd_ne _ _ (Ne.symm hne)]; exact hbb
  have hp := cur_p_eval s1 cc bb e stop l0 hccm hb32 (by omega)
  have hend_ev := cur_end_eval s1 cc bb e stop l0 hccm hb32 hlen32
  have hge : EvE Gen.prog s1 (.bin .ge (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
      (.load .ptr (.field (.var 0) 8))) (boolVal false) := by
    apply EvE.bin hp hend_ev
    have hlt' : stop < e := by
      have hsl : (bytes.take e).length = e := by simp [List.length_take, he]
      simpa [stop, hsl] using hlt
    simp [evalBin, isPtr, boolVal, hlt']
  have hite : ExS Gen.prog s1 (.ite (.bin .ge (some IntTy.u64) (.load .ptr (.field (.var 0) 0))
      (.load .ptr (.field (.var 0) 8))) (.ret (some (.cond (.const (.int ⟨32, true⟩ 0))
        (.const (.int ⟨8, false⟩ 1)) (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s1 :=
    ExS.ite hge (bc := false) (by simp [truthy, boolVal])
      (by simpa using (ExS.skip (p := Gen.prog) (s := s1)))
  -- start = c->p
  have hset3 := ExS.set (p := Gen.prog) (i := 3) hp
  let s2 : State := { s1 with locals := s1.locals.upd 3 (.ptr bb stop) }
  obtain ⟨s3, hloop, hs3⟩ := tk_loop cc bb bytes stop e hstopLe he hb32 hlen32 hne s2
    (by simpa [s2, Locals.upd] using l0) hccm hbbm hro1
  -- *tok = start
  have hv1 : EvE Gen.prog s3 (.var 1) (.ptr tb 0) := EvE.var (by
    rw [hs3]; simpa [s2, Locals.upd] using l1)
  have hv3 : EvE Gen.prog s3 (.var 3) (.ptr bb stop) := EvE.var (by
    rw [hs3]; simp [s2, Locals.upd])
  let M3 := s1.mem.upd cc (curCell bb e te)
  have hm3 : s3.mem = M3 := by rw [hs3]
  have htbM : M3 tb = some tokblk := by
    show (s1.mem.upd cc _) tb = _
    rw [Mem.upd_ne _ _ hnt, hm1, Mem.upd_ne _ _ hnt]; exact htb
  have hst1 := store_ptr_blk8 s3.mem tb bb stop tokblk (by rw [hm3]; exact htbM) htl
  have hexs1 := ExS.store (p := Gen.prog) (s := s3) (ty := .ptr) hv1 hv3
    (by rw [hs3]; exact hro1) hst1
  let s4 : State := { s3 with mem := s3.mem.upd tb (encodeLE 8 (ptrPack (.ptr bb stop))) }
  -- *tok_len = c->p - start
  have l0_4 : s4.locals 0 = some (.ptr cc 0) := by
    show s3.locals 0 = _
    rw [hs3]; simpa [s2, Locals.upd] using l0
  have hcc4 : s4.mem cc = some (curCell bb e te) := by
    show (s3.mem.upd tb _) cc = _
    rw [Mem.upd_ne _ _ (Ne.symm hnt), hm3]; exact Mem.upd_same _ _ _
  have hp4 := cur_p_eval s4 cc bb e te l0_4 hcc4 hb32 (by omega)
  have hv3_4 : EvE Gen.prog s4 (.var 3) (.ptr bb stop) := EvE.var (by
    show s3.locals 3 = _
    rw [hs3]; simp [s2, Locals.upd])
  have hsub : EvE Gen.prog s4 (.bin .sub (some ⟨64, true⟩) (.load .ptr (.field (.var 0) 0))
      (.var 3)) (.int ⟨64, true⟩ (te - stop)) := by
    apply EvE.bin hp4 hv3_4
    simp [evalBin, isPtr, arith, IntTy.inRange, IntTy.wrap, IntTy.modulus, IntTy.minVal,
      IntTy.maxVal]
    rw [if_pos (by omega)]
    congr 2
    omega
  have hcsub : EvE Gen.prog s4 (.cast ⟨64, false⟩ (.bin .sub (some ⟨64, true⟩)
      (.load .ptr (.field (.var 0) 0)) (.var 3))) (.int u64 (te - stop)) :=
    EvE.cast hsub (by simp [evalCast, IntTy.toInt, IntTy.wrap, IntTy.modulus, u64]; omega)
  have hv2 : EvE Gen.prog s4 (.var 2) (.ptr lb 0) := EvE.var (by
    show s3.locals 2 = _
    rw [hs3]; simpa [s2, Locals.upd] using l2)
  have hlbM : s4.mem lb = some lenblk := by
    show (s3.mem.upd tb _) lb = _
    rw [Mem.upd_ne _ _ hntl, hm3]
    show (s1.mem.upd cc _) lb = _
    rw [Mem.upd_ne _ _ hnl, hm1, Mem.upd_ne _ _ hnl]; exact hlb
  have hst2 := store_u64_blk8 s4.mem lb lenblk (te - stop) hlbM hll
  have hexs2 := ExS.store (p := Gen.prog) (s := s4) (ty := .int ⟨64, false⟩) hv2 hcsub
    (by show s3.ro = false; rw [hs3]; exact hro1) hst2
  let s5 : State := { s4 with mem := s4.mem.upd lb (encodeLE 8 (te - stop)) }
  have hret : EvE Gen.prog s5 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
      (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 1) :=
    EvE.cond (EvE.const _) (bc := true) (by simp [truthy]) (EvE.const _)
  refine ⟨s5, ?_, ?_⟩
  · exact ExS.seq hcall (ExS.seq hite (ExS.seq hset3 (ExS.seq hloop (ExS.seq hexs1
      (ExS.seq hexs2 (ExS.ret hret))))))
  · have hM3 : M3 = m.upd cc (curCell bb e te) := by
      simp only [M3, hm1, Mem.upd_upd]
    show (s3.mem.upd tb _).upd lb _ = _
    rw [hm3, hM3]


theorem takeWhile_map_not (bs : List UInt8) :
    (bs.map UInt8.toNat).takeWhile (fun b => !scanSpace b) =
      (bs.takeWhile (fun b => !scanSpace b.toNat)).map UInt8.toNat := by
  induction bs with
  | nil => rfl
  | cons h t ih =>
    by_cases hs : scanSpace h.toNat = true
    · simp [hs]
    · have : scanSpace h.toNat = false := by simpa using hs
      simp [this, ih]

theorem takeWhile_map_space (bs : List UInt8) :
    (bs.map UInt8.toNat).takeWhile scanSpace =
      (bs.takeWhile (fun b => scanSpace b.toNat)).map UInt8.toNat := by
  induction bs with
  | nil => rfl
  | cons h t ih =>
    by_cases hs : scanSpace h.toNat = true
    · simp [hs, ih]
    · simp [hs]

/-- The pure token specification `Obj.nextToken` in terms of the absolute
    offsets `skipStop` / `tokEnd` that the C refinement uses. -/
theorem nextToken_eq (bytes : Block) (pos : Nat) :
    nextToken (bytes.map UInt8.toNat) pos =
      if skipStop bytes pos < bytes.length then
        (some (skipStop bytes pos, tokEnd bytes (skipStop bytes pos) - skipStop bytes pos),
          tokEnd bytes (skipStop bytes pos))
      else (none, skipStop bytes pos) := by
  have hsp : ((bytes.map UInt8.toNat).drop pos).takeWhile scanSpace =
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).map UInt8.toNat := by
    rw [← List.map_drop]; exact takeWhile_map_space _
  have hstart : nextTokenStart (bytes.map UInt8.toNat) pos = skipStop bytes pos := by
    simp only [nextTokenStart, hsp, skipStop, List.length_map]
  have htok : nextTokenBytes (bytes.map UInt8.toNat) pos =
      ((bytes.drop (skipStop bytes pos)).takeWhile (fun b => !scanSpace b.toNat)).map UInt8.toNat := by
    unfold nextTokenBytes
    simp only [hsp, List.length_map]
    rw [← List.map_drop, ← List.map_drop, List.drop_drop, takeWhile_map_not]
    simp [skipStop, Nat.add_comm]
  unfold nextToken
  rw [hstart, htok]
  by_cases hlt : skipStop bytes pos < bytes.length
  · have hbd : ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length <
        (bytes.drop pos).length := by
      have hdl : (bytes.drop pos).length = bytes.length - pos := List.length_drop ..
      unfold skipStop at hlt
      omega
    obtain ⟨x, hx, hns⟩ := tw_boundary (fun b : UInt8 => scanSpace b.toNat) (bytes.drop pos) hbd
    have hxat : bytes[skipStop bytes pos]? = some x := by
      rw [List.getElem?_drop] at hx; exact hx
    have hne : ((bytes.drop (skipStop bytes pos)).takeWhile (fun b => !scanSpace b.toNat)) ≠ [] := by
      have hd : (bytes.drop (skipStop bytes pos)) = x :: bytes.drop (skipStop bytes pos + 1) := by
        rw [List.drop_eq_getElem_cons hlt]
        have := List.getElem?_eq_getElem hlt
        rw [this] at hxat
        rw [Option.some.inj hxat]
      rw [hd]
      have : scanSpace x.toNat = false := by simpa using hns
      simp [List.takeWhile_cons, this]
    rw [if_pos hlt]
    have hne' : (((bytes.drop (skipStop bytes pos)).takeWhile
        (fun b => !scanSpace b.toNat)).map UInt8.toNat).isEmpty = false := by
      cases h : (bytes.drop (skipStop bytes pos)).takeWhile (fun b => !scanSpace b.toNat) with
      | nil => exact absurd h hne
      | cons a l => simp
    simp only [hne', Bool.false_eq_true, if_false, List.length_map]
    simp only [tokEnd]
    have hsub : ∀ a b : Nat, a + b - a = b := fun a b => by omega
    rw [hsub]
  · rw [if_neg hlt]
    have hle : bytes.length ≤ skipStop bytes pos := by omega
    have hnil : (bytes.drop (skipStop bytes pos)) = [] :=
      List.drop_eq_nil_of_le hle
    simp [hnil]

end Obj.C.Proofs
