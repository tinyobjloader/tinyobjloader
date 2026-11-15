/-
  Refinement proof for the translated `tobj_memcpy` (tiny_obj_c.c): the byte
  loop copies `n` bytes from a source block to a distinct destination block.
  Also provides `ExS_call_discard` (a call statement whose returned value is
  dropped) and unsigned 64-bit evaluation helpers, reused by the
  `emit_face_core` proof.
-/
import Obj.C.Proofs.ObjTessFan
namespace Obj.C.Proofs
open Obj.C Obj

/-- A call statement whose result is discarded, to a function that returns a value. -/
theorem ExS_call_discard {p : Prog} {s : State} {f args vs fn v s'}
    (hargs : EvArgs p s args vs) (hf : p f = some fn)
    (hlen : fn.params.length = vs.length)
    (hbody : ExS p ⟨frameLocals fn.params vs, s.mem, s.ro⟩ fn.body (.ret (some v)) s') :
    ExS p s (.call none f args) .normal { s with mem := s'.mem } := by
  obtain ⟨K1, h1⟩ := hargs
  obtain ⟨K2, h2⟩ := hbody
  refine ⟨max K1 K2 + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [execStmt, h1 m (by omega), Res.bind_eq, Res.bind_ok, hf, hlen, ite_true,
    h2 m (by omega)]
  rfl

def u64 : IntTy := ⟨64, false⟩

theorem u64_lt_val (a n : Nat) :
    evalBin .lt (some ⟨64, false⟩) (.int u64 a) (.int u64 n) = .ok (boolVal (decide (a < n))) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind]

theorem u64_add_val (a c : Nat) (h : a + c < 18446744073709551616) :
    evalBin .add (some ⟨64, false⟩) (.int u64 a) (.int u64 c) = .ok (.int u64 (a + c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind]
  omega

theorem cast_u64_u64 (a : Nat) (h : a < 18446744073709551616) :
    evalCast ⟨64, false⟩ (.int u64 a) = .ok (.int u64 a) := by
  simp [evalCast, u64, IntTy.modulus]; omega

theorem cast_u64_i32_zero : evalCast ⟨64, false⟩ (.int ⟨32, true⟩ 0) = .ok (.int u64 0) := by
  simp [evalCast, u64, IntTy.toInt, IntTy.wrap, IntTy.modulus]

theorem encodeLE_one_byte (x : UInt8) : encodeLE 1 x.toNat = [x] := by
  simp [encodeLE]


theorem take_succ_seg (sblk : Block) (soff n i : Nat) (hsl : soff + n ≤ sblk.length) (hi : i < n) :
    ((sblk.drop soff).take n).take (i + 1) =
      ((sblk.drop soff).take n).take i ++ [sblk[soff + i]'(by omega)] := by
  have h : ((sblk.drop soff).take n)[i]? = some (sblk[soff + i]'(by omega)) := by
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop,
      List.getElem?_eq_getElem (by omega)]
  rw [List.take_succ, h]
  simp

theorem load_u8_at (m : Mem) (b o : Nat) (blk : Block) (hm : m b = some blk) (h : o < blk.length) :
    load m (.int ⟨8, false⟩) (.ptr b o) = .ok (.int ⟨8, false⟩ (blk[o]'h).toNat) := by
  have hd : blk.drop o = blk[o] :: blk.drop (o + 1) := List.drop_eq_getElem_cons h
  have hrb : readBytes m b o 1 = .ok [blk[o]] := by
    simp only [readBytes, hm]
    rw [if_pos (by omega), hd]
    rfl
  have : Ty.size (.int ⟨8, false⟩) = 1 := rfl
  simp only [load, this, hrb, Res.bind]
  simp [decodeLE]


def mcBody : Stmt :=
  (.ite (.bin .lt (some ⟨64, false⟩) (.var 5) (.var 2))
    (.store (.int ⟨8, false⟩) (.index (.var 3) (.var 5) 1)
      (.load (.int ⟨8, false⟩) (.index (.var 4) (.var 5) 1))) .brk)

def mcStore : Stmt :=
  (.store (.int ⟨8, false⟩) (.index (.var 3) (.var 5) 1)
    (.load (.int ⟨8, false⟩) (.index (.var 4) (.var 5) 1)))

def mcStep : Stmt :=
  (.set 5 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5))
    (.const (.int ⟨64, false⟩ 1)))))

theorem mc_loop_ast : Gen.tobj_memcpy_loop0 = .loop mcBody mcStep := rfl

/-- Loop invariant of `tobj_memcpy`: `j` bytes remain. -/
def McInv (m : Mem) (db sb : Nat) (dblk sblk : Block) (doff soff n : Nat) (j : Nat)
    (s : State) : Prop :=
  j ≤ n ∧ s.locals 0 = some (.ptr db doff) ∧ s.locals 2 = some (.int u64 n) ∧ s.locals 3 = some (.ptr db doff) ∧
  s.locals 4 = some (.ptr sb soff) ∧ s.locals 5 = some (.int u64 (n - j)) ∧ s.ro = false ∧
  s.mem db = some (splice dblk doff (((sblk.drop soff).take n).take (n - j))) ∧
  ∀ b, b ≠ db → s.mem b = m b

theorem memcpy_loop (m : Mem) (db sb : Nat) (dblk sblk : Block) (doff soff n : Nat)
    (hne : db ≠ sb) (hs : m sb = some sblk)
    (hdl : doff + n ≤ dblk.length) (hsl : soff + n ≤ sblk.length) (hn : n < 18446744073709551616)
    (s1 : State) (hinv : McInv m db sb dblk sblk doff soff n n s1) :
    ∃ sf, ExS Gen.prog s1 (.loop mcBody mcStep) .normal sf ∧
      McInv m db sb dblk sblk doff soff n 0 sf := by
  have hstep : ∀ j s, McInv m db sb dblk sblk doff soff n (j + 1) s → ∃ s1 s2,
      ExS Gen.prog s mcBody .normal s1 ∧ ExS Gen.prog s1 mcStep .normal s2 ∧
      McInv m db sb dblk sblk doff soff n j s2 := by
    intro j s hs'
    obtain ⟨hj, l0', l2, l3, l4, l5, hro, hmem, hrest⟩ := hs'
    generalize hid : n - (j + 1) = i at l5 hmem
    have hi : i < n := by omega
    have hseglen : (((sblk.drop soff).take n)).length = n := by simp; omega
    have hcurlen : (splice dblk doff (((sblk.drop soff).take n).take i)).length = dblk.length := by
      apply splice_length; simp; omega
    have hsmem : s.mem sb = some sblk := by rw [hrest sb hne.symm]; exact hs
    have hv5 : EvE Gen.prog s (.var 5) (.int u64 i) := EvE.var l5
    have hv3 : EvE Gen.prog s (.var 3) (.ptr db doff) := EvE.var l3
    have hv4 : EvE Gen.prog s (.var 4) (.ptr sb soff) := EvE.var l4
    have hv2 : EvE Gen.prog s (.var 2) (.int u64 n) := EvE.var l2
    have hlt : EvE Gen.prog s (.bin .lt (some ⟨64, false⟩) (.var 5) (.var 2))
        (boolVal (decide (i < n))) := EvE.bin hv5 hv2 (u64_lt_val _ _)
    have hsidx : EvE Gen.prog s (.index (.var 4) (.var 5) 1) (.ptr sb (soff + i)) := by
      apply EvE.index hv4 hv5
      simp [u64, ptrAddN, hsmem]
      omega
    have hdidx : EvE Gen.prog s (.index (.var 3) (.var 5) 1) (.ptr db (doff + i)) := by
      apply EvE.index hv3 hv5
      simp [u64, ptrAddN, hmem, hcurlen]
      omega
    have hbyte : EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.var 4) (.var 5) 1))
        (.int ⟨8, false⟩ (sblk[soff + i]'(by omega)).toNat) :=
      EvE.load hsidx (load_u8_at s.mem sb (soff + i) sblk hsmem (by omega))
    have hst := store_int s.mem db (doff + i) _ hmem ⟨8, false⟩ (sblk[soff + i]'(by omega)).toNat
      (by simp [IntTy.bytes, hcurlen]; omega)
    have hstore : ExS Gen.prog s mcStore .normal { s with mem := (s.mem.upd db
        (splice (splice dblk doff (((sblk.drop soff).take n).take i)) (doff + i)
          (encodeLE 1 (sblk[soff + i]'(by omega)).toNat))) } := by
      unfold mcStore
      exact ExS.store hdidx hbyte hro (by simpa [IntTy.bytes] using hst)
    let M1 : Mem := s.mem.upd db
      (splice (splice dblk doff (((sblk.drop soff).take n).take i)) (doff + i)
        (encodeLE 1 (sblk[soff + i]'(by omega)).toNat))
    let s1' : State := { s with mem := M1 }
    have hbodyS : ExS Gen.prog s mcBody .normal s1' := by
      unfold mcBody
      exact ExS.ite hlt (bc := true) (by simp [truthy, boolVal, hi]) (by show ExS Gen.prog s mcStore .normal s1'; exact hstore)
    have l5' : s1'.locals 5 = some (.int u64 i) := l5
    have hcs : EvE Gen.prog s1' (.cast ⟨64, false⟩ (.var 5)) (.int u64 i) :=
      EvE.cast (EvE.var l5') (cast_u64_u64 _ (by omega))
    have hadd : EvE Gen.prog s1' (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5))
        (.const (.int ⟨64, false⟩ 1))) (.int u64 (i + 1)) :=
      EvE.bin hcs (EvE.const _) (u64_add_val _ _ (by omega))
    have hstepS : ExS Gen.prog s1' mcStep .normal
        { s1' with locals := s1'.locals.upd 5 (.int u64 (i + 1)) } := by
      unfold mcStep
      exact ExS.set (EvE.cast hadd (cast_u64_u64 _ (by omega)))
    refine ⟨s1', _, hbodyS, hstepS, ?_⟩
    have e : n - j = i + 1 := by omega
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, hro, ?_, ?_⟩
    · simpa [s1', Locals.upd] using l0'
    · simpa [s1', Locals.upd] using l2
    · simpa [s1', Locals.upd] using l3
    · simpa [s1', Locals.upd] using l4
    · simp [s1', Locals.upd]; omega
    · show M1 db = _
      have hl : (((sblk.drop soff).take n).take i).length = i := by simp; omega
      have hsp := splice_append dblk doff (((sblk.drop soff).take n).take i)
        [sblk[soff + i]'(by omega)] (by simp [hl]; omega)
      rw [hl] at hsp
      rw [e, take_succ_seg sblk soff n i hsl hi]
      simp only [M1, Mem.upd_same]
      rw [encodeLE_one_byte, hsp]
    · intro b hb
      show M1 b = _
      simp only [M1]
      rw [Mem.upd_ne _ _ hb]
      exact hrest b hb
  obtain ⟨sf, hl, hq⟩ := ExS.loop_decreasing_post (p := Gen.prog)
    (P := McInv m db sb dblk sblk doff soff n) (Q := McInv m db sb dblk sblk doff soff n 0)
    (n := n) (s := s1) hinv hstep (by
      intro s hs'
      obtain ⟨_, l0', l2, l3, l4, l5, hro, hmem, hrest⟩ := hs'
      have hv5 : EvE Gen.prog s (.var 5) (.int u64 (n - 0)) := EvE.var l5
      have hv2 : EvE Gen.prog s (.var 2) (.int u64 n) := EvE.var l2
      have hlt : EvE Gen.prog s (.bin .lt (some ⟨64, false⟩) (.var 5) (.var 2))
          (boolVal (decide (n - 0 < n))) := EvE.bin hv5 hv2 (u64_lt_val _ _)
      refine ⟨s, ?_, ⟨by omega, l0', l2, l3, l4, l5, hro, hmem, hrest⟩⟩
      unfold mcBody
      apply ExS.ite hlt (bc := false) (by simp [truthy, boolVal])
      simpa using (ExS.brk (p := Gen.prog) (s := s)))
  exact ⟨sf, hl, hq⟩


/-- **`tobj_memcpy` copies bytes.**  Copying `n` bytes between distinct blocks
    returns `dst` and leaves the destination block equal to the original with
    the source segment spliced in; every other block is unchanged. -/
theorem memcpy_exs (m : Mem) (db sb : Nat) (dblk sblk : Block) (doff soff n : Nat)
    (hne : db ≠ sb) (hd : m db = some dblk) (hs : m sb = some sblk)
    (hdl : doff + n ≤ dblk.length) (hsl : soff + n ≤ sblk.length)
    (hn : n < 18446744073709551616) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.tobj_memcpy.params [.ptr db doff, .ptr sb soff, .int u64 n], m, false⟩
      Gen.tobj_memcpy.body (.ret (some (.ptr db doff))) s' ∧
      s'.mem db = some (splice dblk doff ((sblk.drop soff).take n)) ∧
      ∀ b, b ≠ db → s'.mem b = m b := by
  let s0 : State := ⟨frameLocals Gen.tobj_memcpy.params [.ptr db doff, .ptr sb soff, .int u64 n],
    m, false⟩
  have l0 : s0.locals 0 = some (.ptr db doff) := by
    simp [s0, frameLocals, Gen.tobj_memcpy, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr sb soff) := by
    simp [s0, frameLocals, Gen.tobj_memcpy, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s0.locals 2 = some (.int u64 n) := by
    simp [s0, frameLocals, Gen.tobj_memcpy, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hs3 : ExS Gen.prog s0 (.set 3 (.var 0)) .normal
      { s0 with locals := s0.locals.upd 3 (.ptr db doff) } := ExS.set (EvE.var l0)
  let s1 : State := { s0 with locals := s0.locals.upd 3 (.ptr db doff) }
  have hs4 : ExS Gen.prog s1 (.set 4 (.var 1)) .normal
      { s1 with locals := s1.locals.upd 4 (.ptr sb soff) } :=
    ExS.set (EvE.var (by simpa [s1, Locals.upd] using l1))
  let s2 : State := { s1 with locals := s1.locals.upd 4 (.ptr sb soff) }
  have hs5 : ExS Gen.prog s2 (.set 5 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s2 with locals := s2.locals.upd 5 (.int u64 0) } :=
    ExS.set (EvE.cast (EvE.const _) cast_u64_i32_zero)
  let s3 : State := { s2 with locals := s2.locals.upd 5 (.int u64 0) }
  have hinv : McInv m db sb dblk sblk doff soff n n s3 := by
    refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simpa [s3, s2, s1, Locals.upd] using l0
    · simpa [s3, s2, s1, Locals.upd] using l2
    · simp [s3, s2, s1, Locals.upd]
    · simp [s3, s2, s1, Locals.upd]
    · simp [s3, s2, s1, Locals.upd]
    · have : (((sblk.drop soff).take n).take 0) = [] := by simp
      simp only [s3, s2, s1, s0, Nat.sub_self, this]
      rw [hd]
      simp [splice]
    · intro b _; rfl
  obtain ⟨sf, hl, hq⟩ := memcpy_loop m db sb dblk sblk doff soff n hne hs hdl hsl hn s3 hinv
  obtain ⟨_, hq0, _, _, _, _, hro, hqm, hqr⟩ := hq
  have hret : EvE Gen.prog sf (.var 0) (.ptr db doff) := by
    exact EvE.var hq0
  refine ⟨sf, ?_, ?_, hqr⟩
  · have hbody : Gen.tobj_memcpy.body = .seq (.set 3 (.var 0)) (.seq (.set 4 (.var 1))
        (.seq (.seq (.set 5 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.loop mcBody mcStep))
          (.ret (some (.var 0))))) := rfl
    rw [hbody]
    exact ExS.seq hs3 (ExS.seq hs4 (ExS.seq (ExS.seq hs5 hl) (ExS.ret hret)))
  · rw [hqm]
    simp [List.take_take]

end Obj.C.Proofs
