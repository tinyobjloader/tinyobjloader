/-
  Refinement proof for the translated `tobj_tess_emit` (tobj_tess.c): it writes
  one triangle `(a, b, c)` at slot `k` of a `u32[3*]` output array and
  increments the counter cell `*k`.  Used by `ObjTessFan.lean`.
-/
import Obj.C.Gen
import Obj.C.Logic
import Obj.C.Lemmas
import Obj.C.Splice
namespace Obj.C.Proofs
open Obj.C

def u32 : IntTy := ⟨32, false⟩

theorem load_u32_cell (m : Mem) (b : Nat) (k : Nat)
    (hm : m b = some (encodeLE 4 k)) (hk : k < 4294967296) :
    load m (.int u32) (.ptr b 0) = .ok (.int u32 k) := by
  have hlen : (encodeLE 4 k).length = 4 := encodeLE_length 4 k
  simp [load, readBytes, hm, Ty.size, u32, IntTy.bytes, hlen, Res.bind]
  rw [List.take_of_length_le (by omega), decodeLE_encodeLE]
  have : (256 : Nat) ^ 4 = 4294967296 := by decide
  rw [this]; exact Nat.mod_eq_of_lt hk

theorem emit_index_eval (s : State) (ob kb : Nat) (blk : Block) (k c : Nat)
    (h0 : s.locals 0 = some (.ptr ob 0)) (h1 : s.locals 1 = some (.ptr kb 0))
    (hk : s.mem kb = some (encodeLE 4 k)) (hob : s.mem ob = some blk)
    (hk3 : 3 * k + c < 4294967296) (hc : c < 3) (hlen : 4 * (3 * k + c) ≤ blk.length) :
    EvE Gen.prog s
      (.index (.var 0) (.bin .add (some ⟨32, false⟩)
        (.bin .mul (some ⟨32, false⟩) (.load (.int ⟨32, false⟩) (.var 1))
          (.const (.int ⟨32, false⟩ 3))) (.const (.int ⟨32, false⟩ c))) 4)
      (.ptr ob (4 * (3 * k + c))) := by
  have hv0 : EvE Gen.prog s (.var 0) (.ptr ob 0) := EvE.var h0
  have hv1 : EvE Gen.prog s (.var 1) (.ptr kb 0) := EvE.var h1
  have hl : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.var 1)) (.int u32 k) :=
    EvE.load hv1 (load_u32_cell s.mem kb k hk (by omega))
  have hmul : EvE Gen.prog s (.bin .mul (some ⟨32, false⟩) (.load (.int ⟨32, false⟩) (.var 1))
      (.const (.int ⟨32, false⟩ 3))) (.int u32 (3 * k)) := by
    apply EvE.bin hl (EvE.const _)
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.modulus, Res.bind]
    omega
  have hadd : EvE Gen.prog s (.bin .add (some ⟨32, false⟩)
      (.bin .mul (some ⟨32, false⟩) (.load (.int ⟨32, false⟩) (.var 1))
        (.const (.int ⟨32, false⟩ 3))) (.const (.int ⟨32, false⟩ c))) (.int u32 (3 * k + c)) := by
    apply EvE.bin hmul (EvE.const _)
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.modulus, Res.bind]
    omega
  apply EvE.index hv0 hadd
  simp [u32, ptrAddN, hob]
  rw [if_pos (by omega), Nat.mul_comm]


theorem splice_u32_cell (k k' : Nat) :
    splice (encodeLE 4 k) 0 (encodeLE 4 k') = encodeLE 4 k' := by
  have h1 : (encodeLE 4 k).length = 4 := encodeLE_length 4 k
  have h2 : (encodeLE 4 k').length = 4 := encodeLE_length 4 k'
  simp [splice, h1, h2]

theorem emit_store_step (s : State) (ob kb : Nat) (blk : Block) (k c j v : Nat)
    (h0 : s.locals 0 = some (.ptr ob 0)) (h1 : s.locals 1 = some (.ptr kb 0))
    (hj : s.locals j = some (.int u32 v))
    (hk : s.mem kb = some (encodeLE 4 k)) (hob : s.mem ob = some blk) (hro : s.ro = false)
    (hk3 : 3 * k + c < 4294967296) (hc : c < 3) (hlen : 4 * (3 * k + c) + 4 ≤ blk.length)
    (hv : v < 4294967296) :
    ExS Gen.prog s
      (.store (.int ⟨32, false⟩)
        (.index (.var 0) (.bin .add (some ⟨32, false⟩)
          (.bin .mul (some ⟨32, false⟩) (.load (.int ⟨32, false⟩) (.var 1))
            (.const (.int ⟨32, false⟩ 3))) (.const (.int ⟨32, false⟩ c))) 4)
        (.var j))
      .normal { s with mem := s.mem.upd ob (splice blk (4 * (3 * k + c)) (encodeLE 4 v)) } := by
  have hidx := emit_index_eval s ob kb blk k c h0 h1 hk hob hk3 hc (by omega)
  have hval : EvE Gen.prog s (.var j) (.int u32 v) := EvE.var hj
  have hst := store_int s.mem ob (4 * (3 * k + c)) blk hob ⟨32, false⟩ v (by
    simp [IntTy.bytes]; omega)
  exact ExS.store hidx hval hro (by simpa [u32, IntTy.bytes] using hst)

/-- `tobj_tess_emit`: writes one triangle at slot `k` of the `u32` output array
    and increments the counter cell. -/
theorem emit_exs (m : Mem) (ob kb : Nat) (oblk : Block) (k a b c : Nat)
    (hne : ob ≠ kb) (hob : m ob = some oblk) (hkb : m kb = some (encodeLE 4 k))
    (hk : 3 * (k + 1) < 4294967296) (hlen : 12 * (k + 1) ≤ oblk.length)
    (ha : a < 4294967296) (hb : b < 4294967296) (hc : c < 4294967296) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.tobj_tess_emit.params
        [.ptr ob 0, .ptr kb 0, .int u32 a, .int u32 b, .int u32 c], m, false⟩
      Gen.tobj_tess_emit.body .normal s' ∧
      s'.mem = ((m.upd ob (splice (splice (splice oblk (12 * k) (encodeLE 4 a))
          (12 * k + 4) (encodeLE 4 b)) (12 * k + 8) (encodeLE 4 c))).upd kb
          (encodeLE 4 (k + 1))) := by
  let s0 : State := ⟨frameLocals Gen.tobj_tess_emit.params
    [.ptr ob 0, .ptr kb 0, .int u32 a, .int u32 b, .int u32 c], m, false⟩
  have l0 : s0.locals 0 = some (.ptr ob 0) := by
    simp [s0, frameLocals, Gen.tobj_tess_emit, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr kb 0) := by
    simp [s0, frameLocals, Gen.tobj_tess_emit, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s0.locals 2 = some (.int u32 a) := by
    simp [s0, frameLocals, Gen.tobj_tess_emit, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l3 : s0.locals 3 = some (.int u32 b) := by
    simp [s0, frameLocals, Gen.tobj_tess_emit, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l4 : s0.locals 4 = some (.int u32 c) := by
    simp [s0, frameLocals, Gen.tobj_tess_emit, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have st1 := emit_store_step s0 ob kb oblk k 0 2 a l0 l1 l2 hkb hob rfl
    (by omega) (by omega) (by omega) ha
  let b1 := splice oblk (4 * (3 * k + 0)) (encodeLE 4 a)
  let s1 : State := { s0 with mem := m.upd ob b1 }
  have len1 : b1.length = oblk.length := by
    apply splice_length; simp [encodeLE_length]; omega
  have k1 : s1.mem kb = some (encodeLE 4 k) := by
    show (m.upd ob b1) kb = _
    rw [Mem.upd_ne m b1 hne.symm]; exact hkb
  have o1 : s1.mem ob = some b1 := by
    show (m.upd ob b1) ob = _
    exact Mem.upd_same m ob b1
  have st2 := emit_store_step s1 ob kb b1 k 1 3 b l0 l1 l3 k1 o1 rfl
    (by omega) (by omega) (by omega) hb
  let b2 := splice b1 (4 * (3 * k + 1)) (encodeLE 4 b)
  let s2 : State := { s1 with mem := s1.mem.upd ob b2 }
  have len2 : b2.length = oblk.length := by
    show (splice b1 _ _).length = _
    rw [splice_length b1 _ _ (by simp [encodeLE_length]; omega), len1]
  have k2 : s2.mem kb = some (encodeLE 4 k) := by
    show (s1.mem.upd ob b2) kb = _
    rw [Mem.upd_ne s1.mem b2 hne.symm]; exact k1
  have o2 : s2.mem ob = some b2 := by
    show (s1.mem.upd ob b2) ob = _
    exact Mem.upd_same s1.mem ob b2
  have st3 := emit_store_step s2 ob kb b2 k 2 4 c l0 l1 l4 k2 o2 rfl
    (by omega) (by omega) (by omega) hc
  let b3 := splice b2 (4 * (3 * k + 2)) (encodeLE 4 c)
  let s3 : State := { s2 with mem := s2.mem.upd ob b3 }
  have k3 : s3.mem kb = some (encodeLE 4 k) := by
    show (s2.mem.upd ob b3) kb = _
    rw [Mem.upd_ne s2.mem b3 hne.symm]; exact k2
  -- counter update
  have hv1 : EvE Gen.prog s3 (.var 1) (.ptr kb 0) := EvE.var l1
  have hcell : load s3.mem (.int u32) (.ptr kb 0) = .ok (.int u32 k) :=
    load_u32_cell s3.mem kb k k3 (by omega)
  have hl : EvE Gen.prog s3 (.load (.int ⟨32, false⟩) (.var 1)) (.int u32 k) :=
    EvE.load hv1 hcell
  have hc1 : EvE Gen.prog s3 (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.var 1)))
      (.int u32 k) := by
    apply EvE.cast hl
    simp [evalCast, u32, IntTy.modulus]; omega
  have hadd : EvE Gen.prog s3 (.bin .add (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.var 1)))
      (.const (.int ⟨32, false⟩ 1))) (.int u32 (k + 1)) := by
    apply EvE.bin hc1 (EvE.const _)
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.modulus, Res.bind]
    omega
  have hc2 : EvE Gen.prog s3 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.var 1)))
      (.const (.int ⟨32, false⟩ 1)))) (.int u32 (k + 1)) := by
    apply EvE.cast hadd
    simp [evalCast, u32, IntTy.modulus]; omega
  have hstc := store_int s3.mem kb 0 (encodeLE 4 k) k3 ⟨32, false⟩ (k + 1)
    (by simp [IntTy.bytes, encodeLE_length])
  have st4 : ExS Gen.prog s3
      (.store (.int ⟨32, false⟩) (.var 1) (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩)
        (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.var 1)))
        (.const (.int ⟨32, false⟩ 1)))))
      .normal { s3 with mem := s3.mem.upd kb (splice (encodeLE 4 k) 0 (encodeLE 4 (k + 1))) } :=
    ExS.store hv1 hc2 rfl (by simpa [u32, IntTy.bytes] using hstc)
  refine ⟨{ s3 with mem := s3.mem.upd kb (splice (encodeLE 4 k) 0 (encodeLE 4 (k + 1))) }, ?_, ?_⟩
  · have hbody : Gen.tobj_tess_emit.body = _ := rfl
    rw [hbody]
    exact ExS.seq st1 (ExS.seq st2 (ExS.seq st3 st4))
  · simp only [s3, s2, s1, s0, b3, b2, b1, splice_u32_cell, Mem.upd_upd]
    have e0 : 4 * (3 * k + 0) = 12 * k := by omega
    have e1 : 4 * (3 * k + 1) = 12 * k + 4 := by omega
    have e2 : 4 * (3 * k + 2) = 12 * k + 8 := by omega
    rw [e0, e1, e2]

end Obj.C.Proofs
