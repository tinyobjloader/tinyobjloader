/-
  Refinement proof for the translated `emit_face_core_f` (tiny_obj_c_impl.inc):
  the allocation-free core that copies the corner records selected by a
  triangle table into the output array and advances the caller's counter.

  `emit_face_core_f_exs` proves, for any block layout satisfying the stated
  bounds, that the translated function terminates without undefined behaviour,
  returns 1, leaves the output block equal to the original with the bytes
  `efBytes` written at `oo + 12 * count0`, advances `*out_count` by `3 * ntri`,
  and leaves every other block untouched.  `efBytes_eq_emitTris` identifies the
  written bytes with the pure specification `Obj.emitTris` (`Obj/Tess.lean`).
-/
import Obj.C.Proofs.ObjMemcpy
import Obj.Tess
namespace Obj.C.Proofs
open Obj.C Obj

theorem load_u64_cell (m : Mem) (b : Nat) (k : Nat)
    (hm : m b = some (encodeLE 8 k)) (hk : k < 18446744073709551616) :
    load m (.int u64) (.ptr b 0) = .ok (.int u64 k) := by
  have hlen : (encodeLE 8 k).length = 8 := encodeLE_length 8 k
  simp [load, readBytes, hm, Ty.size, u64, IntTy.bytes, hlen, Res.bind]
  rw [List.take_of_length_le (by omega), decodeLE_encodeLE]
  have : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  rw [this]; exact Nat.mod_eq_of_lt hk

theorem load_u32_at (m : Mem) (b o : Nat) (blk : Block) (x : Nat)
    (hm : m b = some blk) (hl : o + 4 ≤ blk.length)
    (hx : (blk.drop o).take 4 = encodeLE 4 x) (hlt : x < 4294967296) :
    load m (.int u32) (.ptr b o) = .ok (.int u32 x) := by
  have hrb : readBytes m b o 4 = .ok (encodeLE 4 x) := by
    simp only [readBytes, hm]
    rw [if_pos hl, hx]
  have hsz : Ty.size (.int u32) = 4 := rfl
  simp only [load, hsz, hrb, Res.bind_eq, Res.bind_ok]
  have : (256 : Nat) ^ 4 = 4294967296 := by decide
  rw [decodeLE_encodeLE, this, Nat.mod_eq_of_lt hlt]
  rfl

theorem splice_cell8 (k k' : Nat) :
    splice (encodeLE 8 k) 0 (encodeLE 8 k') = encodeLE 8 k' := by
  have h1 : (encodeLE 8 k).length = 8 := encodeLE_length 8 k
  have h2 : (encodeLE 8 k').length = 8 := encodeLE_length 8 k'
  simp [splice, h1, h2]


def efCall (c : Nat) : Stmt :=
  (.call none 17 [(.index (.var 3) (.bin .add (some ⟨64, false⟩)
      (.load (.int ⟨64, false⟩) (.var 4)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ c)))) 12),
    (.index (.var 0) (.load (.int ⟨32, false⟩) (.index (.var 1) (.bin .add (some ⟨32, false⟩)
      (.bin .mul (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 3)) (.var 7))
      (.const (.int ⟨32, false⟩ c))) 4)) 12),
    (.const (.int ⟨64, false⟩ 12))])

def efCount : Stmt :=
  (.store (.int ⟨64, false⟩) (.var 4) (.bin .add (some ⟨64, false⟩)
    (.load (.int ⟨64, false⟩) (.var 4)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))))

def efBody : Stmt :=
  (.ite (.bin .lt (some ⟨32, false⟩) (.var 7) (.var 2))
    (.seq (efCall 0) (.seq (efCall 1) (.seq (efCall 2) efCount))) .brk)

def efStep : Stmt :=
  (.set 7 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 7))
    (.const (.int ⟨32, false⟩ 1)))))

theorem ef_loop_ast : Gen.emit_face_core_f_loop0 = .loop efBody efStep := rfl


theorem cast_u64_u32 (c : Nat) (h : c < 4294967296) :
    evalCast ⟨64, false⟩ (.int ⟨32, false⟩ c) = .ok (.int u64 c) := by
  simp [evalCast, u64, IntTy.modulus]; omega

theorem u32_mul_val (a c : Nat) (h : a * c < 4294967296) (ha : a < 4294967296) (hc : c < 4294967296) :
    evalBin .mul (some ⟨32, false⟩) (.int u32 a) (.int u32 c) = .ok (.int u32 (a * c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.modulus, Res.bind]
  omega

/-- Facts about the interpreter state used by the `emit_face_core` proof. -/
structure EfSt (cb tb ob cntb co to oo t count ntri : Nat) (cblk tblk curblk : Block)
    (s : State) : Prop where
  l0 : s.locals 0 = some (.ptr cb co)
  l1 : s.locals 1 = some (.ptr tb to)
  l2 : s.locals 2 = some (.int u32 ntri)
  l3 : s.locals 3 = some (.ptr ob oo)
  l4 : s.locals 4 = some (.ptr cntb 0)
  l7 : s.locals 7 = some (.int u32 t)
  ro : s.ro = false
  mcb : s.mem cb = some cblk
  mtb : s.mem tb = some tblk
  mob : s.mem ob = some curblk
  mcnt : s.mem cntb = some (encodeLE 8 count)

theorem ef_call_step (cb tb ob cntb co to oo t count ntri : Nat) (cblk tblk curblk : Block)
    (s : State) (hst : EfSt cb tb ob cntb co to oo t count ntri cblk tblk curblk s)
    (hne1 : ob ≠ cb) (c : Nat) (hc : c < 3) (hcount : count + c < 18446744073709551616)
    (ht3 : 3 * t + c < 4294967296) (idx : Nat)
    (hword : (tblk.drop (to + 4 * (3 * t + c))).take 4 = encodeLE 4 idx)
    (hidx32 : idx < 4294967296) (hwl : to + 4 * (3 * t + c) + 4 ≤ tblk.length)
    (hsrc : co + 12 * idx + 12 ≤ cblk.length)
    (hdst : oo + 12 * (count + c) + 12 ≤ curblk.length) :
    ∃ s', ExS Gen.prog s (efCall c) .normal s' ∧ s'.locals = s.locals ∧ s'.ro = s.ro ∧
      s'.mem ob = some (splice curblk (oo + 12 * (count + c))
        ((cblk.drop (co + 12 * idx)).take 12)) ∧ ∀ b, b ≠ ob → s'.mem b = s.mem b := by
  obtain ⟨l0, l1, _, l3, l4, l7, hro, mcb, mtb, mob, mcnt⟩ := hst
  have hv3 : EvE Gen.prog s (.var 3) (.ptr ob oo) := EvE.var l3
  have hv0 : EvE Gen.prog s (.var 0) (.ptr cb co) := EvE.var l0
  have hv1 : EvE Gen.prog s (.var 1) (.ptr tb to) := EvE.var l1
  have hv4 : EvE Gen.prog s (.var 4) (.ptr cntb 0) := EvE.var l4
  have hv7 : EvE Gen.prog s (.var 7) (.int u32 t) := EvE.var l7
  have hcnt : EvE Gen.prog s (.load (.int ⟨64, false⟩) (.var 4)) (.int u64 count) :=
    EvE.load hv4 (load_u64_cell s.mem cntb count mcnt (by omega))
  have hcc : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ c))) (.int u64 c) :=
    EvE.cast (EvE.const _) (cast_u64_u32 c (by omega))
  have hsum : EvE Gen.prog s (.bin .add (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.var 4))
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ c)))) (.int u64 (count + c)) :=
    EvE.bin hcnt hcc (u64_add_val _ _ (by omega))
  have hdstp : EvE Gen.prog s (.index (.var 3) (.bin .add (some ⟨64, false⟩)
      (.load (.int ⟨64, false⟩) (.var 4)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ c)))) 12)
      (.ptr ob (oo + (count + c) * 12)) := by
    apply EvE.index hv3 hsum
    simp [u64, ptrAddN, mob]
    omega
  have h3t : EvE Gen.prog s (.bin .mul (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 3)) (.var 7))
      (.int u32 (3 * t)) :=
    EvE.bin (EvE.const _) hv7 (u32_mul_val _ _ (by omega) (by omega) (by omega))
  have h3tc : EvE Gen.prog s (.bin .add (some ⟨32, false⟩) (.bin .mul (some ⟨32, false⟩)
      (.const (.int ⟨32, false⟩ 3)) (.var 7)) (.const (.int ⟨32, false⟩ c)))
      (.int u32 (3 * t + c)) :=
    EvE.bin h3t (EvE.const _) (u32_add_val _ _ (by omega))
  have htp : EvE Gen.prog s (.index (.var 1) (.bin .add (some ⟨32, false⟩) (.bin .mul
      (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 3)) (.var 7)) (.const (.int ⟨32, false⟩ c))) 4)
      (.ptr tb (to + (3 * t + c) * 4)) := by
    apply EvE.index hv1 h3tc
    simp [u32, ptrAddN, mtb]
    omega
  have hword' : (tblk.drop (to + (3 * t + c) * 4)).take 4 = encodeLE 4 idx := by
    rw [Nat.mul_comm]; exact hword
  have hidxv : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.index (.var 1) (.bin .add
      (some ⟨32, false⟩) (.bin .mul (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 3)) (.var 7))
      (.const (.int ⟨32, false⟩ c))) 4)) (.int u32 idx) :=
    EvE.load htp (load_u32_at s.mem tb _ tblk idx mtb (by omega) hword' hidx32)
  have hsrcp : EvE Gen.prog s (.index (.var 0) (.load (.int ⟨32, false⟩) (.index (.var 1)
      (.bin .add (some ⟨32, false⟩) (.bin .mul (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 3))
      (.var 7)) (.const (.int ⟨32, false⟩ c))) 4)) 12) (.ptr cb (co + idx * 12)) := by
    apply EvE.index hv0 hidxv
    simp [u32, ptrAddN, mcb]
    omega
  have hargs := EvArgs.cons hdstp (EvArgs.cons hsrcp (EvArgs.cons
    (EvE.const (.int ⟨64, false⟩ 12)) EvArgs.nil))
  have hne : ob ≠ cb := hne1
  obtain ⟨sm, hbody, hmo, hmr⟩ := memcpy_exs s.mem ob cb curblk cblk (oo + (count + c) * 12)
    (co + idx * 12) 12 hne mob mcb (by omega) (by omega) (by omega)
  have hstate : (⟨frameLocals Gen.tobj_memcpy.params [.ptr ob (oo + (count + c) * 12),
      .ptr cb (co + idx * 12), .int ⟨64, false⟩ 12], s.mem, s.ro⟩ : State) =
      ⟨frameLocals Gen.tobj_memcpy.params [.ptr ob (oo + (count + c) * 12),
      .ptr cb (co + idx * 12), .int ⟨64, false⟩ 12], s.mem, false⟩ := by rw [hro]
  have hcall := ExS_call_discard (p := Gen.prog) (s := s) (f := 17) (fn := Gen.tobj_memcpy)
    hargs (by rfl) (by rfl) (by rw [hstate]; exact hbody)
  refine ⟨{ s with mem := sm.mem }, ?_, rfl, rfl, ?_, ?_⟩
  · unfold efCall; exact hcall
  · show sm.mem ob = _
    rw [hmo, Nat.mul_comm (count + c) 12, Nat.mul_comm idx 12]
  · intro b hb
    exact hmr b hb


/-- A copy step preserves the state facts (new output block). -/
theorem EfSt.after_call {cb tb ob cntb co to oo t count ntri : Nat} {cblk tblk curblk : Block}
    {s s' : State} (hst : EfSt cb tb ob cntb co to oo t count ntri cblk tblk curblk s)
    (hne1 : ob ≠ cb) (hne2 : ob ≠ tb) (hne3 : ob ≠ cntb) (newblk : Block)
    (hl : s'.locals = s.locals) (hro : s'.ro = s.ro) (hob : s'.mem ob = some newblk)
    (hrest : ∀ b, b ≠ ob → s'.mem b = s.mem b) :
    EfSt cb tb ob cntb co to oo t count ntri cblk tblk newblk s' where
  l0 := by rw [hl]; exact hst.l0
  l1 := by rw [hl]; exact hst.l1
  l2 := by rw [hl]; exact hst.l2
  l3 := by rw [hl]; exact hst.l3
  l4 := by rw [hl]; exact hst.l4
  l7 := by rw [hl]; exact hst.l7
  ro := by rw [hro]; exact hst.ro
  mcb := by rw [hrest cb hne1.symm]; exact hst.mcb
  mtb := by rw [hrest tb hne2.symm]; exact hst.mtb
  mob := hob
  mcnt := by rw [hrest cntb hne3.symm]; exact hst.mcnt


/-- Bytes of the `c`-th corner reference of triangle `t`. -/
def efCc (cblk : Block) (co idx : Nat) : Block := (cblk.drop (co + 12 * idx)).take 12

/-- Bytes copied for triangle `t`. -/
def efChunk (cblk : Block) (co : Nat) (triIdx : Nat → Nat → Nat) (t : Nat) : Block :=
  efCc cblk co (triIdx t 0) ++ efCc cblk co (triIdx t 1) ++ efCc cblk co (triIdx t 2)

/-- Bytes copied for the first `t` triangles. -/
def efBytes (cblk : Block) (co : Nat) (triIdx : Nat → Nat → Nat) (t : Nat) : Block :=
  (List.range t).flatMap (efChunk cblk co triIdx)

theorem efCc_length (cblk : Block) (co idx : Nat) (h : co + 12 * idx + 12 ≤ cblk.length) :
    (efCc cblk co idx).length = 12 := by
  simp [efCc]; omega

/-- Hypotheses on the triangle table and the corner array. -/
structure EfTab (cblk tblk : Block) (co to : Nat) (triIdx : Nat → Nat → Nat) (ntri : Nat) :
    Prop where
  word : ∀ t c, t < ntri → c < 3 →
    (tblk.drop (to + 4 * (3 * t + c))).take 4 = encodeLE 4 (triIdx t c)
  word32 : ∀ t c, t < ntri → c < 3 → triIdx t c < 4294967296
  wlen : ∀ t c, t < ntri → c < 3 → to + 4 * (3 * t + c) + 4 ≤ tblk.length
  src : ∀ t c, t < ntri → c < 3 → co + 12 * triIdx t c + 12 ≤ cblk.length

theorem efChunk_length (cblk tblk : Block) (co to : Nat) (triIdx : Nat → Nat → Nat) (ntri : Nat)
    (tab : EfTab cblk tblk co to triIdx ntri) (t : Nat) (ht : t < ntri) :
    (efChunk cblk co triIdx t).length = 36 := by
  have h0 := efCc_length cblk co _ (tab.src t 0 ht (by omega))
  have h1 := efCc_length cblk co _ (tab.src t 1 ht (by omega))
  have h2 := efCc_length cblk co _ (tab.src t 2 ht (by omega))
  simp [efChunk, h0, h1, h2]

theorem efBytes_length (cblk tblk : Block) (co to : Nat) (triIdx : Nat → Nat → Nat) (ntri : Nat)
    (tab : EfTab cblk tblk co to triIdx ntri) (t : Nat) (ht : t ≤ ntri) :
    (efBytes cblk co triIdx t).length = 36 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have := ih (by omega)
    have hc := efChunk_length cblk tblk co to triIdx ntri tab t (by omega)
    simp only [efBytes, List.range_succ, List.flatMap_append, List.length_append] at *
    simp [hc, this]; omega

theorem efBytes_succ (cblk : Block) (co : Nat) (triIdx : Nat → Nat → Nat) (t : Nat) :
    efBytes cblk co triIdx (t + 1) = efBytes cblk co triIdx t ++ efChunk cblk co triIdx t := by
  simp [efBytes, List.range_succ]


theorem ef_iter (cb tb ob cntb co to oo t count0 ntri : Nat) (cblk tblk oblk : Block)
    (triIdx : Nat → Nat → Nat) (tab : EfTab cblk tblk co to triIdx ntri) (s : State)
    (hne1 : ob ≠ cb) (hne2 : ob ≠ tb) (hne3 : ob ≠ cntb) (hne4 : cb ≠ cntb) (hne5 : tb ≠ cntb)
    (ht : t < ntri) (hn3 : 3 * ntri < 4294967296)
    (hcnt64 : count0 + 3 * ntri < 18446744073709551616)
    (hout : oo + 12 * (count0 + 3 * ntri) ≤ oblk.length)
    (hst : EfSt cb tb ob cntb co to oo t (count0 + 3 * t) ntri cblk tblk
      (splice oblk (oo + 12 * count0) (efBytes cblk co triIdx t)) s) :
    ∃ s1 s2, ExS Gen.prog s efBody .normal s1 ∧ ExS Gen.prog s1 efStep .normal s2 ∧
      EfSt cb tb ob cntb co to oo (t + 1) (count0 + 3 * (t + 1)) ntri cblk tblk
        (splice oblk (oo + 12 * count0) (efBytes cblk co triIdx (t + 1))) s2 ∧
      ∀ b, b ≠ ob → b ≠ cntb → s2.mem b = s.mem b := by
  let P := oo + 12 * count0
  let curblk := splice oblk P (efBytes cblk co triIdx t)
  have hblen : (efBytes cblk co triIdx t).length = 36 * t :=
    efBytes_length cblk tblk co to triIdx ntri tab t (by omega)
  have hcur : curblk.length = oblk.length := by
    apply splice_length; rw [hblen]; omega
  let count := count0 + 3 * t
  -- three copies
  have hA := efCc_length cblk co _ (tab.src t 0 ht (by omega))
  have hB := efCc_length cblk co _ (tab.src t 1 ht (by omega))
  have hC := efCc_length cblk co _ (tab.src t 2 ht (by omega))
  obtain ⟨sa, ha, hal, har, hao, hrest_a⟩ := ef_call_step cb tb ob cntb co to oo t count ntri
    cblk tblk curblk s hst hne1 0 (by omega) (by omega) (by omega) (triIdx t 0)
    (tab.word t 0 ht (by omega)) (tab.word32 t 0 ht (by omega)) (tab.wlen t 0 ht (by omega))
    (tab.src t 0 ht (by omega)) (by omega)
  let blkA := splice curblk (oo + 12 * (count + 0)) (efCc cblk co (triIdx t 0))
  have blkA_len : blkA.length = oblk.length := by
    show (splice curblk _ _).length = _
    rw [splice_length _ _ _ (by omega), hcur]
  have stA := EfSt.after_call hst hne1 hne2 hne3 blkA hal har hao hrest_a
  obtain ⟨sb, hb, hbl, hbr, hbo, hrest_b⟩ := ef_call_step cb tb ob cntb co to oo t count ntri
    cblk tblk blkA sa stA hne1 1 (by omega) (by omega) (by omega) (triIdx t 1)
    (tab.word t 1 ht (by omega)) (tab.word32 t 1 ht (by omega)) (tab.wlen t 1 ht (by omega))
    (tab.src t 1 ht (by omega)) (by omega)
  let blkB := splice blkA (oo + 12 * (count + 1)) (efCc cblk co (triIdx t 1))
  have blkB_len : blkB.length = oblk.length := by
    show (splice blkA _ _).length = _
    rw [splice_length _ _ _ (by omega), blkA_len]
  have stB := EfSt.after_call stA hne1 hne2 hne3 blkB hbl hbr hbo hrest_b
  obtain ⟨sc, hc, hcl, hcr, hco, hrest_c⟩ := ef_call_step cb tb ob cntb co to oo t count ntri
    cblk tblk blkB sb stB hne1 2 (by omega) (by omega) (by omega) (triIdx t 2)
    (tab.word t 2 ht (by omega)) (tab.word32 t 2 ht (by omega)) (tab.wlen t 2 ht (by omega))
    (tab.src t 2 ht (by omega)) (by omega)
  let blkC := splice blkB (oo + 12 * (count + 2)) (efCc cblk co (triIdx t 2))
  have stC := EfSt.after_call stB hne1 hne2 hne3 blkC hcl hcr hco hrest_c
  -- counter update
  have hv4 : EvE Gen.prog sc (.var 4) (.ptr cntb 0) := EvE.var stC.l4
  have hcntv : EvE Gen.prog sc (.load (.int ⟨64, false⟩) (.var 4)) (.int u64 count) :=
    EvE.load hv4 (load_u64_cell sc.mem cntb count stC.mcnt (by omega))
  have hc3 : EvE Gen.prog sc (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3))) (.int u64 3) :=
    EvE.cast (EvE.const _) (cast_u64_u32 3 (by omega))
  have hsum : EvE Gen.prog sc (.bin .add (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.var 4))
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) (.int u64 (count + 3)) :=
    EvE.bin hcntv hc3 (u64_add_val _ _ (by omega))
  have hstc := store_int sc.mem cntb 0 (encodeLE 8 count) stC.mcnt ⟨64, false⟩ (count + 3)
    (by simp [IntTy.bytes])
  have hstoreC : ExS Gen.prog sc efCount .normal { sc with mem := (sc.mem.upd cntb (splice (encodeLE 8 count) 0 (encodeLE 8 (count + 3)))) } := by
    unfold efCount
    exact ExS.store hv4 hsum stC.ro (by simpa [IntTy.bytes, u64] using hstc)
  let s1 : State := { sc with mem := (sc.mem.upd cntb (splice (encodeLE 8 count) 0 (encodeLE 8 (count + 3)))) }
  -- guard
  have hv7 : EvE Gen.prog s (.var 7) (.int u32 t) := EvE.var hst.l7
  have hv2 : EvE Gen.prog s (.var 2) (.int u32 ntri) := EvE.var hst.l2
  have hlt : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 7) (.var 2))
      (boolVal (decide (t < ntri))) := EvE.bin hv7 hv2 (u32_lt_val _ _ (by omega) (by omega))
  have hbody : ExS Gen.prog s efBody .normal s1 := by
    unfold efBody
    exact ExS.ite hlt (bc := true) (by simp [truthy, boolVal, ht])
      (by simpa using ExS.seq ha (ExS.seq hb (ExS.seq hc hstoreC)))
  -- step
  have hl7 : s1.locals 7 = some (.int u32 t) := by
    show sc.locals 7 = _
    exact stC.l7
  have hcs : EvE Gen.prog s1 (.cast ⟨32, false⟩ (.var 7)) (.int u32 t) :=
    EvE.cast (EvE.var hl7) (cast_u32_u32 _ (by omega))
  have hadd : EvE Gen.prog s1 (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 7))
      (.const (.int ⟨32, false⟩ 1))) (.int u32 (t + 1)) :=
    EvE.bin hcs (EvE.const _) (u32_add_val _ _ (by omega))
  have hstep : ExS Gen.prog s1 efStep .normal
      { s1 with locals := s1.locals.upd 7 (.int u32 (t + 1)) } := by
    unfold efStep
    exact ExS.set (EvE.cast hadd (cast_u32_u32 _ (by omega)))
  have hblk : blkC = splice oblk P (efBytes cblk co triIdx (t + 1)) := by
    have e1 : oo + 12 * (count + 1) = (oo + 12 * (count + 0)) +
        (efCc cblk co (triIdx t 0)).length := by rw [hA]; omega
    have sp1 := splice_append curblk (oo + 12 * (count + 0)) (efCc cblk co (triIdx t 0))
      (efCc cblk co (triIdx t 1)) (by simp only [List.length_append, hA, hB]; omega)
    have e2 : oo + 12 * (count + 2) = (oo + 12 * (count + 0)) +
        (efCc cblk co (triIdx t 0) ++ efCc cblk co (triIdx t 1)).length := by
      simp only [List.length_append, hA, hB]; omega
    have sp2 := splice_append curblk (oo + 12 * (count + 0))
      (efCc cblk co (triIdx t 0) ++ efCc cblk co (triIdx t 1)) (efCc cblk co (triIdx t 2))
      (by simp only [List.length_append, hA, hB, hC]; omega)
    have e0 : oo + 12 * (count + 0) = P + (efBytes cblk co triIdx t).length := by
      rw [hblen]; simp only [P, count]; omega
    have sp3 := splice_append oblk P (efBytes cblk co triIdx t)
      (efChunk cblk co triIdx t) (by
        rw [hblen, efChunk_length cblk tblk co to triIdx ntri tab t ht]
        simp only [P]; omega)
    show splice (splice (splice curblk _ _) _ _) _ _ = _
    rw [e1, sp1, e2, sp2, efBytes_succ, ← sp3, ← e0]
    rfl
  have newst : EfSt cb tb ob cntb co to oo (t + 1) (count0 + 3 * (t + 1)) ntri cblk tblk
      (splice oblk P (efBytes cblk co triIdx (t + 1)))
      { s1 with locals := s1.locals.upd 7 (.int u32 (t + 1)) } := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [s1, Locals.upd] using stC.l0
    · simpa [s1, Locals.upd] using stC.l1
    · simpa [s1, Locals.upd] using stC.l2
    · simpa [s1, Locals.upd] using stC.l3
    · simpa [s1, Locals.upd] using stC.l4
    · simp [s1, Locals.upd]
    · exact stC.ro
    · show (sc.mem.upd cntb _) cb = _
      rw [Mem.upd_ne _ _ hne4]; exact stC.mcb
    · show (sc.mem.upd cntb _) tb = _
      rw [Mem.upd_ne _ _ hne5]; exact stC.mtb
    · show (sc.mem.upd cntb _) ob = _
      rw [Mem.upd_ne _ _ hne3, ← hblk]; exact stC.mob
    · show (sc.mem.upd cntb _) cntb = _
      rw [Mem.upd_same, splice_cell8]
      have : count + 3 = count0 + 3 * (t + 1) := by simp only [count]; omega
      rw [this]
  refine ⟨s1, _, hbody, hstep, newst, ?_⟩
  intro b hb1 hb2
  show (sc.mem.upd cntb _) b = _
  rw [Mem.upd_ne _ _ hb2, hrest_c b hb1, hrest_b b hb1, hrest_a b hb1]


theorem splice_nil (blk : Block) (o : Nat) : splice blk o [] = blk := by
  simp [splice]

theorem u64_mul_val (a c : Nat) (h : a * c < 18446744073709551616) :
    evalBin .mul (some ⟨64, false⟩) (.int u64 a) (.int u64 c) = .ok (.int u64 (a * c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind]
  omega

theorem u64_gt_val (a n : Nat) :
    evalBin .gt (some ⟨64, false⟩) (.int u64 a) (.int u64 n) = .ok (boolVal (decide (a > n))) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u64, IntTy.modulus, Res.bind]

theorem cast_u32_i32_zero' : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 0) = .ok (.int u32 0) := by
  simp [evalCast, u32, IntTy.toInt, IntTy.wrap, IntTy.modulus]

/-- Loop invariant of `emit_face_core`: `j` triangles remain. -/
def EfInv (m : Mem) (cb tb ob cntb co to oo count0 ntri : Nat) (cblk tblk oblk : Block)
    (triIdx : Nat → Nat → Nat) (j : Nat) (s : State) : Prop :=
  j ≤ ntri ∧ EfSt cb tb ob cntb co to oo (ntri - j) (count0 + 3 * (ntri - j)) ntri cblk tblk
    (splice oblk (oo + 12 * count0) (efBytes cblk co triIdx (ntri - j))) s ∧
  ∀ b, b ≠ ob → b ≠ cntb → s.mem b = m b

theorem ef_loop (m : Mem) (cb tb ob cntb co to oo count0 ntri : Nat) (cblk tblk oblk : Block)
    (triIdx : Nat → Nat → Nat) (tab : EfTab cblk tblk co to triIdx ntri)
    (hne1 : ob ≠ cb) (hne2 : ob ≠ tb) (hne3 : ob ≠ cntb) (hne4 : cb ≠ cntb) (hne5 : tb ≠ cntb)
    (hn3 : 3 * ntri < 4294967296) (hcnt64 : count0 + 3 * ntri < 18446744073709551616)
    (hout : oo + 12 * (count0 + 3 * ntri) ≤ oblk.length)
    (s1 : State) (hinv : EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx ntri s1) :
    ∃ sf, ExS Gen.prog s1 (.loop efBody efStep) .normal sf ∧
      EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx 0 sf := by
  have hstep : ∀ j s, EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx (j + 1) s →
      ∃ s1 s2, ExS Gen.prog s efBody .normal s1 ∧ ExS Gen.prog s1 efStep .normal s2 ∧
      EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx j s2 := by
    intro j s ⟨hj, hst, hrest⟩
    have e : ntri - (j + 1) + 1 = ntri - j := by omega
    obtain ⟨s1', s2, hb, hs, hst2, hr2⟩ := ef_iter cb tb ob cntb co to oo (ntri - (j + 1)) count0
      ntri cblk tblk oblk triIdx tab s hne1 hne2 hne3 hne4 hne5 (by omega) hn3 hcnt64 hout hst
    refine ⟨s1', s2, hb, hs, by omega, ?_, ?_⟩
    · rw [e] at hst2; exact hst2
    · intro b hb1 hb2; rw [hr2 b hb1 hb2]; exact hrest b hb1 hb2
  have hexit : ∀ s, EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx 0 s →
      ∃ s1, ExS Gen.prog s efBody .brk s1 ∧
        EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx 0 s1 := by
    intro s hs
    obtain ⟨_, hst, hrest⟩ := hs
    have hv7 : EvE Gen.prog s (.var 7) (.int u32 (ntri - 0)) := EvE.var hst.l7
    have hv2 : EvE Gen.prog s (.var 2) (.int u32 ntri) := EvE.var hst.l2
    have hlt : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 7) (.var 2))
        (boolVal (decide (ntri - 0 < ntri))) :=
      EvE.bin hv7 hv2 (u32_lt_val _ _ (by omega) (by omega))
    refine ⟨s, ?_, ⟨by omega, hst, hrest⟩⟩
    unfold efBody
    apply ExS.ite hlt (bc := false) (by simp [truthy, boolVal])
    simpa using (ExS.brk (p := Gen.prog) (s := s))
  obtain ⟨sf, hl, hq⟩ := ExS.loop_decreasing_post (p := Gen.prog)
    (P := EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx)
    (Q := EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx 0)
    (n := ntri) (s := s1) hinv hstep (by
      intro s hs
      obtain ⟨s', hb, hq⟩ := hexit s hs
      exact ⟨s', hb, hq⟩)
  exact ⟨sf, hl, hq⟩


theorem emit_face_core_f_exs (m : Mem) (cb tb ob cntb co to oo count0 ntri outcap : Nat)
    (cblk tblk oblk : Block) (triIdx : Nat → Nat → Nat)
    (tab : EfTab cblk tblk co to triIdx ntri)
    (hne1 : ob ≠ cb) (hne2 : ob ≠ tb) (hne3 : ob ≠ cntb) (hne4 : cb ≠ cntb) (hne5 : tb ≠ cntb)
    (mcb : m cb = some cblk) (mtb : m tb = some tblk) (mob : m ob = some oblk)
    (mcnt : m cntb = some (encodeLE 8 count0))
    (hn3 : 3 * ntri < 4294967296) (hcap : count0 + 3 * ntri ≤ outcap)
    (hcap64 : outcap < 18446744073709551616)
    (hout : oo + 12 * (count0 + 3 * ntri) ≤ oblk.length) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.emit_face_core_f.params
        [.ptr cb co, .ptr tb to, .int u32 ntri, .ptr ob oo, .ptr cntb 0, .int u64 outcap],
        m, false⟩
      Gen.emit_face_core_f.body (.ret (some (.int ⟨8, false⟩ 1))) s' ∧
      s'.mem ob = some (splice oblk (oo + 12 * count0) (efBytes cblk co triIdx ntri)) ∧
      s'.mem cntb = some (encodeLE 8 (count0 + 3 * ntri)) ∧
      ∀ b, b ≠ ob → b ≠ cntb → s'.mem b = m b := by
  let s0 : State := ⟨frameLocals Gen.emit_face_core_f.params
    [.ptr cb co, .ptr tb to, .int u32 ntri, .ptr ob oo, .ptr cntb 0, .int u64 outcap], m, false⟩
  have l0 : s0.locals 0 = some (.ptr cb co) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr tb to) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s0.locals 2 = some (.int u32 ntri) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l3 : s0.locals 3 = some (.ptr ob oo) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l4 : s0.locals 4 = some (.ptr cntb 0) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l5 : s0.locals 5 = some (.int u64 outcap) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  -- null checks
  have nn : ∀ (i : Nat) (v : Val), (∃ b o, v = .ptr b o) → s0.locals i = some v →
      EvE Gen.prog s0 (.un .lnot ⟨32, true⟩ (.var i)) (boolVal false) := by
    intro i v ⟨b, o, hv⟩ hl
    subst hv
    exact EvE.un (EvE.var hl) (by simp [evalUn, truthy, boolVal])
  have g1 := nn 0 _ ⟨cb, co, rfl⟩ l0
  have g2 := nn 1 _ ⟨tb, to, rfl⟩ l1
  have g3 := nn 3 _ ⟨ob, oo, rfl⟩ l3
  have g4 := nn 4 _ ⟨cntb, 0, rfl⟩ l4
  have gor : EvE Gen.prog s0 (.lor (.lor (.lor (.un .lnot ⟨32, true⟩ (.var 0))
      (.un .lnot ⟨32, true⟩ (.var 1))) (.un .lnot ⟨32, true⟩ (.var 3)))
      (.un .lnot ⟨32, true⟩ (.var 4))) (boolVal false) := by
    have a12 := EvE.lor_false g1 (by simp [truthy, boolVal]) g2 (bb := false)
      (by simp [truthy, boolVal])
    have a123 := EvE.lor_false a12 (by simp [truthy, boolVal]) g3 (bb := false)
      (by simp [truthy, boolVal])
    exact EvE.lor_false a123 (by simp [truthy, boolVal]) g4 (bb := false)
      (by simp [truthy, boolVal])
  have hnull : ExS Gen.prog s0 (.ite (.lor (.lor (.lor (.un .lnot ⟨32, true⟩ (.var 0))
      (.un .lnot ⟨32, true⟩ (.var 1))) (.un .lnot ⟨32, true⟩ (.var 3)))
      (.un .lnot ⟨32, true⟩ (.var 4))) (.ret (some (.cond (.const (.int ⟨32, true⟩ 0))
      (.const (.int ⟨8, false⟩ 1)) (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s0 :=
    ExS.ite gor (bc := false) (by simp [truthy, boolVal]) (by simpa using (ExS.skip (p := Gen.prog) (s := s0)))
  -- need = ntri * 3
  have hv2 : EvE Gen.prog s0 (.var 2) (.int u32 ntri) := EvE.var l2
  have hc2 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.var 2)) (.int u64 ntri) :=
    EvE.cast hv2 (by simp [evalCast, u32, u64, IntTy.modulus]; omega)
  have hc3 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3))) (.int u64 3) :=
    EvE.cast (EvE.const _) (cast_u64_u32 3 (by omega))
  have hneed : EvE Gen.prog s0 (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2))
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) (.int u64 (ntri * 3)) :=
    EvE.bin hc2 hc3 (u64_mul_val _ _ (by omega))
  have hset6 := ExS.set (p := Gen.prog) (i := 6) hneed
  let s1 : State := { s0 with locals := s0.locals.upd 6 (.int u64 (ntri * 3)) }
  -- capacity check
  have hv4 : EvE Gen.prog s1 (.var 4) (.ptr cntb 0) := EvE.var (by simpa [s1, Locals.upd] using l4)
  have hcnt : EvE Gen.prog s1 (.load (.int ⟨64, false⟩) (.var 4)) (.int u64 count0) :=
    EvE.load hv4 (load_u64_cell s1.mem cntb count0 mcnt (by omega))
  have hv6 : EvE Gen.prog s1 (.var 6) (.int u64 (ntri * 3)) := EvE.var (by simp [s1, Locals.upd])
  have hsum : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.var 4))
      (.var 6)) (.int u64 (count0 + ntri * 3)) :=
    EvE.bin hcnt hv6 (u64_add_val _ _ (by omega))
  have hv5 : EvE Gen.prog s1 (.var 5) (.int u64 outcap) := EvE.var (by simpa [s1, Locals.upd] using l5)
  have hgt : EvE Gen.prog s1 (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩)
      (.load (.int ⟨64, false⟩) (.var 4)) (.var 6)) (.var 5))
      (boolVal (decide (count0 + ntri * 3 > outcap))) :=
    EvE.bin hsum hv5 (u64_gt_val _ _)
  have hcapck : ExS Gen.prog s1 (.ite (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩)
      (.load (.int ⟨64, false⟩) (.var 4)) (.var 6)) (.var 5))
      (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
        (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s1 :=
    ExS.ite hgt (bc := false) (by simp [truthy, boolVal]; omega)
      (by simpa using (ExS.skip (p := Gen.prog) (s := s1)))
  -- t = 0
  have hset7 : ExS Gen.prog s1 (.set 7 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s1 with locals := s1.locals.upd 7 (.int u32 0) } :=
    ExS.set (EvE.cast (EvE.const _) cast_u32_i32_zero')
  let s2 : State := { s1 with locals := s1.locals.upd 7 (.int u32 0) }
  have hinv : EfInv m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx ntri s2 := by
    refine ⟨Nat.le_refl _, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · simpa [s2, s1, Locals.upd] using l0
      · simpa [s2, s1, Locals.upd] using l1
      · simpa [s2, s1, Locals.upd] using l2
      · simpa [s2, s1, Locals.upd] using l3
      · simpa [s2, s1, Locals.upd] using l4
      · simp [s2, s1, Locals.upd]
      · simpa [s2, s1, s0] using mcb
      · simpa [s2, s1, s0] using mtb
      · simp only [s2, s1, s0, Nat.sub_self, efBytes, List.range_zero, List.flatMap_nil, splice_nil]
        simpa using mob
      · simp only [s2, s1, s0, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
        exact mcnt
    · intro b _ _; rfl
  obtain ⟨sf, hl, hq⟩ := ef_loop m cb tb ob cntb co to oo count0 ntri cblk tblk oblk triIdx tab
    hne1 hne2 hne3 hne4 hne5 hn3 (by omega) hout s2 hinv
  obtain ⟨_, hst, hrest⟩ := hq
  have hret : EvE Gen.prog sf (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
      (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 1) :=
    EvE.cond (EvE.const _) (bc := true) (by simp [truthy]) (EvE.const _)
  refine ⟨sf, ?_, ?_, ?_, ?_⟩
  · refine ExS.seq hnull (ExS.seq hset6 (ExS.seq hcapck (ExS.seq (ExS.seq hset7 hl) (ExS.ret hret))))
  · simpa using hst.mob
  · simpa using hst.mcnt
  · intro b h1 h2; exact hrest b h1 h2


/-- The bytes copied by `emit_face_core` are `Obj.emitTris` of the corner chunks:
    triangle `t` of the table `(triIdx t 0, triIdx t 1, triIdx t 2)` selects 12-byte
    corner records `efCc cblk co i` (`i < N`). -/
theorem efBytes_eq_emitTris (cblk : Block) (co : Nat) (triIdx : Nat → Nat → Nat)
    (ntri N : Nat) (hN : ∀ t c, t < ntri → c < 3 → triIdx t c < N) :
    efBytes cblk co triIdx ntri =
      (emitTris ((List.range N).map (efCc cblk co)) []
        ((List.range ntri).map fun t => (triIdx t 0, triIdx t 1, triIdx t 2))).flatten := by
  have key : ∀ i, i < N → ((List.range N).map (efCc cblk co)).getD i [] = efCc cblk co i := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  unfold efBytes emitTris
  rw [List.flatMap_map]
  have hl : ∀ L : List Nat, (∀ a ∈ L, a < ntri) →
      L.flatMap (efChunk cblk co triIdx) = (L.flatMap fun a =>
        [((List.range N).map (efCc cblk co)).getD
          (triIdx a 0, triIdx a 1, triIdx a 2).fst [],
         ((List.range N).map (efCc cblk co)).getD
          (triIdx a 0, triIdx a 1, triIdx a 2).snd.fst [],
         ((List.range N).map (efCc cblk co)).getD
          (triIdx a 0, triIdx a 1, triIdx a 2).snd.snd []]).flatten := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons a L ih =>
      intro h
      have ha : a < ntri := h a (by simp)
      simp only [List.flatMap_cons, List.flatten_append, ih (fun x hx => h x (by simp [hx]))]
      simp only [key _ (hN a 0 ha (by omega)), key _ (hN a 1 ha (by omega)),
        key _ (hN a 2 ha (by omega)), efChunk, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc]
  exact hl _ (fun a ha => by simpa using ha)


/-- Capacity failure: if the output array cannot hold `3 * ntri` more corners,
    the translated function returns 0 and leaves memory untouched. -/
theorem emit_face_core_f_cap_fail (m : Mem) (cb tb ob cntb co to oo count0 ntri outcap : Nat)
    (mcnt : m cntb = some (encodeLE 8 count0))
    (hn3 : 3 * ntri < 4294967296) (hcap : outcap < count0 + 3 * ntri)
    (hcap64 : outcap < 18446744073709551616)
    (hc64 : count0 + 3 * ntri < 18446744073709551616) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.emit_face_core_f.params
        [.ptr cb co, .ptr tb to, .int u32 ntri, .ptr ob oo, .ptr cntb 0, .int u64 outcap],
        m, false⟩
      Gen.emit_face_core_f.body (.ret (some (.int ⟨8, false⟩ 0))) s' ∧ s'.mem = m := by
  let s0 : State := ⟨frameLocals Gen.emit_face_core_f.params
    [.ptr cb co, .ptr tb to, .int u32 ntri, .ptr ob oo, .ptr cntb 0, .int u64 outcap], m, false⟩
  have l0 : s0.locals 0 = some (.ptr cb co) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr tb to) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s0.locals 2 = some (.int u32 ntri) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l3 : s0.locals 3 = some (.ptr ob oo) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l4 : s0.locals 4 = some (.ptr cntb 0) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l5 : s0.locals 5 = some (.int u64 outcap) := by
    simp [s0, frameLocals, Gen.emit_face_core_f, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have nn : ∀ (i : Nat) (v : Val), (∃ b o, v = .ptr b o) → s0.locals i = some v →
      EvE Gen.prog s0 (.un .lnot ⟨32, true⟩ (.var i)) (boolVal false) := by
    intro i v ⟨b, o, hv⟩ hl
    subst hv
    exact EvE.un (EvE.var hl) (by simp [evalUn, truthy, boolVal])
  have g1 := nn 0 _ ⟨cb, co, rfl⟩ l0
  have g2 := nn 1 _ ⟨tb, to, rfl⟩ l1
  have g3 := nn 3 _ ⟨ob, oo, rfl⟩ l3
  have g4 := nn 4 _ ⟨cntb, 0, rfl⟩ l4
  have gor : EvE Gen.prog s0 (.lor (.lor (.lor (.un .lnot ⟨32, true⟩ (.var 0))
      (.un .lnot ⟨32, true⟩ (.var 1))) (.un .lnot ⟨32, true⟩ (.var 3)))
      (.un .lnot ⟨32, true⟩ (.var 4))) (boolVal false) := by
    have a12 := EvE.lor_false g1 (by simp [truthy, boolVal]) g2 (bb := false)
      (by simp [truthy, boolVal])
    have a123 := EvE.lor_false a12 (by simp [truthy, boolVal]) g3 (bb := false)
      (by simp [truthy, boolVal])
    exact EvE.lor_false a123 (by simp [truthy, boolVal]) g4 (bb := false)
      (by simp [truthy, boolVal])
  have hnull : ExS Gen.prog s0 (.ite (.lor (.lor (.lor (.un .lnot ⟨32, true⟩ (.var 0))
      (.un .lnot ⟨32, true⟩ (.var 1))) (.un .lnot ⟨32, true⟩ (.var 3)))
      (.un .lnot ⟨32, true⟩ (.var 4))) (.ret (some (.cond (.const (.int ⟨32, true⟩ 0))
      (.const (.int ⟨8, false⟩ 1)) (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s0 :=
    ExS.ite gor (bc := false) (by simp [truthy, boolVal])
      (by simpa using (ExS.skip (p := Gen.prog) (s := s0)))
  have hv2 : EvE Gen.prog s0 (.var 2) (.int u32 ntri) := EvE.var l2
  have hc2 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.var 2)) (.int u64 ntri) :=
    EvE.cast hv2 (by simp [evalCast, u32, u64, IntTy.modulus]; omega)
  have hc3 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3))) (.int u64 3) :=
    EvE.cast (EvE.const _) (cast_u64_u32 3 (by omega))
  have hneed : EvE Gen.prog s0 (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2))
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) (.int u64 (ntri * 3)) :=
    EvE.bin hc2 hc3 (u64_mul_val _ _ (by omega))
  have hset6 := ExS.set (p := Gen.prog) (i := 6) hneed
  let s1 : State := { s0 with locals := s0.locals.upd 6 (.int u64 (ntri * 3)) }
  have hv4 : EvE Gen.prog s1 (.var 4) (.ptr cntb 0) :=
    EvE.var (by simpa [s1, Locals.upd] using l4)
  have hcnt : EvE Gen.prog s1 (.load (.int ⟨64, false⟩) (.var 4)) (.int u64 count0) :=
    EvE.load hv4 (load_u64_cell s1.mem cntb count0 mcnt (by omega))
  have hv6 : EvE Gen.prog s1 (.var 6) (.int u64 (ntri * 3)) := EvE.var (by simp [s1, Locals.upd])
  have hsum : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.var 4))
      (.var 6)) (.int u64 (count0 + ntri * 3)) :=
    EvE.bin hcnt hv6 (u64_add_val _ _ (by omega))
  have hv5 : EvE Gen.prog s1 (.var 5) (.int u64 outcap) :=
    EvE.var (by simpa [s1, Locals.upd] using l5)
  have hgt : EvE Gen.prog s1 (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩)
      (.load (.int ⟨64, false⟩) (.var 4)) (.var 6)) (.var 5))
      (boolVal (decide (count0 + ntri * 3 > outcap))) :=
    EvE.bin hsum hv5 (u64_gt_val _ _)
  have hret : EvE Gen.prog s1 (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
      (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 0) :=
    EvE.cond (EvE.const _) (bc := false) (by simp [truthy]) (EvE.const _)
  have hcapck : ExS Gen.prog s1 (.ite (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩)
      (.load (.int ⟨64, false⟩) (.var 4)) (.var 6)) (.var 5))
      (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
        (.const (.int ⟨8, false⟩ 0))))) .skip) (.ret (some (.int ⟨8, false⟩ 0))) s1 :=
    ExS.ite hgt (bc := true) (by simp [truthy, boolVal]; omega) (by simpa using ExS.ret hret)
  refine ⟨s1, ExS.seq hnull (ExS.seq hset6 (ExS.seq_ret hcapck)), rfl⟩


/-- The double-precision instance `emit_face_core_d` has the same translated body. -/
theorem emit_face_core_d_eq_f : Gen.emit_face_core_d = Gen.emit_face_core_f := rfl

theorem emit_face_core_d_exs (m : Mem) (cb tb ob cntb co to oo count0 ntri outcap : Nat)
    (cblk tblk oblk : Block) (triIdx : Nat → Nat → Nat)
    (tab : EfTab cblk tblk co to triIdx ntri)
    (hne1 : ob ≠ cb) (hne2 : ob ≠ tb) (hne3 : ob ≠ cntb) (hne4 : cb ≠ cntb) (hne5 : tb ≠ cntb)
    (mcb : m cb = some cblk) (mtb : m tb = some tblk) (mob : m ob = some oblk)
    (mcnt : m cntb = some (encodeLE 8 count0))
    (hn3 : 3 * ntri < 4294967296) (hcap : count0 + 3 * ntri ≤ outcap)
    (hcap64 : outcap < 18446744073709551616)
    (hout : oo + 12 * (count0 + 3 * ntri) ≤ oblk.length) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.emit_face_core_d.params
        [.ptr cb co, .ptr tb to, .int u32 ntri, .ptr ob oo, .ptr cntb 0, .int u64 outcap],
        m, false⟩
      Gen.emit_face_core_d.body (.ret (some (.int ⟨8, false⟩ 1))) s' ∧
      s'.mem ob = some (splice oblk (oo + 12 * count0) (efBytes cblk co triIdx ntri)) ∧
      s'.mem cntb = some (encodeLE 8 (count0 + 3 * ntri)) ∧
      ∀ b, b ≠ ob → b ≠ cntb → s'.mem b = m b := by
  rw [emit_face_core_d_eq_f]
  exact emit_face_core_f_exs m cb tb ob cntb co to oo count0 ntri outcap cblk tblk oblk triIdx tab
    hne1 hne2 hne3 hne4 hne5 mcb mtb mob mcnt hn3 hcap hcap64 hout

end Obj.C.Proofs
