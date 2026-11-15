/-
  Refinement proof for the translated `tobj_tess_fan` (tobj_tess.c): the fan
  triangulation `(0, k, k+1)` for `k = 1 .. n-2` written through
  `tobj_tess_emit`.  `tess_fan_refines_spec` states that the C output equals
  the pure specification `Obj.fanTris` (`Obj/Tess.lean`), byte for byte.
-/
import Obj.C.Proofs.ObjTessEmit
import Obj.Tess
namespace Obj.C.Proofs
open Obj.C Obj

/-- Block contents after `cnt` fan triangles are emitted starting at slot `k0`. -/
def fanBlock (oblk : Block) (k0 : Nat) : Nat → Block
  | 0 => oblk
  | t + 1 =>
    splice (splice (splice (fanBlock oblk k0 t) (12 * (k0 + t)) (encodeLE 4 0))
      (12 * (k0 + t) + 4) (encodeLE 4 (t + 1))) (12 * (k0 + t) + 8) (encodeLE 4 (t + 2))

theorem fanBlock_length (oblk : Block) (k0 cnt : Nat) (h : 12 * (k0 + cnt) ≤ oblk.length) :
    (fanBlock oblk k0 cnt).length = oblk.length := by
  induction cnt with
  | zero => rfl
  | succ t ih =>
    have l0 : (fanBlock oblk k0 t).length = oblk.length := ih (by omega)
    have h4 : ∀ o, o + 4 ≤ oblk.length → ∀ (blk : Block) (v : Nat), blk.length = oblk.length →
        (splice blk o (encodeLE 4 v)).length = oblk.length := by
      intro o ho blk v hl
      rw [splice_length _ _ _ (by simp [encodeLE_length]; omega), hl]
    simp only [fanBlock]
    exact h4 _ (by omega) _ _ (h4 _ (by omega) _ _ (h4 _ (by omega) _ _ l0))


theorem u32_lt_val (a n : Nat) (ha : a < 4294967296) (hn : n < 4294967296) :
    evalBin .lt (some ⟨32, false⟩) (.int u32 a) (.int u32 n) = .ok (boolVal (decide (a < n))) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.modulus, Res.bind]

theorem u32_add_val (a c : Nat) (h : a + c < 4294967296) :
    evalBin .add (some ⟨32, false⟩) (.int u32 a) (.int u32 c) = .ok (.int u32 (a + c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.modulus, Res.bind]
  omega

theorem cast_u32_i32_one : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 1) = .ok (.int u32 1) := by
  simp [evalCast, u32, IntTy.toInt, IntTy.wrap, IntTy.modulus]

theorem cast_u32_i32_zero : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 0) = .ok (.int u32 0) := by
  simp [evalCast, u32, IntTy.toInt, IntTy.wrap, IntTy.modulus]

theorem cast_u32_u32 (a : Nat) (h : a < 4294967296) :
    evalCast ⟨32, false⟩ (.int u32 a) = .ok (.int u32 a) := by
  simp [evalCast, u32, IntTy.modulus]; omega


def fanBody : Stmt :=
  (.ite (.bin .lt (some ⟨32, false⟩) (.bin .add (some ⟨32, false⟩) (.var 3)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.var 0))
    (.call none 27 [(.var 1), (.var 2), (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))), (.var 3),
      (.bin .add (some ⟨32, false⟩) (.var 3) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))))])
    .brk)

def fanStep : Stmt :=
  (.set 3 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 3))
    (.const (.int ⟨32, false⟩ 1)))))

theorem fan_loop_ast : Gen.tobj_tess_fan_loop0 = .loop fanBody fanStep := rfl

/-- Loop invariant of `tobj_tess_fan`: `j` iterations remain out of `cnt`. -/
def FanInv (m : Mem) (ob kb : Nat) (oblk : Block) (k0 n cnt : Nat) (j : Nat) (s : State) : Prop :=
  j ≤ cnt ∧ s.locals 0 = some (.int u32 n) ∧ s.locals 1 = some (.ptr ob 0) ∧
  s.locals 2 = some (.ptr kb 0) ∧ s.locals 3 = some (.int u32 (cnt - j + 1)) ∧
  s.ro = false ∧ s.mem ob = some (fanBlock oblk k0 (cnt - j)) ∧
  s.mem kb = some (encodeLE 4 (k0 + (cnt - j))) ∧ ∀ b, b ≠ ob → b ≠ kb → s.mem b = m b

theorem tess_fan_exs (m : Mem) (ob kb : Nat) (oblk : Block) (k0 n : Nat)
    (hne : ob ≠ kb) (hob : m ob = some oblk) (hkb : m kb = some (encodeLE 4 k0))
    (hn3 : 3 ≤ n) (hn : n < 4294967296)
    (hk : 3 * (k0 + (n - 2)) < 4294967296) (hlen : 12 * (k0 + (n - 2)) ≤ oblk.length) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.tobj_tess_fan.params [.int u32 n, .ptr ob 0, .ptr kb 0], m, false⟩
      Gen.tobj_tess_fan.body .normal s' ∧
      s'.mem ob = some (fanBlock oblk k0 (n - 2)) ∧
      s'.mem kb = some (encodeLE 4 (k0 + (n - 2))) ∧
      ∀ b, b ≠ ob → b ≠ kb → s'.mem b = m b := by
  let cnt := n - 2
  have hcnt : cnt + 2 = n := by omega
  let s0 : State := ⟨frameLocals Gen.tobj_tess_fan.params [.int u32 n, .ptr ob 0, .ptr kb 0], m, false⟩
  have l0 : s0.locals 0 = some (.int u32 n) := by
    simp [s0, frameLocals, Gen.tobj_tess_fan, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr ob 0) := by
    simp [s0, frameLocals, Gen.tobj_tess_fan, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s0.locals 2 = some (.ptr kb 0) := by
    simp [s0, frameLocals, Gen.tobj_tess_fan, List.idxOf?, List.findIdx?, List.findIdx?.go]
  -- k = 1
  have hset : ExS Gen.prog s0 (.set 3 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))))
      .normal { s0 with locals := s0.locals.upd 3 (.int u32 1) } :=
    ExS.set (EvE.cast (EvE.const _) cast_u32_i32_one)
  let s1 : State := { s0 with locals := s0.locals.upd 3 (.int u32 1) }
  have hinv0 : FanInv m ob kb oblk k0 n cnt cnt s1 := by
    refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simpa [s1, Locals.upd] using l0
    · simpa [s1, Locals.upd] using l1
    · simpa [s1, Locals.upd] using l2
    · simp [s1, Locals.upd]
    · simpa [s1, s0, fanBlock] using hob
    · simpa [s1, s0] using hkb
    · intro b _ _; rfl
  have hstep : ∀ j s, FanInv m ob kb oblk k0 n cnt (j + 1) s → ∃ s1 s2,
      ExS Gen.prog s fanBody .normal s1 ∧
      ExS Gen.prog s1 fanStep .normal s2 ∧
      FanInv m ob kb oblk k0 n cnt j s2 := by
    intro j s hs
    obtain ⟨hj, h0, h1, h2, h3, hro, hob', hkb', hrest⟩ := hs
    have hd : cnt - (j + 1) + 1 = cnt - j := by omega
    let d := cnt - (j + 1)
    have hv3 : EvE Gen.prog s (.var 3) (.int u32 (d + 1)) := by
      apply EvE.var; rw [h3]
    have hc1 : EvE Gen.prog s (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))) (.int u32 1) :=
      EvE.cast (EvE.const _) cast_u32_i32_one
    have hc0 : EvE Gen.prog s (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))) (.int u32 0) :=
      EvE.cast (EvE.const _) cast_u32_i32_zero
    have hadd : EvE Gen.prog s (.bin .add (some ⟨32, false⟩) (.var 3)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.int u32 (d + 1 + 1)) :=
      EvE.bin hv3 hc1 (u32_add_val _ _ (by omega))
    have hv0 : EvE Gen.prog s (.var 0) (.int u32 n) := EvE.var h0
    have hlt : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.bin .add (some ⟨32, false⟩) (.var 3)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.var 0))
        (boolVal (decide (d + 1 + 1 < n))) :=
      EvE.bin hadd hv0 (u32_lt_val _ _ (by omega) hn)
    have htrue : d + 1 + 1 < n := by omega
    have hargs : EvArgs Gen.prog s [(.var 1), (.var 2),
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))), (.var 3),
        (.bin .add (some ⟨32, false⟩) (.var 3) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))))]
        [.ptr ob 0, .ptr kb 0, .int u32 0, .int u32 (d + 1), .int u32 (d + 1 + 1)] :=
      EvArgs.cons (EvE.var h1) (EvArgs.cons (EvE.var h2) (EvArgs.cons hc0
        (EvArgs.cons hv3 (EvArgs.cons hadd EvArgs.nil))))
    have hbl : (fanBlock oblk k0 d).length = oblk.length :=
      fanBlock_length oblk k0 d (by omega)
    have hob2 : s.mem ob = some (fanBlock oblk k0 d) := by
      rw [hob']
    have hkb2 : s.mem kb = some (encodeLE 4 (k0 + d)) := by
      rw [hkb']
    obtain ⟨se, hbody, hmem⟩ := emit_exs s.mem ob kb (fanBlock oblk k0 d) (k0 + d) 0 (d + 1)
      (d + 1 + 1) hne hob2 hkb2 (by omega) (by omega) (by omega) (by omega) (by omega)
    have hstate : (⟨frameLocals Gen.tobj_tess_emit.params
        [.ptr ob 0, .ptr kb 0, .int u32 0, .int u32 (d + 1), .int u32 (d + 1 + 1)], s.mem, s.ro⟩
        : State) = ⟨frameLocals Gen.tobj_tess_emit.params
        [.ptr ob 0, .ptr kb 0, .int u32 0, .int u32 (d + 1), .int u32 (d + 1 + 1)], s.mem, false⟩ := by
      rw [hro]
    have hcall := ExS.call (p := Gen.prog) (s := s) (f := 27) (fn := Gen.tobj_tess_emit)
      hargs (by rfl) (by rfl) (by rw [hstate]; exact hbody) (Or.inl rfl)
    let s1 : State := { s with mem := se.mem }
    have hbodyS : ExS Gen.prog s fanBody .normal s1 := by
      unfold fanBody
      exact ExS.ite hlt (bc := true) (by simp [truthy, boolVal, htrue]) (by simpa using hcall)
    have h3' : s1.locals 3 = some (.int u32 (d + 1)) := by
      show s.locals 3 = _
      rw [h3]
    have hv3' : EvE Gen.prog s1 (.var 3) (.int u32 (d + 1)) := EvE.var h3'
    have hcs : EvE Gen.prog s1 (.cast ⟨32, false⟩ (.var 3)) (.int u32 (d + 1)) :=
      EvE.cast hv3' (cast_u32_u32 _ (by omega))
    have hadd1 : EvE Gen.prog s1 (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 3))
        (.const (.int ⟨32, false⟩ 1))) (.int u32 (d + 1 + 1)) :=
      EvE.bin hcs (EvE.const _) (u32_add_val _ _ (by omega))
    have hstepS : ExS Gen.prog s1 fanStep .normal
        { s1 with locals := s1.locals.upd 3 (.int u32 (d + 1 + 1)) } := by
      unfold fanStep
      exact ExS.set (EvE.cast hadd1 (cast_u32_u32 _ (by omega)))
    refine ⟨s1, _, hbodyS, hstepS, ?_⟩
    have e : cnt - j = d + 1 := by omega
    refine ⟨by omega, ?_, ?_, ?_, ?_, hro, ?_, ?_, ?_⟩
    · simpa [s1, Locals.upd] using h0
    · simpa [s1, Locals.upd] using h1
    · simpa [s1, Locals.upd] using h2
    · simp [s1, Locals.upd]; omega
    · show se.mem ob = _
      rw [hmem, Mem.upd_ne _ _ hne, Mem.upd_same, e]; rfl
    · show se.mem kb = _
      rw [hmem, Mem.upd_same, e, ← Nat.add_assoc]
    · intro b hb1 hb2
      show se.mem b = _
      rw [hmem, Mem.upd_ne _ _ hb2, Mem.upd_ne _ _ hb1]
      exact hrest b hb1 hb2
  have hexit : ∀ s, FanInv m ob kb oblk k0 n cnt 0 s → ∃ s1,
      ExS Gen.prog s fanBody .brk s1 ∧ FanInv m ob kb oblk k0 n cnt 0 s1 := by
    intro s hs
    obtain ⟨_, h0, h1, h2, h3, hro, hob', hkb', hrest⟩ := hs
    have hv3 : EvE Gen.prog s (.var 3) (.int u32 (cnt - 0 + 1)) := EvE.var h3
    have hc1 : EvE Gen.prog s (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))) (.int u32 1) :=
      EvE.cast (EvE.const _) cast_u32_i32_one
    have hadd : EvE Gen.prog s (.bin .add (some ⟨32, false⟩) (.var 3)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.int u32 (cnt - 0 + 1 + 1)) :=
      EvE.bin hv3 hc1 (u32_add_val _ _ (by omega))
    have hv0 : EvE Gen.prog s (.var 0) (.int u32 n) := EvE.var h0
    have hlt : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.bin .add (some ⟨32, false⟩) (.var 3)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.var 0))
        (boolVal (decide (cnt - 0 + 1 + 1 < n))) :=
      EvE.bin hadd hv0 (u32_lt_val _ _ (by omega) hn)
    have hfalse : ¬ (cnt - 0 + 1 + 1 < n) := by omega
    refine ⟨s, ?_, ⟨by omega, h0, h1, h2, h3, hro, hob', hkb', hrest⟩⟩
    apply ExS.ite hlt (bc := false) (by simp [truthy, boolVal]; omega)
    simpa using (ExS.brk (p := Gen.prog) (s := s))
  obtain ⟨sf, hloop, hq⟩ := ExS.loop_decreasing_post (p := Gen.prog)
    (P := FanInv m ob kb oblk k0 n cnt) (Q := FanInv m ob kb oblk k0 n cnt 0)
    (n := cnt) (s := s1) hinv0 hstep hexit
  obtain ⟨_, _, _, _, _, _, hqo, hqk, hqr⟩ := hq
  refine ⟨sf, ?_, ?_, ?_, hqr⟩
  · have hbody : Gen.tobj_tess_fan.body = .seq (.set 3 (.cast ⟨32, false⟩
        (.const (.int ⟨32, true⟩ 1)))) (.loop fanBody fanStep) := rfl
    rw [hbody]
    exact ExS.seq hset hloop
  · simpa using hqo
  · simpa using hqk


/-- Little-endian bytes of one triangle. -/
def triBytes (t : Tri) : Block :=
  encodeLE 4 t.1 ++ encodeLE 4 t.2.1 ++ encodeLE 4 t.2.2

theorem triBytes_length (t : Tri) : (triBytes t).length = 12 := by
  simp [triBytes, encodeLE_length]

theorem fanTris_succ (t : Nat) :
    fanTris (t + 3) = fanTris (t + 2) ++ [(0, t + 1, t + 2)] := by
  simp [fanTris, List.range_succ]

theorem splice_mid (pre mid post xs : Block) (h : xs.length ≤ post.length) :
    splice (pre ++ mid ++ post) (pre.length + mid.length) xs =
      pre ++ mid ++ xs ++ post.drop xs.length := by
  unfold splice
  have h1 : (pre ++ mid ++ post).take (pre.length + mid.length) = pre ++ mid :=
    List.take_left' (by simp)
  have h2 : (pre ++ mid ++ post).drop (pre.length + mid.length + xs.length) =
      post.drop xs.length := by
    rw [← List.drop_drop, List.drop_left' (by simp)]
  rw [h1, h2]

/-- Closed form of the fan output: the emitted block equals the original with
    the spec's `fanTris (cnt + 2)` triples written from slot `k0`. -/
theorem fanBlock_eq (oblk : Block) (k0 cnt : Nat) (h : 12 * (k0 + cnt) ≤ oblk.length) :
    fanBlock oblk k0 cnt = oblk.take (12 * k0) ++
      (fanTris (cnt + 2)).flatMap triBytes ++ oblk.drop (12 * (k0 + cnt)) := by
  induction cnt with
  | zero => simp [fanBlock, fanTris]
  | succ t ih =>
    have ih' := ih (by omega)
    have hbl : (fanBlock oblk k0 t).length = oblk.length := fanBlock_length oblk k0 t (by omega)
    have l4 : ∀ v, (encodeLE 4 v).length = 4 := fun v => encodeLE_length 4 v
    have hsp : fanBlock oblk k0 (t + 1) =
        splice (fanBlock oblk k0 t) (12 * (k0 + t))
          (encodeLE 4 0 ++ encodeLE 4 (t + 1) ++ encodeLE 4 (t + 2)) := by
      simp only [fanBlock]
      have s1 := splice_append (fanBlock oblk k0 t) (12 * (k0 + t)) (encodeLE 4 0)
        (encodeLE 4 (t + 1)) (by simp only [List.length_append, l4]; rw [hbl]; omega)
      rw [l4] at s1
      have s2 := splice_append (fanBlock oblk k0 t) (12 * (k0 + t))
        (encodeLE 4 0 ++ encodeLE 4 (t + 1)) (encodeLE 4 (t + 2))
        (by simp only [List.length_append, l4]; rw [hbl]; omega)
      simp only [List.length_append, l4] at s2
      rw [s1]
      have e : 12 * (k0 + t) + (4 + 4) = 12 * (k0 + t) + 8 := by omega
      rw [e] at s2
      exact s2
    have hflat : ((fanTris (t + 2)).flatMap triBytes).length = 12 * t := by
      have : ∀ ts : List Tri, (ts.flatMap triBytes).length = 12 * ts.length := by
        intro ts
        induction ts with
        | nil => rfl
        | cons x xs ihx => simp [List.flatMap_cons, triBytes_length, ihx]; omega
      rw [this, fanTris_length]; omega
    have hpre : (oblk.take (12 * k0)).length = 12 * k0 := by simp; omega
    have htri : encodeLE 4 0 ++ encodeLE 4 (t + 1) ++ encodeLE 4 (t + 2) =
        triBytes (0, t + 1, t + 2) := rfl
    rw [hsp, ih', htri]
    have hoff : 12 * (k0 + t) = (oblk.take (12 * k0)).length +
        ((fanTris (t + 2)).flatMap triBytes).length := by rw [hpre, hflat]; omega
    rw [hoff, splice_mid _ _ _ _ (by rw [triBytes_length, List.length_drop]; omega),
      fanTris_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.drop_drop,
      triBytes_length, List.append_assoc]
    have : (oblk.take (12 * k0)).length + ((fanTris (t + 2)).flatMap triBytes).length = 12 * (k0 + t) := hoff.symm
    rw [this]
    have e2 : 12 * (k0 + t) + 12 = 12 * (k0 + (t + 1)) := by omega
    rw [e2]


/-- **`tobj_tess_fan` refines the specification `Obj.fanTris`.**  For `n ≥ 3`
    corners, the translated C function leaves the output array equal to the
    original with `triBytes` of each `fanTris n` triangle written from slot
    `k0`, advances the counter cell by `n - 2`, never hits undefined behaviour,
    terminates, and leaves every other memory block untouched. -/
theorem tess_fan_refines_spec (m : Mem) (ob kb : Nat) (oblk : Block) (k0 n : Nat)
    (hne : ob ≠ kb) (hob : m ob = some oblk) (hkb : m kb = some (encodeLE 4 k0))
    (hn3 : 3 ≤ n) (hn : n < 4294967296)
    (hk : 3 * (k0 + (n - 2)) < 4294967296) (hlen : 12 * (k0 + (n - 2)) ≤ oblk.length) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.tobj_tess_fan.params [.int u32 n, .ptr ob 0, .ptr kb 0], m, false⟩
      Gen.tobj_tess_fan.body .normal s' ∧
      s'.mem ob = some (oblk.take (12 * k0) ++ (fanTris n).flatMap triBytes ++
        oblk.drop (12 * (k0 + (n - 2)))) ∧
      s'.mem kb = some (encodeLE 4 (k0 + (n - 2))) ∧
      ∀ b, b ≠ ob → b ≠ kb → s'.mem b = m b := by
  obtain ⟨s', hs, h1, h2, h3⟩ := tess_fan_exs m ob kb oblk k0 n hne hob hkb hn3 hn hk hlen
  refine ⟨s', hs, ?_, h2, h3⟩
  rw [h1, fanBlock_eq oblk k0 (n - 2) hlen]
  have : n - 2 + 2 = n := by omega
  rw [this]

end Obj.C.Proofs
