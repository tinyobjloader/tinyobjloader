/-
  Composition of the refined checked int64 helpers into the translated `orient2i_core`
  (`lib/tess/src/tess.c`, the body of `tess_orient2i`): when the model `orient2iChk` succeeds with sign
  `s`, the translated function returns `1` and stores `s` through the sign pointer
  (`orient2i_core_ok`).
-/
import Tess.C.MulC

namespace Tess.C
open Obj.C

theorem evLoadBlk (st : State) (blk : Nat) (r : Int) (hr : InI64 r)
    (hm : st.mem blk = some (encodeLE 8 (W r))) :
    EvE OrientGen.prog st (.load (.int ⟨64, true⟩) (.const (.ptr blk 0))) (.int IntTy.i64 (W r)) := by
  have hlt : W r < 2 ^ 64 := by
    unfold W IntTy.wrap IntTy.modulus IntTy.i64
    simp only []
    have := Int.emod_lt_of_pos r (show (0:Int) < 2 ^ 64 by norm_num)
    have h0 := Int.emod_nonneg r (show (2:Int) ^ 64 ≠ 0 by norm_num)
    omega
  exact EvE.load (EvE.const _) (load_i64_enc st.mem blk (W r) hlt hm)

theorem subChk_some (a b x : Int) (h : subChk a b = some x) :
    ¬ ((0 < b ∧ a < i64min + b) ∨ (b < 0 ∧ i64max + b < a)) ∧ x = a - b := by
  unfold subChk at h
  by_cases c : (0 < b ∧ a < i64min + b) ∨ (b < 0 ∧ i64max + b < a)
  · rw [if_pos c] at h; cases h
  · rw [if_neg c] at h; exact ⟨c, (Option.some.inj h).symm⟩

theorem lv_keep (L : Locals) (d i : Nat) (v w : Val) (hi : i ≠ d) (hl : L i = some w) :
    (L.upd d v) i = some w := by
  simp [Locals.upd, hi, hl]

theorem tb'' : ∀ c : Bool, truthy (boolVal c) = .ok c := by intro c; cases c <;> rfl

/-- The failure check after a successful call: `if (!ok) return 0;` falls through. -/
theorem okStep (st : State) (hl : st.locals 14 = some (.int ⟨32, true⟩ 1)) :
    ExS OrientGen.prog st (.ite (.un .lnot ⟨32, true⟩ (.var 14)) (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip)
      .normal st :=
  ExS.ite (EvE.un (EvE.var hl) (by simp [evalUn, truthy])) (tb'' false) ExS.skip

theorem store_i32 (m : Mem) (rb : Nat) (blk : Block) (n : Nat) (hm : m rb = some blk)
    (hblk : blk.length = 4) :
    store m (.int ⟨32, true⟩) (.ptr rb 0) (.int ⟨32, true⟩ n) = .ok (m.upd rb (encodeLE 4 n)) := by
  have hbytes : (encodeLE (IntTy.bytes ⟨32, true⟩) n).length = 4 := by rw [encodeLE_length]; rfl
  simp only [store, writeBytes, hm, if_true]
  rw [if_pos (by rw [hbytes, hblk])]
  have hd : List.drop 4 blk = [] := List.drop_eq_nil_of_le (by omega)
  simp [hbytes, hd]
  rfl

theorem orient2i_core_ok (ax ay bx bY cx cy : Int) (h1 : InI64 ax) (h2 : InI64 ay) (h3 : InI64 bx)
    (h4 : InI64 bY) (h5 : InI64 cx) (h6 : InI64 cy) (sp : Nat) (m : Mem) (s0 : State)
    (h0 : s0 = ⟨frameLocals OrientGen.orient2i_core.params
      [.int IntTy.i64 (W ax), .int IntTy.i64 (W ay), .int IntTy.i64 (W bx), .int IntTy.i64 (W bY),
       .int IntTy.i64 (W cx), .int IntTy.i64 (W cy), .ptr sp 0], m, false⟩)
    (B1 B2 B3 B4 B5 B6 B7 : Block) (m1 : m 1007 = some B1) (m2 : m 1008 = some B2)
    (m3 : m 1009 = some B3) (m4 : m 1010 = some B4) (m5 : m 1011 = some B5) (m6 : m 1012 = some B6)
    (m7 : m 1013 = some B7) (l1 : B1.length = 8) (l2 : B2.length = 8) (l3 : B3.length = 8)
    (l4 : B4.length = 8) (l5 : B5.length = 8) (l6 : B6.length = 8) (l7 : B7.length = 8)
    (S : Block) (mS : m sp = some S) (lS : S.length = 4)
    (n1 : sp ≠ 1007) (n2 : sp ≠ 1008) (n3 : sp ≠ 1009) (n4 : sp ≠ 1010) (n5 : sp ≠ 1011)
    (n6 : sp ≠ 1012) (n7 : sp ≠ 1013) (sg : Int)
    (h : orient2iChk ax ay bx bY cx cy = some sg) :
    ∃ sf, ExS OrientGen.prog s0 OrientGen.orient2i_core.body (.ret (some (.int ⟨32, true⟩ 1))) sf := by
  unfold orient2iChk at h
  rcases hx : subChk bx ax with _ | x
  · simp [hx] at h
  rcases hy : subChk bY ay with _ | y
  · simp [hx, hy] at h
  rcases hu : subChk cx ax with _ | u
  · simp [hx, hy, hu] at h
  rcases hv : subChk cy ay with _ | v
  · simp [hx, hy, hu, hv] at h
  rcases hp : mulChk x v with _ | p
  · simp [hx, hy, hu, hv, hp] at h
  rcases hq : mulChk y u with _ | q
  · simp [hx, hy, hu, hv, hp, hq] at h
  rcases hd : subChk p q with _ | d
  · simp [hx, hy, hu, hv, hp, hq, hd] at h
  simp [hx, hy, hu, hv, hp, hq, hd] at h
  -- exactness and ranges
  obtain ⟨gx, hxe⟩ := subChk_some _ _ _ hx
  obtain ⟨gy, hye⟩ := subChk_some _ _ _ hy
  obtain ⟨gu, hue⟩ := subChk_some _ _ _ hu
  obtain ⟨gv, hve⟩ := subChk_some _ _ _ hv
  obtain ⟨gd, hde⟩ := subChk_some _ _ _ hd
  have rx : InI64 x := by
    rcases subChk_spec bx ax h3 h1 with ⟨r, hr, e, hi⟩ | ⟨hr, -⟩
    · rw [hx] at hr; cases hr; exact hi
    · rw [hx] at hr; cases hr
  have ry : InI64 y := by
    rcases subChk_spec bY ay h4 h2 with ⟨r, hr, e, hi⟩ | ⟨hr, -⟩
    · rw [hy] at hr; cases hr; exact hi
    · rw [hy] at hr; cases hr
  have ru : InI64 u := by
    rcases subChk_spec cx ax h5 h1 with ⟨r, hr, e, hi⟩ | ⟨hr, -⟩
    · rw [hu] at hr; cases hr; exact hi
    · rw [hu] at hr; cases hr
  have rv : InI64 v := by
    rcases subChk_spec cy ay h6 h2 with ⟨r, hr, e, hi⟩ | ⟨hr, -⟩
    · rw [hv] at hr; cases hr; exact hi
    · rw [hv] at hr; cases hr
  have rp : InI64 p := by
    rcases mulChk_spec x v rx rv with ⟨r, hr, e, hi⟩ | ⟨hr, -⟩
    · rw [hp] at hr; cases hr; exact hi
    · rw [hp] at hr; cases hr
  have rq : InI64 q := by
    rcases mulChk_spec y u ry ru with ⟨r, hr, e, hi⟩ | ⟨hr, -⟩
    · rw [hq] at hr; cases hr; exact hi
    · rw [hq] at hr; cases hr
  have l0 : s0.locals 0 = some (.int IntTy.i64 (W ax)) := by rw [h0]; rfl
  have l1' : s0.locals 1 = some (.int IntTy.i64 (W ay)) := by rw [h0]; rfl
  have l2' : s0.locals 2 = some (.int IntTy.i64 (W bx)) := by rw [h0]; rfl
  have l3' : s0.locals 3 = some (.int IntTy.i64 (W bY)) := by rw [h0]; rfl
  have l4' : s0.locals 4 = some (.int IntTy.i64 (W cx)) := by rw [h0]; rfl
  have l5' : s0.locals 5 = some (.int IntTy.i64 (W cy)) := by rw [h0]; rfl
  have l6' : s0.locals 6 = some (.ptr sp 0) := by rw [h0]; rfl
  have ro0 : s0.ro = false := by rw [h0]
  have mem0 : s0.mem = m := by rw [h0]
  -- step 1: ok = sub(bx, ax, &x)
  obtain ⟨st1, e1, hl1, hm1, hf1, hr1⟩ := (callSub s0 14 (.var 2) (.var 0) 1007 bx ax h3 h1
    (EvE.var l2') (EvE.var l0) B1 (by rw [mem0]; exact m1) l1 ro0).2 gx
  have hk1 : ∀ i, i ≠ 14 → st1.locals i = s0.locals i := fun i hi => by
    rw [hl1]; simp [Locals.upd, hi]
  have m1x : st1.mem 1007 = some (encodeLE 8 (W x)) := by rw [hxe]; exact hm1
  -- step 2: ok = sub(by, ay, &y)
  obtain ⟨st2, e2, hl2, hm2, hf2, hr2⟩ := (callSub st1 14 (.var 3) (.var 1) 1008 bY ay h4 h2
    (EvE.var (by rw [hk1 3 (by norm_num)]; exact l3')) (EvE.var (by rw [hk1 1 (by norm_num)]; exact l1'))
    B2 (by rw [hf1 1008 (by norm_num), mem0]; exact m2) l2 (by rw [hr1]; exact ro0)).2 gy
  have hk2 : ∀ i, i ≠ 14 → st2.locals i = s0.locals i := fun i hi => by
    rw [hl2]; simp [Locals.upd, hi]; exact hk1 i hi
  have m2y : st2.mem 1008 = some (encodeLE 8 (W y)) := by rw [hye]; exact hm2
  have m2x : st2.mem 1007 = some (encodeLE 8 (W x)) := by rw [hf2 1007 (by norm_num)]; exact m1x
  -- step 3: ok = sub(cx, ax, &u)
  obtain ⟨st3, e3, hl3, hm3, hf3, hr3⟩ := (callSub st2 14 (.var 4) (.var 0) 1009 cx ax h5 h1
    (EvE.var (by rw [hk2 4 (by norm_num)]; exact l4')) (EvE.var (by rw [hk2 0 (by norm_num)]; exact l0))
    B3 (by rw [hf2 1009 (by norm_num), hf1 1009 (by norm_num), mem0]; exact m3) l3 (by rw [hr2, hr1]; exact ro0)).2 gu
  have hk3 : ∀ i, i ≠ 14 → st3.locals i = s0.locals i := fun i hi => by
    rw [hl3]; simp [Locals.upd, hi]; exact hk2 i hi
  have m3u : st3.mem 1009 = some (encodeLE 8 (W u)) := by rw [hue]; exact hm3
  have m3y : st3.mem 1008 = some (encodeLE 8 (W y)) := by rw [hf3 1008 (by norm_num)]; exact m2y
  have m3x : st3.mem 1007 = some (encodeLE 8 (W x)) := by rw [hf3 1007 (by norm_num)]; exact m2x
  -- step 4: ok = sub(cy, ay, &v)
  obtain ⟨st4, e4, hl4, hm4, hf4, hr4⟩ := (callSub st3 14 (.var 5) (.var 1) 1010 cy ay h6 h2
    (EvE.var (by rw [hk3 5 (by norm_num)]; exact l5')) (EvE.var (by rw [hk3 1 (by norm_num)]; exact l1'))
    B4 (by rw [hf3 1010 (by norm_num), hf2 1010 (by norm_num), hf1 1010 (by norm_num), mem0]; exact m4) l4
    (by rw [hr3, hr2, hr1]; exact ro0)).2 gv
  have hk4 : ∀ i, i ≠ 14 → st4.locals i = s0.locals i := fun i hi => by
    rw [hl4]; simp [Locals.upd, hi]; exact hk3 i hi
  have m4v : st4.mem 1010 = some (encodeLE 8 (W v)) := by rw [hve]; exact hm4
  have m4u : st4.mem 1009 = some (encodeLE 8 (W u)) := by rw [hf4 1009 (by norm_num)]; exact m3u
  have m4y : st4.mem 1008 = some (encodeLE 8 (W y)) := by rw [hf4 1008 (by norm_num)]; exact m3y
  have m4x : st4.mem 1007 = some (encodeLE 8 (W x)) := by rw [hf4 1007 (by norm_num)]; exact m3x
  -- step 5: ok = mul(x, v, &p)
  obtain ⟨st5, e5, hl5, hm5, hf5, hr5⟩ := (callMul st4 14 _ _ 1011 x v rx rv
    (evLoadBlk st4 1007 x rx m4x) (evLoadBlk st4 1010 v rv m4v)
    B5 (by rw [hf4 1011 (by norm_num), hf3 1011 (by norm_num), hf2 1011 (by norm_num),
      hf1 1011 (by norm_num), mem0]; exact m5) l5 (by rw [hr4, hr3, hr2, hr1]; exact ro0)).2 p hp
  have hk5 : ∀ i, i ≠ 14 → st5.locals i = s0.locals i := fun i hi => by
    rw [hl5]; simp [Locals.upd, hi]; exact hk4 i hi
  have m5p : st5.mem 1011 = some (encodeLE 8 (W p)) := hm5
  have m5y : st5.mem 1008 = some (encodeLE 8 (W y)) := by rw [hf5 1008 (by norm_num)]; exact m4y
  have m5u : st5.mem 1009 = some (encodeLE 8 (W u)) := by rw [hf5 1009 (by norm_num)]; exact m4u
  -- step 6: ok = mul(y, u, &q)
  obtain ⟨st6, e6, hl6, hm6, hf6, hr6⟩ := (callMul st5 14 _ _ 1012 y u ry ru
    (evLoadBlk st5 1008 y ry m5y) (evLoadBlk st5 1009 u ru m5u)
    B6 (by rw [hf5 1012 (by norm_num), hf4 1012 (by norm_num), hf3 1012 (by norm_num),
      hf2 1012 (by norm_num), hf1 1012 (by norm_num), mem0]; exact m6) l6
    (by rw [hr5, hr4, hr3, hr2, hr1]; exact ro0)).2 q hq
  have hk6 : ∀ i, i ≠ 14 → st6.locals i = s0.locals i := fun i hi => by
    rw [hl6]; simp [Locals.upd, hi]; exact hk5 i hi
  have m6q : st6.mem 1012 = some (encodeLE 8 (W q)) := hm6
  have m6p : st6.mem 1011 = some (encodeLE 8 (W p)) := by rw [hf6 1011 (by norm_num)]; exact m5p
  -- step 7: ok = sub(p, q, &d)
  obtain ⟨st7, e7, hl7, hm7, hf7, hr7⟩ := (callSub st6 14 _ _ 1013 p q rp rq
    (evLoadBlk st6 1011 p rp m6p) (evLoadBlk st6 1012 q rq m6q)
    B7 (by rw [hf6 1013 (by norm_num), hf5 1013 (by norm_num), hf4 1013 (by norm_num),
      hf3 1013 (by norm_num), hf2 1013 (by norm_num), hf1 1013 (by norm_num), mem0]; exact m7) l7
    (by rw [hr6, hr5, hr4, hr3, hr2, hr1]; exact ro0)).2 gd
  have hk7' : ∀ i, i ≠ 14 → st7.locals i = s0.locals i := fun i hi => by
    rw [hl7]; simp [Locals.upd, hi]; exact hk6 i hi
  have rd : InI64 d := by
    rcases subChk_spec p q rp rq with ⟨r, hr, e, hi⟩ | ⟨hr, -⟩
    · rw [hd] at hr; cases hr; exact hi
    · rw [hd] at hr; cases hr
  have m7d : st7.mem 1013 = some (encodeLE 8 (W d)) := by rw [hde]; exact hm7
  have ok1 : st1.locals 14 = some (.int ⟨32, true⟩ 1) := by rw [hl1]; simp [Locals.upd]
  have ok2 : st2.locals 14 = some (.int ⟨32, true⟩ 1) := by rw [hl2]; simp [Locals.upd]
  have ok3 : st3.locals 14 = some (.int ⟨32, true⟩ 1) := by rw [hl3]; simp [Locals.upd]
  have ok4 : st4.locals 14 = some (.int ⟨32, true⟩ 1) := by rw [hl4]; simp [Locals.upd]
  have ok5 : st5.locals 14 = some (.int ⟨32, true⟩ 1) := by rw [hl5]; simp [Locals.upd]
  have ok6 : st6.locals 14 = some (.int ⟨32, true⟩ 1) := by rw [hl6]; simp [Locals.upd]
  have ok7 : st7.locals 14 = some (.int ⟨32, true⟩ 1) := by rw [hl7]; simp [Locals.upd]
  have hld := evLoadBlk st7 1013 d rd m7d
  have g1 := EvE.bin (p := OrientGen.prog) (op := .gt) (t := some ⟨64, true⟩) hld (evC0 st7)
    (evGtS64 d 0 rd InI64_0)
  have g2 := EvE.bin (p := OrientGen.prog) (op := .lt) (t := some ⟨64, true⟩) hld (evC0 st7)
    (evLtS64 d 0 rd InI64_0)
  have hsub : ∀ a b : Bool, ∃ n, evalBin .sub (some ⟨32, true⟩) (boolVal a) (boolVal b) =
      .ok (.int ⟨32, true⟩ n) := by
    intro a b; cases a <;> cases b <;> exact ⟨_, rfl⟩
  obtain ⟨n, hn⟩ := hsub (decide (d > 0)) (decide (d < 0))
  have hval := EvE.bin g1 g2 hn
  have hsp : st7.locals 6 = some (.ptr sp 0) := by rw [hk7' 6 (by norm_num)]; exact l6'
  have hSmem : st7.mem sp = some S := by
    rw [hf7 sp n7, hf6 sp n6, hf5 sp n5, hf4 sp n4, hf3 sp n3, hf2 sp n2, hf1 sp n1, mem0]; exact mS
  have hst := ExS.store (ty := .int ⟨32, true⟩) (EvE.var hsp) hval
    (by rw [hr7, hr6, hr5, hr4, hr3, hr2, hr1]; exact ro0) (store_i32 st7.mem sp S n hSmem lS)
  refine ⟨{ st7 with mem := st7.mem.upd sp (encodeLE 4 n) }, ?_⟩
  unfold OrientGen.orient2i_core
  refine ExS.seq e1 ?_
  refine ExS.seq (okStep st1 ok1) ?_
  refine ExS.seq e2 ?_
  refine ExS.seq (okStep st2 ok2) ?_
  refine ExS.seq e3 ?_
  refine ExS.seq (okStep st3 ok3) ?_
  refine ExS.seq e4 ?_
  refine ExS.seq (okStep st4 ok4) ?_
  refine ExS.seq e5 ?_
  refine ExS.seq (okStep st5 ok5) ?_
  refine ExS.seq e6 ?_
  refine ExS.seq (okStep st6 ok6) ?_
  refine ExS.seq e7 ?_
  refine ExS.seq (okStep st7 ok7) ?_
  exact ExS.seq hst (ExS.ret (EvE.const _))

end Tess.C
