/-
  MiniC refinement of the translated `sub` (`lib/tess/src/tess.c`), the overflow-checked int64
  subtraction of `tess_orient2i`: evaluation never hits undefined behavior, it returns `0` exactly
  when the guard of `OverflowModel.subChk` fires, and otherwise stores `a - b` through the out-pointer
  and returns `1`.
-/
import Tess.C.OrientGen
import Tess.C.OverflowModel
import Tess.C.Magnitude
import Tess.C.ZiMem

namespace Tess.C
open Obj.C

def W (x : Int) : Nat := IntTy.wrap IntTy.i64 x

theorem inI64_lt (x : Int) (h : InI64 x) : -(2 ^ 63) ≤ x ∧ x < 2 ^ 63 := by
  unfold InI64 i64min i64max at h; omega

theorem Wdec (x : Int) (h : InI64 x) : IntTy.toInt IntTy.i64 (W x) = x :=
  magnitude_signed_decode x (inI64_lt x h)

theorem inRange_i64 (z : Int) (h : InI64 z) : IntTy.inRange IntTy.i64 z = true := by
  unfold InI64 i64min i64max at h
  simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i64]; omega

theorem evAddS64 (x y : Int) (hx : InI64 x) (hy : InI64 y) (hz : InI64 (x + y)) :
    evalBin .add (some IntTy.i64) (.int IntTy.i64 (W x)) (.int IntTy.i64 (W y)) =
      .ok (.int IntTy.i64 (W (x + y))) := by
  change arith IntTy.i64 (IntTy.toInt IntTy.i64 (W x) + IntTy.toInt IntTy.i64 (W y)) = _
  rw [Wdec x hx, Wdec y hy]
  simp [arith, inRange_i64 _ hz, W]

theorem evSub64s (x y : Int) (hx : InI64 x) (hy : InI64 y) (hz : InI64 (x - y)) :
    evalBin .sub (some IntTy.i64) (.int IntTy.i64 (W x)) (.int IntTy.i64 (W y)) =
      .ok (.int IntTy.i64 (W (x - y))) := by
  change arith IntTy.i64 (IntTy.toInt IntTy.i64 (W x) - IntTy.toInt IntTy.i64 (W y)) = _
  rw [Wdec x hx, Wdec y hy]
  simp [arith, inRange_i64 _ hz, W]

theorem evLtS64 (x y : Int) (hx : InI64 x) (hy : InI64 y) :
    evalBin .lt (some IntTy.i64) (.int IntTy.i64 (W x)) (.int IntTy.i64 (W y)) =
      .ok (boolVal (decide (x < y))) := by
  change Res.ok (boolVal (decide (IntTy.toInt IntTy.i64 (W x) < IntTy.toInt IntTy.i64 (W y)))) = _
  rw [Wdec x hx, Wdec y hy]

theorem evGtS64 (x y : Int) (hx : InI64 x) (hy : InI64 y) :
    evalBin .gt (some IntTy.i64) (.int IntTy.i64 (W x)) (.int IntTy.i64 (W y)) =
      .ok (boolVal (decide (x > y))) := by
  change Res.ok (boolVal (decide (IntTy.toInt IntTy.i64 (W x) > IntTy.toInt IntTy.i64 (W y)))) = _
  rw [Wdec x hx, Wdec y hy]

theorem evNegS64 (x : Int) (hx : InI64 x) (hz : InI64 (-x)) :
    evalUn .neg IntTy.i64 (.int IntTy.i64 (W x)) = .ok (.int IntTy.i64 (W (-x))) := by
  change arith IntTy.i64 (-(IntTy.toInt IntTy.i64 (W x))) = _
  rw [Wdec x hx]
  simp [arith, inRange_i64 _ hz, W]

theorem W_max : (IntTy.i64 : IntTy) = IntTy.i64 ∧ W i64max = 9223372036854775807 := by
  refine ⟨rfl, ?_⟩; unfold W i64max; decide

theorem tb' : ∀ c : Bool, truthy (boolVal c) = .ok c := by intro c; cases c <;> rfl

theorem InI64_0 : InI64 0 := by unfold InI64 i64min i64max; omega
theorem InI64_max : InI64 i64max := by unfold InI64 i64min i64max; omega
theorem InI64_nmax : InI64 (-i64max) := by unfold InI64 i64min i64max; omega
theorem InI64_1 : InI64 1 := by unfold InI64 i64min i64max; omega
theorem InI64_min : InI64 i64min := by unfold InI64 i64min i64max; omega

theorem evC0 (s : State) : EvE OrientGen.prog s (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 0)))
    (.int IntTy.i64 (W 0)) := EvE.cast (EvE.const _) rfl
theorem evC1 (s : State) : EvE OrientGen.prog s (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 1)))
    (.int IntTy.i64 (W 1)) := EvE.cast (EvE.const _) rfl
theorem evCmax (s : State) : EvE OrientGen.prog s (.const (.int ⟨64, true⟩ 9223372036854775807))
    (.int IntTy.i64 (W i64max)) := by
  rw [W_max.2]; exact EvE.const _

/-- The first half of the guard: `b > 0 && a < (-MAX - 1) + b`. -/
theorem guard1 (s : State) (a b : Int) (ha : InI64 a) (hb : InI64 b)
    (l0 : s.locals 0 = some (.int IntTy.i64 (W a))) (l1 : s.locals 1 = some (.int IntTy.i64 (W b))) :
    EvE OrientGen.prog s (.land (.bin .gt (some ⟨64, true⟩) (.var 1) (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 0))))
      (.bin .lt (some ⟨64, true⟩) (.var 0) (.bin .add (some ⟨64, true⟩)
        (.bin .sub (some ⟨64, true⟩) (.un .neg ⟨64, true⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
          (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.var 1))))
      (boolVal (decide (0 < b ∧ a < i64min + b))) := by
  have hgt := EvE.bin (EvE.var l1) (evC0 s) (evGtS64 b 0 hb InI64_0)
  by_cases hpos : 0 < b
  · have hmid : EvE OrientGen.prog s (.bin .add (some ⟨64, true⟩)
        (.bin .sub (some ⟨64, true⟩) (.un .neg ⟨64, true⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
          (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.var 1))
        (.int IntTy.i64 (W (-i64max - 1 + b))) := by
      have hneg := EvE.un (evCmax s) (evNegS64 i64max InI64_max InI64_nmax)
      have hs := EvE.bin hneg (evC1 s) (evSub64s (-i64max) 1 InI64_nmax InI64_1
        (by unfold InI64 i64min i64max; omega))
      refine EvE.bin hs (EvE.var l1) (evAddS64 _ b (by unfold InI64 i64min i64max; omega) hb ?_)
      unfold InI64 i64min i64max at *; omega
    have hlt := EvE.bin (EvE.var l0) hmid (evLtS64 a _ ha (by unfold InI64 i64min i64max at *; omega))
    have := EvE.land_true hgt (by rw [show decide (b > 0) = true by simpa using hpos]; rfl) hlt
      (tb' _)
    have e : (decide (0 < b ∧ a < i64min + b)) = decide (a < -i64max - 1 + b) := by
      unfold i64min i64max; simp [hpos]
    rw [e]; exact this
  · have := EvE.land_false (b := (.bin .lt (some ⟨64, true⟩) (.var 0) (.bin .add (some ⟨64, true⟩)
        (.bin .sub (some ⟨64, true⟩) (.un .neg ⟨64, true⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
          (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.var 1)))) hgt
      (by rw [show decide (b > 0) = false by simpa using hpos]; rfl)
    have e : decide (0 < b ∧ a < i64min + b) = false := by simp [hpos]
    rw [e]; exact this

/-- The second half of the guard: `b < 0 && a > MAX + b`. -/
theorem guard2 (s : State) (a b : Int) (ha : InI64 a) (hb : InI64 b)
    (l0 : s.locals 0 = some (.int IntTy.i64 (W a))) (l1 : s.locals 1 = some (.int IntTy.i64 (W b))) :
    EvE OrientGen.prog s (.land (.bin .lt (some ⟨64, true⟩) (.var 1) (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 0))))
      (.bin .gt (some ⟨64, true⟩) (.var 0) (.bin .add (some ⟨64, true⟩)
        (.const (.int ⟨64, true⟩ 9223372036854775807)) (.var 1))))
      (boolVal (decide (b < 0 ∧ i64max + b < a))) := by
  have hlt := EvE.bin (EvE.var l1) (evC0 s) (evLtS64 b 0 hb InI64_0)
  by_cases hneg : b < 0
  · have hmid : EvE OrientGen.prog s (.bin .add (some ⟨64, true⟩)
        (.const (.int ⟨64, true⟩ 9223372036854775807)) (.var 1)) (.int IntTy.i64 (W (i64max + b))) :=
      EvE.bin (evCmax s) (EvE.var l1) (evAddS64 i64max b InI64_max hb
        (by unfold InI64 i64min i64max at *; omega))
    have hgt := EvE.bin (EvE.var l0) hmid (evGtS64 a _ ha (by unfold InI64 i64min i64max at *; omega))
    have := EvE.land_true hlt (by rw [show decide (b < 0) = true by simpa using hneg]; rfl) hgt (tb' _)
    have e : (decide (b < 0 ∧ i64max + b < a)) = decide (a > i64max + b) := by
      simp [hneg]
    rw [e]; exact this
  · have := EvE.land_false (b := (.bin .gt (some ⟨64, true⟩) (.var 0) (.bin .add (some ⟨64, true⟩)
        (.const (.int ⟨64, true⟩ 9223372036854775807)) (.var 1)))) hlt
      (by rw [show decide (b < 0) = false by simpa using hneg]; rfl)
    have e : decide (b < 0 ∧ i64max + b < a) = false := by simp [hneg]
    rw [e]; exact this

theorem sub_refines (a b : Int) (ha : InI64 a) (hb : InI64 b) (rb : Nat) (blk : Block)
    (m : Mem) (ro : Bool) (s0 : State)
    (h0 : s0 = ⟨frameLocals OrientGen.sub.params
      [.int IntTy.i64 (W a), .int IntTy.i64 (W b), .ptr rb 0], m, false⟩)
    (hm : m rb = some blk) (hblk : blk.length = 8) :
    ((0 < b ∧ a < i64min + b) ∨ (b < 0 ∧ i64max + b < a) →
      ∃ sf, ExS OrientGen.prog s0 OrientGen.sub.body (.ret (some (.int ⟨32, true⟩ 0))) sf) ∧
    (¬ ((0 < b ∧ a < i64min + b) ∨ (b < 0 ∧ i64max + b < a)) →
      ∃ sf, ExS OrientGen.prog s0 OrientGen.sub.body (.ret (some (.int ⟨32, true⟩ 1))) sf ∧
        sf.mem rb = some (encodeLE 8 (W (a - b))) ∧ (∀ b', b' ≠ rb → sf.mem b' = m b')) := by
  have l0 : s0.locals 0 = some (.int IntTy.i64 (W a)) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.int IntTy.i64 (W b)) := by rw [h0]; rfl
  have l2 : s0.locals 2 = some (.ptr rb 0) := by rw [h0]; rfl
  have hro : s0.ro = false := by rw [h0]
  have hmem : s0.mem = m := by rw [h0]
  have g1 := guard1 s0 a b ha hb l0 l1
  have g2 := guard2 s0 a b ha hb l0 l1
  unfold OrientGen.sub
  show (_ → ∃ sf, ExS OrientGen.prog s0 (.seq _ _) _ sf) ∧ (_ → ∃ sf, ExS OrientGen.prog s0 (.seq _ _) _ sf ∧ _)
  constructor
  · intro hP
    refine ⟨s0, ?_⟩
    by_cases h1 : 0 < b ∧ a < i64min + b
    · have e1 : decide (0 < b ∧ a < i64min + b) = true := by simpa using h1
      rw [e1] at g1
      exact ExS.seq_ret (ExS.ite (EvE.lor_true g1 (by rfl)) (by rfl) (ExS.ret (EvE.const _)))
    · have h2 : b < 0 ∧ i64max + b < a := by tauto
      have e1 : decide (0 < b ∧ a < i64min + b) = false := by simpa using h1
      have e2 : decide (b < 0 ∧ i64max + b < a) = true := by simpa using h2
      rw [e1] at g1; rw [e2] at g2
      exact ExS.seq_ret (ExS.ite (EvE.lor_false g1 (by rfl) g2 (by rfl)) (by rfl)
        (ExS.ret (EvE.const _)))
  · intro hP
    have e1 : decide (0 < b ∧ a < i64min + b) = false := by
      simp only [decide_eq_false_iff_not]; tauto
    have e2 : decide (b < 0 ∧ i64max + b < a) = false := by
      simp only [decide_eq_false_iff_not]; tauto
    rw [e1] at g1; rw [e2] at g2
    have hor := EvE.lor_false g1 (by rfl) g2 (by rfl)
    have hrange : InI64 (a - b) := by
      unfold InI64 i64min i64max at *
      constructor <;> by_contra hc <;> apply hP <;> omega
    have hval : EvE OrientGen.prog s0 (.bin .sub (some ⟨64, true⟩) (.var 0) (.var 1))
        (.int IntTy.i64 (W (a - b))) :=
      EvE.bin (EvE.var l0) (EvE.var l1) (evSub64s a b ha hb hrange)
    have hbytes : (encodeLE (IntTy.i64.bytes) (W (a - b))).length = 8 := by
      rw [encodeLE_length]; rfl
    have hst : store s0.mem (.int IntTy.i64) (.ptr rb 0) (.int IntTy.i64 (W (a - b))) =
        .ok (s0.mem.upd rb (encodeLE 8 (W (a - b)))) := by
      rw [hmem]
      simp only [store, writeBytes, hm, if_true]
      rw [if_pos (by rw [hbytes, hblk])]
      have hd : List.drop 8 blk = [] := List.drop_eq_nil_of_le (by omega)
      simp [hbytes, hd]
      rfl
    have hstore := ExS.store (ty := .int IntTy.i64) (EvE.var l2) hval hro hst
    refine ⟨{ s0 with mem := s0.mem.upd rb (encodeLE 8 (W (a - b))) }, ?_, ?_⟩
    · exact ExS.seq (ExS.ite hor (by rfl) ExS.skip) (ExS.seq hstore (ExS.ret (EvE.const _)))
    · refine ⟨by simp [Mem.upd], fun b' hb' => ?_⟩
      simp [Mem.upd, hb', hmem]

end Tess.C
