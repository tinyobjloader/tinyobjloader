/-
  MiniC refinement of the translated `mul` (`lib/tess/src/tess.c`), the overflow-checked int64
  multiplication of `tess_orient2i`, including its call of `mag`: evaluation never hits undefined
  behavior, it returns `0` exactly when `OverflowModel.mulChk` fails and otherwise stores `mulChk`'s
  value through the out-pointer and returns `1`.
-/
import Tess.C.SubC
import Tess.C.DivSingleC

namespace Tess.C
open Obj.C

theorem mag_body_eq : OrientGen.mag.body = Gen.tess_mag.body := rfl

theorem evMag (s : State) (e : Expr) (a : Int) (ha : InI64 a)
    (he : EvE OrientGen.prog s e (.int IntTy.i64 (W a))) :
    EvE OrientGen.prog s (.call 1 [e]) (.int IntTy.u64 a.natAbs) := by
  refine EvE.call (fn := OrientGen.mag) (s' := ⟨frameLocals OrientGen.mag.params [.int IntTy.i64 (W a)], s.mem, true⟩)
    (EvArgs.cons he EvArgs.nil) rfl rfl ?_
  rw [mag_body_eq]
  exact magnitude_refines_p OrientGen.prog _ a (inI64_lt a ha) (by rfl)

theorem evNeBool (s : State) (e1 e2 : Expr) (p q : Bool)
    (h1 : EvE OrientGen.prog s e1 (boolVal p)) (h2 : EvE OrientGen.prog s e2 (boolVal q)) :
    EvE OrientGen.prog s (.bin .ne (some ⟨32, true⟩) e1 e2) (boolVal (p != q)) :=
  EvE.bin h1 h2 (by cases p <;> cases q <;> rfl)

theorem evCastU64Max (s : State) :
    EvE OrientGen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
      (.int IntTy.u64 (2 ^ 63 - 1)) := EvE.cast (EvE.const _) rfl

theorem evCastU64One (s : State) :
    EvE OrientGen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1))) (.int IntTy.u64 1) :=
  EvE.cast (EvE.const _) rfl

theorem evCap (s : State) :
    EvE OrientGen.prog s (.bin .add (some ⟨64, false⟩)
      (.cast ⟨64, false⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.int IntTy.u64 (2 ^ 63)) :=
  EvE.bin (evCastU64Max s) (evCastU64One s) rfl

theorem store_i64 (m : Mem) (rb : Nat) (blk : Block) (n : Nat) (hm : m rb = some blk)
    (hblk : blk.length = 8) :
    store m (.int IntTy.i64) (.ptr rb 0) (.int IntTy.i64 n) = .ok (m.upd rb (encodeLE 8 n)) := by
  have hbytes : (encodeLE (IntTy.i64.bytes) n).length = 8 := by rw [encodeLE_length]; rfl
  simp only [store, writeBytes, hm, if_true]
  rw [if_pos (by rw [hbytes, hblk])]
  have hd : List.drop 8 blk = [] := List.drop_eq_nil_of_le (by omega)
  simp [hbytes, hd]
  rfl

theorem mul_refines (a b : Int) (ha : InI64 a) (hb : InI64 b) (rb : Nat) (blk : Block)
    (m : Mem) (s0 : State)
    (h0 : s0 = ⟨frameLocals OrientGen.mul.params
      [.int IntTy.i64 (W a), .int IntTy.i64 (W b), .ptr rb 0], m, false⟩)
    (hm : m rb = some blk) (hblk : blk.length = 8) :
    (mulChk a b = none →
      ∃ sf, ExS OrientGen.prog s0 OrientGen.mul.body (.ret (some (.int ⟨32, true⟩ 0))) sf) ∧
    (∀ r, mulChk a b = some r →
      ∃ sf, ExS OrientGen.prog s0 OrientGen.mul.body (.ret (some (.int ⟨32, true⟩ 1))) sf ∧
        sf.mem rb = some (encodeLE 8 (W r)) ∧ (∀ b', b' ≠ rb → sf.mem b' = m b')) := by
  have l0 : s0.locals 0 = some (.int IntTy.i64 (W a)) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.int IntTy.i64 (W b)) := by rw [h0]; rfl
  have l2 : s0.locals 2 = some (.ptr rb 0) := by rw [h0]; rfl
  have hro : s0.ro = false := by rw [h0]
  have hmem : s0.mem = m := by rw [h0]
  -- magnitudes
  have hx := evMag s0 (.var 0) a ha (EvE.var l0)
  have hset3 := ExS.set (i := 3) hx
  set s1 : State := { s0 with locals := s0.locals.upd 3 (.int IntTy.u64 a.natAbs) } with hs1
  have s1_1 : s1.locals 1 = some (.int IntTy.i64 (W b)) := by simpa [hs1, Locals.upd] using l1
  have hy := evMag s1 (.var 1) b hb (EvE.var s1_1)
  have hset4 := ExS.set (i := 4) hy
  set s2 : State := { s1 with locals := s1.locals.upd 4 (.int IntTy.u64 b.natAbs) } with hs2
  -- sign flag
  have s2_0 : s2.locals 0 = some (.int IntTy.i64 (W a)) := by simpa [hs2, hs1, Locals.upd] using l0
  have s2_1 : s2.locals 1 = some (.int IntTy.i64 (W b)) := by simpa [hs2, hs1, Locals.upd] using l1
  have hlta := EvE.bin (EvE.var s2_0) (evC0 s2) (evLtS64 a 0 ha InI64_0)
  have hltb := EvE.bin (EvE.var s2_1) (evC0 s2) (evLtS64 b 0 hb InI64_0)
  have hneg := evNeBool s2 _ _ (decide (a < 0)) (decide (b < 0)) hlta hltb
  have hset6 := ExS.set (i := 6) hneg
  set s3 : State := { s2 with locals := s2.locals.upd 6 (boolVal (decide (a < 0) != decide (b < 0))) } with hs3
  have s3_6 : s3.locals 6 = some (boolVal (decide (a < 0) != decide (b < 0))) := by
    simp [hs3, Locals.upd]
  -- cap
  set negB : Bool := (decide (a < 0) != decide (b < 0)) with hnegB
  have hcap : EvE OrientGen.prog s3 (.cond (.var 6)
      (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
        (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1))))
      (.cast ⟨64, false⟩ (.const (.int ⟨64, true⟩ 9223372036854775807))))
      (.int IntTy.u64 (if negB then 2 ^ 63 else 2 ^ 63 - 1)) := by
    refine EvE.cond (EvE.var s3_6) (tb' negB) ?_
    cases negB
    · simpa using evCastU64Max s3
    · simpa using evCap s3
  have hset7 := ExS.set (i := 7) hcap
  set s4 : State := { s3 with locals := s3.locals.upd 7 (.int IntTy.u64 (if negB then 2 ^ 63 else 2 ^ 63 - 1)) } with hs4
  have s4_3 : s4.locals 3 = some (.int IntTy.u64 a.natAbs) := by simp [hs4, hs3, hs2, hs1, Locals.upd]
  have s4_4 : s4.locals 4 = some (.int IntTy.u64 b.natAbs) := by simp [hs4, hs3, hs2, hs1, Locals.upd]
  have s4_6 : s4.locals 6 = some (boolVal negB) := by simp [hs4, hs3, hs2, hs1, Locals.upd, hnegB]
  have s4_7 : s4.locals 7 = some (.int IntTy.u64 (if negB then 2 ^ 63 else 2 ^ 63 - 1)) := by
    simp [hs4, Locals.upd]
  -- guard `y && x > cap / y`
  set capv : Nat := (if negB then 2 ^ 63 else 2 ^ 63 - 1) with hcapv
  have hcap63 : capv ≤ 2 ^ 63 := by rw [hcapv]; split <;> omega
  have hxlt : a.natAbs ≤ 2 ^ 63 := by have := inI64_lt a ha; omega
  have hylt : b.natAbs ≤ 2 ^ 63 := by have := inI64_lt b hb; omega
  have hG : EvE OrientGen.prog s4 (.land (.var 4) (.bin .gt (some ⟨64, false⟩) (.var 3)
      (.bin .div (some ⟨64, false⟩) (.var 7) (.var 4))))
      (boolVal (decide (b.natAbs ≠ 0 ∧ capv / b.natAbs < a.natAbs))) := by
    by_cases hy0 : b.natAbs = 0
    · have := EvE.land_false (p := OrientGen.prog) (b := (.bin .gt (some ⟨64, false⟩) (.var 3)
        (.bin .div (some ⟨64, false⟩) (.var 7) (.var 4)))) (EvE.var s4_4)
        (by rw [hy0]; simp [truthy])
      simpa [hy0] using this
    · have hypos : 0 < b.natAbs := Nat.pos_of_ne_zero hy0
      have hdiv := EvE.bin (p := OrientGen.prog) (EvE.var s4_7) (EvE.var s4_4) (evDiv64 capv b.natAbs
        (by omega) hypos (by omega))
      have hgt := EvE.bin (p := OrientGen.prog) (EvE.var s4_3) hdiv (show evalBin .gt (some ⟨64, false⟩)
        (.int IntTy.u64 a.natAbs) (.int IntTy.u64 (capv / b.natAbs)) =
          .ok (boolVal (decide (a.natAbs > capv / b.natAbs))) from rfl)
      have := EvE.land_true (p := OrientGen.prog) (EvE.var s4_4) (by simp [truthy, hy0]) hgt (tb' _)
      simpa [hy0, gt_iff_lt] using this
  by_cases hF : b.natAbs ≠ 0 ∧ capv / b.natAbs < a.natAbs
  · -- failure
    have hnone : mulChk a b = none := by
      unfold mulChk; simp only []; rw [if_pos]; exact hF
    refine ⟨fun _ => ?_, fun r hr => by rw [hnone] at hr; cases hr⟩
    refine ⟨s4, ?_⟩
    unfold OrientGen.mul
    have hGt : decide (b.natAbs ≠ 0 ∧ capv / b.natAbs < a.natAbs) = true := by simpa using hF
    rw [hGt] at hG
    show ExS OrientGen.prog s0 (.seq (.seq _ _) (.seq _ (.seq _ (.seq _ _)))) _ s4
    exact ExS.seq (ExS.seq hset3 hset4) (ExS.seq hset6 (ExS.seq hset7
      (ExS.seq_ret (ExS.ite hG (by rfl) (ExS.ret (EvE.const _))))))
  · -- success path
    have hnF : ¬ (b.natAbs ≠ 0 ∧ capv / b.natAbs < a.natAbs) := hF
    have hGf : decide (b.natAbs ≠ 0 ∧ capv / b.natAbs < a.natAbs) = false := by simpa using hnF
    rw [hGf] at hG
    have hz : a.natAbs * b.natAbs ≤ capv := by
      by_cases hy0 : b.natAbs = 0
      · rw [hy0]; simp
      · have hypos : 0 < b.natAbs := Nat.pos_of_ne_zero hy0
        have : a.natAbs ≤ capv / b.natAbs := by
          by_contra hc; exact hnF ⟨hy0, by omega⟩
        exact (Nat.le_div_iff_mul_le hypos).mp this
    have hzlt : a.natAbs * b.natAbs < 2 ^ 64 := by omega
    have hmulv : EvE OrientGen.prog s4 (.bin .mul (some ⟨64, false⟩) (.var 3) (.var 4))
        (.int IntTy.u64 (a.natAbs * b.natAbs)) :=
      EvE.bin (EvE.var s4_3) (EvE.var s4_4) (by
        show Res.ok (Val.int IntTy.u64 (a.natAbs * b.natAbs % 18446744073709551616)) = _
        rw [Nat.mod_eq_of_lt (by simpa using hzlt)])
    have hset5 := ExS.set (i := 5) hmulv
    set z : Nat := a.natAbs * b.natAbs with hzdef
    set s5 : State := { s4 with locals := s4.locals.upd 5 (.int IntTy.u64 z) } with hs5
    have s5_5 : s5.locals 5 = some (.int IntTy.u64 z) := by simp [hs5, Locals.upd]
    have s5_6 : s5.locals 6 = some (boolVal negB) := by simpa [hs5, Locals.upd] using s4_6
    have s5_2 : s5.locals 2 = some (.ptr rb 0) := by
      simpa [hs5, hs4, hs3, hs2, hs1, Locals.upd] using l2
    have hmem5 : s5.mem = m := by simp [hs5, hs4, hs3, hs2, hs1, hmem]
    -- second guard: neg && z == 2^63
    have hG2 : EvE OrientGen.prog s5 (.land (.var 6) (.bin .eq (some ⟨64, false⟩) (.var 5)
        (.bin .add (some ⟨64, false⟩)
          (.cast ⟨64, false⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
          (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1))))))
        (boolVal (negB && decide (z = 2 ^ 63))) := by
      cases hnb : negB
      · have := EvE.land_false (p := OrientGen.prog) (b := (.bin .eq (some ⟨64, false⟩) (.var 5)
          (.bin .add (some ⟨64, false⟩)
            (.cast ⟨64, false⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
            (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))))) (EvE.var s5_6)
          (by rw [hnb]; rfl)
        simpa using this
      · have heq := EvE.bin (p := OrientGen.prog) (EvE.var s5_5) (evCap s5)
          (show evalBin .eq (some ⟨64, false⟩) (.int IntTy.u64 z) (.int IntTy.u64 (2 ^ 63)) =
            .ok (boolVal (decide (z = 2 ^ 63))) from rfl)
        have := EvE.land_true (p := OrientGen.prog) (EvE.var s5_6) (by rw [hnb]; rfl) heq (tb' _)
        simpa using this
    have hrestRet : ∀ s', ExS OrientGen.prog s' (.ret (some (.const (.int ⟨32, true⟩ 1))))
        (.ret (some (.int ⟨32, true⟩ 1))) s' := fun s' => ExS.ret (EvE.const _)
    by_cases hC : negB = true ∧ z = 2 ^ 63
    · -- INT64_MIN
      have hval : EvE OrientGen.prog s5 (.bin .sub (some ⟨64, true⟩)
          (.un .neg ⟨64, true⟩ (.const (.int ⟨64, true⟩ 9223372036854775807)))
          (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.int IntTy.i64 (W i64min)) := by
        have hneg := EvE.un (evCmax s5) (evNegS64 i64max InI64_max InI64_nmax)
        have := EvE.bin hneg (evC1 s5) (evSub64s (-i64max) 1 InI64_nmax InI64_1
          (by unfold InI64 i64min i64max; omega))
        have e : (-i64max - 1) = i64min := by unfold i64min i64max; omega
        rw [e] at this; exact this
      have hst := ExS.store (ty := .int IntTy.i64) (EvE.var s5_2) hval
        (by simp [hs5, hs4, hs3, hs2, hs1, hro]) (by rw [hmem5]; exact store_i64 m rb blk (W i64min) hm hblk)
      have hG2t : decide (negB = true ∧ z = 2 ^ 63) = true := by simpa using hC
      have hb2 : (negB && decide (z = 2 ^ 63)) = true := by simpa using hC
      rw [hb2] at hG2
      refine ⟨?_, fun r hr => ?_⟩
      · intro hn
        exfalso; unfold mulChk at hn; simp only [] at hn; rw [if_neg hF] at hn; cases hn
      · have hrr : r = i64min := by
          unfold mulChk at hr; simp only [] at hr; rw [if_neg hF] at hr
          have := Option.some.inj hr
          rw [← this, if_pos]; exact hC
        subst hrr
        refine ⟨{ s5 with mem := m.upd rb (encodeLE 8 (W i64min)) }, ?_, ⟨by simp [Mem.upd], fun b' hb' => by simp [Mem.upd, hb']⟩⟩
        unfold OrientGen.mul
        show ExS OrientGen.prog s0 (.seq (.seq _ _) (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ _)))))) _ _
        exact ExS.seq (ExS.seq hset3 hset4) (ExS.seq hset6 (ExS.seq hset7
          (ExS.seq (ExS.ite hG (by rfl) ExS.skip) (ExS.seq hset5
            (ExS.seq (ExS.ite (bc := true) hG2 (by rfl) hst) (hrestRet _))))))
    · -- ordinary store of ±z
      have hz63 : z < 2 ^ 63 := by
        have hc : capv ≤ 2 ^ 63 := hcap63
        by_cases hnb : negB = true
        · have : z ≠ 2 ^ 63 := fun h => hC ⟨hnb, h⟩
          have : capv = 2 ^ 63 := by rw [hcapv, hnb]; simp
          omega
        · have : negB = false := by simpa using hnb
          have : capv = 2 ^ 63 - 1 := by rw [hcapv, this]; simp
          omega
      have hzI : InI64 (z : Int) := by
        unfold InI64 i64min i64max; constructor <;> push_cast <;> omega
      have hzI' : InI64 (-(z : Int)) := by
        unfold InI64 i64min i64max; constructor <;> push_cast <;> omega
      have hcastz : EvE OrientGen.prog s5 (.cast ⟨64, true⟩ (.var 5)) (.int IntTy.i64 (W (z : Int))) :=
        EvE.cast (EvE.var s5_5) (by
          change Res.ok (Val.int IntTy.i64 (IntTy.wrap IntTy.i64 (IntTy.toInt IntTy.u64 z))) = _
          simp [IntTy.toInt, IntTy.u64, W])
      have hval : EvE OrientGen.prog s5 (.cond (.var 6) (.un .neg ⟨64, true⟩ (.cast ⟨64, true⟩ (.var 5)))
          (.cast ⟨64, true⟩ (.var 5))) (.int IntTy.i64 (W (if negB then -(z : Int) else (z : Int)))) := by
        refine EvE.cond (EvE.var s5_6) (tb' negB) ?_
        cases negB
        · exact hcastz
        · exact EvE.un hcastz (evNegS64 (z : Int) hzI hzI')
      have hst := ExS.store (ty := .int IntTy.i64) (EvE.var s5_2) hval
        (by simp [hs5, hs4, hs3, hs2, hs1, hro])
        (by rw [hmem5]; exact store_i64 m rb blk (W (if negB then -(z : Int) else (z : Int))) hm hblk)
      have hb2 : (negB && decide (z = 2 ^ 63)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases hnb : negB = true
        · right; exact fun h => hC ⟨hnb, h⟩
        · left; simpa using hnb
      rw [hb2] at hG2
      have hmv : ∀ r, mulChk a b = some r → r = (if negB then -(z : Int) else (z : Int)) := by
        intro r hr
        unfold mulChk at hr; simp only [] at hr; rw [if_neg hF] at hr
        have := Option.some.inj hr
        rw [← this, if_neg hC]
      refine ⟨?_, fun r hr => ?_⟩
      · intro hn
        exfalso; unfold mulChk at hn; simp only [] at hn; rw [if_neg hF] at hn; cases hn
      · rw [hmv r hr]
        refine ⟨{ s5 with mem := m.upd rb (encodeLE 8 (W (if negB then -(z : Int) else (z : Int)))) }, ?_, ⟨by simp [Mem.upd], fun b' hb' => by simp [Mem.upd, hb']⟩⟩
        unfold OrientGen.mul
        show ExS OrientGen.prog s0 (.seq (.seq _ _) (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ _)))))) _ _
        exact ExS.seq (ExS.seq hset3 hset4) (ExS.seq hset6 (ExS.seq hset7
          (ExS.seq (ExS.ite hG (by rfl) ExS.skip) (ExS.seq hset5
            (ExS.seq (ExS.ite (bc := false) hG2 (by rfl) hst) (hrestRet _))))))

end Tess.C

namespace Tess.C
open Obj.C

theorem load_i64_enc (m : Mem) (rb n : Nat) (hn : n < 2 ^ 64) (hm : m rb = some (encodeLE 8 n)) :
    load m (.int IntTy.i64) (.ptr rb 0) = .ok (.int IntTy.i64 n) := by
  have hlen : (encodeLE 8 n).length = 8 := encodeLE_length 8 n
  have hsz : Ty.size (.int IntTy.i64) = 8 := rfl
  simp only [load, hsz, readBytes, hm]
  rw [if_pos (by rw [hlen])]
  rw [List.drop_zero, List.take_of_length_le (by rw [hlen])]
  simp [decodeLE_encodeLE]
  simpa using hn

end Tess.C
