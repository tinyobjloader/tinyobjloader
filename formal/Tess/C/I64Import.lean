/-
  MiniC refinement of the pure kernels of `zi_i64` (`lib/tess/src/exact.c`): `i64_limb_count` and
  `i64_fill`, factored out of `zi_i64`. For the magnitude `u` of an int64 they produce the limb count
  (0, 1 or 2), the little-endian limbs `[u % 2^32, u / 2^32]` truncated to that count, and the sign
  `-1`/`1`, so that the denoted integer is `u` with the sign of the input.
-/
import Tess.C.DblDecode
import Tess.C.ZiMem
import Tess.C.ZiValue

namespace Tess.C
open Obj.C

/-- Limb count chosen by the C code. -/
def i64Count (u : Nat) : Nat := if u > 4294967295 then 2 else if u ≠ 0 then 1 else 0

/-- Limbs written by `i64_fill` (for a block of exactly `i64Count u` limbs). -/
def i64Limbs (u : Nat) : List Nat :=
  if u > 4294967295 then [u % 2 ^ 32, u / 2 ^ 32] else if u ≠ 0 then [u] else []

theorem lv_i64Limbs (u : Nat) (hu : u < 2 ^ 64) : lv (i64Limbs u) = u := by
  unfold i64Limbs
  split_ifs with h1 h2
  · simp only [lv]; omega
  · simp only [lv]; omega
  · simp only [lv]; omega

theorem i64Limbs_length (u : Nat) : (i64Limbs u).length = i64Count u := by
  unfold i64Limbs i64Count; split_ifs <;> rfl

theorem i64_limb_count_refines (u : Nat) (hu : u < 2 ^ 64) (m : Mem) (ro : Bool) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.i64_limb_count.params [.int ⟨64, false⟩ u], m, ro⟩) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.i64_limb_count.body
      (.ret (some (.int ⟨64, false⟩ (i64Count u)))) sf := by
  have l0 : s0.locals 0 = some (.int ⟨64, false⟩ u) := by rw [h0]; rfl
  refine ⟨s0, ?_⟩
  unfold LimbGen.i64_limb_count
  apply ExS.ret
  have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
  have hgt : EvE LimbGen.prog s0 (.bin .gt (some ⟨64, false⟩) (.var 0)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4294967295)))) (boolVal (decide (u > 4294967295))) :=
    EvE.bin (EvE.var l0) (EvE.cast (EvE.const _) rfl) rfl
  by_cases h1 : u > 4294967295
  · have hd : decide (u > 4294967295) = true := by simpa using h1
    have hc : EvE LimbGen.prog s0 (.cond (.bin .gt (some ⟨64, false⟩) (.var 0)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4294967295)))) (.const (.int ⟨32, true⟩ 2))
        (.cond (.var 0) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))
        (.int ⟨32, true⟩ 2) :=
      EvE.cond hgt (by rw [hd, tb]) (by simpa using EvE.const (p := LimbGen.prog) (s := s0) (.int ⟨32, true⟩ 2))
    have := EvE.cast (t := ⟨64, false⟩) hc (v := .int ⟨64, false⟩ 2) rfl
    simpa [i64Count, h1] using this
  · have hd : decide (u > 4294967295) = false := by simpa using h1
    by_cases h2 : u = 0
    · have hu0 : truthy (.int ⟨64, false⟩ u) = .ok false := by simp [truthy, h2]
      have hin : EvE LimbGen.prog s0 (.cond (.var 0) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))
          (.int ⟨32, true⟩ 0) := EvE.cond (EvE.var l0) hu0 (by simpa using EvE.const (p := LimbGen.prog) (s := s0) (.int ⟨32, true⟩ 0))
      have hc : EvE LimbGen.prog s0 (.cond (.bin .gt (some ⟨64, false⟩) (.var 0)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4294967295)))) (.const (.int ⟨32, true⟩ 2))
          (.cond (.var 0) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))
          (.int ⟨32, true⟩ 0) := EvE.cond hgt (by rw [hd, tb]) (by simpa using hin)
      have := EvE.cast (t := ⟨64, false⟩) hc (v := .int ⟨64, false⟩ 0) rfl
      simpa [i64Count, h1, h2] using this
    · have hu1 : truthy (.int ⟨64, false⟩ u) = .ok true := by
        have : (u != 0) = true := by simpa using h2
        simp [truthy, this]
      have hin : EvE LimbGen.prog s0 (.cond (.var 0) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))
          (.int ⟨32, true⟩ 1) := EvE.cond (EvE.var l0) hu1 (by simpa using EvE.const (p := LimbGen.prog) (s := s0) (.int ⟨32, true⟩ 1))
      have hc : EvE LimbGen.prog s0 (.cond (.bin .gt (some ⟨64, false⟩) (.var 0)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4294967295)))) (.const (.int ⟨32, true⟩ 2))
          (.cond (.var 0) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))
          (.int ⟨32, true⟩ 1) := EvE.cond hgt (by rw [hd, tb]) (by simpa using hin)
      have := EvE.cast (t := ⟨64, false⟩) hc (v := .int ⟨64, false⟩ 1) rfl
      simpa [i64Count, h1, h2] using this

theorem store_ziBlock_sign (m : Mem) (zb vb n : Nat) (sg sg' : Int)
    (hm : m zb = some (ziBlock vb n sg)) :
    store m (.int ⟨32, true⟩) (.ptr zb 16) (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ sg')) =
      .ok (m.upd zb (ziBlock vb n sg')) := by
  have e : ∀ s : Int, ziBlock vb n s = (encodeLE 8 (ptrPack (.ptr vb 0)) ++ encodeLE 8 n) ++
      (encodeLE 4 (IntTy.wrap IntTy.i32 s) ++ [0, 0, 0, 0]) := by
    intro s; simp [ziBlock, List.append_assoc]
  have h16 : (encodeLE 8 (ptrPack (.ptr vb 0)) ++ encodeLE 8 n).length = 16 := by
    simp [encodeLE_length]
  have hlen : (ziBlock vb n sg).length = 24 := ziBlock_length vb n sg
  simp only [store, if_true]
  show writeBytes m zb 16 (encodeLE 4 (IntTy.wrap IntTy.i32 sg')) = _
  simp only [writeBytes, hm, encodeLE_length, hlen]
  rw [if_pos (by norm_num)]
  congr 2

/-- Address of limb `k` in `t->v` with a constant signed index. -/
theorem evIdxConst (s : State) (zb vb n : Nat) (sg : Int) (limbs : List Nat) (k : Nat)
    (hz : s.mem zb = some (ziBlock vb n sg)) (hv : s.mem vb = some (limbBytes limbs))
    (hk : k < limbs.length) (hk31 : k < 2147483648) (hvb : vb < 4294967296) (h0 : s.locals 0 = some (.ptr zb 0)) :
    EvE LimbGen.prog s (.index (.load .ptr (.field (.var 0) 0)) (.const (.int ⟨32, true⟩ k)) 4)
      (.ptr vb (4 * k)) := by
  have hfield : EvE LimbGen.prog s (.field (.var 0) 0) (.ptr zb 0) :=
    EvE.field (EvE.var h0) (by simp [ptrAddN, hz, ziBlock_length])
  have hbase : EvE LimbGen.prog s (.load .ptr (.field (.var 0) 0)) (.ptr vb 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vb n sg hz hvb)
  apply EvE.index hbase (EvE.const _)
  have hi : IntTy.toInt ⟨32, true⟩ k = (k : Int) := by
    unfold IntTy.toInt
    have : ¬ (k ≥ 2 ^ (32 - 1)) := by omega
    simp only [this, and_false, if_false]
  have hlen := limbBytes_length limbs
  simp only [show (IntTy.signed ⟨32, true⟩) = true from rfl, if_true, hi]
  simp only [ptrAdd, hv]
  rw [if_pos (by constructor <;> omega)]
  congr 2
  omega

theorem i64_fill_refines (zb vb n : Nat) (sg0 : Int) (old : List Nat) (u : Nat) (x : Int)
    (hu : u < 2 ^ 64) (hx1 : -9223372036854775808 ≤ x) (hx2 : x < 9223372036854775808)
    (hn : n = i64Count u) (hold : old.length = n)
    (m : Mem) (hz : m zb = some (ziBlock vb n sg0)) (hv : m vb = some (limbBytes old))
    (hne : zb ≠ vb) (hvb : vb < 4294967296) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.i64_fill.params
      [.ptr zb 0, .int ⟨64, true⟩ (IntTy.wrap ⟨64, true⟩ x), .int ⟨64, false⟩ u], m, false⟩) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.i64_fill.body .normal sf ∧
      (n = 0 → sf.mem zb = some (ziBlock vb n sg0) ∧ sf.mem vb = some (limbBytes old)) ∧
      (n ≠ 0 → sf.mem zb = some (ziBlock vb n (if x < 0 then -1 else 1)) ∧
        sf.mem vb = some (limbBytes (i64Limbs u))) := by
  have l0 : s0.locals 0 = some (.ptr zb 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.int ⟨64, true⟩ (IntTy.wrap ⟨64, true⟩ x)) := by rw [h0]; rfl
  have l2 : s0.locals 2 = some (.int ⟨64, false⟩ u) := by rw [h0]; rfl
  have hmem : s0.mem = m := by rw [h0]
  have hro : s0.ro = false := by rw [h0]
  have hnn : n < 3 := by rw [hn]; unfold i64Count; split_ifs <;> omega
  have hfield8 : EvE LimbGen.prog s0 (.field (.var 0) 8) (.ptr zb 8) :=
    EvE.field (EvE.var l0) (by simp [ptrAddN, hmem, hz, ziBlock_length])
  have hnload : EvE LimbGen.prog s0 (.load (.int ⟨64, false⟩) (.field (.var 0) 8)) (.int ⟨64, false⟩ n) := by
    have := load_ziBlock_n s0.mem zb vb n sg0 (by rw [hmem]; exact hz)
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hfield8 this
  by_cases hn0 : n = 0
  · refine ⟨s0, ?_, fun _ => ⟨by rw [hmem]; exact hz, by rw [hmem]; exact hv⟩, fun h => absurd hn0 h⟩
    unfold LimbGen.i64_fill
    have ht : truthy (.int ⟨64, false⟩ n) = .ok false := by simp [truthy, hn0]
    exact ExS.ite hnload ht ExS.skip
  · have ht : truthy (.int ⟨64, false⟩ n) = .ok true := by
      have : (n != 0) = true := by simpa using hn0
      simp [truthy, this]
    -- sign value
    have hlt64 : IntTy.toInt ⟨64, true⟩ (IntTy.wrap ⟨64, true⟩ x) = x := by
      have hmod : IntTy.modulus ⟨64, true⟩ = 18446744073709551616 := rfl
      unfold IntTy.toInt IntTy.wrap
      rw [hmod]
      by_cases hz : 0 ≤ x
      · have e : x % ((18446744073709551616 : Nat) : Int) = x := by omega
        rw [e]
        have : (x.toNat : Int) = x := Int.toNat_of_nonneg hz
        have hlt : ¬ (x.toNat ≥ 2 ^ (64 - 1)) := by omega
        simp only [hlt, and_false, if_false]
        exact this
      · have e : x % ((18446744073709551616 : Nat) : Int) = x + 18446744073709551616 := by omega
        rw [e]
        have : ((x + 18446744073709551616).toNat : Int) = x + 18446744073709551616 :=
          Int.toNat_of_nonneg (by omega)
        have hge : ((x + 18446744073709551616).toNat ≥ 2 ^ (64 - 1)) := by omega
        simp only [hge, and_self, if_true, this]
        omega
    have hnn' : n = 1 ∨ n = 2 := by omega
    have hz0 : s0.mem zb = some (ziBlock vb n sg0) := by rw [hmem]; exact hz
    have hv0 : s0.mem vb = some (limbBytes old) := by rw [hmem]; exact hv
    -- store of limb 0
    have hidx0 := evIdxConst s0 zb vb n sg0 old 0 hz0 hv0 (by omega) (by norm_num) hvb l0
    have hval0 : EvE LimbGen.prog s0 (.cast ⟨32, false⟩ (.var 2)) (.int ⟨32, false⟩ (u % 2 ^ 32)) :=
      EvE.cast (EvE.var l2) rfl
    have hst0 := ExS.store (ty := .int ⟨32, false⟩) hidx0 hval0 hro (by
      have := store_limb s0.mem vb old 0 (u % 2 ^ 32) hv0 (by omega)
      exact this)
    set s1 : State := { s0 with mem := s0.mem.upd vb (limbBytes (old.set 0 (u % 2 ^ 32))) } with hs1
    have l1_0 : s1.locals 0 = some (.ptr zb 0) := l0
    have l1_1 : s1.locals 1 = some (.int ⟨64, true⟩ (IntTy.wrap ⟨64, true⟩ x)) := l1
    have l1_2 : s1.locals 2 = some (.int ⟨64, false⟩ u) := l2
    have hro1 : s1.ro = false := hro
    have hz1 : s1.mem zb = some (ziBlock vb n sg0) := by
      simp only [hs1, Mem.upd, hne, if_false]; exact hz0
    have hv1 : s1.mem vb = some (limbBytes (old.set 0 (u % 2 ^ 32))) := by
      simp [hs1, Mem.upd]
    have hset0len : (old.set 0 (u % 2 ^ 32)).length = n := by simp [hold]
    have hnload1 : EvE LimbGen.prog s1 (.load (.int ⟨64, false⟩) (.field (.var 0) 8)) (.int ⟨64, false⟩ n) := by
      have hf : EvE LimbGen.prog s1 (.field (.var 0) 8) (.ptr zb 8) :=
        EvE.field (EvE.var l1_0) (by simp [ptrAddN, hz1, ziBlock_length])
      have := load_ziBlock_n s1.mem zb vb n sg0 hz1
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact EvE.load hf this
    have hcond2 : EvE LimbGen.prog s1 (.bin .eq (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
        (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 2)))) (boolVal (decide (n = 2))) :=
      EvE.bin hnload1 (EvE.cast (EvE.const _) rfl) rfl
    have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
    obtain ⟨s2, hrun2, hz2, hv2, l2_0, l2_1, l2_2, hro2⟩ : ∃ s2 : State,
        ExS LimbGen.prog s1 (.ite (.bin .eq (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
          (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 2))))
          (.store (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.const (.int ⟨32, true⟩ 1)) 4)
            (.cast ⟨32, false⟩ (.bin .shr (some ⟨64, false⟩) (.var 2) (.const (.int ⟨32, true⟩ 32))))) .skip)
          .normal s2 ∧
        s2.mem zb = some (ziBlock vb n sg0) ∧ s2.mem vb = some (limbBytes (i64Limbs u)) ∧
        s2.locals 0 = some (.ptr zb 0) ∧
        s2.locals 1 = some (.int ⟨64, true⟩ (IntTy.wrap ⟨64, true⟩ x)) ∧
        s2.locals 2 = some (.int ⟨64, false⟩ u) ∧ s2.ro = false := by
      rcases hnn' with h1 | h2'
      · have hf : truthy (boolVal (decide (n = 2))) = .ok false := by rw [tb]; simp [h1]
        refine ⟨s1, ExS.ite hcond2 hf ExS.skip, hz1, ?_, l1_0, l1_1, l1_2, hro1⟩
        rw [hv1]
        have hu1 : ¬ u > 4294967295 := by
          intro h; have : n = 2 := by rw [hn]; unfold i64Count; simp [h]
          omega
        have hu0 : u ≠ 0 := by
          intro h; have : n = 0 := by rw [hn]; unfold i64Count; simp [h]
          omega
        unfold i64Limbs
        rw [if_neg hu1, if_pos hu0]
        have hl1 : old.length = 1 := by rw [hold, h1]
        obtain ⟨o0, rfl⟩ : ∃ o0, old = [o0] := by
          match old, hl1 with
          | [o0], _ => exact ⟨o0, rfl⟩
        have : u % 4294967296 = u := Nat.mod_eq_of_lt (by omega)
        simp [this]
      · have ht2 : truthy (boolVal (decide (n = 2))) = .ok true := by rw [tb]; simp [h2']
        have hlen2 : 1 < (old.set 0 (u % 2 ^ 32)).length := by
          rw [List.length_set, hold, h2']; norm_num
        have hidx1 := evIdxConst s1 zb vb n sg0 (old.set 0 (u % 2 ^ 32)) 1 hz1 hv1 hlen2
          (by norm_num) hvb l1_0
        have hval1 : EvE LimbGen.prog s1 (.cast ⟨32, false⟩ (.bin .shr (some ⟨64, false⟩) (.var 2)
            (.const (.int ⟨32, true⟩ 32)))) (.int ⟨32, false⟩ ((u / 2 ^ 32) % 2 ^ 32)) :=
          EvE.cast (EvE.bin (EvE.var l1_2) (EvE.const _) rfl) rfl
        have hst1 := ExS.store (ty := .int ⟨32, false⟩) hidx1 hval1 hro1 (by
          have := store_limb s1.mem vb (old.set 0 (u % 2 ^ 32)) 1 ((u / 2 ^ 32) % 2 ^ 32) hv1 hlen2
          exact this)
        refine ⟨_, ExS.ite hcond2 ht2 hst1, ?_, ?_, l1_0, l1_1, l1_2, hro1⟩
        · show (s1.mem.upd vb _) zb = _
          simp only [Mem.upd, hne, if_false]; exact hz1
        · show (s1.mem.upd vb _) vb = _
          simp only [Mem.upd, if_true]
          congr 1
          have hu2 : u > 4294967295 := by
            by_contra h
            have : i64Count u ≠ 2 := by
              unfold i64Count; rw [if_neg h]; split_ifs <;> omega
            exact this (hn ▸ h2')
          have hl2 : old.length = 2 := by rw [hold, h2']
          obtain ⟨o0, o1, rfl⟩ : ∃ o0 o1, old = [o0, o1] := by
            match old, hl2 with
            | [o0, o1], _ => exact ⟨o0, o1, rfl⟩
          have e1 : (u / 2 ^ 32) % 2 ^ 32 = u / 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
          unfold i64Limbs
          rw [if_pos hu2, e1]
          rfl
    -- sign store
    have hlt : EvE LimbGen.prog s2 (.bin .lt (some ⟨64, true⟩) (.var 1)
        (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 0)))) (boolVal (decide (x < 0))) := by
      refine EvE.bin (EvE.var l2_1) (EvE.cast (EvE.const _) rfl) ?_
      have h0' : IntTy.toInt ⟨64, true⟩ 0 = 0 := by decide
      have h0'' : IntTy.wrap ⟨64, true⟩ (IntTy.toInt ⟨32, true⟩ 0) = 0 := by decide
      simp only [evalBin, isPtr, Bool.and_false, Bool.false_eq_true, ite_false, evalBinInt, binInt, intOf,
        if_true, if_false, hlt64, h0', h0'', Res.bind_eq, Res.bind_ok, Res.pure_eq]
    have hsv : EvE LimbGen.prog s2 (.cond (.bin .lt (some ⟨64, true⟩) (.var 1)
        (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 0))))
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))) (.const (.int ⟨32, true⟩ 1)))
        (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (if x < 0 then -1 else 1))) := by
      by_cases hxn : x < 0
      · have hd : decide (x < 0) = true := by simpa using hxn
        refine EvE.cond hlt (by rw [hd, tb]) ?_
        simp only [hd, if_true, hxn]
        exact EvE.un (EvE.const _) rfl
      · have hd : decide (x < 0) = false := by simpa using hxn
        refine EvE.cond hlt (by rw [hd, tb]) ?_
        simp only [hd, Bool.false_eq_true, if_false, hxn]
        exact EvE.const _
    have hf16 : EvE LimbGen.prog s2 (.field (.var 0) 16) (.ptr zb 16) :=
      EvE.field (EvE.var l2_0) (by simp [ptrAddN, hz2, ziBlock_length])
    have hst3 := ExS.store (ty := .int ⟨32, true⟩) hf16 hsv hro2
      (store_ziBlock_sign s2.mem zb vb n sg0 (if x < 0 then -1 else 1) hz2)
    refine ⟨{ s2 with mem := s2.mem.upd zb (ziBlock vb n (if x < 0 then -1 else 1)) }, ?_,
      fun h => absurd h hn0, fun _ => ⟨?_, ?_⟩⟩
    · unfold LimbGen.i64_fill
      exact ExS.ite hnload ht (ExS.seq hst0 (ExS.seq hrun2 hst3))
    · show (s2.mem.upd zb _) zb = _
      simp [Mem.upd]
    · show (s2.mem.upd zb _) vb = _
      simp only [Mem.upd, Ne.symm hne, if_false]
      exact hv2

end Tess.C
