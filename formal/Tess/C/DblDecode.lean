/-
  MiniC refinement of the translated `dbl_decode` (`lib/tess/src/exact.c`, the binary64 field decode
  used by `qr_double`): for a finite bit pattern it stores the mantissa with the implicit bit and the
  unbiased exponent through the output pointers and returns 1; for exponent field 2047 it returns 0.
  The stored values are `QrModel.dblMant`/`dblExp`. The function is analysed as a standalone
  (statement-level) call, so stores are permitted (`ro = false`).
-/
import Tess.C.QrModel
import Tess.C.LimbGen
import Tess.C.ZiMem

namespace Tess.C
open Obj.C

theorem store_load_int (m : Mem) (b o : Nat) (t : IntTy) (k : Nat) (n : Nat) (blk : Block)
    (hm : m b = some blk) (hk : t.bytes = k) (hmod : t.modulus = 256 ^ k) (hb : o + k ≤ blk.length) :
    ∃ m', store m (.int t) (.ptr b o) (.int t n) = .ok m' ∧
      load m' (.int t) (.ptr b o) = .ok (.int t (n % t.modulus)) ∧
      (∀ b', b' ≠ b → m' b' = m b') ∧
      (∃ blk', m' b = some blk' ∧ blk'.length = blk.length) := by
  have hlen : (encodeLE k n).length = k := encodeLE_length k n
  have hw : writeBytes m b o (encodeLE k n) =
      .ok (m.upd b (blk.take o ++ encodeLE k n ++ blk.drop (o + k))) := by
    simp only [writeBytes, hm, hlen, if_pos hb]
  refine ⟨m.upd b (blk.take o ++ encodeLE k n ++ blk.drop (o + k)), ?_, ?_, ?_, ?_⟩
  · simp only [store, if_true, hk]
    exact hw
  · have hoff : o ≤ blk.length := by omega
    have hrd : readBytes (m.upd b (blk.take o ++ encodeLE k n ++ blk.drop (o + k))) b o k =
        .ok (encodeLE k n) := by
      simp only [readBytes, Mem.upd, if_true]
      have hl : (blk.take o ++ encodeLE k n ++ blk.drop (o + k)).length = blk.length := by
        simp [List.length_take, List.length_drop, hlen]; omega
      rw [hl, if_pos hb]
      have hdrop : (blk.take o ++ encodeLE k n ++ blk.drop (o + k)).drop o =
          encodeLE k n ++ blk.drop (o + k) := by
        rw [List.append_assoc, List.drop_append_of_le_length (by simp; omega)]
        simp [List.length_take, Nat.min_eq_left hoff]
      rw [hdrop, List.take_append_of_le_length (le_of_eq hlen.symm)]
      rw [List.take_of_length_le (le_of_eq hlen)]
    simp only [load, hrd, Ty.size, hk, Res.bind_eq, Res.bind_ok]
    rw [decodeLE_encodeLE, ← hmod]
    rfl
  · intro b' hb'
    simp [Mem.upd, hb']
  · refine ⟨blk.take o ++ encodeLE k n ++ blk.drop (o + k), by simp [Mem.upd], ?_⟩
    simp [List.length_take, List.length_drop, hlen]; omega

end Tess.C

namespace Tess.C
open Obj.C

theorem i32_toInt_wrap (z : Int) (h1 : -2147483648 ≤ z) (h2 : z < 2147483648) :
    IntTy.toInt ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ z) = z := by
  have hmod : IntTy.modulus ⟨32, true⟩ = 4294967296 := rfl
  unfold IntTy.toInt IntTy.wrap
  rw [hmod]
  by_cases hz : 0 ≤ z
  · have e : z % ((4294967296 : Nat) : Int) = z := by omega
    rw [e]
    have : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
    have hlt : ¬ (z.toNat ≥ 2 ^ (32 - 1)) := by omega
    simp only [hlt, and_false, if_false]
    exact this
  · have e : z % ((4294967296 : Nat) : Int) = z + 4294967296 := by omega
    rw [e]
    have : ((z + 4294967296).toNat : Int) = z + 4294967296 := Int.toNat_of_nonneg (by omega)
    have hge : ((z + 4294967296).toNat ≥ 2 ^ (32 - 1)) := by omega
    simp only [hge, and_self, if_true, this]
    omega

theorem i32_sub_wrap (x y : Int) (hx1 : -2147483648 ≤ x) (hx2 : x < 2147483648)
    (hy1 : -2147483648 ≤ y) (hy2 : y < 2147483648)
    (h1 : -2147483648 ≤ x - y) (h2 : x - y < 2147483648) :
    evalBin .sub (some ⟨32, true⟩) (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ x))
      (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ y)) = .ok (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (x - y))) := by
  have ex := i32_toInt_wrap x hx1 hx2
  have ey := i32_toInt_wrap y hy1 hy2
  have hr : IntTy.inRange ⟨32, true⟩ (x - y) = true := by
    simp only [IntTy.inRange, IntTy.minVal, IntTy.maxVal, Bool.and_eq_true, decide_eq_true_eq]
    simp only [if_true]
    constructor <;> omega
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, ex, ey, arith, hr]

theorem i32_wrap_nat (x : Nat) (h : x < 2147483648) : IntTy.wrap ⟨32, true⟩ (x : Int) = x := by
  unfold IntTy.wrap
  have hmod : IntTy.modulus ⟨32, true⟩ = 4294967296 := rfl
  rw [hmod]
  have e : (x : Int) % ((4294967296 : Nat) : Int) = x := by omega
  rw [e]; simp

theorem dbl_decode_refines (u : Nat) (hu : u < 2 ^ 64) (blkM blkE : Nat) (bm be : Block) (m : Mem)
    (hm : m blkM = some bm) (he : m blkE = some be) (hbm : 8 ≤ bm.length) (hbe : 4 ≤ be.length)
    (hne : blkM ≠ blkE) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.dbl_decode.params
      [.int ⟨64, false⟩ u, .ptr blkM 0, .ptr blkE 0], m, false⟩) :
    ((u / 2 ^ 52) % 2048 = 2047 →
      ∃ sf, ExS LimbGen.prog s0 LimbGen.dbl_decode.body (.ret (some (.int ⟨32, true⟩ 0))) sf) ∧
    ((u / 2 ^ 52) % 2048 ≠ 2047 →
      ∃ sf, ExS LimbGen.prog s0 LimbGen.dbl_decode.body (.ret (some (.int ⟨32, true⟩ 1))) sf ∧
        load sf.mem (.int ⟨64, false⟩) (.ptr blkM 0) = .ok (.int ⟨64, false⟩ (dblMant u)) ∧
        load sf.mem (.int ⟨32, true⟩) (.ptr blkE 0) =
          .ok (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (dblExp u)))) := by
  have hl0 : s0.locals 0 = some (.int ⟨64, false⟩ u) := by rw [h0]; rfl
  have hl1 : s0.locals 1 = some (.ptr blkM 0) := by rw [h0]; rfl
  have hl2 : s0.locals 2 = some (.ptr blkE 0) := by rw [h0]; rfl
  have hmem : s0.mem = m := by rw [h0]
  have hro : s0.ro = false := by rw [h0]
  obtain ⟨e, he_def⟩ : ∃ e, e = (u / 2 ^ 52) % 2048 := ⟨_, rfl⟩
  have he2048 : e < 2048 := by rw [he_def]; exact Nat.mod_lt _ (by norm_num)
  -- step 1: local 3 := e
  have hE : EvE LimbGen.prog s0 (.cast ⟨32, false⟩ (.bin .band (some ⟨64, false⟩)
      (.bin .shr (some ⟨64, false⟩) (.var 0) (.const (.int ⟨32, true⟩ 52)))
      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 2047))))) (.int ⟨32, false⟩ e) := by
    have hshr : EvE LimbGen.prog s0 (.bin .shr (some ⟨64, false⟩) (.var 0) (.const (.int ⟨32, true⟩ 52)))
        (.int ⟨64, false⟩ (u / 2 ^ 52)) := EvE.bin (EvE.var hl0) (EvE.const _) rfl
    have h2047 : EvE LimbGen.prog s0 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 2047)))
        (.int ⟨64, false⟩ 2047) := EvE.cast (EvE.const _) rfl
    have hand : EvE LimbGen.prog s0 (.bin .band (some ⟨64, false⟩)
        (.bin .shr (some ⟨64, false⟩) (.var 0) (.const (.int ⟨32, true⟩ 52)))
        (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 2047)))) (.int ⟨64, false⟩ e) := by
      refine EvE.bin hshr h2047 ?_
      have : (u / 2 ^ 52) &&& 2047 = e := by
        have := Nat.and_two_pow_sub_one_eq_mod (u / 2 ^ 52) 11
        rw [he_def]
        simpa using this
      show Res.ok (Val.int ⟨64, false⟩ ((u / 4503599627370496) &&& 2047)) = Res.ok (Val.int ⟨64, false⟩ e)
      rw [show (4503599627370496 : Nat) = 2 ^ 52 from rfl, this]
    exact EvE.cast hand (by
      show Res.ok (Val.int ⟨32, false⟩ (e % 4294967296)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hset1 := ExS.set (i := 3) hE
  set s1 : State := { s0 with locals := s0.locals.upd 3 (.int ⟨32, false⟩ e) } with hs1
  have l1_0 : s1.locals 0 = some (.int ⟨64, false⟩ u) := by simpa [hs1, Locals.upd] using hl0
  have l1_3 : s1.locals 3 = some (.int ⟨32, false⟩ e) := by simp [hs1, Locals.upd]
  -- step 2: local 4 := u & mask
  have hM : EvE LimbGen.prog s1 (.bin .band (some ⟨64, false⟩) (.var 0)
      (.const (.int ⟨64, false⟩ 4503599627370495))) (.int ⟨64, false⟩ (u % 2 ^ 52)) := by
    refine EvE.bin (EvE.var l1_0) (EvE.const _) ?_
    have := Nat.and_two_pow_sub_one_eq_mod u 52
    show Res.ok (Val.int ⟨64, false⟩ (u &&& 4503599627370495)) = _
    rw [show (4503599627370495 : Nat) = 2 ^ 52 - 1 from rfl, this]
  have hset2 := ExS.set (i := 4) hM
  set s2 : State := { s1 with locals := s1.locals.upd 4 (.int ⟨64, false⟩ (u % 2 ^ 52)) } with hs2
  have l2_3 : s2.locals 3 = some (.int ⟨32, false⟩ e) := by simpa [hs2, Locals.upd] using l1_3
  have l2_4 : s2.locals 4 = some (.int ⟨64, false⟩ (u % 2 ^ 52)) := by simp [hs2, Locals.upd]
  have l2_1 : s2.locals 1 = some (.ptr blkM 0) := by simpa [hs2, hs1, Locals.upd] using hl1
  have l2_2 : s2.locals 2 = some (.ptr blkE 0) := by simpa [hs2, hs1, Locals.upd] using hl2
  have hcond : EvE LimbGen.prog s2 (.bin .eq (some ⟨32, false⟩) (.var 3)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2047)))) (boolVal (decide (e = 2047))) :=
    EvE.bin (EvE.var l2_3) (EvE.cast (EvE.const _) rfl) rfl
  have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
  constructor
  · intro h2047
    rw [← he_def] at h2047
    have hdec : decide (e = 2047) = true := by simpa using h2047
    refine ⟨s2, ?_⟩
    unfold LimbGen.dbl_decode
    exact ExS.seq hset1 (ExS.seq hset2 (ExS.seq_ret (ExS.ite hcond (by rw [hdec, tb]) (ExS.ret (EvE.const _)))))
  · intro h2047
    rw [← he_def] at h2047
    have hdec : decide (e = 2047) = false := by simpa using h2047
    have hif : ExS LimbGen.prog s2 (.ite (.bin .eq (some ⟨32, false⟩) (.var 3)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2047)))) (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip)
        .normal s2 := ExS.ite hcond (by rw [hdec, tb]) ExS.skip
    have hroS2 : s2.ro = false := by simp [hs2, hs1, hro]
    have hmS2 : s2.mem = m := by simp [hs2, hs1, hmem]
    have hdExp : dblExp u = if e ≠ 0 then (e : Int) - 1075 else -1074 := by
      unfold dblExp; rw [← he_def]
    have hdMant : dblMant u = if e ≠ 0 then u % 2 ^ 52 + 2 ^ 52 else u % 2 ^ 52 := by
      unfold dblMant; rw [← he_def]
    -- the exponent value
    have hX : EvE LimbGen.prog s2 (.cond (.var 3)
        (.bin .sub (some ⟨32, true⟩) (.bin .sub (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3))
          (.const (.int ⟨32, true⟩ 1023))) (.const (.int ⟨32, true⟩ 52)))
        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1074))))
        (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (dblExp u))) := by
      by_cases he0 : e = 0
      · have hbool : truthy (.int ⟨32, false⟩ e) = .ok false := by simp [truthy, he0]
        have hB : EvE LimbGen.prog s2 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1074)))
            (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1074))) := EvE.un (EvE.const _) rfl
        rw [hdExp]
        simp only [he0, ne_eq, not_true_eq_false, if_false]
        refine EvE.cond (EvE.var l2_3) hbool ?_
        simpa using hB
      · have hbool : truthy (.int ⟨32, false⟩ e) = .ok true := by
          have : (e != 0) = true := by simpa using he0
          simp [truthy, this]
        have hc1 : EvE LimbGen.prog s2 (.cast ⟨32, true⟩ (.var 3)) (.int ⟨32, true⟩ e) :=
          EvE.cast (EvE.var l2_3) (by
            show Res.ok (Val.int ⟨32, true⟩ (e % 4294967296)) = _
            rw [Nat.mod_eq_of_lt (by omega)])
        have hs1' : EvE LimbGen.prog s2 (.bin .sub (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3))
            (.const (.int ⟨32, true⟩ 1023))) (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ ((e : Int) - 1023))) := by
          refine EvE.bin hc1 (EvE.const _) ?_
          have := i32_sub_wrap (e : Int) 1023 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          rw [i32_wrap_nat e (by omega)] at this
          have e1023 : IntTy.wrap ⟨32, true⟩ (1023 : Int) = 1023 := i32_wrap_nat 1023 (by norm_num)
          rw [e1023] at this
          exact this
        have hs2' : EvE LimbGen.prog s2 (.bin .sub (some ⟨32, true⟩) (.bin .sub (some ⟨32, true⟩)
            (.cast ⟨32, true⟩ (.var 3)) (.const (.int ⟨32, true⟩ 1023))) (.const (.int ⟨32, true⟩ 52)))
            (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ ((e : Int) - 1023 - 52))) := by
          refine EvE.bin hs1' (EvE.const _) ?_
          have := i32_sub_wrap ((e : Int) - 1023) 52 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          have e52 : IntTy.wrap ⟨32, true⟩ (52 : Int) = 52 := i32_wrap_nat 52 (by norm_num)
          rw [e52] at this
          exact this
        rw [hdExp]
        simp only [he0, ne_eq, not_false_eq_true, if_true]
        refine EvE.cond (EvE.var l2_3) hbool ?_
        have e3 : (e : Int) - 1075 = (e : Int) - 1023 - 52 := by ring
        rw [e3]
        simpa using hs2'
    have hmodE : IntTy.modulus ⟨32, true⟩ = 256 ^ 4 := by norm_num [IntTy.modulus]
    have hmodM : IntTy.modulus ⟨64, false⟩ = 256 ^ 8 := by norm_num [IntTy.modulus]
    obtain ⟨m1, hst1, hld1, hother1, blk1, hb1, hl1len⟩ := store_load_int m blkE 0 ⟨32, true⟩ 4
      (IntTy.wrap ⟨32, true⟩ (dblExp u)) be he rfl hmodE (by omega)
    have hstore1 : ExS LimbGen.prog s2 (.store (.int ⟨32, true⟩) (.var 2) _) .normal
        { s2 with mem := m1 } :=
      ExS.store (EvE.var l2_2) hX hroS2 (by rw [hmS2]; exact hst1)
    set s3 : State := { s2 with mem := m1 } with hs3
    have l3_3 : s3.locals 3 = some (.int ⟨32, false⟩ e) := l2_3
    have l3_4 : s3.locals 4 = some (.int ⟨64, false⟩ (u % 2 ^ 52)) := l2_4
    have l3_1 : s3.locals 1 = some (.ptr blkM 0) := l2_1
    have hm1M : m1 blkM = some bm := by rw [hother1 blkM hne]; exact hm
    obtain ⟨s4, hrun, l4_4, l4_1, hmem4, hro4⟩ : ∃ s4 : State, ExS LimbGen.prog s3
        (.ite (.var 3) (.set 4 (.cast ⟨64, false⟩ (.bin .bor (some ⟨64, false⟩)
          (.cast ⟨64, false⟩ (.var 4))
          (.cast ⟨64, false⟩ (.bin .shl (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 1))
            (.const (.int ⟨32, true⟩ 52))))))) .skip) .normal s4 ∧
        s4.locals 4 = some (.int ⟨64, false⟩ (dblMant u)) ∧ s4.locals 1 = some (.ptr blkM 0) ∧
        s4.mem = m1 ∧ s4.ro = false := by
      by_cases he0 : e = 0
      · have hbool : truthy (.int ⟨32, false⟩ e) = .ok false := by simp [truthy, he0]
        refine ⟨s3, ExS.ite (EvE.var l3_3) hbool ExS.skip, ?_, l3_1, rfl, by simp [hs3, hroS2]⟩
        rw [hdMant]; simpa [he0] using l3_4
      · have hbool : truthy (.int ⟨32, false⟩ e) = .ok true := by
          have : (e != 0) = true := by simpa using he0
          simp [truthy, this]
        have hbor : EvE LimbGen.prog s3 (.cast ⟨64, false⟩ (.bin .bor (some ⟨64, false⟩)
            (.cast ⟨64, false⟩ (.var 4))
            (.cast ⟨64, false⟩ (.bin .shl (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 1))
              (.const (.int ⟨32, true⟩ 52)))))) (.int ⟨64, false⟩ (dblMant u)) := by
          have hc4 : EvE LimbGen.prog s3 (.cast ⟨64, false⟩ (.var 4)) (.int ⟨64, false⟩ (u % 2 ^ 52)) :=
            EvE.cast (EvE.var l3_4) (by
              show Res.ok (Val.int ⟨64, false⟩ ((u % 2 ^ 52) % 18446744073709551616)) = _
              rw [Nat.mod_eq_of_lt (by omega)])
          have hsh : EvE LimbGen.prog s3 (.cast ⟨64, false⟩ (.bin .shl (some ⟨64, false⟩)
              (.const (.int ⟨64, false⟩ 1)) (.const (.int ⟨32, true⟩ 52)))) (.int ⟨64, false⟩ (2 ^ 52)) :=
            EvE.cast (EvE.bin (EvE.const _) (EvE.const _) rfl) rfl
          have hbo : EvE LimbGen.prog s3 (.bin .bor (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
              (.cast ⟨64, false⟩ (.bin .shl (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 1))
                (.const (.int ⟨32, true⟩ 52))))) (.int ⟨64, false⟩ (dblMant u)) := by
            refine EvE.bin hc4 hsh ?_
            have hlt : u % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
            have := Nat.or_two_pow_eq_add_of_lt hlt
            show Res.ok (Val.int ⟨64, false⟩ ((u % 2 ^ 52) ||| 2 ^ 52)) = _
            rw [this, hdMant]; simp [he0]
          exact EvE.cast hbo (by
            show Res.ok (Val.int ⟨64, false⟩ (dblMant u % 18446744073709551616)) = _
            rw [Nat.mod_eq_of_lt (by rw [hdMant]; simp [he0]; omega)])
        refine ⟨{ s3 with locals := s3.locals.upd 4 (.int ⟨64, false⟩ (dblMant u)) },
          ExS.ite (EvE.var l3_3) hbool (ExS.set hbor), by simp [Locals.upd], ?_, rfl, by simp [hs3, hroS2]⟩
        simpa [Locals.upd] using l3_1
    obtain ⟨m2, hst2, hld2, hother2, blk2, hb2, hl2len⟩ := store_load_int m1 blkM 0 ⟨64, false⟩ 8
      (dblMant u) bm hm1M rfl hmodM (by omega)
    have hstore2 : ExS LimbGen.prog s4 (.store (.int ⟨64, false⟩) (.var 1) (.var 4)) .normal
        { s4 with mem := m2 } :=
      ExS.store (EvE.var l4_1) (EvE.var l4_4) hro4 (by rw [hmem4]; exact hst2)
    refine ⟨{ s4 with mem := m2 }, ?_, ?_, ?_⟩
    · unfold LimbGen.dbl_decode
      exact ExS.seq hset1 (ExS.seq hset2 (ExS.seq hif (ExS.seq hstore1 (ExS.seq hrun
        (ExS.seq hstore2 (ExS.ret (EvE.const _)))))))
    · rw [show (dblMant u) % IntTy.modulus ⟨64, false⟩ = dblMant u from ?_] at hld2
      · exact hld2
      · apply Nat.mod_eq_of_lt
        show dblMant u < 18446744073709551616
        rw [hdMant]; split_ifs <;> omega
    · show load m2 (.int ⟨32, true⟩) (.ptr blkE 0) = _
      have : load m2 (.int ⟨32, true⟩) (.ptr blkE 0) = load m1 (.int ⟨32, true⟩) (.ptr blkE 0) := by
        simp only [load, readBytes, hother2 blkE (Ne.symm hne)]
      rw [this, hld1]
      have hrange : IntTy.wrap ⟨32, true⟩ (dblExp u) % IntTy.modulus ⟨32, true⟩ =
          IntTy.wrap ⟨32, true⟩ (dblExp u) := by
        apply Nat.mod_eq_of_lt
        unfold IntTy.wrap
        have hm : IntTy.modulus ⟨32, true⟩ = 4294967296 := rfl
        rw [hm]
        omega
      rw [hrange]

end Tess.C
