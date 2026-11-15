/-
  Refinement of the translated `tobj_scan_int` in the loader's *cursor layout*
  (cursor cell `p` in its own block, bytes in another block, `int` output in a
  third), the layout in which `parse_corner_n_f` calls it.

  * `scan_int_cursor_failure` / `scan_int_cursor_success`: for every input and
    start offset, the translated function agrees with the pure model
    `Obj.scanInt` -- flag, committed cursor (`*pp`), value stored to `*out`
    (wrapped to i32) and untouched memory elsewhere. The scanner end is an
    arbitrary `e ≤ bytes.length` and the pure side reads `(bytes.take e)`, so
    a token inside a larger block is covered; `e = bytes.length` is the
    whole-buffer case.
  * Building blocks: `isDigit_call_raw`, `sd_loop` (the saturating digit loop,
    refining `scanCLoopStep` folds), `si_sign`, `si_value`, `scanInt_eq2`.
-/
import Obj.C.Proofs.ObjNextToken
import Obj.C.Proofs.ObjIsDigit
import Obj.C.Proofs.ObjFixIndex
namespace Obj.C.Proofs
open Obj.C Obj

theorem i8_signed (byte : UInt8) :
    IntTy.inRange IntTy.i8 (IntTy.toInt IntTy.i8 byte.toNat) = true ∧
    IntTy.wrap IntTy.i8 (IntTy.toInt IntTy.i8 byte.toNat) = byte.toNat ∧
    (byte.toNat < 128 → IntTy.toInt IntTy.i8 byte.toNat = byte.toNat) ∧
    (128 ≤ byte.toNat → IntTy.toInt IntTy.i8 byte.toNat < 0) := by
  have hlt : byte.toNat < 256 := byte.toNat_lt
  by_cases h : byte.toNat < 128
  · have hc : IntTy.toInt IntTy.i8 byte.toNat = byte.toNat := by
      have : ¬ 128 ≤ byte.toNat := by omega
      simp [IntTy.toInt, IntTy.modulus, IntTy.i8, this]
    refine ⟨?_, ?_, fun _ => hc, fun h' => by omega⟩
    · rw [hc]; simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8]; omega
    · rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
  · have hc : IntTy.toInt IntTy.i8 byte.toNat = (byte.toNat : Int) - 256 := by
      have : 128 ≤ byte.toNat := by omega
      simp [IntTy.toInt, IntTy.modulus, IntTy.i8, this]
    refine ⟨?_, ?_, fun h' => by omega, fun _ => by rw [hc]; omega⟩
    · rw [hc]; simp [IntTy.inRange, IntTy.minVal, IntTy.maxVal, IntTy.i8]; omega
    · rw [hc]
      simp only [IntTy.wrap, IntTy.modulus, IntTy.i8]
      have : ((byte.toNat : Int) - 256) % (256 : Int) = byte.toNat := by omega
      change (((byte.toNat : Int) - 256) % (256 : Int)).toNat = byte.toNat
      rw [this]; simp

theorem isDigit_body (byte : UInt8) (m : Mem) :
    ExS Gen.prog ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], m, true⟩ Gen.tobj_is_digit.body
      (.ret (some (.int IntTy.u8 (if scanDigit byte.toNat then 1 else 0))))
      ⟨frameLocals [0] [.int IntTy.i8 byte.toNat], m, true⟩ := by
  obtain ⟨hr, hw, hs, hn⟩ := i8_signed byte
  have hl : (frameLocals [0] [.int IntTy.i8 byte.toNat]) 0 =
      some (.int IntTy.i8 (IntTy.wrap IntTy.i8 (IntTy.toInt IntTy.i8 byte.toNat))) := by
    simp [frameLocals, hw]
  by_cases hd : scanDigit byte.toNat = true
  · have h2 : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 := by simpa [scanDigit] using hd
    have := tobj_is_digit_ge _ m _ (ro := true) hr (by rw [hs (by omega)]; omega)
      (by rw [hs (by omega)]; omega) hl
    simpa [hd] using this
  · have hd' : scanDigit byte.toNat = false := by simpa using hd
    have h2 : ¬ (48 ≤ byte.toNat ∧ byte.toNat ≤ 57) := by simpa [scanDigit] using hd'
    by_cases hb : byte.toNat < 128
    · by_cases hlo : byte.toNat < 48
      · have := tobj_is_digit_lo _ m _ (ro := true) hr (by rw [hs hb]; omega) hl
        simpa [hd'] using this
      · have := tobj_is_digit_hi _ m _ (ro := true) hr (by rw [hs hb]; omega) hl
        simpa [hd'] using this
    · have := tobj_is_digit_lo _ m _ (ro := true) hr (by have := hn (by omega); omega) hl
      simpa [hd'] using this

theorem isDigit_call_raw (s : State) (e : Expr) (b o : Nat) (blk : Block) (byte : UInt8)
    (he : EvE Gen.prog s e (.ptr b o)) (hm : s.mem b = some blk) (hlt : o < blk.length)
    (ho : blk[o]? = some byte) :
    EvE Gen.prog s (.call 7 [.load (.int ⟨8, true⟩) e])
      (.int IntTy.u8 (if scanDigit byte.toNat then 1 else 0)) := by
  have hbyte : blk[o]'hlt = byte := by
    have := List.getElem?_eq_getElem hlt
    rw [this] at ho; exact Option.some.inj ho
  have hload : EvE Gen.prog s (.load (.int ⟨8, true⟩) e) (.int ⟨8, true⟩ byte.toNat) := by
    apply EvE.load he
    have := load_i8_at s.mem b o blk hm hlt
    rw [hbyte] at this; exact this
  have hargs : EvArgs Gen.prog s [.load (.int ⟨8, true⟩) e] [.int ⟨8, true⟩ byte.toNat] :=
    EvArgs.cons hload EvArgs.nil
  have := EvE.call hargs (f := 7) (fn := Gen.tobj_is_digit) (by rfl) (by rfl)
    (isDigit_body byte s.mem)
  simpa using this


def i64 : IntTy := ⟨64, true⟩
def i32 : IntTy := ⟨32, true⟩

theorem i64_mul_val (a c : Nat) (ha : a < 9223372036854775808) (hc : c < 9223372036854775808)
    (h : a * c < 9223372036854775808) :
    evalBin .mul (some ⟨64, true⟩) (.int i64 a) (.int i64 c) = .ok (.int i64 (a * c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i64, arith, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, IntTy.inRange, IntTy.minVal, IntTy.maxVal, Res.bind]
  have ha' : ¬ 9223372036854775808 ≤ a := by omega
  have hc' : ¬ 9223372036854775808 ≤ c := by omega
  have e : (a : Int) * c = ((a * c : Nat) : Int) := (Int.natCast_mul a c).symm
  simp only [ha', hc', if_false, e]
  rw [if_pos (by omega)]
  congr 2
  omega

theorem i64_add_val (a c : Nat) (ha : a < 9223372036854775808) (hc : c < 9223372036854775808)
    (h : a + c < 9223372036854775808) :
    evalBin .add (some ⟨64, true⟩) (.int i64 a) (.int i64 c) = .ok (.int i64 (a + c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i64, arith, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, IntTy.inRange, IntTy.minVal, IntTy.maxVal, Res.bind]
  have ha' : ¬ 9223372036854775808 ≤ a := by omega
  have hc' : ¬ 9223372036854775808 ≤ c := by omega
  simp only [ha', hc', if_false]
  rw [if_pos (by omega)]
  congr 2
  omega

theorem i64_gt_val (a c : Nat) (ha : a < 9223372036854775808) (hc : c < 9223372036854775808) :
    evalBin .gt (some ⟨64, true⟩) (.int i64 a) (.int i64 c) = .ok (boolVal (decide (a > c))) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i64, IntTy.toInt, IntTy.modulus, Res.bind]
  have ha' : ¬ 9223372036854775808 ≤ a := by omega
  have hc' : ¬ 9223372036854775808 ≤ c := by omega
  simp only [ha', hc', if_false]
  simp

theorem i32_sub_val (a c : Nat) (ha : a < 2147483648) (hc : c < 2147483648) (h : c ≤ a) :
    evalBin .sub (some ⟨32, true⟩) (.int i32 a) (.int i32 c) = .ok (.int i32 (a - c)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, arith, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, IntTy.inRange, IntTy.minVal, IntTy.maxVal, Res.bind]
  have ha' : ¬ 2147483648 ≤ a := by omega
  have hc' : ¬ 2147483648 ≤ c := by omega
  simp only [ha', hc', if_false]
  rw [if_pos (by omega)]
  congr 2
  omega

theorem cast_i32_i8_small (d : Nat) (h : d < 128) :
    evalCast ⟨32, true⟩ (.int ⟨8, true⟩ d) = .ok (.int i32 d) := by
  simp [evalCast, IntTy.toInt, IntTy.wrap, IntTy.modulus, i32]
  have : ¬ 128 ≤ d := by omega
  simp [this]
  omega

theorem cast_i64_i32_small (d : Nat) (h : d < 2147483648) :
    evalCast ⟨64, true⟩ (.int i32 d) = .ok (.int i64 d) := by
  simp [evalCast, IntTy.toInt, IntTy.wrap, IntTy.modulus, i32, i64]
  have : ¬ 2147483648 ≤ d := by omega
  simp [this]
  omega

theorem cast_i64_i32_const (d : Nat) (h : d < 2147483648) :
    evalCast ⟨64, true⟩ (.int ⟨32, true⟩ d) = .ok (.int i64 d) := cast_i64_i32_small d h


def sdAcc : Expr :=
  (.bin .add (some ⟨64, true⟩) (.bin .mul (some ⟨64, true⟩) (.var 5)
    (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 10))))
    (.cast ⟨64, true⟩ (.bin .sub (some ⟨32, true⟩)
      (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 48)))))

def sdBody : Stmt :=
  (.ite (.land (.bin .lt (some IntTy.u64) (.var 3) (.var 1))
      (.cast ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))])))
    (.seq (.ite (.un .lnot ⟨32, true⟩ (.var 6))
      (.seq (.set 5 sdAcc)
        (.ite (.bin .gt (some ⟨64, true⟩) (.var 5) (.const (.int ⟨64, true⟩ 2147483647)))
          (.seq (.set 5 (.const (.int ⟨64, true⟩ 2147483647)))
            (.set 6 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
              (.const (.int ⟨8, false⟩ 0))))) .skip)) .skip)
      (.set 3 (.index (.var 3) (.const (.int ⟨64, true⟩ 1)) 1))) .brk)

theorem sd_ast : Gen.tobj_scan_int_loop0 = .loop sdBody .skip := rfl

/-- Loop state: cursor `q`, accumulator and saturation flag. -/
def sdSt (s : State) (bb q acc : Nat) (sat : Bool) : State :=
  { s with locals := (((s.locals.upd 3 (.ptr bb q)).upd 5 (.int i64 acc)).upd 6 (.int IntTy.u8 (if sat then 1 else 0))) }

theorem sd_step (s : State) (bb e q acc : Nat) (sat : Bool) (bytes : Block) (d : UInt8)
    (he : e ≤ bytes.length) (l1 : s.locals 1 = some (.ptr bb e))
    (hm : s.mem bb = some bytes) (hq : q < e) (hd : bytes[q]? = some d)
    (hdig : scanDigit d.toNat = true) (hacc : acc ≤ 2147483647)
    (hsat : sat = true → acc = 2147483647) :
    ExS Gen.prog (sdSt s bb q acc sat) sdBody .normal
      (sdSt s bb (q + 1) (scanCLoopStep (acc, sat) d.toNat).1 (scanCLoopStep (acc, sat) d.toNat).2) := by
  have hq' : q < bytes.length := by omega
  let st := sdSt s bb q acc sat
  have l3 : st.locals 3 = some (.ptr bb q) := by simp [st, sdSt, Locals.upd]
  have l5 : st.locals 5 = some (.int i64 acc) := by simp [st, sdSt, Locals.upd]
  have l6 : st.locals 6 = some (.int IntTy.u8 (if sat then 1 else 0)) := by
    simp [st, sdSt, Locals.upd]
  have l1' : st.locals 1 = some (.ptr bb e) := by simpa [st, sdSt, Locals.upd] using l1
  have hmst : st.mem bb = some bytes := hm
  have hv3 : EvE Gen.prog st (.var 3) (.ptr bb q) := EvE.var l3
  have hv1 : EvE Gen.prog st (.var 1) (.ptr bb e) := EvE.var l1'
  have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
    apply EvE.bin hv3 hv1
    simp [evalBin, isPtr, boolVal, hq]
  have hcall := isDigit_call_raw st (.var 3) bb q bytes d hv3 hmst hq' hd
  rw [hdig] at hcall
  simp only [if_true] at hcall
  have hcallc : EvE Gen.prog st (.cast ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))]))
      (.int i32 1) := by
    apply EvE.cast hcall
    simp [evalCast, IntTy.u8, IntTy.modulus, i32]
  have hland : EvE Gen.prog st (.land (.bin .lt (some IntTy.u64) (.var 3) (.var 1))
      (.cast ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))]))) (boolVal true) :=
    EvE.land_true (bb := true) hlt (by simp [truthy, boolVal]) hcallc (by simp [truthy, i32])
  have hdv : 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by simpa [scanDigit] using hdig
  -- pointer increment
  have hidx : ∀ st' : State, st'.mem bb = some bytes → st'.locals 3 = some (.ptr bb q) →
      EvE Gen.prog st' (.index (.var 3) (.const (.int ⟨64, true⟩ 1)) 1) (.ptr bb (q + 1)) := by
    intro st' hm' hl'
    apply EvE.index (EvE.var hl') (EvE.const _)
    have h1 : IntTy.toInt ⟨64, true⟩ 1 = 1 := by simp [IntTy.toInt, IntTy.modulus]
    simp [IntTy.signed, ptrAdd, hm', h1]
    omega
  have hset3 : ∀ st' : State, st'.mem bb = some bytes → st'.locals 3 = some (.ptr bb q) →
      ExS Gen.prog st' (.set 3 (.index (.var 3) (.const (.int ⟨64, true⟩ 1)) 1)) .normal
        { st' with locals := st'.locals.upd 3 (.ptr bb (q + 1)) } :=
    fun st' hm' hl' => ExS.set (hidx st' hm' hl')
  have eq3 : ∀ (a : Nat) (sv : Bool), ({ sdSt s bb q a sv with locals := ((sdSt s bb q a sv).locals.upd 3 (.ptr bb (q + 1))) } : State) = sdSt s bb (q + 1) a sv := by
    intro a sv
    simp only [sdSt, State.mk.injEq, and_true]
    funext i
    by_cases h3 : i = 3 <;> by_cases h5 : i = 5 <;> by_cases h6 : i = 6 <;>
      simp [Locals.upd, *]
  have hbl : (sdSt s bb q acc sat).mem = s.mem := rfl
  by_cases hs : sat = true
  · subst hs
    have hacc' : acc = 2147483647 := hsat rfl
    have hv6 : EvE Gen.prog st (.var 6) (.int IntTy.u8 1) := EvE.var (by simpa using l6)
    have hnot : EvE Gen.prog st (.un .lnot ⟨32, true⟩ (.var 6)) (boolVal false) :=
      EvE.un hv6 (by simp [evalUn, truthy, boolVal])
    have hif : ExS Gen.prog st (.ite (.un .lnot ⟨32, true⟩ (.var 6)) (.seq (.set 5 sdAcc)
        (.ite (.bin .gt (some ⟨64, true⟩) (.var 5) (.const (.int ⟨64, true⟩ 2147483647)))
          (.seq (.set 5 (.const (.int ⟨64, true⟩ 2147483647)))
            (.set 6 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
              (.const (.int ⟨8, false⟩ 0))))) .skip)) .skip) .normal st :=
      ExS.ite hnot (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.skip (p := Gen.prog) (s := st)))
    have h3 := hset3 st hmst l3
    have : ExS Gen.prog st sdBody .normal { st with locals := st.locals.upd 3 (.ptr bb (q + 1)) } := by
      unfold sdBody
      exact ExS.ite hland (bc := true) (by simp [truthy, boolVal]) (by simpa using ExS.seq hif h3)
    simpa [scanCLoopStep, st, eq3] using this
  · have hs' : sat = false := by simpa using hs
    subst hs'
    have hv6 : EvE Gen.prog st (.var 6) (.int IntTy.u8 0) := EvE.var (by simpa using l6)
    have hnot : EvE Gen.prog st (.un .lnot ⟨32, true⟩ (.var 6)) (boolVal true) :=
      EvE.un hv6 (by simp [evalUn, truthy, boolVal])
    have hdlt : d.toNat < 128 := by omega
    have hv5 : EvE Gen.prog st (.var 5) (.int i64 acc) := EvE.var l5
    have c10 : EvE Gen.prog st (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 10))) (.int i64 10) :=
      EvE.cast (EvE.const _) (cast_i64_i32_const 10 (by omega))
    have hmul : EvE Gen.prog st (.bin .mul (some ⟨64, true⟩) (.var 5)
        (.cast ⟨64, true⟩ (.const (.int ⟨32, true⟩ 10)))) (.int i64 (acc * 10)) :=
      EvE.bin hv5 c10 (i64_mul_val _ _ (by omega) (by omega) (by omega))
    have hld : EvE Gen.prog st (.load (.int ⟨8, true⟩) (.var 3)) (.int ⟨8, true⟩ d.toNat) := by
      apply EvE.load hv3
      have := load_i8_at st.mem bb q bytes hmst hq'
      have hb : bytes[q]'hq' = d := by
        have := List.getElem?_eq_getElem (l := bytes) hq'
        rw [this] at hd; exact Option.some.inj hd
      rw [hb] at this; exact this
    have hci : EvE Gen.prog st (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3))) (.int i32 d.toNat) :=
      EvE.cast hld (cast_i32_i8_small _ hdlt)
    have hsub : EvE Gen.prog st (.bin .sub (some ⟨32, true⟩)
        (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 48)))
        (.int i32 (d.toNat - 48)) :=
      EvE.bin hci (EvE.const _) (i32_sub_val _ 48 (by omega) (by omega) (by omega))
    have hcs : EvE Gen.prog st (.cast ⟨64, true⟩ (.bin .sub (some ⟨32, true⟩)
        (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 48))))
        (.int i64 (d.toNat - 48)) :=
      EvE.cast hsub (cast_i64_i32_small _ (by omega))
    have hcand : EvE Gen.prog st sdAcc (.int i64 (acc * 10 + (d.toNat - 48))) :=
      EvE.bin hmul hcs (i64_add_val _ _ (by omega) (by omega) (by omega))
    have hset5 := ExS.set (p := Gen.prog) (i := 5) hcand
    let st1 : State := { st with locals := st.locals.upd 5 (.int i64 (acc * 10 + (d.toNat - 48))) }
    have l5' : st1.locals 5 = some (.int i64 (acc * 10 + (d.toNat - 48))) := by
      simp [st1, Locals.upd]
    have hv5' : EvE Gen.prog st1 (.var 5) (.int i64 (acc * 10 + (d.toNat - 48))) := EvE.var l5'
    have hgt : EvE Gen.prog st1 (.bin .gt (some ⟨64, true⟩) (.var 5)
        (.const (.int ⟨64, true⟩ 2147483647)))
        (boolVal (decide (acc * 10 + (d.toNat - 48) > 2147483647))) :=
      EvE.bin hv5' (EvE.const _) (i64_gt_val _ _ (by omega) (by omega))
    have hm1 : st1.mem bb = some bytes := hmst
    have l3_1 : st1.locals 3 = some (.ptr bb q) := by simpa [st1, Locals.upd] using l3
    have h3 := hset3 st1 hm1 l3_1
    by_cases hov : acc * 10 + (d.toNat - 48) > 2147483647
    · have hset5b := ExS.set (p := Gen.prog) (s := st1) (i := 5)
        (EvE.const (.int ⟨64, true⟩ 2147483647))
      let st2 : State := { st1 with locals := st1.locals.upd 5 (.int ⟨64, true⟩ 2147483647) }
      have hc1 : EvE Gen.prog st2 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
          (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 1) :=
        EvE.cond (EvE.const _) (bc := true) (by simp [truthy]) (EvE.const _)
      have hset6 := ExS.set (p := Gen.prog) (s := st2) (i := 6) hc1
      let st3 : State := { st2 with locals := st2.locals.upd 6 (.int ⟨8, false⟩ 1) }
      have hm3 : st3.mem bb = some bytes := hmst
      have l3_3 : st3.locals 3 = some (.ptr bb q) := by
        simpa [st3, st2, st1, Locals.upd] using l3
      have h3' := hset3 st3 hm3 l3_3
      have hite : ExS Gen.prog st1 (.ite (.bin .gt (some ⟨64, true⟩) (.var 5)
          (.const (.int ⟨64, true⟩ 2147483647)))
          (.seq (.set 5 (.const (.int ⟨64, true⟩ 2147483647)))
            (.set 6 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
              (.const (.int ⟨8, false⟩ 0))))) .skip) .normal st3 :=
        ExS.ite hgt (bc := true) (by simp [truthy, boolVal, hov]) (by simpa using ExS.seq hset5b hset6)
      have hif : ExS Gen.prog st (.ite (.un .lnot ⟨32, true⟩ (.var 6)) (.seq (.set 5 sdAcc)
          (.ite (.bin .gt (some ⟨64, true⟩) (.var 5) (.const (.int ⟨64, true⟩ 2147483647)))
            (.seq (.set 5 (.const (.int ⟨64, true⟩ 2147483647)))
              (.set 6 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
                (.const (.int ⟨8, false⟩ 0))))) .skip)) .skip) .normal st3 :=
        ExS.ite hnot (bc := true) (by simp [truthy, boolVal]) (by simpa using ExS.seq hset5 hite)
      have hbody : ExS Gen.prog st sdBody .normal
          { st3 with locals := st3.locals.upd 3 (.ptr bb (q + 1)) } := by
        unfold sdBody
        exact ExS.ite hland (bc := true) (by simp [truthy, boolVal]) (by simpa using ExS.seq hif h3')
      have hstep : scanCLoopStep (acc, false) d.toNat = (2147483647, true) := by
        simp [scanCLoopStep, hov]
      rw [hstep]
      have heqS : ({ st3 with locals := st3.locals.upd 3 (.ptr bb (q + 1)) } : State) =
          sdSt s bb (q + 1) 2147483647 true := by
        simp only [sdSt, st3, st2, st1, st, State.mk.injEq, and_true]
        funext i
        by_cases h3 : i = 3 <;> by_cases h5 : i = 5 <;> by_cases h6 : i = 6 <;>
          simp [Locals.upd, *, i64, IntTy.u8]
      show ExS Gen.prog st sdBody .normal (sdSt s bb (q + 1) 2147483647 true)
      rw [← heqS]; exact hbody
    · have hite : ExS Gen.prog st1 (.ite (.bin .gt (some ⟨64, true⟩) (.var 5)
          (.const (.int ⟨64, true⟩ 2147483647)))
          (.seq (.set 5 (.const (.int ⟨64, true⟩ 2147483647)))
            (.set 6 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
              (.const (.int ⟨8, false⟩ 0))))) .skip) .normal st1 :=
        ExS.ite hgt (bc := false) (by simp [truthy, boolVal, hov])
          (by simpa using (ExS.skip (p := Gen.prog) (s := st1)))
      have hif : ExS Gen.prog st (.ite (.un .lnot ⟨32, true⟩ (.var 6)) (.seq (.set 5 sdAcc)
          (.ite (.bin .gt (some ⟨64, true⟩) (.var 5) (.const (.int ⟨64, true⟩ 2147483647)))
            (.seq (.set 5 (.const (.int ⟨64, true⟩ 2147483647)))
              (.set 6 (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
                (.const (.int ⟨8, false⟩ 0))))) .skip)) .skip) .normal st1 :=
        ExS.ite hnot (bc := true) (by simp [truthy, boolVal]) (by simpa using ExS.seq hset5 hite)
      have hbody : ExS Gen.prog st sdBody .normal
          { st1 with locals := st1.locals.upd 3 (.ptr bb (q + 1)) } := by
        unfold sdBody
        exact ExS.ite hland (bc := true) (by simp [truthy, boolVal]) (by simpa using ExS.seq hif h3)
      have hstep : scanCLoopStep (acc, false) d.toNat =
          (acc * 10 + (d.toNat - 48), false) := by
        simp [scanCLoopStep, hov]
      rw [hstep]
      have heqS : ({ st1 with locals := st1.locals.upd 3 (.ptr bb (q + 1)) } : State) =
          sdSt s bb (q + 1) (acc * 10 + (d.toNat - 48)) false := by
        simp only [sdSt, st1, st, State.mk.injEq, and_true]
        funext i
        by_cases h3 : i = 3 <;> by_cases h5 : i = 5 <;> by_cases h6 : i = 6 <;>
          simp [Locals.upd, *, i64]
      show ExS Gen.prog st sdBody .normal (sdSt s bb (q + 1) (acc * 10 + (d.toNat - 48)) false)
      rw [← heqS]; exact hbody


theorem scanCLoopStep_le (v b : Nat) (sat : Bool) (h : v ≤ 2147483647) :
    (scanCLoopStep (v, sat) b).1 ≤ 2147483647 := by
  unfold scanCLoopStep
  cases sat with
  | true => simpa using h
  | false =>
    by_cases hc : v * 10 + (b - 48) > 2147483647
    · simp [hc]
    · simp [hc]; omega

theorem scanCLoopStep_sat (v b : Nat) (sat : Bool) (h : sat = true → v = 2147483647) :
    (scanCLoopStep (v, sat) b).2 = true → (scanCLoopStep (v, sat) b).1 = 2147483647 :=
  scanCLoopStep_saturated v b sat h

/-- Partial fold over the first `k` digit values. -/
def pfold (ds : List Nat) (k : Nat) : Nat × Bool := (ds.take k).foldl scanCLoopStep (0, false)

theorem pfold_succ (ds : List Nat) (k : Nat) (hk : k < ds.length) :
    pfold ds (k + 1) = scanCLoopStep (pfold ds k) ds[k] := by
  unfold pfold
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem pfold_full (ds : List Nat) (k : Nat) (hk : ds.length ≤ k) : pfold ds k = pfold ds ds.length := by
  unfold pfold
  rw [List.take_of_length_le hk, List.take_length]

theorem pfold_inv (ds : List Nat) (k : Nat) :
    (pfold ds k).1 ≤ 2147483647 ∧ ((pfold ds k).2 = true → (pfold ds k).1 = 2147483647) := by
  induction k with
  | zero => simp [pfold]
  | succ k ih =>
    by_cases hk : k < ds.length
    · rw [pfold_succ ds k hk]
      obtain ⟨h1, h2⟩ := ih
      exact ⟨scanCLoopStep_le _ _ _ h1, scanCLoopStep_sat _ _ _ h2⟩
    · rw [pfold_full ds (k + 1) (by omega), ← pfold_full ds k (by omega)]; exact ih


theorem tw_getElem {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (hk : k < (l.takeWhile p).length) : (l.takeWhile p)[k]? = l[k]? := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    by_cases ha : p a = true
    · simp only [List.takeWhile_cons, ha, if_true, List.length_cons] at hk ⊢
      cases k with
      | zero => rfl
      | succ k => simpa using ih k (by omega)
    · simp [List.takeWhile_cons, ha] at hk

theorem sd_loop (s : State) (bb e p1 : Nat) (bytes : Block)
    (he : e ≤ bytes.length)
    (hp1 : p1 ≤ e) (l1 : s.locals 1 = some (.ptr bb e)) (hm : s.mem bb = some bytes) :
    ∃ sf, ExS Gen.prog (sdSt s bb p1 0 false) (.loop sdBody .skip) .normal sf ∧
      sf = sdSt s bb (p1 + (((bytes.take e).drop p1).takeWhile (fun b => scanDigit b.toNat)).length)
        (pfold ((((bytes.take e).drop p1).takeWhile (fun b => scanDigit b.toNat)).map UInt8.toNat)
          (((bytes.take e).drop p1).takeWhile (fun b => scanDigit b.toNat)).length).1
        (pfold ((((bytes.take e).drop p1).takeWhile (fun b => scanDigit b.toNat)).map UInt8.toNat)
          (((bytes.take e).drop p1).takeWhile (fun b => scanDigit b.toNat)).length).2 := by
  have hseLen : (bytes.take e).length = e := by simp [List.length_take, he]
  let Ld := ((bytes.take e).drop p1).takeWhile (fun b : UInt8 => scanDigit b.toNat)
  let ds := Ld.map UInt8.toNat
  let cnt := Ld.length
  have hcntLe : p1 + cnt ≤ e := by
    show p1 + Ld.length ≤ e
    have h2 : Ld.length ≤ ((bytes.take e).drop p1).length :=
      (List.takeWhile_prefix (fun b : UInt8 => scanDigit b.toNat) (l := (bytes.take e).drop p1)).length_le
    rw [List.length_drop, hseLen] at h2
    omega
  have hcntLe' : p1 + cnt ≤ bytes.length := by omega
  let P : Nat → State → Prop := fun j st => ∃ k, k + j = cnt ∧
    st = sdSt s bb (p1 + k) (pfold ds k).1 (pfold ds k).2
  have hget : ∀ i, i < ((bytes.take e).drop p1).length → ((bytes.take e).drop p1)[i]? = bytes[p1 + i]? := by
    intro i hi
    have hie : i < e - p1 := by
      have hd : ((bytes.take e).drop p1).length = e - p1 := by simp [List.length_drop, hseLen]
      omega
    show ((bytes.take e).drop p1)[i]? = _
    rw [List.drop_take, List.getElem?_take, if_pos hie, List.getElem?_drop]
  have hstep : ∀ j st, P (j + 1) st → ∃ s1 s2, ExS Gen.prog st sdBody .normal s1 ∧
      ExS Gen.prog s1 .skip .normal s2 ∧ P j s2 := by
    intro j st ⟨k, hk, hst⟩
    subst hst
    have hkc : k < cnt := by omega
    obtain ⟨d, hd, hdig⟩ := tw_inside (fun b : UInt8 => scanDigit b.toNat) ((bytes.take e).drop p1) k
      (by simpa [Ld] using hkc)
    have hdat : bytes[p1 + k]? = some d := by
      have hi : k < ((bytes.take e).drop p1).length := by
        have hdlen : ((bytes.take e).drop p1).length = e - p1 := by simp [List.length_drop, hseLen]
        have : k < e - p1 := by
          have hLd : Ld.length ≤ ((bytes.take e).drop p1).length := by
            exact (List.takeWhile_prefix (fun b : UInt8 => scanDigit b.toNat) (l := (bytes.take e).drop p1)).length_le
          simp [Ld] at hLd
          omega
        omega
      have hd' := hget k hi
      rw [hd'] at hd
      exact hd
    have hdsk : ds[k]? = some d.toNat := by
      simp only [ds, List.getElem?_map]
      rw [tw_getElem (fun b : UInt8 => scanDigit b.toNat) ((bytes.take e).drop p1) k (by simpa [Ld] using hkc), hd]
      rfl
    have hdsk' : k < ds.length := by
      show k < (Ld.map UInt8.toNat).length
      rw [List.length_map]; exact hkc
    have hdk : ds[k] = d.toNat := by
      have := List.getElem?_eq_getElem hdsk'
      rw [this] at hdsk; exact Option.some.inj hdsk
    obtain ⟨hb1, hb2⟩ := pfold_inv ds k
    have hq1 : p1 + k < e := by omega
    have hst := sd_step s bb e (p1 + k) (pfold ds k).1 (pfold ds k).2 bytes d he l1 hm
      hq1 hdat hdig hb1 hb2
    refine ⟨_, _, hst, ExS.skip, k + 1, by omega, ?_⟩
    rw [pfold_succ ds k hdsk', hdk, Nat.add_assoc]
  have hexit : ∀ st, P 0 st → ∃ s1, ExS Gen.prog st sdBody .brk s1 ∧ P 0 s1 := by
    intro st ⟨k, hk, hst⟩
    have hkc : k = cnt := by omega
    subst hst
    refine ⟨_, ?_, ⟨k, hk, rfl⟩⟩
    let st := sdSt s bb (p1 + k) (pfold ds k).1 (pfold ds k).2
    have l3 : st.locals 3 = some (.ptr bb (p1 + k)) := by simp [st, sdSt, Locals.upd]
    have l1' : st.locals 1 = some (.ptr bb e) := by simpa [st, sdSt, Locals.upd] using l1
    have hmst : st.mem bb = some bytes := hm
    have hv3 : EvE Gen.prog st (.var 3) (.ptr bb (p1 + k)) := EvE.var l3
    have hv1 : EvE Gen.prog st (.var 1) (.ptr bb e) := EvE.var l1'
    unfold sdBody
    by_cases hend : p1 + k = e
    · have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
        apply EvE.bin hv3 hv1
        simp [evalBin, isPtr, boolVal, hend]
      have hland := EvE.land_false (b := (.cast ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩)
        (.var 3))]))) hlt (by simp [truthy, boolVal])
      exact ExS.ite hland (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.brk (p := Gen.prog) (s := st)))
    · have hqlt : p1 + k < e := by omega
      have hqlt' : p1 + k < bytes.length := by omega
      have hlt : EvE Gen.prog st (.bin .lt (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
        apply EvE.bin hv3 hv1
        simp [evalBin, isPtr, boolVal, hqlt]
      have hbd : ((((bytes.take e).drop p1).takeWhile (fun b : UInt8 => scanDigit b.toNat))).length <
          ((bytes.take e).drop p1).length := by
        rw [List.length_drop, hseLen]; show Ld.length < _; omega
      obtain ⟨x, hx, hnd⟩ := tw_boundary (fun b : UInt8 => scanDigit b.toNat) ((bytes.take e).drop p1) hbd
      have hkL : k = Ld.length := by simpa using hk
      have hxat : bytes[p1 + k]? = some x := by
        have hi : Ld.length < ((bytes.take e).drop p1).length := by
          have hdlen : ((bytes.take e).drop p1).length = e - p1 := by simp [List.length_drop, hseLen]
          have := hbd
          omega
        have hd' := hget Ld.length hi
        subst hkL
        rw [hd'] at hx
        exact hx
      have hnd' : scanDigit x.toNat = false := by simpa using hnd
      have hcall := isDigit_call_raw st (.var 3) bb (p1 + k) bytes x hv3 hmst hqlt' hxat
      rw [hnd'] at hcall
      simp only [Bool.false_eq_true, if_false] at hcall
      have hcallc : EvE Gen.prog st (.cast ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))]))
          (.int i32 0) := by
        apply EvE.cast hcall
        simp [evalCast, IntTy.u8, IntTy.modulus, i32]
      have hland := EvE.land_true (bb := false) hlt (by simp [truthy, boolVal]) hcallc
        (by simp [truthy, i32])
      exact ExS.ite hland (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.brk (p := Gen.prog) (s := st)))
  have hinit : P cnt (sdSt s bb p1 0 false) := ⟨0, by omega, by simp [pfold]⟩
  obtain ⟨sf, hl, k, hk, hsf⟩ := ExS.loop_decreasing_post (p := Gen.prog) (P := P)
    (Q := fun st => ∃ k, k + 0 = cnt ∧ st = sdSt s bb (p1 + k) (pfold ds k).1 (pfold ds k).2)
    (n := cnt) (s := sdSt s bb p1 0 false) hinit hstep hexit
  refine ⟨sf, hl, ?_⟩
  have : k = cnt := by omega
  subst this
  exact hsf


theorem scanInt_eq (bytes : Block) (pos : Nat) :
    scanInt (bytes.map UInt8.toNat) pos =
      scanIntDigits
        (if (bytes[skipStop bytes pos]?.map UInt8.toNat == some 43 ||
             bytes[skipStop bytes pos]?.map UInt8.toNat == some 45) = true
         then ((bytes.drop (skipStop bytes pos)).map UInt8.toNat).drop 1
         else (bytes.drop (skipStop bytes pos)).map UInt8.toNat)
        (bytes[skipStop bytes pos]?.map UInt8.toNat == some 45)
        (skipStop bytes pos +
          (if (bytes[skipStop bytes pos]?.map UInt8.toNat == some 43 ||
               bytes[skipStop bytes pos]?.map UInt8.toNat == some 45) = true then 1 else 0))
        (skipStop bytes pos) := by
  have hmap : ((bytes.map UInt8.toNat).drop pos).takeWhile scanSpace =
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).map UInt8.toNat := by
    rw [← List.map_drop]; exact takeWhile_map_space _
  have hlen : (((bytes.map UInt8.toNat).drop pos).takeWhile scanSpace).length =
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length := by
    rw [hmap]; simp
  have hdd : ((bytes.map UInt8.toNat).drop pos).drop
      ((bytes.drop pos).takeWhile (fun b => scanSpace b.toNat)).length =
      (bytes.drop (skipStop bytes pos)).map UInt8.toNat := by
    rw [← List.map_drop, ← List.map_drop, List.drop_drop]
    rfl
  have hhead : (((bytes.drop (skipStop bytes pos)).map UInt8.toNat).head?) =
      bytes[skipStop bytes pos]?.map UInt8.toNat := by
    rw [List.head?_map, List.head?_drop]
  unfold scanInt
  simp only [hlen, hdd, hhead]
  rfl


def hasSignB (bytes : Block) (stop : Nat) : Bool :=
  (bytes[stop]?.map UInt8.toNat == some 43 || bytes[stop]?.map UInt8.toNat == some 45)

def negB (bytes : Block) (stop : Nat) : Bool := (bytes[stop]?.map UInt8.toNat == some 45)

def p1Of (bytes : Block) (stop : Nat) : Nat := stop + (if hasSignB bytes stop = true then 1 else 0)

theorem scanInt_eq2 (bytes : Block) (pos : Nat) :
    scanInt (bytes.map UInt8.toNat) pos =
      scanIntDigits ((bytes.drop (p1Of bytes (skipStop bytes pos))).map UInt8.toNat)
        (negB bytes (skipStop bytes pos)) (p1Of bytes (skipStop bytes pos)) (skipStop bytes pos) := by
  rw [scanInt_eq]
  unfold p1Of hasSignB negB
  by_cases h : (bytes[skipStop bytes pos]?.map UInt8.toNat == some 43 ||
      bytes[skipStop bytes pos]?.map UInt8.toNat == some 45) = true
  · simp only [h, if_true]
    rw [← List.map_drop, List.drop_drop]
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, if_false, Nat.add_zero]


theorem byte_eq_eval (s : State) (e : Expr) (b o : Nat) (blk : Block) (byte : UInt8) (k : Nat)
    (hk : k < 128) (he : EvE Gen.prog s e (.ptr b o)) (hm : s.mem b = some blk)
    (hlt : o < blk.length) (ho : blk[o]? = some byte) :
    EvE Gen.prog s (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) e))
      (.const (.int ⟨32, true⟩ k))) (boolVal (decide (byte.toNat = k))) := by
  have hbyte : blk[o]'hlt = byte := by
    have := List.getElem?_eq_getElem hlt
    rw [this] at ho; exact Option.some.inj ho
  have hload : EvE Gen.prog s (.load (.int ⟨8, true⟩) e) (.int ⟨8, true⟩ byte.toNat) := by
    apply EvE.load he
    have := load_i8_at s.mem b o blk hm hlt
    rw [hbyte] at this; exact this
  obtain ⟨hr, hw, hs, hn⟩ := i8_signed byte
  have hc : evalCast ⟨32, true⟩ (.int ⟨8, true⟩ byte.toNat) =
      .ok (.int ⟨32, true⟩ (IntTy.wrap IntTy.i32 (IntTy.toInt IntTy.i8 byte.toNat))) := by
    simp [evalCast]; rfl
  have hcast := EvE.cast hload hc
  apply EvE.bin hcast (EvE.const _)
  have hbd : -2147483648 ≤ IntTy.toInt IntTy.i8 byte.toNat ∧
      IntTy.toInt IntTy.i8 byte.toNat ≤ 2147483647 := by
    have hlt256 : byte.toNat < 256 := byte.toNat_lt
    by_cases h : byte.toNat < 128
    · rw [hs h]; omega
    · have := hn (by omega)
      simp only [IntTy.toInt, IntTy.modulus, IntTy.i8] at this ⊢
      have : (128 ≤ byte.toNat) := by omega
      simp [this]; omega
  have hti := toInt_i32_wrap _ hbd
  have hk' : IntTy.toInt ⟨32, true⟩ k = k := by
    have : ¬ 2147483648 ≤ k := by omega
    simp [IntTy.toInt, IntTy.modulus, this]
  have key : decide (IntTy.toInt IntTy.i8 byte.toNat = (k : Int)) = decide (byte.toNat = k) := by
    by_cases hb : byte.toNat < 128
    · rw [hs hb]; exact decide_eq_decide.mpr (by omega)
    · have := hn (by omega)
      have h2 : ¬ (IntTy.toInt IntTy.i8 byte.toNat = (k : Int)) := by omega
      have h3 : ¬ byte.toNat = k := by omega
      simp [h2, h3]
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, hk', Res.bind]
  have hti' : IntTy.toInt ⟨32, true⟩ (IntTy.wrap IntTy.i32 (IntTy.toInt IntTy.i8 byte.toNat)) =
      IntTy.toInt IntTy.i8 byte.toNat := hti
  rw [hti', key]


/-- Prefix of `tobj_scan_int` in the cursor layout: whitespace skip and `p = *pp`. -/
theorem si_pre (m : Mem) (cc bb ob : Nat) (bytes : Block) (pos e : Nat) (tail : Block)
    (hne : cc ≠ bb) (hbb : m bb = some bytes)
    (hcc : m cc = some (encodeLE 8 (ptrPack (.ptr bb pos)) ++ tail))
    (hpos : pos ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296) :
    let s0 : State := ⟨frameLocals Gen.tobj_scan_int.params
        [.ptr cc 0, .ptr bb e, .ptr ob 0], m, false⟩
    ∃ s1 s2 : State, ExS Gen.prog s0 (.call none 23 [.var 0, .var 1]) .normal s1 ∧
      ExS Gen.prog s1 (.set 3 (.load .ptr (.var 0))) .normal s2 ∧
      (∀ i, i ≠ 3 → s2.locals i = s0.locals i) ∧
      s2.locals 3 = some (.ptr bb (skipStop (bytes.take e) pos)) ∧
      s2.ro = false ∧
      s2.mem = m.upd cc (encodeLE 8 (ptrPack (.ptr bb (skipStop (bytes.take e) pos))) ++ tail) := by
  intro s0
  have l0 : s0.locals 0 = some (.ptr cc 0) := by
    simp [s0, frameLocals, Gen.tobj_scan_int, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.ptr bb e) := by
    simp [s0, frameLocals, Gen.tobj_scan_int, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hargs := EvArgs.cons (p := Gen.prog) (EvE.var l0) (EvArgs.cons (EvE.var l1) EvArgs.nil)
  obtain ⟨sk, hbody, hmem⟩ := skip_space_exs m cc bb bytes pos e tail hne hbb hcc hpos he hb32
    hlen32
  have hcall := ExS.call (p := Gen.prog) (s := s0) (f := 23) (fn := Gen.tobj_skip_space)
    (vs := [.ptr cc 0, .ptr bb e]) (o := .normal) (s' := sk) hargs (by rfl) (by rfl)
    hbody (Or.inl rfl)
  let s1 : State := { s0 with mem := sk.mem }
  have hseLen' : (bytes.take e).length = e := by simp [List.length_take, he]
  have hskip32 : skipStop (bytes.take e) pos < 4294967296 := by
    have hst := skipStop_le (bytes.take e) pos (by simpa [hseLen'] using hpos)
    rw [hseLen'] at hst
    omega
  have hld : EvE Gen.prog s1 (.load .ptr (.var 0)) (.ptr bb (skipStop (bytes.take e) pos)) := by
    apply EvE.load (EvE.var (by simpa [s1] using l0))
    apply load_ptr_cell s1.mem cc bb (skipStop (bytes.take e) pos) tail _ hb32 hskip32
    show sk.mem cc = _
    rw [hmem]; exact Mem.upd_same _ _ _
  have hset := ExS.set (p := Gen.prog) (i := 3) hld
  exact ⟨s1, { s1 with locals := s1.locals.upd 3 (.ptr bb (skipStop (bytes.take e) pos)) },
    hcall, hset, fun i hi => by simp [s1, Locals.upd, hi], by simp [s1, Locals.upd],
    rfl, by simpa [s1] using hmem⟩


def siSign : Stmt :=
  (.ite (.lor (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3)))
      (.const (.int ⟨32, true⟩ 43)))
    (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3)))
      (.const (.int ⟨32, true⟩ 45))))
    (.seq (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3)))
      (.const (.int ⟨32, true⟩ 45))) (.set 4 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) .skip)
      (.set 3 (.index (.var 3) (.const (.int ⟨64, true⟩ 1)) 1))) .skip)

theorem neg_one_eval : evalUn .neg ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (.int i32 4294967295) := by
  simp [evalUn, intOf, arith, IntTy.toInt, IntTy.wrap, IntTy.modulus, IntTy.inRange, IntTy.minVal,
    IntTy.maxVal, i32, Res.bind]

theorem si_sign (s : State) (bb stop e : Nat) (bytes : Block) (b : UInt8)
    (hlt : stop < e) (he : e ≤ bytes.length) (hlen : e < 4294967296)
    (l3 : s.locals 3 = some (.ptr bb stop)) (l4 : s.locals 4 = some (.int i32 1))
    (hm : s.mem bb = some bytes) (hb : bytes[stop]? = some b) :
    ∃ s', ExS Gen.prog s siSign .normal s' ∧
      s'.locals 3 = some (.ptr bb (p1Of (bytes.take e) stop)) ∧
      s'.locals 4 = some (.int i32 (if negB (bytes.take e) stop = true then 4294967295 else 1)) ∧
      (∀ i, i ≠ 3 → i ≠ 4 → s'.locals i = s.locals i) ∧ s'.mem = s.mem ∧ s'.ro = s.ro := by
  have hlt' : stop < bytes.length := by omega
  have hbt : (bytes.take e)[stop]? = some b := by
    rw [List.getElem?_take_of_lt hlt]; exact hb
  have hv3 : EvE Gen.prog s (.var 3) (.ptr bb stop) := EvE.var l3
  have e43 := byte_eq_eval s (.var 3) bb stop bytes b 43 (by omega) hv3 hm hlt' hb
  have e45 := byte_eq_eval s (.var 3) bb stop bytes b 45 (by omega) hv3 hm hlt' hb
  have hidx : EvE Gen.prog s (.index (.var 3) (.const (.int ⟨64, true⟩ 1)) 1) (.ptr bb (stop + 1)) := by
    apply EvE.index hv3 (EvE.const _)
    have h1 : IntTy.toInt ⟨64, true⟩ 1 = 1 := by simp [IntTy.toInt, IntTy.modulus]
    simp [IntTy.signed, ptrAdd, hm, h1]
    omega
  by_cases h43 : b.toNat = 43
  · have hl : EvE Gen.prog s (.lor (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
        (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 43)))
      (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3)))
        (.const (.int ⟨32, true⟩ 45)))) (boolVal true) :=
      EvE.lor_true e43 (by simp [truthy, boolVal, h43])
    have hn45 : EvE Gen.prog s (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
        (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 45))) (boolVal false) := by
      have := e45; simpa [h43] using this
    have hinner : ExS Gen.prog s (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
        (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 45)))
        (.set 4 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) .skip) .normal s :=
      ExS.ite hn45 (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.skip (p := Gen.prog) (s := s)))
    have hset3 := ExS.set (p := Gen.prog) (i := 3) hidx
    refine ⟨{ s with locals := s.locals.upd 3 (.ptr bb (stop + 1)) }, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · unfold siSign
      exact ExS.ite hl (bc := true) (by simp [truthy, boolVal])
        (by simpa using ExS.seq hinner hset3)
    · simp [Locals.upd, p1Of, hasSignB, hbt, h43]
    · simp [Locals.upd, negB, hbt, h43, l4]
    · intro i h3 _; simp [Locals.upd, h3]
  · by_cases h45 : b.toNat = 45
    · have hl : EvE Gen.prog s (.lor (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
          (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 43)))
        (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3)))
          (.const (.int ⟨32, true⟩ 45)))) (boolVal true) := by
        apply EvE.lor_false (bb := true) (by simpa [h43] using e43) (by simp [truthy, boolVal, h43])
          (by simpa [h45] using e45) (by simp [truthy, boolVal, h45])
      have hset4 := ExS.set (p := Gen.prog) (s := s) (i := 4)
        (EvE.un (EvE.const (.int ⟨32, true⟩ 1)) neg_one_eval)
      let sa : State := { s with locals := s.locals.upd 4 (.int i32 4294967295) }
      have hinner : ExS Gen.prog s (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
          (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 45)))
          (.set 4 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) .skip) .normal sa :=
        ExS.ite (by simpa [h45] using e45) (bc := true) (by simp [truthy, boolVal, h45])
          (by simpa using hset4)
      have hidxa : EvE Gen.prog sa (.index (.var 3) (.const (.int ⟨64, true⟩ 1)) 1)
          (.ptr bb (stop + 1)) := by
        apply EvE.index (EvE.var (by simpa [sa, Locals.upd] using l3)) (EvE.const _)
        have h1 : IntTy.toInt ⟨64, true⟩ 1 = 1 := by simp [IntTy.toInt, IntTy.modulus]
        have hma : sa.mem bb = some bytes := hm
        simp [IntTy.signed, ptrAdd, hma, h1]
        omega
      have hset3 := ExS.set (p := Gen.prog) (s := sa) (i := 3) hidxa
      refine ⟨{ sa with locals := sa.locals.upd 3 (.ptr bb (stop + 1)) }, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · unfold siSign
        exact ExS.ite hl (bc := true) (by simp [truthy, boolVal])
          (by simpa using ExS.seq hinner hset3)
      · simp [Locals.upd, p1Of, hasSignB, hbt, h45]
      · simp [sa, Locals.upd, negB, hbt, h45]
      · intro i h3 h4; simp [sa, Locals.upd, h3, h4]
    · have hl : EvE Gen.prog s (.lor (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
          (.load (.int ⟨8, true⟩) (.var 3))) (.const (.int ⟨32, true⟩ 43)))
        (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, true⟩) (.var 3)))
          (.const (.int ⟨32, true⟩ 45)))) (boolVal false) := by
        apply EvE.lor_false (bb := false) (by simpa [h43] using e43) (by simp [truthy, boolVal, h43])
          (by simpa [h45] using e45) (by simp [truthy, boolVal, h45])
      refine ⟨s, ?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl⟩
      · unfold siSign
        exact ExS.ite hl (bc := false) (by simp [truthy, boolVal])
          (by simpa using (ExS.skip (p := Gen.prog) (s := s)))
      · simp [p1Of, hasSignB, hbt, h43, h45, l3]
      · simp [negB, hbt, h45, l4]


def siVal : Expr :=
  (.cast ⟨32, true⟩ (.cond (.bin .lt (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
    (.un .neg ⟨64, true⟩ (.var 5)) (.var 5)))

theorem cast_i32_of_i64 (z : Int) (h64 : -9223372036854775808 ≤ z ∧ z ≤ 9223372036854775807) :
    evalCast ⟨32, true⟩ (.int i64 (IntTy.wrap IntTy.i64 z)) =
      .ok (.int i32 (IntTy.wrap IntTy.i32 z)) := by
  have := toInt_i64_wrap z h64
  simp only [evalCast]
  have h2 : (i64).signed = true := rfl
  simp [h2]
  refine ⟨rfl, ?_⟩
  show IntTy.wrap IntTy.i32 (IntTy.toInt IntTy.i64 (IntTy.wrap IntTy.i64 z)) = _
  rw [this]

theorem si_value (st : State) (acc : Nat) (neg : Bool) (hacc : acc ≤ 2147483647)
    (l4 : st.locals 4 = some (.int i32 (if neg then 4294967295 else 1)))
    (l5 : st.locals 5 = some (.int i64 acc)) :
    EvE Gen.prog st siVal (.int i32 (IntTy.wrap IntTy.i32 (if neg then -(acc : Int) else (acc : Int)))) := by
  have hv4 : EvE Gen.prog st (.var 4) (.int i32 (if neg then 4294967295 else 1)) := EvE.var l4
  have hv5 : EvE Gen.prog st (.var 5) (.int i64 acc) := EvE.var l5
  have hlt : EvE Gen.prog st (.bin .lt (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
      (boolVal neg) := by
    apply EvE.bin hv4 (EvE.const _)
    cases neg <;> simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.toInt, IntTy.modulus,
      boolVal, Res.bind]
  have hw : IntTy.wrap IntTy.i64 (acc : Int) = acc := by
    simp [IntTy.wrap, IntTy.modulus, IntTy.i64]; omega
  unfold siVal
  cases neg with
  | false =>
    have := cast_i32_of_i64 (acc : Int) (by omega)
    rw [hw] at this
    apply EvE.cast (EvE.cond hlt (bc := false) (by simp [truthy, boolVal]) (by simpa using hv5))
    simpa using this
  | true =>
    have hneg : EvE Gen.prog st (.un .neg ⟨64, true⟩ (.var 5))
        (.int i64 (IntTy.wrap IntTy.i64 (-(acc : Int)))) := by
      apply EvE.un hv5
      have h1 : IntTy.toInt IntTy.i64 acc = acc := by
        simp [IntTy.toInt, IntTy.modulus, IntTy.i64]; omega
      have h1' : IntTy.toInt ⟨64, true⟩ acc = acc := h1
      simp [evalUn, intOf, arith, Res.bind, h1', IntTy.inRange, IntTy.minVal, IntTy.maxVal, i64]
      rw [if_pos (by omega)]
      rfl
    have := cast_i32_of_i64 (-(acc : Int)) (by omega)
    apply EvE.cast (EvE.cond hlt (bc := true) (by simp [truthy, boolVal]) (by simpa using hneg))
    simpa using this


theorem takeWhile_map_digit (bs : List UInt8) :
    (bs.map UInt8.toNat).takeWhile scanDigit =
      (bs.takeWhile (fun b => scanDigit b.toNat)).map UInt8.toNat := by
  induction bs with
  | nil => rfl
  | cons h t ih =>
    by_cases hs : scanDigit h.toNat = true
    · simp [hs, ih]
    · simp [hs]

theorem pure_succ (bytes : Block) (p1 : Nat) (neg : Bool) (stop : Nat) (x : UInt8)
    (hx : bytes[p1]? = some x) (hdig : scanDigit x.toNat = true) :
    let Ld := (bytes.drop p1).takeWhile (fun b : UInt8 => scanDigit b.toNat)
    let ds := Ld.map UInt8.toNat
    scanIntDigits ((bytes.drop p1).map UInt8.toNat) neg p1 stop =
      (true, (if neg then -((pfold ds Ld.length).1 : Int) else ((pfold ds Ld.length).1 : Int)),
        p1 + Ld.length) := by
  intro Ld ds
  have hlt : p1 < bytes.length := (List.getElem?_eq_some_iff.mp hx).1
  have hd : bytes.drop p1 = x :: bytes.drop (p1 + 1) := by
    rw [List.drop_eq_getElem_cons hlt]
    have := List.getElem?_eq_getElem hlt
    rw [this] at hx
    rw [Option.some.inj hx]
  have hL : (bytes.drop p1).map UInt8.toNat = x.toNat :: (bytes.drop (p1 + 1)).map UInt8.toNat := by
    rw [hd]; rfl
  have hcnt : (scanDigits ((bytes.drop p1).map UInt8.toNat) 0).1 = Ld.length := by
    rw [scanDigits_count_exact, takeWhile_map_digit]; simp [Ld]
  have hval : (scanDigits ((bytes.drop p1).map UInt8.toNat) 0).2 = (pfold ds Ld.length).1 := by
    rw [← scanCLoopFold_scanDigits]
    unfold scanCLoopFold pfold
    rw [takeWhile_map_digit, List.take_of_length_le (by simp [ds])]
  rw [hL]
  unfold scanIntDigits
  simp only [hdig, if_true]
  rw [← hL]
  simp only [scanIntSignedValue, hcnt, hval]


theorem Mem.upd_comm' (m : Mem) (a b : Nat) (x y : Block) (h : a ≠ b) :
    (m.upd a x).upd b y = (m.upd b y).upd a x := by
  funext z
  by_cases hz : z = b <;> by_cases hz' : z = a <;> simp [Mem.upd, hz, hz'] <;> omega

/-- `tobj_scan_int` in the loader's cursor layout, failure part: returns false at the
    start-of-token offset `stop`, leaving the cursor cell there and the output untouched. -/
theorem scan_int_cursor_failure (m : Mem) (cc bb ob : Nat) (bytes : Block) (pos e : Nat) (tail : Block)
    (hne : cc ≠ bb) (hbb : m bb = some bytes)
    (hcc : m cc = some (encodeLE 8 (ptrPack (.ptr bb pos)) ++ tail))
    (hpos : pos ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296)
    {value : Int} {cursor : Nat}
    (hpure : scanInt ((bytes.take e).map UInt8.toNat) pos = (false, value, cursor)) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_scan_int.params
        [.ptr cc 0, .ptr bb e, .ptr ob 0], m, false⟩ Gen.tobj_scan_int.body
        (.ret (some (.int ⟨8, false⟩ 0))) s' ∧
      s'.mem = m.upd cc (encodeLE 8 (ptrPack (.ptr bb cursor)) ++ tail) := by
  obtain ⟨s1, s2, hc1, hs2, hl2, l3, hro2, hm2⟩ := si_pre m cc bb ob bytes pos e tail hne hbb hcc hpos he hb32 hlen32
  let stop := skipStop (bytes.take e) pos
  have hseLen : (bytes.take e).length = e := by simp [List.length_take, he]
  have hstopLe : stop ≤ e := by
    have := skipStop_le (bytes.take e) pos (by simpa [hseLen] using hpos)
    rwa [hseLen] at this
  have hstopLe' : stop ≤ bytes.length := by omega
  have hc := scanInt_failure_contract ((bytes.take e).map UInt8.toNat) pos hpure
  have hcstop : cursor = stop := by
    have := hc.2
    rw [← List.map_drop, takeWhile_map_space] at this
    simpa [stop, skipStop] using this
  have l0 : s2.locals 0 = some (.ptr cc 0) := by
    rw [hl2 0 (by omega)]
    simp [frameLocals, Gen.tobj_scan_int, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s2.locals 1 = some (.ptr bb e) := by
    rw [hl2 1 (by omega)]
    simp [frameLocals, Gen.tobj_scan_int, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l4n : ∀ st : State, True := fun _ => trivial
  have hv3 : EvE Gen.prog s2 (.var 3) (.ptr bb stop) := EvE.var l3
  have hv1 : EvE Gen.prog s2 (.var 1) (.ptr bb e) := EvE.var l1
  have hfalseV : EvE Gen.prog s2 (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
      (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 0) :=
    EvE.cond (EvE.const _) (bc := false) (by simp [truthy]) (EvE.const _)
  by_cases hend : stop < e
  · have hge : EvE Gen.prog s2 (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
      apply EvE.bin hv3 hv1
      simp [evalBin, isPtr, boolVal, hend]
    have hif1 : ExS Gen.prog s2 (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
          (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s2 :=
      ExS.ite hge (bc := false) (by simp [truthy, boolVal])
        (by simpa using (ExS.skip (p := Gen.prog) (s := s2)))
    have hset4 := ExS.set (p := Gen.prog) (s := s2) (i := 4) (EvE.const (.int ⟨32, true⟩ 1))
    let s3 : State := { s2 with locals := s2.locals.upd 4 (.int ⟨32, true⟩ 1) }
    have hm3 : s3.mem bb = some bytes := by
      show s2.mem bb = _
      rw [hm2]; show (m.upd cc _) bb = _
      rw [Mem.upd_ne _ _ (Ne.symm hne)]; exact hbb
    obtain ⟨b, hb⟩ : ∃ b, bytes[stop]? = some b := by
      have hend' : stop < bytes.length := by omega
      exact ⟨bytes[stop]'hend', List.getElem?_eq_getElem hend'⟩
    obtain ⟨s4, hsign, l3_4, l4_4, hoth, hm4, hro4⟩ := si_sign s3 bb stop e bytes b hend he hlen32
      (by simpa [s3, Locals.upd] using l3) (by simp [s3, Locals.upd, i32]) hm3 hb
    have l1_4 : s4.locals 1 = some (.ptr bb e) := by
      rw [hoth 1 (by omega) (by omega)]; simpa [s3, Locals.upd] using l1
    have hv3_4 : EvE Gen.prog s4 (.var 3) (.ptr bb (p1Of (bytes.take e) stop)) := EvE.var l3_4
    have hv1_4 : EvE Gen.prog s4 (.var 1) (.ptr bb e) := EvE.var l1_4
    have hm4' : s4.mem bb = some bytes := by rw [hm4]; exact hm3
    have hm4c : s4.mem = m.upd cc (encodeLE 8 (ptrPack (.ptr bb stop)) ++ tail) := by
      rw [hm4]; exact hm2
    have hfin : ∀ (hr : ExS Gen.prog s4 (.ite (.lor (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.un .lnot ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))])))
        (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
          (.const (.int ⟨8, false⟩ 0))))) .skip) (.ret (some (.int ⟨8, false⟩ 0))) s4),
        ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_scan_int.params
          [.ptr cc 0, .ptr bb e, .ptr ob 0], m, false⟩ Gen.tobj_scan_int.body
          (.ret (some (.int ⟨8, false⟩ 0))) s' ∧
          s'.mem = m.upd cc (encodeLE 8 (ptrPack (.ptr bb cursor)) ++ tail) := by
      intro hr
      refine ⟨s4, ExS.seq hc1 (ExS.seq hs2 (ExS.seq hif1 (ExS.seq hset4 (ExS.seq hsign
        (ExS.seq_ret hr))))), ?_⟩
      rw [hm4c, hcstop]
    have hfv : EvE Gen.prog s4 (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
        (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 0) :=
      EvE.cond (EvE.const _) (bc := false) (by simp [truthy]) (EvE.const _)
    have hp1Le : p1Of (bytes.take e) stop ≤ e := by
      unfold p1Of
      by_cases hs : hasSignB (bytes.take e) stop = true <;> simp [hs] <;> omega
    by_cases hp : p1Of (bytes.take e) stop < e
    · obtain ⟨x, hx⟩ : ∃ x, bytes[p1Of (bytes.take e) stop]? = some x := by
        have hp' : p1Of (bytes.take e) stop < bytes.length := by omega
        exact ⟨bytes[p1Of (bytes.take e) stop]'hp', List.getElem?_eq_getElem hp'⟩
      by_cases hd : scanDigit x.toNat = true
      · exfalso
        rw [scanInt_eq2] at hpure
        have hxs : (bytes.take e)[p1Of (bytes.take e) stop]? = some x := by
          rw [List.getElem?_take_of_lt hp]; exact hx
        have hpc := pure_succ (bytes.take e) (p1Of (bytes.take e) stop)
          (negB (bytes.take e) stop) stop x hxs hd
        rw [hpc] at hpure
        simp at hpure
      · have hd' : scanDigit x.toNat = false := by simpa using hd
        have hge2 : EvE Gen.prog s4 (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
          apply EvE.bin hv3_4 hv1_4
          simp [evalBin, isPtr, boolVal, hp]
        have hcall := isDigit_call_raw s4 (.var 3) bb (p1Of (bytes.take e) stop) bytes x hv3_4 hm4' (by omega) hx
        rw [hd'] at hcall
        simp only [Bool.false_eq_true, if_false] at hcall
        have hnot : EvE Gen.prog s4 (.un .lnot ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩)
            (.var 3))])) (boolVal true) :=
          EvE.un hcall (by simp [evalUn, truthy, boolVal])
        have hor := EvE.lor_false (bb := true) hge2 (by simp [truthy, boolVal]) hnot
          (by simp [truthy, boolVal])
        exact hfin (ExS.ite hor (bc := true) (by simp [truthy, boolVal]) (ExS.ret hfv))
    · have hge2 : EvE Gen.prog s4 (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
        apply EvE.bin hv3_4 hv1_4
        simp [evalBin, isPtr, boolVal]; omega
      have hor : EvE Gen.prog s4 (.lor (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
          (.un .lnot ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))]))) (boolVal true) :=
        EvE.lor_true hge2 (by simp [truthy, boolVal])
      exact hfin (ExS.ite hor (bc := true) (by simp [truthy, boolVal]) (ExS.ret hfv))
  · -- only whitespace: first check returns false
    have hge : EvE Gen.prog s2 (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal true) := by
      apply EvE.bin hv3 hv1
      simp [evalBin, isPtr, boolVal]; omega
    have hite : ExS Gen.prog s2 (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
        (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
          (.const (.int ⟨8, false⟩ 0))))) .skip) (.ret (some (.int ⟨8, false⟩ 0))) s2 :=
      ExS.ite hge (bc := true) (by simp [truthy, boolVal]) (ExS.ret hfalseV)
    refine ⟨s2, ExS.seq hc1 (ExS.seq hs2 (ExS.seq_ret hite)), ?_⟩
    rw [hm2, hcstop]


theorem succ_shape (bytes : Block) (pos : Nat) {v : Int} {c : Nat}
    (h : scanInt (bytes.map UInt8.toNat) pos = (true, v, c)) :
    ∃ x, bytes[p1Of bytes (skipStop bytes pos)]? = some x ∧ scanDigit x.toNat = true := by
  rw [scanInt_eq2] at h
  generalize hL : bytes.drop (p1Of bytes (skipStop bytes pos)) = L at h
  cases L with
  | nil => simp [scanIntDigits] at h
  | cons x tl =>
    refine ⟨x, ?_, ?_⟩
    · have : bytes[p1Of bytes (skipStop bytes pos)]? = (bytes.drop (p1Of bytes (skipStop bytes pos)))[0]? := by
        rw [List.getElem?_drop]; simp
      rw [this, hL]; rfl
    · by_cases hd : scanDigit x.toNat = true
      · exact hd
      · simp [scanIntDigits, hd] at h


theorem scan_int_cursor_success (m : Mem) (cc bb ob : Nat) (bytes : Block) (pos e : Nat)
    (tail oblk : Block)
    (hne : cc ≠ bb) (hne2 : ob ≠ cc) (hne3 : ob ≠ bb) (hbb : m bb = some bytes)
    (hcc : m cc = some (encodeLE 8 (ptrPack (.ptr bb pos)) ++ tail))
    (hob : m ob = some oblk) (hol : 4 ≤ oblk.length)
    (hpos : pos ≤ e) (he : e ≤ bytes.length) (hb32 : bb < 4294967295)
    (hlen32 : e < 4294967296)
    {value : Int} {cursor : Nat}
    (hpure : scanInt ((bytes.take e).map UInt8.toNat) pos = (true, value, cursor)) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tobj_scan_int.params
        [.ptr cc 0, .ptr bb e, .ptr ob 0], m, false⟩ Gen.tobj_scan_int.body
        (.ret (some (.int ⟨8, false⟩ 1))) s' ∧
      s'.mem = (m.upd cc (encodeLE 8 (ptrPack (.ptr bb cursor)) ++ tail)).upd ob
        (splice oblk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 value))) := by
  obtain ⟨s1, s2, hc1, hs2, hl2, l3, hro2, hm2⟩ := si_pre m cc bb ob bytes pos e tail hne hbb hcc hpos he hb32 hlen32
  have hseLen : (bytes.take e).length = e := by simp [List.length_take, he]
  let stop := skipStop (bytes.take e) pos
  have hstopLe : stop ≤ e := by
    have hst := skipStop_le (bytes.take e) pos (by simpa [hseLen] using hpos)
    rwa [hseLen] at hst
  have hstopLe' : stop ≤ bytes.length := by omega
  obtain ⟨x, hx, hdig⟩ := succ_shape (bytes.take e) pos hpure
  have hp1e : p1Of (bytes.take e) stop < e := by
    have hl : (bytes.take e).length = e := by simp [List.length_take, he]
    have := (List.getElem?_eq_some_iff.mp hx).1
    rwa [hl] at this
  have hp1lt : p1Of (bytes.take e) stop < bytes.length := by omega
  have hxB : bytes[p1Of (bytes.take e) stop]? = some x := by
    rw [← List.getElem?_take_of_lt hp1e]; exact hx
  have hp1ge : stop ≤ p1Of (bytes.take e) stop := by unfold p1Of; omega
  have hend : stop < e := by omega
  have l0 : s2.locals 0 = some (.ptr cc 0) := by
    rw [hl2 0 (by omega)]
    simp [frameLocals, Gen.tobj_scan_int, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s2.locals 1 = some (.ptr bb e) := by
    rw [hl2 1 (by omega)]
    simp [frameLocals, Gen.tobj_scan_int, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l2 : s2.locals 2 = some (.ptr ob 0) := by
    rw [hl2 2 (by omega)]
    simp [frameLocals, Gen.tobj_scan_int, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hv3 : EvE Gen.prog s2 (.var 3) (.ptr bb stop) := EvE.var l3
  have hv1 : EvE Gen.prog s2 (.var 1) (.ptr bb e) := EvE.var l1
  have hge : EvE Gen.prog s2 (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin hv3 hv1
    simp [evalBin, isPtr, boolVal, hend]
  have hif1 : ExS Gen.prog s2 (.ite (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
      (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
        (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s2 :=
    ExS.ite hge (bc := false) (by simp [truthy, boolVal])
      (by simpa using (ExS.skip (p := Gen.prog) (s := s2)))
  have hset4 := ExS.set (p := Gen.prog) (s := s2) (i := 4) (EvE.const (.int ⟨32, true⟩ 1))
  let s3 : State := { s2 with locals := s2.locals.upd 4 (.int ⟨32, true⟩ 1) }
  have hm3 : s3.mem bb = some bytes := by
    show s2.mem bb = _
    rw [hm2]; show (m.upd cc _) bb = _
    rw [Mem.upd_ne _ _ (Ne.symm hne)]; exact hbb
  have hend' : stop < bytes.length := by omega
  obtain ⟨b, hb⟩ : ∃ b, bytes[stop]? = some b :=
    ⟨bytes[stop]'hend', List.getElem?_eq_getElem hend'⟩
  obtain ⟨s4, hsign, l3_4, l4_4, hoth, hm4, hro4⟩ := si_sign s3 bb stop e bytes b hend he hlen32
    (by simpa [s3, Locals.upd] using l3) (by simp [s3, Locals.upd, i32]) hm3 hb
  have hm4c : s4.mem = m.upd cc (encodeLE 8 (ptrPack (.ptr bb stop)) ++ tail) := by
    rw [hm4]; exact hm2
  have hm4' : s4.mem bb = some bytes := by rw [hm4c]; show (m.upd cc _) bb = _; rw [Mem.upd_ne _ _ (Ne.symm hne)]; exact hbb
  have hro4' : s4.ro = false := by rw [hro4]; exact hro2
  have hl1_4 : s4.locals 1 = some (.ptr bb e) := by
    rw [hoth 1 (by omega) (by omega)]; simpa [s3, Locals.upd] using l1
  have hv3_4 : EvE Gen.prog s4 (.var 3) (.ptr bb (p1Of (bytes.take e) stop)) := EvE.var l3_4
  have hv1_4 : EvE Gen.prog s4 (.var 1) (.ptr bb e) := EvE.var hl1_4
  -- second guard: false
  have hge2 : EvE Gen.prog s4 (.bin .ge (some IntTy.u64) (.var 3) (.var 1)) (boolVal false) := by
    apply EvE.bin hv3_4 hv1_4
    simp [evalBin, isPtr, boolVal, hp1e]
  have hcall := isDigit_call_raw s4 (.var 3) bb (p1Of (bytes.take e) stop) bytes x hv3_4 hm4' hp1lt hxB
  rw [hdig] at hcall
  simp only [if_true] at hcall
  have hnot : EvE Gen.prog s4 (.un .lnot ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))]))
      (boolVal false) := EvE.un hcall (by simp [evalUn, truthy, boolVal])
  have hor := EvE.lor_false (bb := false) hge2 (by simp [truthy, boolVal]) hnot
    (by simp [truthy, boolVal])
  have hif2 : ExS Gen.prog s4 (.ite (.lor (.bin .ge (some IntTy.u64) (.var 3) (.var 1))
      (.un .lnot ⟨32, true⟩ (.call 7 [(.load (.int ⟨8, true⟩) (.var 3))])))
      (.ret (some (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
        (.const (.int ⟨8, false⟩ 0))))) .skip) .normal s4 :=
    ExS.ite hor (bc := false) (by simp [truthy, boolVal])
      (by simpa using (ExS.skip (p := Gen.prog) (s := s4)))
  have hset5 := ExS.set (p := Gen.prog) (s := s4) (i := 5)
    (EvE.cast (EvE.const (.int ⟨32, true⟩ 0)) (cast_i64_i32_const 0 (by omega)))
  let s5 : State := { s4 with locals := s4.locals.upd 5 (.int i64 0) }
  have hc0 : EvE Gen.prog s5 (.cond (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨8, false⟩ 1))
      (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 0) :=
    EvE.cond (EvE.const _) (bc := false) (by simp [truthy]) (EvE.const _)
  have hset6 := ExS.set (p := Gen.prog) (s := s5) (i := 6) hc0
  let s6 : State := { s5 with locals := s5.locals.upd 6 (.int ⟨8, false⟩ 0) }
  have hs6 : s6 = sdSt s4 bb (p1Of (bytes.take e) stop) 0 false := by
    simp only [s6, s5, sdSt, State.mk.injEq, and_true]
    funext i
    by_cases h3 : i = 3 <;> by_cases h5 : i = 5 <;> by_cases h6 : i = 6 <;>
      simp [Locals.upd, *, i64, IntTy.u8]
    all_goals (subst h3; exact l3_4)
  obtain ⟨sf, hloop, hsf⟩ := sd_loop s4 bb e (p1Of (bytes.take e) stop) bytes he
    (by unfold p1Of; split <;> omega) hl1_4 hm4'
  rw [← hs6] at hloop
  let Ld := ((bytes.take e).drop (p1Of (bytes.take e) stop)).takeWhile (fun b : UInt8 => scanDigit b.toNat)
  let ds := Ld.map UInt8.toNat
  obtain ⟨hacc, hsatinv⟩ := pfold_inv ds Ld.length
  have hl4f : sf.locals 4 = some (.int i32 (if negB (bytes.take e) stop = true then 4294967295 else 1)) := by
    rw [hsf]; simpa [sdSt, Locals.upd] using l4_4
  have hl5f : sf.locals 5 = some (.int i64 (pfold ds Ld.length).1) := by
    rw [hsf]; simp [sdSt, Locals.upd]; rfl
  have hval := si_value sf (pfold ds Ld.length).1 (negB (bytes.take e) stop) hacc hl4f hl5f
  have hl2f : sf.locals 2 = some (.ptr ob 0) := by
    rw [hsf]; simp [sdSt, Locals.upd]
    have := hoth 2 (by omega) (by omega)
    rw [this]; simpa [s3, Locals.upd] using l2
  have hv2 : EvE Gen.prog sf (.var 2) (.ptr ob 0) := EvE.var hl2f
  have hmf : sf.mem = m.upd cc (encodeLE 8 (ptrPack (.ptr bb stop)) ++ tail) := by
    rw [hsf]; exact hm4c
  have hobf : sf.mem ob = some oblk := by
    rw [hmf]; show (m.upd cc _) ob = _
    rw [Mem.upd_ne _ _ hne2]; exact hob
  have hst1 := store_int sf.mem ob 0 oblk hobf ⟨32, true⟩ (IntTy.wrap IntTy.i32 (if negB (bytes.take e) stop = true then -(((pfold ds Ld.length).1 : Nat) : Int) else (((pfold ds Ld.length).1 : Nat) : Int)))
    (by simp [IntTy.bytes]; omega)
  have hexs1 := ExS.store (p := Gen.prog) (s := sf) (ty := .int ⟨32, true⟩) hv2 hval
    (by rw [hsf]; exact hro4') (by simpa [IntTy.bytes, i32] using hst1)
  let sg : State := { sf with mem := (sf.mem.upd ob (splice oblk 0 (encodeLE 4 (IntTy.wrap IntTy.i32 (if negB (bytes.take e) stop = true then -(((pfold ds Ld.length).1 : Nat) : Int) else (((pfold ds Ld.length).1 : Nat) : Int)))))) }
  have hl0g : sg.locals 0 = some (.ptr cc 0) := by
    show sf.locals 0 = _
    rw [hsf]; simp [sdSt, Locals.upd]
    rw [hoth 0 (by omega) (by omega)]; simpa [s3, Locals.upd] using l0
  have hl3g : sg.locals 3 = some (.ptr bb (p1Of (bytes.take e) stop + Ld.length)) := by
    show sf.locals 3 = _
    rw [hsf]; simp [sdSt, Locals.upd]; rfl
  have hv0g : EvE Gen.prog sg (.var 0) (.ptr cc 0) := EvE.var hl0g
  have hv3g : EvE Gen.prog sg (.var 3) (.ptr bb (p1Of (bytes.take e) stop + Ld.length)) := EvE.var hl3g
  have hmg : sg.mem cc = some (encodeLE 8 (ptrPack (.ptr bb stop)) ++ tail) := by
    show (sf.mem.upd ob _) cc = _
    rw [Mem.upd_ne _ _ (Ne.symm hne2), hmf]; exact Mem.upd_same _ _ _
  have hst2 := store_ptr_cell sg.mem cc bb stop bb (p1Of (bytes.take e) stop + Ld.length) tail hmg
  have hexs2 := ExS.store (p := Gen.prog) (s := sg) (ty := .ptr) hv0g hv3g
    (by show sf.ro = false; rw [hsf]; exact hro4') hst2
  let sh : State := { sg with mem := (sg.mem.upd cc (encodeLE 8 (ptrPack (.ptr bb (p1Of (bytes.take e) stop + Ld.length))) ++ tail)) }
  have hret : EvE Gen.prog sh (.cond (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨8, false⟩ 1))
      (.const (.int ⟨8, false⟩ 0))) (.int ⟨8, false⟩ 1) :=
    EvE.cond (EvE.const _) (bc := true) (by simp [truthy]) (EvE.const _)
  -- pure side
  have hpure' := hpure
  rw [scanInt_eq2] at hpure'
  have hps := pure_succ (bytes.take e) (p1Of (bytes.take e) stop) (negB (bytes.take e) stop) stop x hx hdig
  simp only [stop] at hps hpure'
  rw [hps] at hpure'
  simp only [Prod.mk.injEq, true_and] at hpure'
  obtain ⟨hvv, hcc'⟩ := hpure'
  refine ⟨sh, ?_, ?_⟩
  · exact ExS.seq hc1 (ExS.seq hs2 (ExS.seq hif1 (ExS.seq hset4 (ExS.seq hsign (ExS.seq hif2
      (ExS.seq hset5 (ExS.seq hset6 (ExS.seq hloop (ExS.seq hexs1 (ExS.seq hexs2
        (ExS.ret hret)))))))))))
  · show (sg.mem.upd cc _) = _
    show ((sf.mem.upd ob _).upd cc _) = _
    rw [hmf, ← hcc', ← hvv]
    rw [Mem.upd_comm' _ _ _ _ _ (Ne.symm hne2), Mem.upd_upd]
    simp only [Ld, ds]
    first | rfl | exact (Mem.upd_comm' _ _ _ _ _ (Ne.symm hne2)).symm | exact Mem.upd_comm' _ _ _ _ _ hne2

end Obj.C.Proofs
