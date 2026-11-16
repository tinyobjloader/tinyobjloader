/-
  MiniC refinement of the translated `div_single_fill` (`lib/tess/src/exact.c`, the single-limb
  path of `zi_divrem`): it overwrites the `a.n` quotient limbs of the destination block with the limbs
  of `DivSingleModel.dsRun` (denoting `lv a / d`) and returns the remainder `lv a % d`.
  The destination content before the call is arbitrary (all limbs are overwritten).
-/
import Tess.C.DivSingleModel
import Tess.C.ShiftC

namespace Tess.C
open Obj.C

theorem evShl32 (x : Nat) (hx : x < 2 ^ 32) :
    evalBin .shl (some ⟨64, false⟩) (.int ⟨64, false⟩ x) (.int ⟨32, true⟩ 32) =
      .ok (.int ⟨64, false⟩ (x * 2 ^ 32)) := by
  have hlt : x * 2 ^ 32 < 2 ^ 64 := by
    calc x * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hx (by positivity)
      _ = 2 ^ 64 := by norm_num
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.modulus]
  have hm : x * 4294967296 % 18446744073709551616 = x * 4294967296 :=
    Nat.mod_eq_of_lt (by simpa using hlt)
  simp only [Obj.C.guard, if_true, Res.bind_ok, hm]

/-- Load of limb `j` of the source (struct = local 1) with counter local 4 holding `j + 1`. -/
theorem evLimbLoadA {sg : Int} (s : State) (zb vblk : Nat)
    (limbs : List Nat) (j : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length sg)) (hb : vblk < 4294967296)
    (hl : s.locals 1 = some (.ptr zb 0))
    (hl1 : s.locals 4 = some (.int ⟨64, false⟩ (j + 1)))
    (hlm : s.mem vblk = some (limbBytes limbs)) (hj : j < limbs.length)
    (hlt : ∀ x ∈ limbs, x < 2 ^ 32) :
    EvE LimbGen.prog s (.load (.int u32) (.index (.load .ptr (.field (.var 1) 0))
        (.bin .sub (some ⟨64, false⟩) (.var 4)
          (.cast u64 (.const (.int i32c 1)))) 4))
      (.int u32 (limbs[j]'hj)) := by
  have hfield : EvE LimbGen.prog s (.field (.var 1) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var 1) 0)) (.ptr vblk 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length sg hm hb)
  have hsub : EvE LimbGen.prog s (.bin .sub (some ⟨64, false⟩) (.var 4)
        (.cast u64 (.const (.int i32c 1)))) (.int ⟨64, false⟩ j) := by
    have h2 : EvE LimbGen.prog s (.var 4) (.int ⟨64, false⟩ (j + 1)) := EvE.var hl1
    have hc : EvE LimbGen.prog s (.const (.int i32c 1)) (.int i32c 1) := EvE.const _
    have hcast : evalCast u64 (.int i32c 1) = .ok (.int ⟨64, false⟩ 1) := rfl
    have hsub' : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ (j + 1)) (.int ⟨64, false⟩ 1) = .ok (.int ⟨64, false⟩ j) := rfl
    exact EvE.bin h2 (EvE.cast hc hcast) hsub'
  have hidxlen : (limbBytes limbs).length = 4 * limbs.length := limbBytes_length limbs
  have hbounds : 0 + j * 4 ≤ (limbBytes limbs).length := by
    rw [hidxlen]
    omega
  have hidx : EvE LimbGen.prog s
      (.index (.load .ptr (.field (.var 1) 0))
        (.bin .sub (some ⟨64, false⟩) (.var 4)
          (.cast u64 (.const (.int i32c 1)))) 4)
      (.ptr vblk (0 + j * 4)) := by
    apply EvE.index hloadPtr hsub
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, hlm]
    rw [if_pos hbounds]
  have hload : load s.mem (.int u32) (.ptr vblk (0 + j * 4)) = .ok (.int u32 (limbs[j]'hj)) := by
    have hl4 : 0 + j * 4 = 4 * j := Nat.zero_add _ |>.trans (Nat.mul_comm _ _)
    rw [hl4, load_limb s.mem vblk limbs j hlm hj]
    congr 1
    rw [Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hj))]
  exact EvE.load hidx hload

def dvBody : Stmt :=
  .ite (.var 4)
    (.seq (.set 5 (.bin .bor (some ⟨64, false⟩)
        (.bin .shl (some ⟨64, false⟩) (.var 3) (.const (.int ⟨32, true⟩ 32)))
        (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var 1) 0))
            (.bin .sub (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4)))))
      (.seq (.store (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var 0) 0))
            (.bin .sub (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4)
          (.cast ⟨32, false⟩ (.bin .div (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.var 2)))))
        (.set 3 (.bin .mod (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.var 2))))))
    .brk

def dvStep : Stmt :=
  .set 4 (.cast ⟨64, false⟩ (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
    (.const (.int ⟨64, false⟩ 1))))

theorem dvLoop_ast : LimbGen.div_single_fill_loop0 = .loop dvBody dvStep := rfl

/-- Loop simulation relation with `k` limbs still to process. -/
def dvInv (ts tarr as aarr : Nat) (a : List Nat) (d : Nat) (sg sga : Int) (k : Nat) (s : State) : Prop :=
  s.locals 0 = some (.ptr ts 0) ∧ s.locals 1 = some (.ptr as 0) ∧
  s.locals 2 = some (.int ⟨32, false⟩ d) ∧
  s.locals 3 = some (.int ⟨64, false⟩ (dsRun a d (a.length - k)).2) ∧
  s.locals 4 = some (.int ⟨64, false⟩ k) ∧ s.ro = false ∧
  s.mem ts = some (ziBlock tarr a.length sg) ∧
  s.mem as = some (ziBlock aarr a.length sga) ∧ s.mem aarr = some (limbBytes a) ∧
  (∃ pre : List Nat, pre.length = k ∧
    s.mem tarr = some (limbBytes (pre ++ (dsRun a d (a.length - k)).1))) ∧
  tarr ≠ aarr ∧ tarr ≠ ts ∧ tarr ≠ as ∧ ts < 4294967296 ∧ as < 4294967296 ∧ tarr < 4294967296 ∧
  aarr < 4294967296 ∧ 0 < d ∧ d < 4294967296 ∧ a.length < 18446744073709551616

theorem set_pre (pre Q : List Nat) (k v : Nat) (h : pre.length = k + 1) :
    (pre ++ Q).set k v = (pre.take k ++ [v]) ++ Q := by
  rw [List.set_append_left _ _ (by omega), List.set_eq_take_append_cons_drop]
  have : pre.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
  simp [this, show k < pre.length by omega]

theorem evDiv64 (x d : Nat) (hx : x < 2 ^ 64) (hd : 0 < d) (hd2 : d < 2 ^ 64) :
    evalBin .div (some ⟨64, false⟩) (.int ⟨64, false⟩ x) (.int ⟨64, false⟩ d) =
      .ok (.int ⟨64, false⟩ (x / d)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus]
  omega

theorem evMod64 (x d : Nat) (hx : x < 2 ^ 64) (hd : 0 < d) (hd2 : d < 2 ^ 64) :
    evalBin .mod (some ⟨64, false⟩) (.int ⟨64, false⟩ x) (.int ⟨64, false⟩ d) =
      .ok (.int ⟨64, false⟩ (x % d)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus]
  omega

theorem dvIter (ts tarr as aarr : Nat) (a : List Nat) (d : Nat) (sg sga : Int) (k : Nat)
    (s : State) (ha : ∀ x ∈ a, x < 2 ^ 32) (hk : k < a.length)
    (hInv : dvInv ts tarr as aarr a d sg sga (k + 1) s) :
    ∃ s1 s2, ExS LimbGen.prog s dvBody .normal s1 ∧ ExS LimbGen.prog s1 dvStep .normal s2 ∧
      dvInv ts tarr as aarr a d sg sga k s2 := by
  obtain ⟨l0, l1, l2, l3, l4, hro, hts, has, haarr, ⟨pre, hpre, htarr⟩, hne1, hne2, hne3, hb1, hb2,
    hb3, hb4, hd0, hd32, hlen64⟩ := hInv
  set n := a.length with hn
  have hj : n - (k + 1) ≤ n := by omega
  obtain ⟨hR, hQl, hQb, -⟩ := dsRun_props a d ha hd0 (n - (k + 1)) hj
  set R := (dsRun a d (n - (k + 1))).2 with hRdef
  set Q := (dsRun a d (n - (k + 1))).1 with hQdef
  have hxk : a[k]'hk < 2 ^ 32 := ha _ (List.getElem_mem hk)
  have hrun : dsRun a d (n - k) = dsStep d (a[k]'hk) (dsRun a d (n - (k + 1))) := by
    rw [show n - k = (n - (k + 1)) + 1 by omega]
    simp only [dsRun]
    have : n - 1 - (n - (k + 1)) = k := by omega
    rw [this]
    unfold ziAddTerm; rw [dif_pos hk]
  have hRlt32 : R < 2 ^ 32 := by have : d < 2 ^ 32 := hd32; omega
  have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
  have htr : truthy (.int ⟨64, false⟩ (k + 1)) = .ok true := by simp [truthy]
  -- value
  have hx := evLimbLoadA (sg := sga) s as aarr a k has hb4 l1 l4 haarr hk ha
  have hxc : EvE LimbGen.prog s (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
      (.index (.load .ptr (.field (.var 1) 0))
        (.bin .sub (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4)))
      (.int ⟨64, false⟩ (a[k]'hk)) :=
    EvE.cast hx (by
      show Res.ok (Val.int ⟨64, false⟩ (a[k]'hk % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hshl : EvE LimbGen.prog s (.bin .shl (some ⟨64, false⟩) (.var 3) (.const (.int ⟨32, true⟩ 32)))
      (.int ⟨64, false⟩ (R * 2 ^ 32)) := EvE.bin (EvE.var l3) (EvE.const _) (evShl32 R hRlt32)
  have hor : (R * 2 ^ 32) ||| a[k]'hk = R * 2 ^ 32 + a[k]'hk := by
    have h := sh_or_add R 32 (a[k]'hk) hxk
    rwa [Nat.shiftLeft_eq] at h
  have hvv : EvE LimbGen.prog s (.bin .bor (some ⟨64, false⟩)
      (.bin .shl (some ⟨64, false⟩) (.var 3) (.const (.int ⟨32, true⟩ 32)))
      (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
        (.index (.load .ptr (.field (.var 1) 0))
          (.bin .sub (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4))))
      (.int ⟨64, false⟩ (R * 2 ^ 32 + a[k]'hk)) := by
    rw [← hor]; exact EvE.bin hshl hxc rfl
  set vv := R * 2 ^ 32 + a[k]'hk with hvvdef
  have hvlt : vv < 2 ^ 64 := by
    have : vv < 2 ^ 32 * 2 ^ 32 := by rw [hvvdef]; nlinarith
    exact lt_of_lt_of_eq this (by norm_num)
  have hcomm : 2 ^ 32 * R + a[k]'hk = vv := by rw [hvvdef]; ring
  set s' : State := { s with locals := s.locals.upd 5 (.int ⟨64, false⟩ vv) } with hs'
  have hset5 := ExS.set (i := 5) hvv
  have s'_0 : s'.locals 0 = some (.ptr ts 0) := by simpa [hs', Locals.upd] using l0
  have s'_2 : s'.locals 2 = some (.int ⟨32, false⟩ d) := by simpa [hs', Locals.upd] using l2
  have s'_3 : s'.locals 3 = some (.int ⟨64, false⟩ R) := by simpa [hs', Locals.upd] using l3
  have s'_4 : s'.locals 4 = some (.int ⟨64, false⟩ (k + 1)) := by simpa [hs', Locals.upd] using l4
  have s'_5 : s'.locals 5 = some (.int ⟨64, false⟩ vv) := by simp [hs', Locals.upd]
  have s'_ts : s'.mem ts = some (ziBlock tarr n sg) := hts
  have s'_tarr : s'.mem tarr = some (limbBytes (pre ++ Q)) := htarr
  have hPQ : (pre ++ Q).length = n := by simp [hpre, hQl]; omega
  have hd64 : EvE LimbGen.prog s' (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ d) :=
    EvE.cast (EvE.var s'_2) (by
      show Res.ok (Val.int ⟨64, false⟩ (d % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hdiv : EvE LimbGen.prog s' (.bin .div (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.var 2)))
      (.int ⟨64, false⟩ (vv / d)) :=
    EvE.bin (EvE.var s'_5) hd64 (evDiv64 vv d hvlt hd0 (by omega))
  have hqlt : vv / d < 2 ^ 32 := by rw [← hcomm]; exact dsStep_lt d _ _ hd0 hxk hR
  have hval : EvE LimbGen.prog s' (.cast ⟨32, false⟩ (.bin .div (some ⟨64, false⟩) (.var 5)
      (.cast ⟨64, false⟩ (.var 2)))) (.int ⟨32, false⟩ (vv / d % 2 ^ 32)) :=
    EvE.cast hdiv rfl
  have hfld : EvE LimbGen.prog s' (.field (.var 0) 0) (.ptr ts 0) :=
    EvE.field (EvE.var s'_0) (by simp [ptrAddN, s'_ts, ziBlock_length])
  have hbase : EvE LimbGen.prog s' (.load .ptr (.field (.var 0) 0)) (.ptr tarr 0) :=
    EvE.load hfld (load_ziBlock_v s'.mem ts tarr n sg s'_ts hb3)
  have hsub : EvE LimbGen.prog s' (.bin .sub (some ⟨64, false⟩) (.var 4)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.int ⟨64, false⟩ k) := by
    have hc : EvE LimbGen.prog s' (.const (.int ⟨32, true⟩ 1)) (.int ⟨32, true⟩ 1) := EvE.const _
    have hcast : evalCast ⟨64, false⟩ (.int ⟨32, true⟩ 1) = .ok (.int ⟨64, false⟩ 1) := rfl
    have hsub' : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ (k + 1)) (.int ⟨64, false⟩ 1) =
        .ok (.int ⟨64, false⟩ k) := rfl
    exact EvE.bin (EvE.var s'_4) (EvE.cast hc hcast) hsub'
  have hidxe : EvE LimbGen.prog s' (.index (.load .ptr (.field (.var 0) 0))
      (.bin .sub (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 1)))) 4)
      (.ptr tarr (4 * k)) := by
    apply EvE.index hbase hsub
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, s'_tarr]
    have hbl := limbBytes_length (pre ++ Q)
    rw [if_pos (by rw [hbl, hPQ]; omega)]
    congr 2
    omega
  have hstoreEq := store_limb s'.mem tarr (pre ++ Q) k (vv / d % 2 ^ 32) s'_tarr (by rw [hPQ]; omega)
  have hst := ExS.store (ty := .int ⟨32, false⟩) hidxe hval hro hstoreEq
  set s'' : State := { s' with mem := s'.mem.upd tarr (limbBytes ((pre ++ Q).set k (vv / d % 2 ^ 32))) }
    with hs''
  have s''_2 : s''.locals 2 = some (.int ⟨32, false⟩ d) := s'_2
  have s''_5 : s''.locals 5 = some (.int ⟨64, false⟩ vv) := s'_5
  have hmod : EvE LimbGen.prog s'' (.bin .mod (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.var 2)))
      (.int ⟨64, false⟩ (vv % d)) :=
    EvE.bin (EvE.var s''_5) (EvE.cast (EvE.var s''_2) (by
      show Res.ok (Val.int ⟨64, false⟩ (d % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])) (evMod64 vv d hvlt hd0 (by omega))
  have hset3 := ExS.set (i := 3) hmod
  set s3 : State := { s'' with locals := s''.locals.upd 3 (.int ⟨64, false⟩ (vv % d)) } with hs3
  have hbody : ExS LimbGen.prog s dvBody .normal s3 := by
    unfold dvBody
    exact ExS.ite (EvE.var l4) htr (ExS.seq hset5 (ExS.seq hst hset3))
  have s3_4 : s3.locals 4 = some (.int ⟨64, false⟩ (k + 1)) := by
    simpa [hs3, hs'', Locals.upd] using s'_4
  have cast1 : EvE LimbGen.prog s3 (.cast ⟨64, false⟩ (.var 4)) (.int ⟨64, false⟩ (k + 1)) :=
    EvE.cast (EvE.var s3_4) (cast_u64_u64' (k + 1) (by omega))
  have hsub1 : EvE LimbGen.prog s3 (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
      (.const (.int ⟨64, false⟩ 1))) (.int ⟨64, false⟩ k) :=
    EvE.bin cast1 (EvE.const _) rfl
  have hstep : ExS LimbGen.prog s3 dvStep .normal
      { s3 with locals := s3.locals.upd 4 (.int ⟨64, false⟩ k) } := by
    unfold dvStep
    exact ExS.set (EvE.cast hsub1 (cast_u64_u64' k (by omega)))
  refine ⟨s3, _, hbody, hstep, ?_⟩
  have hm4 : ∀ b, b ≠ tarr → (s.mem.upd tarr (limbBytes ((pre ++ Q).set k (vv / d % 2 ^ 32)))) b = s.mem b := by
    intro b hb; simp [Mem.upd, hb]
  have hdsr : dsRun a d (n - k) = ((2 ^ 32 * R + a[k]'hk) / d :: Q, (2 ^ 32 * R + a[k]'hk) % d) := by
    rw [hrun]; rfl
  rw [hcomm] at hdsr
  refine ⟨?_, ?_, ?_, ?_, ?_, hro, ?_, ?_, ?_, ?_, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hd0, hd32, hlen64⟩
  · simpa [hs3, hs'', hs', Locals.upd] using l0
  · simpa [hs3, hs'', hs', Locals.upd] using l1
  · simpa [hs3, hs'', hs', Locals.upd] using l2
  · simp [hs3, hs'', hs', Locals.upd]
    show vv % d = (dsRun a d (n - k)).2
    rw [hdsr]
  · simp [hs3, hs'', hs', Locals.upd]
  · show (s.mem.upd tarr _) ts = _
    rw [hm4 ts (Ne.symm hne2)]; exact hts
  · show (s.mem.upd tarr _) as = _
    rw [hm4 as (Ne.symm hne3)]; exact has
  · show (s.mem.upd tarr _) aarr = _
    rw [hm4 aarr (Ne.symm hne1)]; exact haarr
  · refine ⟨pre.take k, by simp [hpre], ?_⟩
    show (s.mem.upd tarr _) tarr = _
    simp only [Mem.upd, ite_true]
    rw [set_pre pre Q k _ hpre, hdsr, Nat.mod_eq_of_lt hqlt]
    simp

theorem dvLoop (ts tarr as aarr : Nat) (a : List Nat) (d : Nat) (sg sga : Int)
    (ha : ∀ x ∈ a, x < 2 ^ 32) :
    ∀ k : Nat, k ≤ a.length → ∀ s : State, dvInv ts tarr as aarr a d sg sga k s →
      ∃ sf, ExS LimbGen.prog s LimbGen.div_single_fill_loop0 .normal sf ∧
        dvInv ts tarr as aarr a d sg sga 0 sf := by
  intro k
  induction k with
  | zero =>
      intro _ s hInv
      refine ⟨s, ?_, hInv⟩
      rw [dvLoop_ast]
      have l4 := hInv.2.2.2.2.1
      apply ExS.loop_brk
      unfold dvBody
      exact ExS.ite (EvE.var l4) (show truthy (.int ⟨64, false⟩ 0) = .ok false by simp [truthy]) ExS.brk
  | succ k ih =>
      intro hk s hInv
      obtain ⟨s1, s2, hb, hs, hInv2⟩ := dvIter ts tarr as aarr a d sg sga k s ha (by omega) hInv
      obtain ⟨sf, hl, hfin⟩ := ih (by omega) s2 hInv2
      refine ⟨sf, ?_, hfin⟩
      rw [dvLoop_ast]
      rw [dvLoop_ast] at hl
      exact ExS.loop_next hb (Or.inl rfl) hs hl

/-- `div_single_fill` fills the quotient limbs `dsRun` and returns the remainder `lv a % d`. -/
theorem div_single_fill_refines (ts tarr as aarr : Nat) (a junk : List Nat) (d : Nat) (sg sga : Int)
    (m : Mem) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.div_single_fill.params
      [.ptr ts 0, .ptr as 0, .int ⟨32, false⟩ d], m, false⟩)
    (ha : ∀ x ∈ a, x < 2 ^ 32)
    (hts : m ts = some (ziBlock tarr a.length sg))
    (has : m as = some (ziBlock aarr a.length sga)) (haarr : m aarr = some (limbBytes a))
    (hjunk : junk.length = a.length) (htarr : m tarr = some (limbBytes junk))
    (hne1 : tarr ≠ aarr) (hne2 : tarr ≠ ts) (hne3 : tarr ≠ as)
    (hb1 : ts < 4294967296) (hb2 : as < 4294967296) (hb3 : tarr < 4294967296)
    (hb4 : aarr < 4294967296) (hd0 : 0 < d) (hd32 : d < 4294967296)
    (hlen64 : a.length < 18446744073709551616) :
    ∃ sf s', ExS LimbGen.prog s0 LimbGen.div_single_fill.body
        (.ret (some (.int ⟨64, false⟩ (lv a % d)))) sf ∧
      s'.mem tarr = some (limbBytes (dsRun a d a.length).1) ∧ s'.mem ts = m ts ∧
      s'.mem as = m as ∧ s'.mem aarr = m aarr ∧ s' = sf := by
  have l0 : s0.locals 0 = some (.ptr ts 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.ptr as 0) := by rw [h0]; rfl
  have l2 : s0.locals 2 = some (.int ⟨32, false⟩ d) := by rw [h0]; rfl
  have hmem : s0.mem = m := by rw [h0]
  have hro : s0.ro = false := by rw [h0]
  have hset3 : ExS LimbGen.prog s0 (.set 3 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s0 with locals := s0.locals.upd 3 (.int ⟨64, false⟩ 0) } :=
    ExS.set (EvE.cast (EvE.const _) rfl)
  set s1 : State := { s0 with locals := s0.locals.upd 3 (.int ⟨64, false⟩ 0) } with hs1
  have hnload : EvE LimbGen.prog s1 (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.int ⟨64, false⟩ a.length) := by
    have hf : EvE LimbGen.prog s1 (.field (.var 1) 8) (.ptr as 8) :=
      EvE.field (EvE.var (by simpa [hs1, Locals.upd] using l1))
        (by simp [hs1, hmem, ptrAddN, has, ziBlock_length])
    have := load_ziBlock_n s1.mem as aarr a.length sga (by simpa [hs1, hmem] using has)
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hf this
  have hset4 := ExS.set (i := 4) hnload
  set s2 : State := { s1 with locals := s1.locals.upd 4 (.int ⟨64, false⟩ a.length) } with hs2
  have hInv0 : dvInv ts tarr as aarr a d sg sga a.length s2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hd0, hd32,
      hlen64⟩
    · simpa [hs2, hs1, Locals.upd] using l0
    · simpa [hs2, hs1, Locals.upd] using l1
    · simpa [hs2, hs1, Locals.upd] using l2
    · simp [hs2, hs1, Locals.upd, dsRun]
    · simp [hs2, hs1, Locals.upd]
    · simp [hs2, hs1, hro]
    · simp [hs2, hs1, hmem]; exact hts
    · simp [hs2, hs1, hmem]; exact has
    · simp [hs2, hs1, hmem]; exact haarr
    · exact ⟨junk, hjunk, by simp [hs2, hs1, hmem, dsRun, htarr]⟩
  obtain ⟨sf, hloop, hfin⟩ := dvLoop ts tarr as aarr a d sg sga ha a.length le_rfl s2 hInv0
  obtain ⟨-, -, -, l3', -, -, hts', has', haarr', ⟨pre, hpre, htarr'⟩, -, -, -, -, -, -, -, -, -, -⟩ := hfin
  have hres : (dsRun a d (a.length - 0)).2 = lv a % d := by
    rw [Nat.sub_zero]; exact (dsRun_final a d ha hd0).2
  rw [hres] at l3'
  have hpre0 : pre = [] := List.length_eq_zero_iff.mp (by simpa using hpre)
  subst hpre0
  refine ⟨sf, sf, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · unfold LimbGen.div_single_fill
    show ExS LimbGen.prog s0 (.seq _ (.seq (.seq _ LimbGen.div_single_fill_loop0) (.ret (some (.var 3))))) _ sf
    exact ExS.seq hset3 (ExS.seq (ExS.seq hset4 hloop) (ExS.ret (EvE.var l3')))
  · simpa [Nat.sub_zero] using htarr'
  · rw [hts', hts]
  · rw [has', has]
  · rw [haarr', haarr]

end Tess.C
