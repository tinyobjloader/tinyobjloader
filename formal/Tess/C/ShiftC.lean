/-
  MiniC refinement of the translated `shift_fill` (`lib/tess/src/exact.c`, the limb carry chain of
  `shift`): into a zeroed destination block of `a.n + bits/32 + 1` limbs it writes exactly the limbs of
  `ShiftModel.shiftLimbs`, i.e. a value `a * 2^bits`. The destination is the `t` of `shift`, freshly
  allocated and zero-initialized (precondition on the limb block).
-/
import Tess.C.ShiftModel
import Tess.C.TrimLen
import Tess.C.I64Import

namespace Tess.C
open Obj.C

/-- Loop simulation relation after `k` limbs. -/
def shInv (ts tarr as aarr : Nat) (a : List Nat) (bits : Nat) (sg sga : Int) (k : Nat) (s : State) : Prop :=
  s.locals 0 = some (.ptr ts 0) ∧ s.locals 1 = some (.ptr as 0) ∧
  s.locals 2 = some (.int ⟨32, false⟩ bits) ∧ s.locals 3 = some (.int ⟨64, false⟩ k) ∧
  s.locals 4 = some (.int ⟨64, false⟩ (shCarry a (bits % 32) k)) ∧ s.ro = false ∧
  s.mem ts = some (ziBlock tarr (a.length + bits / 32 + 1) sg) ∧
  s.mem as = some (ziBlock aarr a.length sga) ∧ s.mem aarr = some (limbBytes a) ∧
  s.mem tarr = some (limbBytes (List.replicate (bits / 32) 0 ++ shPrefix a (bits % 32) k ++
    List.replicate (a.length - k + 1) 0)) ∧
  tarr ≠ aarr ∧ tarr ≠ ts ∧ tarr ≠ as ∧ ts < 4294967296 ∧ as < 4294967296 ∧ tarr < 4294967296 ∧
  aarr < 4294967296 ∧ bits < 4294967296 ∧ a.length + bits / 32 + 1 < 18446744073709551616

/-- Load of limb `k` of the source with the index in local 3 (no `-1`). -/
theorem evLimbAt {sg : Int} (s : State) (zb vblk : Nat) (limbs : List Nat) (k : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length sg)) (hb : vblk < 4294967296)
    (hl : s.locals 1 = some (.ptr zb 0)) (hl3 : s.locals 3 = some (.int ⟨64, false⟩ k))
    (hlm : s.mem vblk = some (limbBytes limbs)) (hk : k < limbs.length)
    (hlt : ∀ x ∈ limbs, x < 2 ^ 32) :
    EvE LimbGen.prog s (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4))
      (.int ⟨32, false⟩ (limbs[k]'hk)) := by
  have hfield : EvE LimbGen.prog s (.field (.var 1) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var 1) 0)) (.ptr vblk 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length sg hm hb)
  have hidxlen : (limbBytes limbs).length = 4 * limbs.length := limbBytes_length limbs
  have hidx : EvE LimbGen.prog s (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)
      (.ptr vblk (0 + k * 4)) := by
    apply EvE.index hloadPtr (EvE.var hl3)
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, hlm]
    rw [if_pos (by omega)]
  have hload : load s.mem (.int u32) (.ptr vblk (0 + k * 4)) = .ok (.int u32 (limbs[k]'hk)) := by
    have hl4 : 0 + k * 4 = 4 * k := Nat.zero_add _ |>.trans (Nat.mul_comm _ _)
    rw [hl4, load_limb s.mem vblk limbs k hlm hk]
    congr 1
    rw [Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hk))]
  exact EvE.load hidx hload

theorem shT_set (q k n : Nat) (P : List Nat) (hP : P.length = k) (v : Nat) (hk : k < n) :
    (List.replicate q 0 ++ P ++ List.replicate (n - k + 1) 0).set (q + k) v =
      List.replicate q 0 ++ (P ++ [v]) ++ List.replicate (n - (k + 1) + 1) 0 := by
  have hn : n - k + 1 = (n - (k + 1) + 1) + 1 := by omega
  rw [hn, List.replicate_succ]
  have hlen : (List.replicate q 0 ++ P).length = q + k := by simp [hP]
  rw [List.set_append_right _ _ (by rw [hlen])]
  rw [hlen, Nat.sub_self]
  simp [List.append_assoc]

/-- Shift of a limb by `r < 32` bits as the C expression computes it: no truncation occurs. -/
theorem evShl64 (x r : Nat) (hx : x < 2 ^ 32) (hr : r < 32) :
    evalBin .shl (some ⟨64, false⟩) (.int ⟨64, false⟩ x) (.int ⟨32, false⟩ r) =
      .ok (.int ⟨64, false⟩ (x * 2 ^ r)) := by
  have hlt : x * 2 ^ r < 2 ^ 64 := by
    calc x * 2 ^ r < 2 ^ 32 * 2 ^ r := Nat.mul_lt_mul_of_pos_right hx (by positivity)
      _ ≤ 2 ^ 32 * 2 ^ 32 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr.le)
      _ = 2 ^ 64 := by norm_num
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.modulus]
  have h64 : decide (r < 64) = true := by simp; omega
  have hm : x * 2 ^ r % 18446744073709551616 = x * 2 ^ r := Nat.mod_eq_of_lt (by simpa using hlt)
  simp only [Obj.C.guard, h64, if_true, Res.bind_ok, hm]

/-- The loop body of `shift_fill`. -/
def shBody : Stmt :=
  .ite (.bin .lt (some ⟨64, false⟩) (.var 3) (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
    (.seq (.set 5 (.bin .bor (some ⟨64, false⟩)
        (.bin .shl (some ⟨64, false⟩)
          (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
            (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)))
          (.bin .mod (some ⟨32, false⟩) (.var 2) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))
        (.var 4)))
      (.seq (.store (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var 0) 0))
            (.bin .add (some ⟨64, false⟩) (.var 3)
              (.cast ⟨64, false⟩ (.bin .div (some ⟨32, false⟩) (.var 2)
                (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))) 4)
          (.cast ⟨32, false⟩ (.var 5)))
        (.set 4 (.bin .shr (some ⟨64, false⟩) (.var 5) (.const (.int ⟨32, true⟩ 32))))))
    .brk

def shStep : Stmt :=
  .set 3 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
    (.const (.int ⟨64, false⟩ 1))))

theorem shLoop_ast : LimbGen.shift_fill_loop0 = .loop shBody shStep := rfl

theorem shIter (ts tarr as aarr : Nat) (a : List Nat) (bits : Nat) (sg sga : Int) (k : Nat)
    (s : State) (ha : ∀ x ∈ a, x < 2 ^ 32)
    (hInv : shInv ts tarr as aarr a bits sg sga k s) (hk : k < a.length) :
    ∃ s1 s2, ExS LimbGen.prog s shBody .normal s1 ∧ ExS LimbGen.prog s1 shStep .normal s2 ∧
      shInv ts tarr as aarr a bits sg sga (k + 1) s2 := by
  obtain ⟨l0, l1, l2, l3, l4, hro, hts, has, haarr, htarr, hne1, hne2, hne3, hb1, hb2, hb3, hb4,
    hbits, hlen64⟩ := hInv
  set r := bits % 32 with hr
  set q := bits / 32 with hq
  have hr32 : r < 32 := Nat.mod_lt _ (by norm_num)
  have hak : a[k]'hk < 2 ^ 32 := ha _ (List.getElem_mem hk)
  have hcar : shCarry a r k < 2 ^ r := shCarry_lt a r ha hr32 k
  -- condition
  have hnload : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.int ⟨64, false⟩ a.length) := by
    have hf : EvE LimbGen.prog s (.field (.var 1) 8) (.ptr as 8) :=
      EvE.field (EvE.var l1) (by simp [ptrAddN, has, ziBlock_length])
    have := load_ziBlock_n s.mem as aarr a.length sga has
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hf this
  have hcond : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 3)
      (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (boolVal (decide (k < a.length))) :=
    EvE.bin (EvE.var l3) hnload rfl
  have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
  have hdec : decide (k < a.length) = true := by simpa using hk
  -- the shifted value
  have hx := evLimbAt (sg := sga) s as aarr a k has hb4 l1 l3 haarr hk ha
  have hxc : EvE LimbGen.prog s (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
      (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4))) (.int ⟨64, false⟩ (a[k]'hk)) :=
    EvE.cast hx (by
      show Res.ok (Val.int ⟨64, false⟩ (a[k]'hk % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hrv : EvE LimbGen.prog s (.bin .mod (some ⟨32, false⟩) (.var 2)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))) (.int ⟨32, false⟩ r) :=
    EvE.bin (EvE.var l2) (EvE.cast (EvE.const _) rfl) rfl
  have hshl : EvE LimbGen.prog s (.bin .shl (some ⟨64, false⟩)
      (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
        (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)))
      (.bin .mod (some ⟨32, false⟩) (.var 2) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))
      (.int ⟨64, false⟩ (a[k]'hk * 2 ^ r)) :=
    EvE.bin hxc hrv (evShl64 _ _ hak hr32)
  have hvv : EvE LimbGen.prog s (.bin .bor (some ⟨64, false⟩)
      (.bin .shl (some ⟨64, false⟩)
        (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)))
        (.bin .mod (some ⟨32, false⟩) (.var 2) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))
      (.var 4)) (.int ⟨64, false⟩ ((a[k]'hk * 2 ^ r) ||| shCarry a r k)) :=
    EvE.bin hshl (EvE.var l4) rfl
  obtain ⟨vv, hvv_def⟩ : ∃ vv, vv = (a[k]'hk * 2 ^ r) ||| shCarry a r k := ⟨_, rfl⟩
  rw [← hvv_def] at hvv
  have hvv_limb : vv % 2 ^ 32 = shLimb a r k := by
    unfold shLimb
    rw [hvv_def, ziAddTerm, dif_pos hk, Nat.shiftLeft_eq]
  have hvv_carry : vv / 2 ^ 32 = shCarry a r (k + 1) := by
    simp only [shCarry]
    rw [hvv_def, ziAddTerm, dif_pos hk, Nat.shiftLeft_eq]
  have hvv_lt : vv < 2 ^ 64 := by
    rw [hvv_def, ← Nat.shiftLeft_eq, sh_or_add _ _ _ hcar]
    calc a[k]'hk * 2 ^ r + shCarry a r k < a[k]'hk * 2 ^ r + 2 ^ r := by omega
      _ = (a[k]'hk + 1) * 2 ^ r := by ring
      _ ≤ 2 ^ 32 * 2 ^ r := Nat.mul_le_mul_right _ hak
      _ ≤ 2 ^ 32 * 2 ^ 32 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr32.le)
      _ = 2 ^ 64 := by norm_num
  set s' : State := { s with locals := s.locals.upd 5 (.int ⟨64, false⟩ vv) } with hs'
  have hset5 := ExS.set (i := 5) hvv
  have s'_0 : s'.locals 0 = some (.ptr ts 0) := by simpa [hs', Locals.upd] using l0
  have s'_2 : s'.locals 2 = some (.int ⟨32, false⟩ bits) := by simpa [hs', Locals.upd] using l2
  have s'_3 : s'.locals 3 = some (.int ⟨64, false⟩ k) := by simpa [hs', Locals.upd] using l3
  have s'_5 : s'.locals 5 = some (.int ⟨64, false⟩ vv) := by simp [hs', Locals.upd]
  have s'_ts : s'.mem ts = some (ziBlock tarr (a.length + q + 1) sg) := hts
  have s'_tarr : s'.mem tarr = some (limbBytes (List.replicate q 0 ++ shPrefix a r k ++
      List.replicate (a.length - k + 1) 0)) := htarr
  have hTlen : (List.replicate q 0 ++ shPrefix a r k ++ List.replicate (a.length - k + 1) 0).length =
      q + a.length + 1 := by
    simp [shPrefix_length]; omega
  have hq32 : q < 4294967296 := by omega
  have hdivq : EvE LimbGen.prog s' (.bin .div (some ⟨32, false⟩) (.var 2)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))) (.int ⟨32, false⟩ q) :=
    EvE.bin (EvE.var s'_2) (EvE.cast (EvE.const _) rfl) rfl
  have hcastq : EvE LimbGen.prog s' (.cast ⟨64, false⟩ (.bin .div (some ⟨32, false⟩) (.var 2)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32))))) (.int ⟨64, false⟩ q) :=
    EvE.cast hdivq (by
      show Res.ok (Val.int ⟨64, false⟩ (q % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hsum : EvE LimbGen.prog s' (.bin .add (some ⟨64, false⟩) (.var 3)
      (.cast ⟨64, false⟩ (.bin .div (some ⟨32, false⟩) (.var 2)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))) (.int ⟨64, false⟩ (k + q)) :=
    EvE.bin (EvE.var s'_3) hcastq (by
      show Res.ok (Val.int ⟨64, false⟩ ((k + q) % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hfld : EvE LimbGen.prog s' (.field (.var 0) 0) (.ptr ts 0) :=
    EvE.field (EvE.var s'_0) (by simp [ptrAddN, s'_ts, ziBlock_length])
  have hbase : EvE LimbGen.prog s' (.load .ptr (.field (.var 0) 0)) (.ptr tarr 0) :=
    EvE.load hfld (load_ziBlock_v s'.mem ts tarr (a.length + q + 1) sg s'_ts hb3)
  have hidxe : EvE LimbGen.prog s' (.index (.load .ptr (.field (.var 0) 0))
      (.bin .add (some ⟨64, false⟩) (.var 3) (.cast ⟨64, false⟩ (.bin .div (some ⟨32, false⟩) (.var 2)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))) 4) (.ptr tarr (4 * (q + k))) := by
    apply EvE.index hbase hsum
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, s'_tarr]
    have hbl := limbBytes_length (List.replicate q 0 ++ shPrefix a r k ++ List.replicate (a.length - k + 1) 0)
    rw [if_pos (by rw [hbl, hTlen]; omega)]
    congr 2
    omega
  have hval : EvE LimbGen.prog s' (.cast ⟨32, false⟩ (.var 5)) (.int ⟨32, false⟩ (vv % 2 ^ 32)) :=
    EvE.cast (EvE.var s'_5) rfl
  have hstoreEq := store_limb s'.mem tarr (List.replicate q 0 ++ shPrefix a r k ++
    List.replicate (a.length - k + 1) 0) (q + k) (vv % 2 ^ 32) s'_tarr (by rw [hTlen]; omega)
  have hst := ExS.store (ty := .int ⟨32, false⟩) hidxe hval hro hstoreEq
  set s'' : State := { s' with mem := s'.mem.upd tarr (limbBytes ((List.replicate q 0 ++
    shPrefix a r k ++ List.replicate (a.length - k + 1) 0).set (q + k) (vv % 2 ^ 32))) } with hs''
  have s''_5 : s''.locals 5 = some (.int ⟨64, false⟩ vv) := s'_5
  have hcarry : EvE LimbGen.prog s'' (.bin .shr (some ⟨64, false⟩) (.var 5)
      (.const (.int ⟨32, true⟩ 32))) (.int ⟨64, false⟩ (vv / 2 ^ 32)) :=
    EvE.bin (EvE.var s''_5) (EvE.const _) rfl
  have hset4 := ExS.set (i := 4) hcarry
  set s3 : State := { s'' with locals := s''.locals.upd 4 (.int ⟨64, false⟩ (vv / 2 ^ 32)) } with hs3
  have hbody : ExS LimbGen.prog s shBody .normal s3 := by
    unfold shBody
    have htr : truthy (boolVal (decide (k < a.length))) = .ok true := by rw [hdec, tb]
    exact ExS.ite hcond htr (ExS.seq hset5 (ExS.seq hst hset4))
  have s3_3 : s3.locals 3 = some (.int ⟨64, false⟩ k) := by simpa [hs3, hs'', Locals.upd] using s'_3
  have cast1 : EvE LimbGen.prog s3 (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ k) :=
    EvE.cast (EvE.var s3_3) (cast_u64_u64' k (by omega))
  have hadd : EvE LimbGen.prog s3 (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
      (.const (.int ⟨64, false⟩ 1))) (.int ⟨64, false⟩ (k + 1)) :=
    EvE.bin cast1 (EvE.const _) (by
      show Res.ok (Val.int ⟨64, false⟩ ((k + 1) % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hstep : ExS LimbGen.prog s3 shStep .normal
      { s3 with locals := s3.locals.upd 3 (.int ⟨64, false⟩ (k + 1)) } := by
    unfold shStep
    exact ExS.set (EvE.cast hadd (cast_u64_u64' (k + 1) (by omega)))
  refine ⟨s3, _, hbody, hstep, ?_⟩
  have hset : (List.replicate q 0 ++ shPrefix a r k ++ List.replicate (a.length - k + 1) 0).set
      (q + k) (vv % 2 ^ 32) = List.replicate q 0 ++ shPrefix a r (k + 1) ++
        List.replicate (a.length - (k + 1) + 1) 0 := by
    rw [hvv_limb, shT_set q k a.length (shPrefix a r k) (shPrefix_length a r k) _ hk]
    rfl
  have hm4 : ∀ b, b ≠ tarr → (s.mem.upd tarr (limbBytes ((List.replicate q 0 ++ shPrefix a r k ++
      List.replicate (a.length - k + 1) 0).set (q + k) (vv % 2 ^ 32)))) b = s.mem b := by
    intro b hb; simp [Mem.upd, hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, hro, ?_, ?_, ?_, ?_, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hbits, hlen64⟩
  · simpa [hs3, hs'', hs', Locals.upd] using l0
  · simpa [hs3, hs'', hs', Locals.upd] using l1
  · simpa [hs3, hs'', hs', Locals.upd] using l2
  · simp [hs3, hs'', hs', Locals.upd]
  · simp [hs3, hs'', hs', Locals.upd]
    exact hvv_carry
  · show (s.mem.upd tarr _) ts = _
    rw [hm4 ts (Ne.symm hne2)]; exact hts
  · show (s.mem.upd tarr _) as = _
    rw [hm4 as (Ne.symm hne3)]; exact has
  · show (s.mem.upd tarr _) aarr = _
    rw [hm4 aarr (Ne.symm hne1)]; exact haarr
  · show (s.mem.upd tarr _) tarr = _
    simp only [Mem.upd, if_true]
    rw [hset]

/-- The whole translated loop. -/
theorem shLoop (ts tarr as aarr : Nat) (a : List Nat) (bits : Nat) (sg sga : Int)
    (ha : ∀ x ∈ a, x < 2 ^ 32) :
    ∀ d k : Nat, k + d = a.length → ∀ s : State, shInv ts tarr as aarr a bits sg sga k s →
      ∃ sf, ExS LimbGen.prog s LimbGen.shift_fill_loop0 .normal sf ∧
        shInv ts tarr as aarr a bits sg sga a.length sf := by
  intro d
  induction d with
  | zero =>
      intro k hk s hInv
      have hkn : k = a.length := by omega
      subst hkn
      refine ⟨s, ?_, hInv⟩
      rw [shLoop_ast]
      obtain ⟨l0, l1, l2, l3, l4, hro, hts, has, haarr, htarr, hne1, hne2, hne3, hb1, hb2, hb3, hb4,
        hbits, hlen64⟩ := hInv
      have hnload : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
          (.int ⟨64, false⟩ a.length) := by
        have hf : EvE LimbGen.prog s (.field (.var 1) 8) (.ptr as 8) :=
          EvE.field (EvE.var l1) (by simp [ptrAddN, has, ziBlock_length])
        have := load_ziBlock_n s.mem as aarr a.length sga has
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact EvE.load hf this
      have hcond : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 3)
          (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (boolVal (decide (a.length < a.length))) :=
        EvE.bin (EvE.var l3) hnload rfl
      have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
      have hf : truthy (boolVal (decide (a.length < a.length))) = .ok false := by
        rw [tb]; simp
      apply ExS.loop_brk
      unfold shBody
      exact ExS.ite hcond hf ExS.brk
  | succ d ih =>
      intro k hk s hInv
      obtain ⟨s1, s2, hb, hs, hInv2⟩ := shIter ts tarr as aarr a bits sg sga k s ha hInv (by omega)
      obtain ⟨sf, hl, hfin⟩ := ih (k + 1) (by omega) s2 hInv2
      refine ⟨sf, ?_, hfin⟩
      rw [shLoop_ast]
      rw [shLoop_ast] at hl
      exact ExS.loop_next hb (Or.inl rfl) hs hl

/-- `shift_fill` writes `shiftLimbs a bits` into a zeroed destination block. -/
theorem shift_fill_refines (ts tarr as aarr : Nat) (a : List Nat) (bits : Nat) (sg sga : Int)
    (m : Mem) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.shift_fill.params
      [.ptr ts 0, .ptr as 0, .int ⟨32, false⟩ bits], m, false⟩)
    (ha : ∀ x ∈ a, x < 2 ^ 32)
    (hts : m ts = some (ziBlock tarr (a.length + bits / 32 + 1) sg))
    (has : m as = some (ziBlock aarr a.length sga)) (haarr : m aarr = some (limbBytes a))
    (htarr : m tarr = some (limbBytes (List.replicate (bits / 32 + a.length + 1) 0)))
    (hne1 : tarr ≠ aarr) (hne2 : tarr ≠ ts) (hne3 : tarr ≠ as)
    (hb1 : ts < 4294967296) (hb2 : as < 4294967296) (hb3 : tarr < 4294967296)
    (hb4 : aarr < 4294967296) (hbits : bits < 4294967296)
    (hlen64 : a.length + bits / 32 + 1 < 18446744073709551616) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.shift_fill.body .normal sf ∧
      sf.mem tarr = some (limbBytes (shiftLimbs a bits)) ∧ sf.mem ts = m ts ∧ sf.mem as = m as ∧
      sf.mem aarr = m aarr := by
  have l0 : s0.locals 0 = some (.ptr ts 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.ptr as 0) := by rw [h0]; rfl
  have l2 : s0.locals 2 = some (.int ⟨32, false⟩ bits) := by rw [h0]; rfl
  have hmem : s0.mem = m := by rw [h0]
  have hro : s0.ro = false := by rw [h0]
  have hset4 : ExS LimbGen.prog s0 (.set 4 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s0 with locals := s0.locals.upd 4 (.int ⟨64, false⟩ 0) } :=
    ExS.set (EvE.cast (EvE.const _) rfl)
  set s1 : State := { s0 with locals := s0.locals.upd 4 (.int ⟨64, false⟩ 0) } with hs1
  have hset3 : ExS LimbGen.prog s1 (.set 3 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s1 with locals := s1.locals.upd 3 (.int ⟨64, false⟩ 0) } :=
    ExS.set (EvE.cast (EvE.const _) rfl)
  set s2 : State := { s1 with locals := s1.locals.upd 3 (.int ⟨64, false⟩ 0) } with hs2
  have hInv0 : shInv ts tarr as aarr a bits sg sga 0 s2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hbits, hlen64⟩
    · simpa [hs2, hs1, Locals.upd] using l0
    · simpa [hs2, hs1, Locals.upd] using l1
    · simpa [hs2, hs1, Locals.upd] using l2
    · simp [hs2, hs1, Locals.upd]
    · simp [hs2, hs1, Locals.upd, shCarry]
    · simp [hs2, hs1, hro]
    · simp [hs2, hs1, hmem]; exact hts
    · simp [hs2, hs1, hmem]; exact has
    · simp [hs2, hs1, hmem]; exact haarr
    · simp only [hs2, hs1, hmem, shPrefix, List.append_nil]
      rw [htarr]
      congr 2
      rw [Nat.sub_zero, List.replicate_append_replicate]
      congr 1
  obtain ⟨sf, hloop, hfin⟩ := shLoop ts tarr as aarr a bits sg sga ha a.length 0 (by omega) s2 hInv0
  obtain ⟨l0', l1', l2', l3', l4', hro', hts', has', haarr', htarr', -, -, -, -, -, -, -, -, -⟩ := hfin
  set r := bits % 32 with hr
  set q := bits / 32 with hq
  have hr32 : r < 32 := Nat.mod_lt _ (by norm_num)
  have hcar : shCarry a r a.length < 2 ^ r := shCarry_lt a r ha hr32 a.length
  have hnload : EvE LimbGen.prog sf (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.int ⟨64, false⟩ a.length) := by
    have hf : EvE LimbGen.prog sf (.field (.var 1) 8) (.ptr as 8) :=
      EvE.field (EvE.var l1') (by simp [ptrAddN, has', ziBlock_length])
    have := load_ziBlock_n sf.mem as aarr a.length sga has'
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hf this
  have hdivq : EvE LimbGen.prog sf (.bin .div (some ⟨32, false⟩) (.var 2)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))) (.int ⟨32, false⟩ q) :=
    EvE.bin (EvE.var l2') (EvE.cast (EvE.const _) rfl) rfl
  have hq32 : q < 4294967296 := by omega
  have hcastq : EvE LimbGen.prog sf (.cast ⟨64, false⟩ (.bin .div (some ⟨32, false⟩) (.var 2)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32))))) (.int ⟨64, false⟩ q) :=
    EvE.cast hdivq (by
      show Res.ok (Val.int ⟨64, false⟩ (q % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hsum : EvE LimbGen.prog sf (.bin .add (some ⟨64, false⟩)
      (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.cast ⟨64, false⟩ (.bin .div (some ⟨32, false⟩) (.var 2)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))) (.int ⟨64, false⟩ (a.length + q)) :=
    EvE.bin hnload hcastq (by
      show Res.ok (Val.int ⟨64, false⟩ ((a.length + q) % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hfld : EvE LimbGen.prog sf (.field (.var 0) 0) (.ptr ts 0) :=
    EvE.field (EvE.var l0') (by simp [ptrAddN, hts', ziBlock_length])
  have hbase : EvE LimbGen.prog sf (.load .ptr (.field (.var 0) 0)) (.ptr tarr 0) :=
    EvE.load hfld (load_ziBlock_v sf.mem ts tarr (a.length + q + 1) sg hts' hb3)
  have hTfin : List.replicate q 0 ++ shPrefix a r a.length ++ List.replicate (a.length - a.length + 1) 0 =
      (List.replicate q 0 ++ shPrefix a r a.length) ++ [0] := by simp
  rw [hTfin] at htarr'
  have hTlen : ((List.replicate q 0 ++ shPrefix a r a.length) ++ [0]).length = q + a.length + 1 := by
    simp [shPrefix_length]; omega
  have hidxe : EvE LimbGen.prog sf (.index (.load .ptr (.field (.var 0) 0))
      (.bin .add (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
        (.cast ⟨64, false⟩ (.bin .div (some ⟨32, false⟩) (.var 2)
          (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 32)))))) 4)
      (.ptr tarr (4 * (q + a.length))) := by
    apply EvE.index hbase hsum
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, htarr']
    have hbl := limbBytes_length ((List.replicate q 0 ++ shPrefix a r a.length) ++ [0])
    rw [if_pos (by rw [hbl, hTlen]; omega)]
    congr 2
    omega
  have hval : EvE LimbGen.prog sf (.cast ⟨32, false⟩ (.var 4))
      (.int ⟨32, false⟩ (shCarry a r a.length % 2 ^ 32)) :=
    EvE.cast (EvE.var l4') rfl
  have hstoreEq := store_limb sf.mem tarr ((List.replicate q 0 ++ shPrefix a r a.length) ++ [0])
    (q + a.length) (shCarry a r a.length % 2 ^ 32) htarr' (by rw [hTlen]; omega)
  have hst := ExS.store (ty := .int ⟨32, false⟩) hidxe hval hro' hstoreEq
  refine ⟨{ sf with mem := sf.mem.upd tarr (limbBytes ((List.replicate q 0 ++ shPrefix a r a.length ++ [0]).set (q + a.length) (shCarry a r a.length % 2 ^ 32))) }, ?_, ?_, ?_, ?_, ?_⟩
  · unfold LimbGen.shift_fill
    exact ExS.seq hset4 (ExS.seq (ExS.seq hset3 hloop) hst)
  · simp only [Mem.upd, if_true]
    have hcl : shCarry a r a.length % 2 ^ 32 = shCarry a r a.length :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hcar (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hcl]
    have hlen : (List.replicate q 0 ++ shPrefix a r a.length).length = q + a.length := by
      simp [shPrefix_length]
    rw [List.set_append_right _ _ (by rw [hlen]), hlen, Nat.sub_self]
    simp [shiftLimbs, List.append_assoc]
    rfl
  · simp only [Mem.upd, if_neg (Ne.symm hne2)]; rw [hts', hts]
  · simp only [Mem.upd, if_neg (Ne.symm hne3)]; rw [has', has]
  · simp only [Mem.upd, if_neg (Ne.symm hne1)]; rw [haarr', haarr]
