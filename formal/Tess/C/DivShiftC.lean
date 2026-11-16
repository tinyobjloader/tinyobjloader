/-
  MiniC refinement of the translated `div_shift_in` (`lib/tess/src/exact.c`, the per-bit
  `rt = 2*rt + k` step of the binary path of `zi_divrem`): in place over the limbs of `rt` it writes the
  limbs of the model `siPrefix` (value `2*lv rt + k` modulo the carry limb) and returns the carry out
  `siCarry`. The in-place array is read and written limb by limb.
-/
import Tess.C.DivSingleC

namespace Tess.C
open Obj.C

/-- Carry into limb `k` of the in-place doubling with initial carry `c0`. -/
def siCarry (a : List Nat) (c0 : Nat) : Nat → Nat
  | 0 => c0
  | k + 1 => (ziAddTerm a k * 2 + siCarry a c0 k) / 2 ^ 32

def siLimb (a : List Nat) (c0 k : Nat) : Nat := (ziAddTerm a k * 2 + siCarry a c0 k) % 2 ^ 32

def siPrefix (a : List Nat) (c0 : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => siPrefix a c0 k ++ [siLimb a c0 k]

theorem siPrefix_length (a : List Nat) (c0 k : Nat) : (siPrefix a c0 k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [siPrefix, ih]

theorem siCarry_le (a : List Nat) (c0 : Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hc : c0 ≤ 1) :
    ∀ k, siCarry a c0 k ≤ 1 := by
  intro k
  induction k with
  | zero => exact hc
  | succ k ih =>
      have hx : ziAddTerm a k < 2 ^ 32 := by
        unfold ziAddTerm; split
        · exact ha _ (List.getElem_mem _)
        · positivity
      simp only [siCarry]
      rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
      omega

theorem si_value (a : List Nat) (c0 : Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hc : c0 ≤ 1) (k : Nat) :
    lv (siPrefix a c0 k) + siCarry a c0 k * 2 ^ (32 * k) = tv a k * 2 + c0 := by
  induction k with
  | zero => simp [siPrefix, siCarry, lv, tv]
  | succ k ih =>
      have hstep : siLimb a c0 k + 2 ^ 32 * siCarry a c0 (k + 1) =
          ziAddTerm a k * 2 + siCarry a c0 k := by
        unfold siLimb
        simp only [siCarry]
        have := Nat.mod_add_div (ziAddTerm a k * 2 + siCarry a c0 k) (2 ^ 32)
        omega
      have hp : lv (siPrefix a c0 (k + 1)) =
          lv (siPrefix a c0 k) + siLimb a c0 k * 2 ^ (32 * k) := by
        show lv (siPrefix a c0 k ++ [_]) = _
        rw [lv_append_single, siPrefix_length]
      rw [hp, show 32 * (k + 1) = 32 * k + 32 from by omega, pow_add]
      have := congrArg (· * 2 ^ (32 * k)) hstep
      show _ = (tv a k + ziAddTerm a k * 2 ^ (32 * k)) * 2 + c0
      nlinarith [ih, this]

theorem evShl1 (x : Nat) (hx : x < 2 ^ 32) :
    evalBin .shl (some ⟨64, false⟩) (.int ⟨64, false⟩ x) (.int ⟨32, true⟩ 1) =
      .ok (.int ⟨64, false⟩ (x * 2 ^ 1)) := by
  have hlt : x * 2 ^ 1 < 2 ^ 64 := by
    calc x * 2 ^ 1 < 2 ^ 32 * 2 ^ 1 := Nat.mul_lt_mul_of_pos_right hx (by positivity)
      _ ≤ 2 ^ 64 := by norm_num
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.modulus]
  have hm : x * 2 % 18446744073709551616 = x * 2 := Nat.mod_eq_of_lt (by simpa using hlt)
  simp only [Obj.C.guard, if_true, Res.bind_ok, hm]

/-- Load of limb `j` (struct = local 0, counter = local 2 holding `j`). -/
theorem evLimbLoadI {sg : Int} (s : State) (zb vblk : Nat)
    (limbs : List Nat) (j : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length sg)) (hb : vblk < 4294967296)
    (hl : s.locals 0 = some (.ptr zb 0))
    (hl2 : s.locals 2 = some (.int ⟨64, false⟩ j))
    (hlm : s.mem vblk = some (limbBytes limbs)) (hj : j < limbs.length)
    (hlt : ∀ x ∈ limbs, x < 2 ^ 32) :
    EvE LimbGen.prog s (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4))
      (.int ⟨32, false⟩ (limbs[j]'hj)) := by
  have hfield : EvE LimbGen.prog s (.field (.var 0) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var 0) 0)) (.ptr vblk 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length sg hm hb)
  have hidxlen : (limbBytes limbs).length = 4 * limbs.length := limbBytes_length limbs
  have hidx : EvE LimbGen.prog s (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4)
      (.ptr vblk (0 + j * 4)) := by
    apply EvE.index hloadPtr (EvE.var hl2)
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, hlm]
    rw [if_pos (by omega)]
  have hload : load s.mem (.int u32) (.ptr vblk (0 + j * 4)) = .ok (.int u32 (limbs[j]'hj)) := by
    have hl4 : 0 + j * 4 = 4 * j := Nat.zero_add _ |>.trans (Nat.mul_comm _ _)
    rw [hl4, load_limb s.mem vblk limbs j hlm hj]
    congr 1
    rw [Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hj))]
  exact EvE.load hidx hload

def siBody : Stmt :=
  .ite (.bin .lt (some ⟨64, false⟩) (.var 2) (.load (.int ⟨64, false⟩) (.field (.var 0) 8)))
    (.seq (.set 3 (.bin .bor (some ⟨64, false⟩)
        (.bin .shl (some ⟨64, false⟩)
          (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
            (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4)))
          (.const (.int ⟨32, true⟩ 1)))
        (.var 1)))
      (.seq (.store (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4)
          (.cast ⟨32, false⟩ (.var 3)))
        (.set 1 (.bin .shr (some ⟨64, false⟩) (.var 3) (.const (.int ⟨32, true⟩ 32))))))
    .brk

def siStep : Stmt :=
  .set 2 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2))
    (.const (.int ⟨64, false⟩ 1))))

theorem siLoop_ast : LimbGen.div_shift_in_loop0 = .loop siBody siStep := rfl

/-- Loop simulation relation after `j` limbs. -/
def siInv (zs varr : Nat) (a : List Nat) (c0 : Nat) (sg : Int) (j : Nat) (s : State) : Prop :=
  s.locals 0 = some (.ptr zs 0) ∧ s.locals 1 = some (.int ⟨64, false⟩ (siCarry a c0 j)) ∧
  s.locals 2 = some (.int ⟨64, false⟩ j) ∧ s.ro = false ∧
  s.mem zs = some (ziBlock varr a.length sg) ∧
  s.mem varr = some (limbBytes (siPrefix a c0 j ++ a.drop j)) ∧
  zs < 4294967296 ∧ varr < 4294967296 ∧ zs ≠ varr ∧ a.length < 18446744073709551616

theorem siPrefix_lt (a : List Nat) (c0 : Nat) : ∀ k, ∀ x ∈ siPrefix a c0 k, x < 2 ^ 32 := by
  intro k
  induction k with
  | zero => intro x hx; simp [siPrefix] at hx
  | succ k ih =>
      intro x hx
      simp only [siPrefix, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih x hx
      · exact Nat.mod_lt _ (by positivity)

theorem siIter (zs varr : Nat) (a : List Nat) (c0 : Nat) (sg : Int) (j : Nat) (s : State)
    (ha : ∀ x ∈ a, x < 2 ^ 32) (hc : c0 ≤ 1) (hj : j < a.length)
    (hInv : siInv zs varr a c0 sg j s) :
    ∃ s1 s2, ExS LimbGen.prog s siBody .normal s1 ∧ ExS LimbGen.prog s1 siStep .normal s2 ∧
      siInv zs varr a c0 sg (j + 1) s2 := by
  obtain ⟨l0, l1, l2, hro, hzs, hv, hb1, hb2, hne, hlen64⟩ := hInv
  set n := a.length with hn
  have hLlen : (siPrefix a c0 j ++ a.drop j).length = n := by
    simp [siPrefix_length]; omega
  have hxj : a[j]'hj < 2 ^ 32 := ha _ (List.getElem_mem hj)
  have hcar : siCarry a c0 j ≤ 1 := siCarry_le a c0 ha hc j
  have hLget : (siPrefix a c0 j ++ a.drop j)[j]'(by omega) = a[j]'hj := by
    rw [List.getElem_append_right (by simp [siPrefix_length])]
    simp [siPrefix_length]
  have hLbound : ∀ x ∈ siPrefix a c0 j ++ a.drop j, x < 2 ^ 32 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact siPrefix_lt a c0 j x hx
    · exact ha x (List.mem_of_mem_drop hx)
  have hnload : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
      (.int ⟨64, false⟩ n) := by
    have hf : EvE LimbGen.prog s (.field (.var 0) 8) (.ptr zs 8) :=
      EvE.field (EvE.var l0) (by simp [ptrAddN, hzs, ziBlock_length])
    have := load_ziBlock_n s.mem zs varr n sg hzs
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hf this
  have hcond : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 2)
      (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) (boolVal (decide (j < n))) :=
    EvE.bin (EvE.var l2) hnload rfl
  have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
  have htr : truthy (boolVal (decide (j < n))) = .ok true := by rw [tb]; simp [hj]
  have hx := evLimbLoadI (sg := sg) s zs varr (siPrefix a c0 j ++ a.drop j) j
    (by rw [hLlen]; exact hzs) hb2 l0 l2 hv (by omega) hLbound
  have hxc : EvE LimbGen.prog s (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
      (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4))) (.int ⟨64, false⟩ (a[j]'hj)) :=
    EvE.cast (by rw [hLget] at hx; exact hx) (by
      show Res.ok (Val.int ⟨64, false⟩ (a[j]'hj % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hshl : EvE LimbGen.prog s (.bin .shl (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.load
      (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4)))
      (.const (.int ⟨32, true⟩ 1))) (.int ⟨64, false⟩ (a[j]'hj * 2 ^ 1)) :=
    EvE.bin hxc (EvE.const _) (evShl1 _ hxj)
  have hor : (a[j]'hj * 2 ^ 1) ||| siCarry a c0 j = a[j]'hj * 2 + siCarry a c0 j := by
    have h := sh_or_add (a[j]'hj) 1 (siCarry a c0 j) (by simpa using Nat.lt_succ_of_le hcar)
    rw [Nat.shiftLeft_eq] at h
    simpa using h
  have hvv : EvE LimbGen.prog s (.bin .bor (some ⟨64, false⟩) (.bin .shl (some ⟨64, false⟩)
      (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
        (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4))) (.const (.int ⟨32, true⟩ 1)))
      (.var 1)) (.int ⟨64, false⟩ (a[j]'hj * 2 + siCarry a c0 j)) := by
    rw [← hor]; exact EvE.bin hshl (EvE.var l1) rfl
  set vv := a[j]'hj * 2 + siCarry a c0 j with hvvdef
  have hvlt : vv < 2 ^ 33 := by
    have h33 : (2:Nat) ^ 33 = 2 * 2 ^ 32 := by norm_num
    omega
  have hvl64 : vv < 2 ^ 64 := lt_of_lt_of_le hvlt (by norm_num)
  set s' : State := { s with locals := s.locals.upd 3 (.int ⟨64, false⟩ vv) } with hs'
  have hset3 := ExS.set (i := 3) hvv
  have s'_0 : s'.locals 0 = some (.ptr zs 0) := by simpa [hs', Locals.upd] using l0
  have s'_1 : s'.locals 1 = some (.int ⟨64, false⟩ (siCarry a c0 j)) := by simpa [hs', Locals.upd] using l1
  have s'_2 : s'.locals 2 = some (.int ⟨64, false⟩ j) := by simpa [hs', Locals.upd] using l2
  have s'_3 : s'.locals 3 = some (.int ⟨64, false⟩ vv) := by simp [hs', Locals.upd]
  have s'_zs : s'.mem zs = some (ziBlock varr n sg) := hzs
  have s'_v : s'.mem varr = some (limbBytes (siPrefix a c0 j ++ a.drop j)) := hv
  have hfld : EvE LimbGen.prog s' (.field (.var 0) 0) (.ptr zs 0) :=
    EvE.field (EvE.var s'_0) (by simp [ptrAddN, s'_zs, ziBlock_length])
  have hbase : EvE LimbGen.prog s' (.load .ptr (.field (.var 0) 0)) (.ptr varr 0) :=
    EvE.load hfld (load_ziBlock_v s'.mem zs varr n sg s'_zs hb2)
  have hidxe : EvE LimbGen.prog s' (.index (.load .ptr (.field (.var 0) 0)) (.var 2) 4)
      (.ptr varr (4 * j)) := by
    apply EvE.index hbase (EvE.var s'_2)
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, s'_v]
    have hbl := limbBytes_length (siPrefix a c0 j ++ a.drop j)
    rw [if_pos (by rw [hbl, hLlen]; omega)]
    congr 2
    omega
  have hval : EvE LimbGen.prog s' (.cast ⟨32, false⟩ (.var 3)) (.int ⟨32, false⟩ (vv % 2 ^ 32)) :=
    EvE.cast (EvE.var s'_3) rfl
  have hstoreEq := store_limb s'.mem varr (siPrefix a c0 j ++ a.drop j) j (vv % 2 ^ 32) s'_v
    (by rw [hLlen]; omega)
  have hst := ExS.store (ty := .int ⟨32, false⟩) hidxe hval hro hstoreEq
  set s'' : State := { s' with mem := s'.mem.upd varr (limbBytes ((siPrefix a c0 j ++ a.drop j).set j (vv % 2 ^ 32))) } with hs''
  have s''_3 : s''.locals 3 = some (.int ⟨64, false⟩ vv) := s'_3
  have hcarry : EvE LimbGen.prog s'' (.bin .shr (some ⟨64, false⟩) (.var 3)
      (.const (.int ⟨32, true⟩ 32))) (.int ⟨64, false⟩ (vv / 2 ^ 32)) :=
    EvE.bin (EvE.var s''_3) (EvE.const _) rfl
  have hset1 := ExS.set (i := 1) hcarry
  set s3 : State := { s'' with locals := s''.locals.upd 1 (.int ⟨64, false⟩ (vv / 2 ^ 32)) } with hs3
  have hbody : ExS LimbGen.prog s siBody .normal s3 := by
    unfold siBody
    exact ExS.ite hcond htr (ExS.seq hset3 (ExS.seq hst hset1))
  have s3_2 : s3.locals 2 = some (.int ⟨64, false⟩ j) := by
    simpa [hs3, hs'', Locals.upd] using s'_2
  have cast1 : EvE LimbGen.prog s3 (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ j) :=
    EvE.cast (EvE.var s3_2) (cast_u64_u64' j (by omega))
  have hadd : EvE LimbGen.prog s3 (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2))
      (.const (.int ⟨64, false⟩ 1))) (.int ⟨64, false⟩ (j + 1)) :=
    EvE.bin cast1 (EvE.const _) (by
      show Res.ok (Val.int ⟨64, false⟩ ((j + 1) % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hstep : ExS LimbGen.prog s3 siStep .normal
      { s3 with locals := s3.locals.upd 2 (.int ⟨64, false⟩ (j + 1)) } := by
    unfold siStep
    exact ExS.set (EvE.cast hadd (cast_u64_u64' (j + 1) (by omega)))
  refine ⟨s3, _, hbody, hstep, ?_⟩
  have hset : (siPrefix a c0 j ++ a.drop j).set j (vv % 2 ^ 32) =
      siPrefix a c0 (j + 1) ++ a.drop (j + 1) := by
    rw [List.set_append_right _ _ (by simp [siPrefix_length]), siPrefix_length, Nat.sub_self,
      List.drop_eq_getElem_cons hj]
    simp only [List.set_cons_zero, siPrefix, List.append_assoc, List.singleton_append]
    have : vv % 2 ^ 32 = siLimb a c0 j := by
      unfold siLimb ziAddTerm; rw [dif_pos hj]
    rw [this]
  refine ⟨?_, ?_, ?_, hro, ?_, ?_, hb1, hb2, hne, hlen64⟩
  · simpa [hs3, hs'', hs', Locals.upd] using l0
  · simp [hs3, hs'', hs', Locals.upd]
    show vv / 2 ^ 32 = siCarry a c0 (j + 1)
    simp only [siCarry]
    unfold ziAddTerm; rw [dif_pos hj]
  · simp [hs3, hs'', hs', Locals.upd]
  · show (s.mem.upd varr _) zs = _
    simp only [Mem.upd, if_neg hne]; exact hzs
  · show (s.mem.upd varr _) varr = _
    simp only [Mem.upd, ite_true]
    rw [hset]

theorem siLoop (zs varr : Nat) (a : List Nat) (c0 : Nat) (sg : Int)
    (ha : ∀ x ∈ a, x < 2 ^ 32) (hc : c0 ≤ 1) :
    ∀ d j : Nat, j + d = a.length → ∀ s : State, siInv zs varr a c0 sg j s →
      ∃ sf, ExS LimbGen.prog s LimbGen.div_shift_in_loop0 .normal sf ∧
        siInv zs varr a c0 sg a.length sf := by
  intro d
  induction d with
  | zero =>
      intro j hj s hInv
      have hjn : j = a.length := by omega
      subst hjn
      refine ⟨s, ?_, hInv⟩
      rw [siLoop_ast]
      obtain ⟨l0, l1, l2, hro, hzs, hv, hb1, hb2, hne, hlen64⟩ := hInv
      have hnload : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
          (.int ⟨64, false⟩ a.length) := by
        have hf : EvE LimbGen.prog s (.field (.var 0) 8) (.ptr zs 8) :=
          EvE.field (EvE.var l0) (by simp [ptrAddN, hzs, ziBlock_length])
        have := load_ziBlock_n s.mem zs varr a.length sg hzs
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact EvE.load hf this
      have hcond : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 2)
          (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) (boolVal (decide (a.length < a.length))) :=
        EvE.bin (EvE.var l2) hnload rfl
      have tb : ∀ b : Bool, truthy (boolVal b) = .ok b := by intro b; cases b <;> rfl
      have hf : truthy (boolVal (decide (a.length < a.length))) = .ok false := by
        rw [tb]; simp
      apply ExS.loop_brk
      unfold siBody
      exact ExS.ite hcond hf ExS.brk
  | succ d ih =>
      intro j hj s hInv
      obtain ⟨s1, s2, hb, hs, hInv2⟩ := siIter zs varr a c0 sg j s ha hc (by omega) hInv
      obtain ⟨sf, hl, hfin⟩ := ih (j + 1) (by omega) s2 hInv2
      refine ⟨sf, ?_, hfin⟩
      rw [siLoop_ast]
      rw [siLoop_ast] at hl
      exact ExS.loop_next hb (Or.inl rfl) hs hl

/-- `div_shift_in` doubles the limbs in place, adds the bit, and returns the carry out. -/
theorem div_shift_in_refines (zs varr : Nat) (a : List Nat) (c0 : Nat) (sg : Int)
    (m : Mem) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.div_shift_in.params [.ptr zs 0, .int ⟨64, false⟩ c0], m, false⟩)
    (ha : ∀ x ∈ a, x < 2 ^ 32) (hc : c0 ≤ 1)
    (hzs : m zs = some (ziBlock varr a.length sg)) (hv : m varr = some (limbBytes a))
    (hb1 : zs < 4294967296) (hb2 : varr < 4294967296) (hne : zs ≠ varr)
    (hlen64 : a.length < 18446744073709551616) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.div_shift_in.body
        (.ret (some (.int ⟨64, false⟩ (siCarry a c0 a.length)))) sf ∧
      sf.mem varr = some (limbBytes (siPrefix a c0 a.length)) ∧ sf.mem zs = m zs := by
  have l0 : s0.locals 0 = some (.ptr zs 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.int ⟨64, false⟩ c0) := by rw [h0]; rfl
  have hmem : s0.mem = m := by rw [h0]
  have hro : s0.ro = false := by rw [h0]
  have hset2 : ExS LimbGen.prog s0 (.set 2 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s0 with locals := s0.locals.upd 2 (.int ⟨64, false⟩ 0) } :=
    ExS.set (EvE.cast (EvE.const _) rfl)
  set s1 : State := { s0 with locals := s0.locals.upd 2 (.int ⟨64, false⟩ 0) } with hs1
  have hInv0 : siInv zs varr a c0 sg 0 s1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hb1, hb2, hne, hlen64⟩
    · simpa [hs1, Locals.upd] using l0
    · simpa [hs1, Locals.upd, siCarry] using l1
    · simp [hs1, Locals.upd]
    · simp [hs1, hro]
    · simpa [hs1, hmem] using hzs
    · simpa [hs1, hmem, siPrefix] using hv
  obtain ⟨sf, hloop, hfin⟩ := siLoop zs varr a c0 sg ha hc a.length 0 (by omega) s1 hInv0
  obtain ⟨-, l1', -, -, hzs', hv', -, -, -, -⟩ := hfin
  refine ⟨sf, ?_, ?_, ?_⟩
  · unfold LimbGen.div_shift_in
    show ExS LimbGen.prog s0 (.seq (.seq _ LimbGen.div_shift_in_loop0) (.ret (some (.var 1)))) _ sf
    exact ExS.seq (ExS.seq hset2 hloop) (ExS.ret (EvE.var l1'))
  · simpa [siPrefix_length, List.drop_length] using hv'
  · rw [hzs', hzs]

end Tess.C
