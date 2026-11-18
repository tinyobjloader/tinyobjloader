/-
  MiniC refinement of the translated `div_sub_in` (`lib/tess/src/exact.c`, the compare-then-subtract step of
  the binary path of `zi_divrem`): in place `r -= b` limb by limb with borrow. The model `sbPrefix`
  denotes `lv r - lv b` modulo `2^(32 n)` and `sbBorrow` is the final borrow
  (`sb_value`: `lv (sbPrefix) + tv b n = tv a n + 2^(32 n) * sbBorrow`).
-/
import Tess.C.DivShiftC

namespace Tess.C
open Obj.C

def sbBorrow (a b : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if ziAddTerm a k < ziAddTerm b k + sbBorrow a b k then 1 else 0

def sbLimb (a b : List Nat) (k : Nat) : Nat :=
  (if ziAddTerm b k + sbBorrow a b k ≤ ziAddTerm a k then ziAddTerm a k - (ziAddTerm b k + sbBorrow a b k)
   else ziAddTerm a k + 2 ^ 64 - (ziAddTerm b k + sbBorrow a b k)) % 2 ^ 32

def sbPrefix (a b : List Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => sbPrefix a b k ++ [sbLimb a b k]

theorem sbPrefix_length (a b : List Nat) (k : Nat) : (sbPrefix a b k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sbPrefix, ih]

theorem zat_lt (l : List Nat) (hl : ∀ x ∈ l, x < 2 ^ 32) (k : Nat) : ziAddTerm l k < 2 ^ 32 := by
  unfold ziAddTerm; split
  · exact hl _ (List.getElem_mem _)
  · positivity

theorem sbBorrow_le (a b : List Nat) : ∀ k, sbBorrow a b k ≤ 1 := by
  intro k; cases k <;> simp [sbBorrow] <;> split <;> omega

theorem sbLimb_step (a b : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32) (k : Nat) :
    sbLimb a b k + (ziAddTerm b k + sbBorrow a b k) =
      ziAddTerm a k + 2 ^ 32 * sbBorrow a b (k + 1) := by
  have hx := zat_lt a ha k
  have hy := zat_lt b hb k
  have hbr := sbBorrow_le a b k
  unfold sbLimb
  simp only [sbBorrow]
  split_ifs with h1 h2 h3
  · omega
  · omega
  · have : ziAddTerm a k + 2 ^ 64 - (ziAddTerm b k + sbBorrow a b k) =
        (ziAddTerm a k + 2 ^ 32 - (ziAddTerm b k + sbBorrow a b k)) + (2 ^ 64 - 2 ^ 32) := by
      have : (2:Nat) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    rw [this]
    have h64 : (2:Nat) ^ 64 - 2 ^ 32 = 2 ^ 32 * (2 ^ 32 - 1) := by norm_num
    rw [h64, Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · omega

theorem sb_value (a b : List Nat) (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32) (k : Nat) :
    lv (sbPrefix a b k) + tv b k = tv a k + 2 ^ (32 * k) * sbBorrow a b k := by
  induction k with
  | zero => simp [sbPrefix, sbBorrow, lv, tv]
  | succ k ih =>
      have hs := sbLimb_step a b ha hb k
      have hp : lv (sbPrefix a b (k + 1)) = lv (sbPrefix a b k) + sbLimb a b k * 2 ^ (32 * k) := by
        show lv (sbPrefix a b k ++ [_]) = _
        rw [lv_append_single, sbPrefix_length]
      rw [hp, show 32 * (k + 1) = 32 * k + 32 from by omega, pow_add]
      have := congrArg (· * 2 ^ (32 * k)) hs
      show _ = tv a k + ziAddTerm a k * 2 ^ (32 * k) + _ 
      show _ + (tv b k + ziAddTerm b k * 2 ^ (32 * k)) = _
      nlinarith [ih, this]

/-- Load of limb `j` through struct local `sv` with the counter in local `cv` (holding `j`). -/
theorem evLimbLoadG {sg : Int} (sv cv : Nat) (s : State) (zb vblk : Nat)
    (limbs : List Nat) (j : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length sg)) (hb : vblk < 4294967296)
    (hl : s.locals sv = some (.ptr zb 0))
    (hl2 : s.locals cv = some (.int ⟨64, false⟩ j))
    (hlm : s.mem vblk = some (limbBytes limbs)) (hj : j < limbs.length)
    (hlt : ∀ x ∈ limbs, x < 2 ^ 32) :
    EvE LimbGen.prog s (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var sv) 0)) (.var cv) 4))
      (.int ⟨32, false⟩ (limbs[j]'hj)) := by
  have hfield : EvE LimbGen.prog s (.field (.var sv) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var sv) 0)) (.ptr vblk 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length sg hm hb)
  have hidxlen : (limbBytes limbs).length = 4 * limbs.length := limbBytes_length limbs
  have hidx : EvE LimbGen.prog s (.index (.load .ptr (.field (.var sv) 0)) (.var cv) 4)
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

theorem evSub64 (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ x) (.int ⟨64, false⟩ y) =
      .ok (.int ⟨64, false⟩ (if y ≤ x then x - y else x + 2 ^ 64 - y)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.modulus]

def sbBody : Stmt :=
  .ite (.bin .lt (some ⟨64, false⟩) (.var 3) (.load (.int ⟨64, false⟩) (.field (.var 0) 8)))
    (.seq (.seq (.set 4 (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var 0) 0)) (.var 3) 4))))
        (.set 5 (.bin .add (some ⟨64, false⟩)
          (.cast ⟨64, false⟩ (.cond
            (.bin .lt (some ⟨64, false⟩) (.var 3) (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
            (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4))
            (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
          (.var 2))))
      (.seq (.store (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.var 3) 4)
          (.cast ⟨32, false⟩ (.bin .sub (some ⟨64, false⟩) (.var 4) (.var 5))))
        (.set 2 (.cast ⟨64, false⟩ (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 5))))))
    .brk

def sbStep : Stmt :=
  .set 3 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
    (.const (.int ⟨64, false⟩ 1))))

theorem sbLoop_ast : LimbGen.div_sub_in_loop0 = .loop sbBody sbStep := rfl

theorem castBool64 (c : Bool) :
    evalCast ⟨64, false⟩ (boolVal c) = .ok (.int ⟨64, false⟩ (if c then 1 else 0)) := by
  cases c <;> rfl

/-- Loop simulation relation after `j` limbs. -/
def sbInv (zs bs varr barr : Nat) (a b : List Nat) (sg sgb : Int) (j : Nat) (s : State) : Prop :=
  s.locals 0 = some (.ptr zs 0) ∧ s.locals 1 = some (.ptr bs 0) ∧
  s.locals 2 = some (.int ⟨64, false⟩ (sbBorrow a b j)) ∧ s.locals 3 = some (.int ⟨64, false⟩ j) ∧
  s.ro = false ∧ s.mem zs = some (ziBlock varr a.length sg) ∧
  s.mem bs = some (ziBlock barr b.length sgb) ∧ s.mem barr = some (limbBytes b) ∧
  s.mem varr = some (limbBytes (sbPrefix a b j ++ a.drop j)) ∧
  varr ≠ zs ∧ varr ≠ bs ∧ varr ≠ barr ∧ zs < 4294967296 ∧ bs < 4294967296 ∧
  varr < 4294967296 ∧ barr < 4294967296 ∧ a.length < 18446744073709551616 ∧
  b.length < 18446744073709551616

theorem sbPrefix_lt (a b : List Nat) : ∀ k, ∀ x ∈ sbPrefix a b k, x < 2 ^ 32 := by
  intro k
  induction k with
  | zero => intro x hx; simp [sbPrefix] at hx
  | succ k ih =>
      intro x hx
      simp only [sbPrefix, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih x hx
      · exact Nat.mod_lt _ (by positivity)

theorem sbIter (zs bs varr barr : Nat) (a b : List Nat) (sg sgb : Int) (j : Nat) (s : State)
    (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32) (hj : j < a.length)
    (hInv : sbInv zs bs varr barr a b sg sgb j s) :
    ∃ s1 s2, ExS LimbGen.prog s sbBody .normal s1 ∧ ExS LimbGen.prog s1 sbStep .normal s2 ∧
      sbInv zs bs varr barr a b sg sgb (j + 1) s2 := by
  obtain ⟨l0, l1, l2, l3, hro, hzs, hbs, hbarr, hv, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hn64, hbl64⟩ :=
    hInv
  set n := a.length with hn
  set br := sbBorrow a b j with hbr
  have hbrle : br ≤ 1 := sbBorrow_le a b j
  have hLlen : (sbPrefix a b j ++ a.drop j).length = n := by
    simp [sbPrefix_length]; omega
  have hxj : a[j]'hj < 2 ^ 32 := ha _ (List.getElem_mem hj)
  have hzx : ziAddTerm a j = a[j]'hj := by unfold ziAddTerm; rw [dif_pos hj]
  have hLget : (sbPrefix a b j ++ a.drop j)[j]'(by omega) = a[j]'hj := by
    rw [List.getElem_append_right (by simp [sbPrefix_length])]
    simp [sbPrefix_length]
  have hLbound : ∀ x ∈ sbPrefix a b j ++ a.drop j, x < 2 ^ 32 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact sbPrefix_lt a b j x hx
    · exact ha x (List.mem_of_mem_drop hx)
  have tb : ∀ c : Bool, truthy (boolVal c) = .ok c := by intro c; cases c <;> rfl
  -- loop condition
  have hnload : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
      (.int ⟨64, false⟩ n) := by
    have hf : EvE LimbGen.prog s (.field (.var 0) 8) (.ptr zs 8) :=
      EvE.field (EvE.var l0) (by simp [ptrAddN, hzs, ziBlock_length])
    have := load_ziBlock_n s.mem zs varr n sg hzs
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hf this
  have hcond : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 3)
      (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) (boolVal (decide (j < n))) :=
    EvE.bin (EvE.var l3) hnload rfl
  have htr : truthy (boolVal (decide (j < n))) = .ok true := by rw [tb]; simp [hj]
  -- x = r[j]
  have hx := evLimbLoadG (sg := sg) 0 3 s zs varr (sbPrefix a b j ++ a.drop j) j
    (by rw [hLlen]; exact hzs) hb3 l0 l3 hv (by omega) hLbound
  rw [hLget] at hx
  have hxc : EvE LimbGen.prog s (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩)
      (.index (.load .ptr (.field (.var 0) 0)) (.var 3) 4))) (.int ⟨64, false⟩ (a[j]'hj)) :=
    EvE.cast hx (by
      show Res.ok (Val.int ⟨64, false⟩ (a[j]'hj % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  set s1 : State := { s with locals := s.locals.upd 4 (.int ⟨64, false⟩ (a[j]'hj)) } with hs1
  have hset4 := ExS.set (i := 4) hxc
  have s1_0 : s1.locals 0 = some (.ptr zs 0) := by simpa [hs1, Locals.upd] using l0
  have s1_1 : s1.locals 1 = some (.ptr bs 0) := by simpa [hs1, Locals.upd] using l1
  have s1_2 : s1.locals 2 = some (.int ⟨64, false⟩ br) := by simpa [hs1, Locals.upd] using l2
  have s1_3 : s1.locals 3 = some (.int ⟨64, false⟩ j) := by simpa [hs1, Locals.upd] using l3
  have s1_4 : s1.locals 4 = some (.int ⟨64, false⟩ (a[j]'hj)) := by simp [hs1, Locals.upd]
  -- y = b[j] + borrow
  have hbnload : EvE LimbGen.prog s1 (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.int ⟨64, false⟩ b.length) := by
    have hf : EvE LimbGen.prog s1 (.field (.var 1) 8) (.ptr bs 8) :=
      EvE.field (EvE.var s1_1) (by simp [hs1, ptrAddN, hbs, ziBlock_length])
    have := load_ziBlock_n s1.mem bs barr b.length sgb hbs
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hf this
  have hcondb : EvE LimbGen.prog s1 (.bin .lt (some ⟨64, false⟩) (.var 3)
      (.load (.int ⟨64, false⟩) (.field (.var 1) 8))) (boolVal (decide (j < b.length))) :=
    EvE.bin (EvE.var s1_3) hbnload rfl
  have hyv : EvE LimbGen.prog s1 (.cast ⟨64, false⟩ (.cond
      (.bin .lt (some ⟨64, false⟩) (.var 3) (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
      (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4))
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))) (.int ⟨64, false⟩ (ziAddTerm b j)) := by
    by_cases hjb : j < b.length
    · have hbx := evLimbLoadG (sg := sgb) 1 3 s1 bs barr b j (by simpa [hs1] using hbs) hb4 s1_1 s1_3
        (by simpa [hs1] using hbarr) hjb hb
      have hzb : ziAddTerm b j = b[j]'hjb := by unfold ziAddTerm; rw [dif_pos hjb]
      refine EvE.cast (EvE.cond (bc := true) hcondb (by rw [tb]; simp [hjb]) (by simpa using hbx)) ?_
      show Res.ok (Val.int ⟨64, false⟩ (b[j]'hjb % 18446744073709551616)) = _
      rw [hzb, Nat.mod_eq_of_lt (by have := hb _ (List.getElem_mem hjb); omega)]
    · have hzb : ziAddTerm b j = 0 := by unfold ziAddTerm; rw [dif_neg hjb]
      have hz0 : EvE LimbGen.prog s1 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))) (.int ⟨32, false⟩ 0) :=
        EvE.cast (EvE.const _) rfl
      refine EvE.cast (EvE.cond (bc := false) hcondb (by rw [tb]; simp [hjb]) (by simpa using hz0)) ?_
      rw [hzb]; rfl
  have hzbl : ziAddTerm b j < 2 ^ 32 := zat_lt b hb j
  set y := ziAddTerm b j + br with hydef
  have hy64 : y < 2 ^ 64 := by
    have : (2:Nat) ^ 32 < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    omega
  have hset5e : EvE LimbGen.prog s1 (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.cond
      (.bin .lt (some ⟨64, false⟩) (.var 3) (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
      (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4))
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))) (.var 2)) (.int ⟨64, false⟩ y) :=
    EvE.bin hyv (EvE.var s1_2) (by
      show Res.ok (Val.int ⟨64, false⟩ ((ziAddTerm b j + br) % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by simpa using hy64)])
  set s2 : State := { s1 with locals := s1.locals.upd 5 (.int ⟨64, false⟩ y) } with hs2
  have hset5 := ExS.set (i := 5) hset5e
  have s2_0 : s2.locals 0 = some (.ptr zs 0) := by simpa [hs2, Locals.upd] using s1_0
  have s2_2 : s2.locals 2 = some (.int ⟨64, false⟩ br) := by simpa [hs2, Locals.upd] using s1_2
  have s2_3 : s2.locals 3 = some (.int ⟨64, false⟩ j) := by simpa [hs2, Locals.upd] using s1_3
  have s2_4 : s2.locals 4 = some (.int ⟨64, false⟩ (a[j]'hj)) := by simpa [hs2, Locals.upd] using s1_4
  have s2_5 : s2.locals 5 = some (.int ⟨64, false⟩ y) := by simp [hs2, Locals.upd]
  have s2_zs : s2.mem zs = some (ziBlock varr n sg) := hzs
  have s2_v : s2.mem varr = some (limbBytes (sbPrefix a b j ++ a.drop j)) := hv
  -- store of the difference limb
  have hxlt : a[j]'hj < 2 ^ 64 := by
    have : (2:Nat) ^ 32 < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    omega
  have hdiff : EvE LimbGen.prog s2 (.bin .sub (some ⟨64, false⟩) (.var 4) (.var 5))
      (.int ⟨64, false⟩ (if y ≤ a[j]'hj then a[j]'hj - y else a[j]'hj + 2 ^ 64 - y)) :=
    EvE.bin (EvE.var s2_4) (EvE.var s2_5) (evSub64 _ _ hxlt hy64)
  have hlimb : (if y ≤ a[j]'hj then a[j]'hj - y else a[j]'hj + 2 ^ 64 - y) % 2 ^ 32 = sbLimb a b j := by
    unfold sbLimb
    rw [hzx, hydef]
  have hval : EvE LimbGen.prog s2 (.cast ⟨32, false⟩ (.bin .sub (some ⟨64, false⟩) (.var 4) (.var 5)))
      (.int ⟨32, false⟩ (sbLimb a b j)) :=
    EvE.cast hdiff (by rw [← hlimb]; rfl)
  have hfld : EvE LimbGen.prog s2 (.field (.var 0) 0) (.ptr zs 0) :=
    EvE.field (EvE.var s2_0) (by simp [ptrAddN, s2_zs, ziBlock_length])
  have hbase : EvE LimbGen.prog s2 (.load .ptr (.field (.var 0) 0)) (.ptr varr 0) :=
    EvE.load hfld (load_ziBlock_v s2.mem zs varr n sg s2_zs hb3)
  have hidxe : EvE LimbGen.prog s2 (.index (.load .ptr (.field (.var 0) 0)) (.var 3) 4)
      (.ptr varr (4 * j)) := by
    apply EvE.index hbase (EvE.var s2_3)
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, s2_v]
    have hbl := limbBytes_length (sbPrefix a b j ++ a.drop j)
    rw [if_pos (by rw [hbl, hLlen]; omega)]
    congr 2
    omega
  have hstoreEq := store_limb s2.mem varr (sbPrefix a b j ++ a.drop j) j (sbLimb a b j) s2_v
    (by rw [hLlen]; omega)
  have hst := ExS.store (ty := .int ⟨32, false⟩) hidxe hval hro hstoreEq
  set s3 : State := { s2 with mem := s2.mem.upd varr (limbBytes ((sbPrefix a b j ++ a.drop j).set j (sbLimb a b j))) } with hs3
  have s3_4 : s3.locals 4 = some (.int ⟨64, false⟩ (a[j]'hj)) := s2_4
  have s3_5 : s3.locals 5 = some (.int ⟨64, false⟩ y) := s2_5
  have hltv : EvE LimbGen.prog s3 (.cast ⟨64, false⟩ (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 5)))
      (.int ⟨64, false⟩ (if a[j]'hj < y then 1 else 0)) :=
    EvE.cast (EvE.bin (EvE.var s3_4) (EvE.var s3_5) rfl) (by simpa using castBool64 (decide (a[j]'hj < y)))
  have hset2 := ExS.set (i := 2) hltv
  set s4 : State := { s3 with locals := s3.locals.upd 2 (.int ⟨64, false⟩ (if a[j]'hj < y then 1 else 0)) } with hs4
  have hbody : ExS LimbGen.prog s sbBody .normal s4 := by
    unfold sbBody
    exact ExS.ite hcond htr (ExS.seq (ExS.seq hset4 hset5) (ExS.seq hst hset2))
  have s4_3 : s4.locals 3 = some (.int ⟨64, false⟩ j) := by
    simpa [hs4, hs3, Locals.upd] using s2_3
  have cast1 : EvE LimbGen.prog s4 (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ j) :=
    EvE.cast (EvE.var s4_3) (cast_u64_u64' j (by omega))
  have hadd : EvE LimbGen.prog s4 (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
      (.const (.int ⟨64, false⟩ 1))) (.int ⟨64, false⟩ (j + 1)) :=
    EvE.bin cast1 (EvE.const _) (by
      show Res.ok (Val.int ⟨64, false⟩ ((j + 1) % 18446744073709551616)) = _
      rw [Nat.mod_eq_of_lt (by omega)])
  have hstep : ExS LimbGen.prog s4 sbStep .normal
      { s4 with locals := s4.locals.upd 3 (.int ⟨64, false⟩ (j + 1)) } := by
    unfold sbStep
    exact ExS.set (EvE.cast hadd (cast_u64_u64' (j + 1) (by omega)))
  refine ⟨s4, _, hbody, hstep, ?_⟩
  have hset : (sbPrefix a b j ++ a.drop j).set j (sbLimb a b j) =
      sbPrefix a b (j + 1) ++ a.drop (j + 1) := by
    rw [List.set_append_right _ _ (by simp [sbPrefix_length]), sbPrefix_length, Nat.sub_self,
      List.drop_eq_getElem_cons hj]
    simp only [List.set_cons_zero, sbPrefix, List.append_assoc, List.singleton_append]
  have hbrn : sbBorrow a b (j + 1) = if a[j]'hj < y then 1 else 0 := by
    simp only [sbBorrow]; rw [hzx]
  refine ⟨?_, ?_, ?_, ?_, hro, ?_, ?_, ?_, ?_, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hn64, hbl64⟩
  · simpa [hs4, hs3, hs2, hs1, Locals.upd] using l0
  · simpa [hs4, hs3, hs2, hs1, Locals.upd] using l1
  · simp [hs4, hs3, hs2, hs1, Locals.upd]
    rw [hbrn]
  · simp [hs4, hs3, hs2, hs1, Locals.upd]
  · show (s.mem.upd varr _) zs = _
    simp only [Mem.upd, if_neg (Ne.symm hne1)]; exact hzs
  · show (s.mem.upd varr _) bs = _
    simp only [Mem.upd, if_neg (Ne.symm hne2)]; exact hbs
  · show (s.mem.upd varr _) barr = _
    simp only [Mem.upd, if_neg (Ne.symm hne3)]; exact hbarr
  · show (s.mem.upd varr _) varr = _
    simp only [Mem.upd, ite_true]
    rw [hset]

theorem sbLoop (zs bs varr barr : Nat) (a b : List Nat) (sg sgb : Int)
    (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32) :
    ∀ d j : Nat, j + d = a.length → ∀ s : State, sbInv zs bs varr barr a b sg sgb j s →
      ∃ sf, ExS LimbGen.prog s LimbGen.div_sub_in_loop0 .normal sf ∧
        sbInv zs bs varr barr a b sg sgb a.length sf := by
  intro d
  induction d with
  | zero =>
      intro j hj s hInv
      have hjn : j = a.length := by omega
      subst hjn
      refine ⟨s, ?_, hInv⟩
      rw [sbLoop_ast]
      obtain ⟨l0, l1, l2, l3, hro, hzs, hbs, hbarr, hv, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hn64,
        hbl64⟩ := hInv
      have hnload : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 0) 8))
          (.int ⟨64, false⟩ a.length) := by
        have hf : EvE LimbGen.prog s (.field (.var 0) 8) (.ptr zs 8) :=
          EvE.field (EvE.var l0) (by simp [ptrAddN, hzs, ziBlock_length])
        have := load_ziBlock_n s.mem zs varr a.length sg hzs
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact EvE.load hf this
      have hcond : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 3)
          (.load (.int ⟨64, false⟩) (.field (.var 0) 8))) (boolVal (decide (a.length < a.length))) :=
        EvE.bin (EvE.var l3) hnload rfl
      have tb : ∀ c : Bool, truthy (boolVal c) = .ok c := by intro c; cases c <;> rfl
      have hf : truthy (boolVal (decide (a.length < a.length))) = .ok false := by
        rw [tb]; simp
      apply ExS.loop_brk
      unfold sbBody
      exact ExS.ite hcond hf ExS.brk
  | succ d ih =>
      intro j hj s hInv
      obtain ⟨s1, s2, hb', hs, hInv2⟩ := sbIter zs bs varr barr a b sg sgb j s ha hb (by omega) hInv
      obtain ⟨sf, hl, hfin⟩ := ih (j + 1) (by omega) s2 hInv2
      refine ⟨sf, ?_, hfin⟩
      rw [sbLoop_ast]
      rw [sbLoop_ast] at hl
      exact ExS.loop_next hb' (Or.inl rfl) hs hl

/-- `div_sub_in` subtracts `b` from `r` in place and returns the final borrow. -/
theorem div_sub_in_refines (zs bs varr barr : Nat) (a b : List Nat) (sg sgb : Int)
    (m : Mem) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.div_sub_in.params [.ptr zs 0, .ptr bs 0], m, false⟩)
    (ha : ∀ x ∈ a, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (hzs : m zs = some (ziBlock varr a.length sg)) (hbs : m bs = some (ziBlock barr b.length sgb))
    (hbarr : m barr = some (limbBytes b)) (hv : m varr = some (limbBytes a))
    (hne1 : varr ≠ zs) (hne2 : varr ≠ bs) (hne3 : varr ≠ barr)
    (hb1 : zs < 4294967296) (hb2 : bs < 4294967296) (hb3 : varr < 4294967296)
    (hb4 : barr < 4294967296) (hn64 : a.length < 18446744073709551616)
    (hbl64 : b.length < 18446744073709551616) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.div_sub_in.body
        (.ret (some (.int ⟨64, false⟩ (sbBorrow a b a.length)))) sf ∧
      sf.mem varr = some (limbBytes (sbPrefix a b a.length)) ∧ sf.mem zs = m zs ∧
      sf.mem bs = m bs ∧ sf.mem barr = m barr := by
  have l0 : s0.locals 0 = some (.ptr zs 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.ptr bs 0) := by rw [h0]; rfl
  have hmem : s0.mem = m := by rw [h0]
  have hro : s0.ro = false := by rw [h0]
  have hset2 : ExS LimbGen.prog s0 (.set 2 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s0 with locals := s0.locals.upd 2 (.int ⟨64, false⟩ 0) } :=
    ExS.set (EvE.cast (EvE.const _) rfl)
  set s1 : State := { s0 with locals := s0.locals.upd 2 (.int ⟨64, false⟩ 0) } with hs1
  have hset3 : ExS LimbGen.prog s1 (.set 3 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s1 with locals := s1.locals.upd 3 (.int ⟨64, false⟩ 0) } :=
    ExS.set (EvE.cast (EvE.const _) rfl)
  set s2 : State := { s1 with locals := s1.locals.upd 3 (.int ⟨64, false⟩ 0) } with hs2
  have hInv0 : sbInv zs bs varr barr a b sg sgb 0 s2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne1, hne2, hne3, hb1, hb2, hb3, hb4, hn64, hbl64⟩
    · simpa [hs2, hs1, Locals.upd] using l0
    · simpa [hs2, hs1, Locals.upd] using l1
    · simp [hs2, hs1, Locals.upd, sbBorrow]
    · simp [hs2, hs1, Locals.upd]
    · simp [hs2, hs1, hro]
    · simpa [hs2, hs1, hmem] using hzs
    · simpa [hs2, hs1, hmem] using hbs
    · simpa [hs2, hs1, hmem] using hbarr
    · simpa [hs2, hs1, hmem, sbPrefix] using hv
  obtain ⟨sf, hloop, hfin⟩ := sbLoop zs bs varr barr a b sg sgb ha hb a.length 0 (by omega) s2 hInv0
  obtain ⟨-, -, l2', -, -, hzs', hbs', hbarr', hv', -, -, -, -, -, -, -, -, -⟩ := hfin
  refine ⟨sf, ?_, ?_, ?_, ?_, ?_⟩
  · unfold LimbGen.div_sub_in
    show ExS LimbGen.prog s0 (.seq _ (.seq (.seq _ LimbGen.div_sub_in_loop0) (.ret (some (.var 2))))) _ sf
    exact ExS.seq hset2 (ExS.seq (ExS.seq hset3 hloop) (ExS.ret (EvE.var l2')))
  · simpa [sbPrefix_length, List.drop_length] using hv'
  · rw [hzs', hzs]
  · rw [hbs', hbs]
  · rw [hbarr', hbarr]

end Tess.C
