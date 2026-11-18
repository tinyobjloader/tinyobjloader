/-
  MiniC refinement of the translated `div_cmp` (`lib/tess/src/exact.c`, the compare step of the binary
  path of `zi_divrem`): for `r` with `|b|+1` limbs it returns `1` when `lv r > lv b`, `0` when equal and
  `-1` when `lv r < lv b` (`dcFull_spec`). Pure: reads the two limb arrays only.
-/
import Tess.C.DivBitStep
import Tess.C.Acmp
import Tess.C.TrimLen

namespace Tess.C
open Obj.C

theorem tv_succ (l : List Nat) (k : Nat) :
    tv l (k + 1) = tv l k + ziAddTerm l k * 2 ^ (32 * k) := rfl

theorem tv_lt (l : List Nat) (hl : ∀ x ∈ l, x < 2 ^ 32) : ∀ k, tv l k < 2 ^ (32 * k) := by
  intro k
  induction k with
  | zero => simp [tv]
  | succ k ih =>
      have hx := zat_lt l hl k
      rw [tv_succ, show 32 * (k + 1) = 32 * k + 32 from by omega, pow_add]
      nlinarith [Nat.mul_le_mul_right (2 ^ (32 * k)) (show ziAddTerm l k + 1 ≤ 2 ^ 32 by omega)]

/-- Scan code over the low `k` limbs (top-down): 0 equal, 1 `r > b`, `2^32 - 1` (= int `-1`) `r < b`. -/
def dcCode (r b : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      if ziAddTerm r k ≠ ziAddTerm b k then (if ziAddTerm r k > ziAddTerm b k then 1 else 4294967295)
      else dcCode r b k

def dcFull (r b : List Nat) : Nat :=
  if ziAddTerm r b.length ≠ 0 then 1 else dcCode r b b.length

theorem dcCode_spec (r b : List Nat) (hr : ∀ x ∈ r, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32) :
    ∀ k, (dcCode r b k = 0 ∧ tv r k = tv b k) ∨ (dcCode r b k = 1 ∧ tv b k < tv r k) ∨
      (dcCode r b k = 4294967295 ∧ tv r k < tv b k) := by
  intro k
  induction k with
  | zero => left; simp [dcCode, tv]
  | succ k ih =>
      have hx := zat_lt r hr k
      have hy := zat_lt b hb k
      have hP : 0 < 2 ^ (32 * k) := by positivity
      have hrl : tv r k < 2 ^ (32 * k) := tv_lt r hr k
      have hbl : tv b k < 2 ^ (32 * k) := tv_lt b hb k
      simp only [dcCode, tv_succ]
      by_cases hne : ziAddTerm r k = ziAddTerm b k
      · rw [if_neg (by simpa using hne)]
        rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; refine ⟨h1, ?_⟩; rw [h2, hne]
        · right; left; refine ⟨h1, ?_⟩; rw [hne]; omega
        · right; right; refine ⟨h1, ?_⟩; rw [hne]; omega
      · rw [if_pos (by simpa using hne)]
        by_cases hgt : ziAddTerm r k > ziAddTerm b k
        · rw [if_pos hgt]; right; left; refine ⟨rfl, ?_⟩
          nlinarith [Nat.mul_le_mul_right (2 ^ (32 * k)) (show ziAddTerm b k + 1 ≤ ziAddTerm r k by omega)]
        · rw [if_neg hgt]; right; right; refine ⟨rfl, ?_⟩
          have : ziAddTerm r k + 1 ≤ ziAddTerm b k := by omega
          nlinarith [Nat.mul_le_mul_right (2 ^ (32 * k)) this]

theorem dcFull_spec (r b : List Nat) (hr : ∀ x ∈ r, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (hrl : r.length = b.length + 1) :
    (dcFull r b = 1 ∧ lv b < lv r) ∨ (dcFull r b = 0 ∧ lv r = lv b) ∨
      (dcFull r b = 4294967295 ∧ lv r < lv b) := by
  have hlr : lv r = tv r b.length + ziAddTerm r b.length * 2 ^ (32 * b.length) := by
    rw [← tv_len r, hrl]; exact tv_succ r b.length
  have hbl := lv_lt b hb
  unfold dcFull
  by_cases hz : ziAddTerm r b.length ≠ 0
  · rw [if_pos hz]; left; refine ⟨rfl, ?_⟩
    have : 2 ^ (32 * b.length) ≤ ziAddTerm r b.length * 2 ^ (32 * b.length) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hz)
    omega
  · rw [if_neg hz]
    have hz0 : ziAddTerm r b.length = 0 := by simpa using hz
    rw [hz0, Nat.zero_mul, Nat.add_zero] at hlr
    have hbv : tv b b.length = lv b := tv_len b
    rcases dcCode_spec r b hr hb b.length with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left; exact ⟨h1, by omega⟩
    · left; exact ⟨h1, by omega⟩
    · right; right; exact ⟨h1, by omega⟩

theorem dcLoop_ast : LimbGen.div_cmp_loop0 =
    .loop (.ite (.var 2) (.ite acmpNe (.seq (.set 3 acmpRetCond) .brk) .skip) .brk)
      (.set 2 (.cast u64 (.bin .sub (some ⟨64, false⟩) (.cast u64 (.var 2))
        (.const (.int ⟨64, false⟩ 1))))) := rfl

theorem wrap_m1 : IntTy.wrap ⟨32, true⟩ (-1) = 4294967295 := by decide

/-- Loop simulation relation with `k` limbs still to scan. -/
def dcInv (zr zb rarr barr : Nat) (r b : List Nat) (sg sgb : Int) (k : Nat) (s : State) : Prop :=
  k ≤ b.length ∧ s.locals 0 = some (.ptr zr 0) ∧ s.locals 1 = some (.ptr zb 0) ∧
  s.locals 2 = some (.int ⟨64, false⟩ k) ∧ s.locals 3 = some (.int ⟨32, true⟩ 0) ∧
  r.length = b.length + 1 ∧ (∀ x ∈ r, x < 2 ^ 32) ∧ (∀ x ∈ b, x < 2 ^ 32) ∧
  s.mem zr = some (ziBlock rarr r.length sg) ∧ s.mem zb = some (ziBlock barr b.length sgb) ∧
  s.mem rarr = some (limbBytes r) ∧ s.mem barr = some (limbBytes b) ∧
  zr < 4294967296 ∧ zb < 4294967296 ∧ rarr < 4294967296 ∧ barr < 4294967296 ∧
  b.length < 18446744073709551616

theorem dcLoop (zr zb rarr barr : Nat) (r b : List Nat) (sg sgb : Int) :
    ∀ k s, dcInv zr zb rarr barr r b sg sgb k s →
      ∃ sf, ExS LimbGen.prog s LimbGen.div_cmp_loop0 .normal sf ∧
        sf.locals 3 = some (.int ⟨32, true⟩ (dcCode r b k)) := by
  intro k
  induction k with
  | zero =>
      intro s hinv
      obtain ⟨-, -, -, l2, l3, -⟩ := hinv
      refine ⟨s, ?_, by simpa [dcCode] using l3⟩
      rw [dcLoop_ast]
      exact ExS.loop_brk (ExS.ite (EvE.var l2) (by rfl) ExS.brk)
  | succ k ih =>
      intro s hinv
      obtain ⟨hk, l0, l1, l2, l3, hrl, hr, hb, hzr, hzb, hrm, hbm, b1, b2, b3, b4, hbl⟩ := hinv
      have hkr : k < r.length := by omega
      have hkb : k < b.length := by omega
      have hj64 : k < 18446744073709551616 := by omega
      have hloadA : EvE LimbGen.prog s acmpLoadA (.int ⟨32, false⟩ (r[k]'hkr)) :=
        evLimbLoad s 0 zr rarr r k hzr b3 l0 l2 hrm hkr hr hj64
      have hloadB : EvE LimbGen.prog s acmpLoadB (.int ⟨32, false⟩ (b[k]'hkb)) :=
        evLimbLoad s 1 zb barr b k hzb b4 l1 l2 hbm hkb hb hj64
      have hne : EvE LimbGen.prog s acmpNe (boolVal (decide (r[k]'hkr ≠ b[k]'hkb))) :=
        EvE.bin hloadA hloadB (evNeU32 _ _)
      have hgt : EvE LimbGen.prog s acmpGt (boolVal (decide (r[k]'hkr > b[k]'hkb))) :=
        EvE.bin hloadA hloadB (evGtU32 _ _)
      have hout : EvE LimbGen.prog s (.var 2) (.int ⟨64, false⟩ (k + 1)) := EvE.var l2
      have htr : truthy (.int ⟨64, false⟩ (k + 1)) = .ok true := by simp [truthy]
      have hzr' : ziAddTerm r k = r[k]'hkr := by unfold ziAddTerm; rw [dif_pos hkr]
      have hzb' : ziAddTerm b k = b[k]'hkb := by unfold ziAddTerm; rw [dif_pos hkb]
      by_cases hlimb : r[k]'hkr = b[k]'hkb
      · have hdec : decide (r[k]'hkr ≠ b[k]'hkb) = false := by
          rw [decide_eq_false_iff_not]; simp [hlimb]
        have hbody : ExS LimbGen.prog s
            (.ite (.var 2) (.ite acmpNe (.seq (.set 3 acmpRetCond) .brk) .skip) .brk) .normal s :=
          ExS.ite hout htr (ExS.ite hne (by rw [hdec]; rfl) ExS.skip)
        have cast1 : EvE LimbGen.prog s (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ (k + 1)) :=
          EvE.cast (EvE.var l2) (cast_u64_u64' (k + 1) (by omega))
        have subb : EvE LimbGen.prog s (.bin .sub (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2))
            (.const (.int ⟨64, false⟩ 1))) (.int ⟨64, false⟩ k) :=
          EvE.bin cast1 (EvE.const _) (by
            show evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ (k + 1)) (.int ⟨64, false⟩ 1) = .ok (.int ⟨64, false⟩ k)
            simp only [evalBin, isPtr, Bool.and_false, ite_false, Nat.mod_eq_of_lt (by omega : k + 1 < 18446744073709551616)]
            show Res.ok (Val.int ⟨64, false⟩ (if (1:Nat) ≤ k + 1 then k + 1 - 1 else k + 1 + 18446744073709551616 - 1)) = Res.ok (Val.int ⟨64, false⟩ k)
            rw [if_pos (by omega : (1:Nat) ≤ k + 1), Nat.add_sub_cancel])
        have hstep : ExS LimbGen.prog s (.set 2 (.cast u64 (.bin .sub (some ⟨64, false⟩)
            (.cast u64 (.var 2)) (.const (.int ⟨64, false⟩ 1))))) .normal
            { s with locals := s.locals.upd 2 (.int ⟨64, false⟩ k) } :=
          ExS.set (EvE.cast subb (cast_u64_u64' k (by omega)))
        obtain ⟨sf, hl, hres⟩ := ih { s with locals := s.locals.upd 2 (.int ⟨64, false⟩ k) }
          ⟨by omega, by simpa using l0, by simpa using l1, by simp [Locals.upd], by simpa using l3,
            hrl, hr, hb, hzr, hzb, hrm, hbm, b1, b2, b3, b4, hbl⟩
        refine ⟨sf, ?_, ?_⟩
        · rw [dcLoop_ast]; rw [dcLoop_ast] at hl
          exact ExS.loop_next hbody (Or.inl rfl) hstep hl
        · rw [hres]
          simp [dcCode, hzr', hzb', hlimb]
      · have hdec : decide (r[k]'hkr ≠ b[k]'hkb) = true := by
          rw [decide_eq_true_iff]; exact hlimb
        have htn : truthy (boolVal (decide (r[k]'hkr ≠ b[k]'hkb))) = .ok true := by rw [hdec]; rfl
        by_cases hg : r[k]'hkr > b[k]'hkb
        · have hd : decide (r[k]'hkr > b[k]'hkb) = true := by rw [decide_eq_true_iff]; exact hg
          have htrt : truthy (boolVal (decide (r[k]'hkr > b[k]'hkb))) = .ok true := by rw [hd]; rfl
          have hret : EvE LimbGen.prog s acmpRetCond (.int ⟨32, true⟩ 1) :=
            EvE.cond hgt htrt (EvE.const _)
          refine ⟨{ s with locals := s.locals.upd 3 (.int ⟨32, true⟩ 1) }, ?_, ?_⟩
          · rw [dcLoop_ast]
            exact ExS.loop_brk (ExS.ite hout htr (ExS.ite hne htn (ExS.seq (ExS.set hret) ExS.brk)))
          · simp [dcCode, hzr', hzb', hlimb, hg, Locals.upd]
        · have hd : decide (r[k]'hkr > b[k]'hkb) = false := by rw [decide_eq_false_iff_not]; exact hg
          have htrt : truthy (boolVal (decide (r[k]'hkr > b[k]'hkb))) = .ok false := by rw [hd]; rfl
          have hret : EvE LimbGen.prog s acmpRetCond (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))) :=
            EvE.cond hgt htrt (EvE.un (EvE.const _) (by rfl))
          refine ⟨{ s with locals := s.locals.upd 3 (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-1))) }, ?_, ?_⟩
          · rw [dcLoop_ast]
            exact ExS.loop_brk (ExS.ite hout htr (ExS.ite hne htn (ExS.seq (ExS.set hret) ExS.brk)))
          · simp [dcCode, hzr', hzb', hlimb, hg, Locals.upd, wrap_m1]

/-- `div_cmp` returns `dcFull r b` (1 / 0 / -1). -/
theorem div_cmp_refines (zr zb rarr barr : Nat) (r b : List Nat) (sg sgb : Int)
    (m : Mem) (ro : Bool) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.div_cmp.params [.ptr zr 0, .ptr zb 0], m, ro⟩)
    (hrl : r.length = b.length + 1) (hr : ∀ x ∈ r, x < 2 ^ 32) (hb : ∀ x ∈ b, x < 2 ^ 32)
    (hzr : m zr = some (ziBlock rarr r.length sg)) (hzb : m zb = some (ziBlock barr b.length sgb))
    (hrm : m rarr = some (limbBytes r)) (hbm : m barr = some (limbBytes b))
    (b1 : zr < 4294967296) (b2 : zb < 4294967296) (b3 : rarr < 4294967296) (b4 : barr < 4294967296)
    (hbl : b.length < 18446744073709551616) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.div_cmp.body (.ret (some (.int ⟨32, true⟩ (dcFull r b)))) sf := by
  have l0 : s0.locals 0 = some (.ptr zr 0) := by rw [h0]; rfl
  have l1 : s0.locals 1 = some (.ptr zb 0) := by rw [h0]; rfl
  have hmem : s0.mem = m := by rw [h0]
  have hzr' : s0.mem zr = some (ziBlock rarr r.length sg) := by rw [hmem]; exact hzr
  have hzb' : s0.mem zb = some (ziBlock barr b.length sgb) := by rw [hmem]; exact hzb
  have hrm' : s0.mem rarr = some (limbBytes r) := by rw [hmem]; exact hrm
  have hbm' : s0.mem barr = some (limbBytes b) := by rw [hmem]; exact hbm
  have hbn : b.length < r.length := by omega
  have tb : ∀ c : Bool, truthy (boolVal c) = .ok c := by intro c; cases c <;> rfl
  -- the top limb load: index = b.n
  have hbnload : EvE LimbGen.prog s0 (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
      (.int ⟨64, false⟩ b.length) := by
    have hf : EvE LimbGen.prog s0 (.field (.var 1) 8) (.ptr zb 8) :=
      EvE.field (EvE.var l1) (by simp [ptrAddN, hzb', ziBlock_length])
    have := load_ziBlock_n s0.mem zb barr b.length sgb hzb'
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact EvE.load hf this
  have hbase : EvE LimbGen.prog s0 (.load .ptr (.field (.var 0) 0)) (.ptr rarr 0) :=
    evVPointer s0 0 zr rarr r.length hzr' b3 l0
  have hidx : EvE LimbGen.prog s0 (.index (.load .ptr (.field (.var 0) 0))
      (.load (.int ⟨64, false⟩) (.field (.var 1) 8)) 4) (.ptr rarr (4 * b.length)) := by
    apply EvE.index hbase hbnload
    simp only [u64, Bool.false_eq_true, if_false]
    simp only [ptrAddN, hrm']
    have hbl' := limbBytes_length r
    rw [if_pos (by rw [hbl']; omega)]
    congr 2
    omega
  have hload : EvE LimbGen.prog s0 (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
      (.load (.int ⟨64, false⟩) (.field (.var 1) 8)) 4)) (.int ⟨32, false⟩ (r[b.length]'hbn)) := by
    apply EvE.load hidx
    show load s0.mem (.int u32) (.ptr rarr (4 * b.length)) = .ok (.int u32 (r[b.length]'hbn))
    rw [load_limb s0.mem rarr r b.length hrm' hbn]
    congr 1
    rw [Nat.mod_eq_of_lt (hr _ (List.getElem_mem hbn))]
  have hzt : ziAddTerm r b.length = r[b.length]'hbn := by unfold ziAddTerm; rw [dif_pos hbn]
  by_cases htop : r[b.length]'hbn = 0
  · -- top limb zero: scan
    have hdec : decide (r[b.length]'hbn ≠ 0) = false := by simp [htop]
    have hc : EvE LimbGen.prog s0 (.cond (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
        (.load (.int ⟨64, false⟩) (.field (.var 1) 8)) 4)) (.const (.int ⟨32, true⟩ 1))
        (.const (.int ⟨32, true⟩ 0))) (.int ⟨32, true⟩ 0) :=
      EvE.cond (bc := false) hload (by simp [truthy, htop]) (EvE.const _)
    have hset3 := ExS.set (i := 3) hc
    set s1 : State := { s0 with locals := s0.locals.upd 3 (.int ⟨32, true⟩ 0) } with hs1
    have s1_3 : s1.locals 3 = some (.int ⟨32, true⟩ 0) := by simp [hs1, Locals.upd]
    have hnot : EvE LimbGen.prog s1 (.un .lnot ⟨32, true⟩ (.var 3)) (boolVal true) :=
      EvE.un (EvE.var s1_3) (by simp [evalUn, truthy])
    have s1_1 : s1.locals 1 = some (.ptr zb 0) := by simpa [hs1, Locals.upd] using l1
    have hbn1 : EvE LimbGen.prog s1 (.load (.int ⟨64, false⟩) (.field (.var 1) 8))
        (.int ⟨64, false⟩ b.length) := by
      have hf : EvE LimbGen.prog s1 (.field (.var 1) 8) (.ptr zb 8) :=
        EvE.field (EvE.var s1_1) (by simp [hs1, ptrAddN, hzb', ziBlock_length])
      have := load_ziBlock_n s1.mem zb barr b.length sgb (by simpa [hs1] using hzb')
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact EvE.load hf this
    have hset2 := ExS.set (i := 2) hbn1
    set s2 : State := { s1 with locals := s1.locals.upd 2 (.int ⟨64, false⟩ b.length) } with hs2
    obtain ⟨sf, hloop, hres⟩ := dcLoop zr zb rarr barr r b sg sgb b.length s2
      ⟨le_rfl, by simpa [hs2, hs1, Locals.upd] using l0, by simpa [hs2, hs1, Locals.upd] using l1,
        by simp [hs2, hs1, Locals.upd], by simp [hs2, hs1, Locals.upd], hrl, hr, hb,
        by simpa [hs2, hs1, hmem] using hzr, by simpa [hs2, hs1, hmem] using hzb,
        by simpa [hs2, hs1, hmem] using hrm, by simpa [hs2, hs1, hmem] using hbm, b1, b2, b3, b4, hbl⟩
    have hfull : dcFull r b = dcCode r b b.length := by
      unfold dcFull; rw [hzt, if_neg (by simpa using htop)]
    refine ⟨sf, ?_⟩
    unfold LimbGen.div_cmp
    show ExS LimbGen.prog s0 (.seq _ (.seq (.ite _ (.seq _ LimbGen.div_cmp_loop0) .skip)
      (.ret (some (.var 3))))) _ sf
    rw [← hfull] at hres
    exact ExS.seq hset3 (ExS.seq (ExS.ite hnot (tb true) (ExS.seq hset2 hloop))
      (ExS.ret (EvE.var hres)))
  · -- nonzero top limb: result 1
    have hc : EvE LimbGen.prog s0 (.cond (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
        (.load (.int ⟨64, false⟩) (.field (.var 1) 8)) 4)) (.const (.int ⟨32, true⟩ 1))
        (.const (.int ⟨32, true⟩ 0))) (.int ⟨32, true⟩ 1) :=
      EvE.cond (bc := true) hload (by simp [truthy, htop]) (EvE.const _)
    have hset3 := ExS.set (i := 3) hc
    set s1 : State := { s0 with locals := s0.locals.upd 3 (.int ⟨32, true⟩ 1) } with hs1
    have s1_3 : s1.locals 3 = some (.int ⟨32, true⟩ 1) := by simp [hs1, Locals.upd]
    have hnot : EvE LimbGen.prog s1 (.un .lnot ⟨32, true⟩ (.var 3)) (boolVal false) :=
      EvE.un (EvE.var s1_3) (by simp [evalUn, truthy])
    have hfull : dcFull r b = 1 := by
      unfold dcFull; rw [hzt, if_pos (by simpa using htop)]
    refine ⟨s1, ?_⟩
    unfold LimbGen.div_cmp
    show ExS LimbGen.prog s0 (.seq _ (.seq (.ite _ (.seq _ LimbGen.div_cmp_loop0) .skip)
      (.ret (some (.var 3))))) _ s1
    rw [hfull]
    exact ExS.seq hset3 (ExS.seq (ExS.ite hnot (tb false) ExS.skip) (ExS.ret (EvE.var s1_3)))

end Tess.C
