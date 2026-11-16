/-
  Refinement proof for the `zi_add_mixed` kernel in `lib/tess/src/exact.c`,
  as translated by c2lean into `Tess/C/LimbGen.lean`. The loop sweeps from
  least significant limb to most significant, subtracting `y` from `x` at
  64-bit precision and recording the borrow.

  Claims are about the translated MiniC program, arbitrary memories
  containing the `zi` struct/array blocks and one writable block for the
  destination limb array with capacity at least n + 1. No claim is made
  about the C allocator, `norm`, `move`, `zi_add`, `zi_sub`, or error
  handling; the C budget checks are outside this refinement.
-/
import Obj.C.Hoare
import Obj.C.Splice
import Tess.C.LimbGen
import Tess.C.ZiMem
import Tess.C.Acmp
import Tess.C.ZiAdd

namespace Tess.C
open Obj.C

/-- Limb of the mixed difference at position `i`: `y' := yLimb + borrow`, then
`x ≥ y'`: `x - y'` else `x + 2^32 - y'` (wraps; borrow only when `x < y'`). -/
def ziMixedLimb (aLimbs bLimbs : List Nat) (i borrow : Nat) : Nat :=
  if ziAddTerm aLimbs i ≥ ziAddTerm bLimbs i + borrow
  then ziAddTerm aLimbs i - (ziAddTerm bLimbs i + borrow)
  else ziAddTerm aLimbs i + 2 ^ 32 - (ziAddTerm bLimbs i + borrow)

/-- Borrow out of position `i`. -/
def ziMixedBorrow (aLimbs bLimbs : List Nat) (i borrow : Nat) : Nat :=
  if ziAddTerm aLimbs i < ziAddTerm bLimbs i + borrow then 1 else 0

/-- Borrow after `k` positions. -/
def ziMixedBorrowPrefix (aLimbs bLimbs : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ziMixedBorrow aLimbs bLimbs k (ziMixedBorrowPrefix aLimbs bLimbs k)

/-- Result limbs after `k` positions, low to high. -/
def ziMixedPrefix (aLimbs bLimbs : List Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => ziMixedPrefix aLimbs bLimbs k ++
      [ziMixedLimb aLimbs bLimbs k (ziMixedBorrowPrefix aLimbs bLimbs k)]

theorem ziMixedBorrowPrefix_bound (aLimbs bLimbs : List Nat) (i : Nat) :
    ziMixedBorrowPrefix aLimbs bLimbs i ≤ 1 := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      unfold ziMixedBorrowPrefix ziMixedBorrow
      split
      · exact Nat.one_le_iff_ne_zero.mpr (by decide)
      · omega

/-- `y'` never exceeds `2 ^ 32`: limb is at most `2 ^ 32 - 1` plus borrow 1. -/
theorem ziMixed_yv_bound (bLimbs : List Nat) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (i carry : Nat) (hcarry : carry ≤ 1) :
    ziAddTerm bLimbs i + carry ≤ 2 ^ 32 := by
  have := ziAddTerm_bound bLimbs hllb i
  omega

/-- Every `ziMixedLimb` result fits a 32-bit limb. -/
theorem ziMixedLimb_bound (aLimbs bLimbs : List Nat)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (i carry : Nat) (hcarry : carry ≤ 1) :
    ziMixedLimb aLimbs bLimbs i carry < 2 ^ 32 := by
  have hxv := ziAddTerm_bound aLimbs hlla i
  have hyv := ziMixed_yv_bound bLimbs hllb i carry hcarry
  unfold ziMixedLimb
  split
  · omega
  · omega

theorem ziMixedPrefix_length (aLimbs bLimbs : List Nat) (k : Nat) :
    (ziMixedPrefix aLimbs bLimbs k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ziMixedPrefix, ih]


/-- Simulation relation for the `zi_add_mixed` sweep after `i` positions.
`tsblk` is the `zi` struct block for the destination (`t`), `tarr` its limb
array; `asblk`/`aarr` and `bsblk`/`barr` the struct/array blocks of the sources.
Tail limbs above `i` are zero-initialized fresh limbs. -/
def ziMixedLoopInv (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n i carry : Nat)
    (s : State) : Prop :=
  i ≤ n ∧ i < 18446744073709551616 ∧ n < 18446744073709551616 ∧
    aLen < 18446744073709551616 ∧ bLen < 18446744073709551616 ∧ carry ≤ 1 ∧
    s.ro = false ∧
    aLimbs.length = aLen ∧ bLimbs.length = bLen ∧
    (∀ x ∈ aLimbs, x < 2 ^ 32) ∧ (∀ x ∈ bLimbs, x < 2 ^ 32) ∧
    carry = ziMixedBorrowPrefix aLimbs bLimbs i ∧
    s.locals 0 = some (.ptr tsblk 0) ∧ s.locals 1 = some (.ptr asblk 0) ∧
    s.locals 2 = some (.ptr bsblk 0) ∧ s.locals 3 = some (.int ⟨64, false⟩ n) ∧
    s.locals 4 = some (.int ⟨64, false⟩ i) ∧ s.locals 5 = some (.int ⟨64, false⟩ carry) ∧
    s.mem tsblk = some (ziBlock tarr (n + 1) 1) ∧ s.mem asblk = some (ziBlock aarr aLen 1) ∧
    s.mem bsblk = some (ziBlock barr bLen 1) ∧
    s.mem aarr = some (limbBytes aLimbs) ∧ s.mem barr = some (limbBytes bLimbs) ∧
    (s.mem tarr = some (limbBytes ((ziMixedPrefix aLimbs bLimbs i) ++
      (List.replicate (n + 1 - i) 0)))) ∧
    tsblk < 4294967296 ∧ tarr < 4294967296 ∧ asblk < 4294967296 ∧
    aarr < 4294967296 ∧ bsblk < 4294967296 ∧ barr < 4294967296 ∧
    tarr ≠ tsblk ∧ tarr ≠ asblk ∧ tarr ≠ bsblk ∧ tarr ≠ aarr ∧ tarr ≠ barr

/-- Store the truncated sub-limb into the destination at index `i`. -/
def ziMixedStoreVal : Expr := .cast ⟨32, false⟩ (.bin .sub (some ⟨64, false⟩) (.var 6) (.var 7))

/-- The y'-add of prior borrow: adds borrow to the conditional term. -/
def ziMixedYvExpr : Expr := (.bin .add (some ⟨64, false⟩)
  (.cast ⟨64, false⟩
    (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
        (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
      (.load (.int ⟨32, false⟩)
         (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4))
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
  (.var 5))

/-- The full x-load expression: `.set 6` with the conditional limb load. -/
def ziMixedXvSet : Expr := (.cast ⟨64, false⟩
    (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
        (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
      (.load (.int ⟨32, false⟩)
         (.index (.load .ptr (.field (.var 1) 0)) (.var 4) 4))
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))

/-- Set borrow: `.set 5` with the limb comparison. -/
def ziMixedSetBorrow : Stmt := .set 5
  (.cast ⟨64, false⟩ (.bin .lt (some ⟨64, false⟩) (.var 6) (.var 7)))

/-- The store target for the mixed-difference limb. -/
def ziMixedStoreIdx : Expr := .index (.load .ptr (.field (.var 0) 0)) (.var 4) 4

/-- The loop body AST for `zi_add_mixed_loop0`. -/
def ziMixedBody : Stmt :=
  .ite (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 3))
    (.seq (.seq (.set 6 ziMixedXvSet) (.set 7 ziMixedYvExpr))
      (.seq (.store (.int ⟨32, false⟩) ziMixedStoreIdx ziMixedStoreVal) ziMixedSetBorrow))
    .brk

/-- The step statement of the mixed loop. -/
def ziMixedStep : Stmt :=
  .set 4 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
    (.const (.int ⟨64, false⟩ 1))))

theorem ziMixedLoop_ast : Tess.C.LimbGen.zi_add_mixed_loop0 =
    Stmt.loop ziMixedBody ziMixedStep := by
  rfl

/-- Unsigned 64-bit subtract of two u64 values in the mixed sweep. -/
theorem evSubVal (xv yv : Nat) : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ xv) (.int ⟨64, false⟩ yv) =
    .ok (.int ⟨64, false⟩ (if yv ≤ xv then xv - yv else xv + 2 ^ 64 - yv)) := rfl

/-- The stored limb is the mixed limb of the positional sum. -/
theorem evCastSub (xv yv : Nat) (hxv : xv < 2 ^ 32) (hyv : yv ≤ 2 ^ 32) :
    evalCast ⟨32, false⟩
      (.int ⟨64, false⟩ (if yv ≤ xv then xv - yv else xv + 2 ^ 64 - yv)) =
    .ok (.int ⟨32, false⟩ (if xv ≥ yv then xv - yv else xv + 2 ^ 32 - yv)) := by
  by_cases h : xv ≥ yv
  · simp only [evalCast, Bool.false_eq_true, if_false, IntTy.modulus, if_pos (by omega : yv ≤ xv),
      if_pos (by omega : xv ≥ yv)]
    rw [Nat.mod_eq_of_lt (by omega : xv - yv < 4294967296)]
  · simp only [evalCast, Bool.false_eq_true, if_false, IntTy.modulus, if_neg (by omega : ¬ (yv ≤ xv)),
      if_neg (by omega : ¬ (xv ≥ yv))]
    have hpow : (2 ^ 32 : Nat) = 4294967296 := rfl
    rw [hpow]
    have hdec : xv + 18446744073709551616 - yv =
        (xv + 4294967296 - yv) + 4294967296 * 4294967295 := by omega
    rw [hdec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : xv + 4294967296 - yv < 4294967296)]

/-- The `xv < yv` comparison evaluates to `.int i32 1/0`. -/
theorem evLt64 (xv yv : Nat) :
    evalBin .lt (some ⟨64, false⟩) (.int ⟨64, false⟩ xv) (.int ⟨64, false⟩ yv) =
    .ok (.int ⟨32, true⟩ (if decide (xv < yv) then 1 else 0)) := rfl

theorem ziMixedPrefix_set (aLimbs bLimbs : List Nat) (n i carry : Nat) (h : i < n)
    (hcarry : carry = ziMixedBorrowPrefix aLimbs bLimbs i) :
    (ziMixedPrefix aLimbs bLimbs i ++ List.replicate (n + 1 - i) 0).set i
      (ziMixedLimb aLimbs bLimbs i carry) =
      ziMixedPrefix aLimbs bLimbs (i + 1) ++ List.replicate (n - i) 0 := by
  have hlen : (ziMixedPrefix aLimbs bLimbs i).length = i := ziMixedPrefix_length aLimbs bLimbs i
  rw [List.set_append, if_neg (by omega), hlen]
  have hne : n + 1 - i = (n - i) + 1 := by omega
  rw [hne, Nat.sub_self, List.replicate_succ, List.set_cons_zero]
  show ziMixedPrefix aLimbs bLimbs i ++
      (ziMixedLimb aLimbs bLimbs i carry :: List.replicate (n - i) 0) =
      ziMixedPrefix aLimbs bLimbs (i + 1) ++ List.replicate (n - i) 0
  simp [ziMixedPrefix]
  rw [hcarry]

/-- The store target index expression. -/
def ziMixedStoreStmt : Stmt := .store (.int ⟨32, false⟩) ziMixedStoreIdx ziMixedStoreVal

theorem ziMixed_iCell (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n i carry : Nat)
    (hInv : ziMixedLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry s)
    (hi : i < n) :
    ∃ s1 s2, ExS LimbGen.prog s ziMixedBody .normal s1 ∧
      ExS LimbGen.prog s1 ziMixedStep .normal s2 ∧
      ziMixedLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n (i + 1)
        (ziMixedBorrow aLimbs bLimbs i carry) s2 := by
  obtain ⟨hle, hlt64, hn64, hLen64, hLen64B, hcarry, hro, hna, hnb, hlla, hllb, hcarryEq,
    hloc0, hloc1, hloc2, hloc3, hloc4, hloc5,
    hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
    _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
    _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩ := hInv
  have hi' : i < 18446744073709551616 := by omega
  have nBoundA : aLimbs.length < 18446744073709551616 := by rw [hna]; exact hLen64
  have nBoundB : bLimbs.length < 18446744073709551616 := by rw [hnb]; exact hLen64B
  have step_def : ziAddTerm aLimbs i + ziAddTerm bLimbs i + carry = ziAddStep aLimbs bLimbs i carry := rfl
  have step_grouish : ziAddTerm aLimbs i + (ziAddTerm bLimbs i + carry) < 18446744073709551616 := by
    have hA := ziAddTerm_bound aLimbs hlla i
    have hB := ziAddTerm_bound bLimbs hllb i
    omega
  have hyv' : ziAddTerm bLimbs i + carry ≤ 2 ^ 32 := ziMixed_yv_bound bLimbs hllb i carry hcarry
  have hxv' := ziAddTerm_bound aLimbs hlla i
  let s6 : State := { s with locals := s.locals.upd 6 (.int ⟨64, false⟩ (ziAddTerm aLimbs i)) }
  have hset6 : ExS LimbGen.prog s (.set 6 ziMixedXvSet) .normal s6 := by
    exact ExS.set (evAddTermCond s 1 asblk aarr aLimbs i (by rw [hna]; exact hastruct) _haarrBound hloc1 hloc4
      haLimbs hlla hi' (by rw [hna]; omega))
  have hloc5' : s6.locals 5 = some (.int ⟨64, false⟩ carry) := by simp [s6, Locals.upd]; exact hloc5
  have hl4' : s6.locals 4 = some (.int ⟨64, false⟩ i) := by simp [s6, Locals.upd]; exact hloc4
  have hloc6' : s6.locals 6 = some (.int ⟨64, false⟩ (ziAddTerm aLimbs i)) := by simp [s6, Locals.upd]
  have hloc0' : s6.locals 0 = some (Val.ptr tsblk 0) := by simp [s6, Locals.upd]; exact hloc0
  have hloc1' : s6.locals 1 = some (Val.ptr asblk 0) := by simp [s6, Locals.upd]; exact hloc1
  have hloc2' : s6.locals 2 = some (Val.ptr bsblk 0) := by simp [s6, Locals.upd]; exact hloc2
  have hloc3' : s6.locals 3 = some (Val.int ⟨64, false⟩ n) := by simp [s6, Locals.upd]; exact hloc3
  have hyvb : EvE LimbGen.prog s6 ziMixedYvExpr (.int ⟨64, false⟩ (ziAddTerm bLimbs i + carry)) := by
    show EvE LimbGen.prog s6
      (.bin .add (some ⟨64, false⟩)
        (.cast ⟨64, false⟩
          (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
              (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
            (.load (.int ⟨32, false⟩)
               (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4))
            (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
        (.var 5)) _
    have hyvbwd : EvE LimbGen.prog s6
        (.cast ⟨64, false⟩
          (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
              (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
            (.load (.int ⟨32, false⟩)
               (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4))
            (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
        (.int ⟨64, false⟩ (ziAddTerm bLimbs i)) :=
      evAddTermCond s6 2 bsblk barr bLimbs i (by rw [hnb]; exact hbstruct) _hbarBound hloc2' hl4'
        hbLimbs hllb hi' (by rw [hnb]; omega)
    have hsumBound : ziAddTerm bLimbs i + carry < 18446744073709551616 := by omega
    exact EvE.bin hyvbwd (EvE.var hloc5') (add_u64_bound (ziAddTerm bLimbs i) carry hsumBound)
  let s7 : State := { s6 with locals := s6.locals.upd 7 (.int ⟨64, false⟩ (ziAddTerm bLimbs i + carry)) }
  have hset7 : ExS LimbGen.prog s6 (.set 7 ziMixedYvExpr) .normal s7 := ExS.set hyvb
  have hloc6'' : s7.locals 6 = some (.int ⟨64, false⟩ (ziAddTerm aLimbs i)) := by simp [s7, s6, Locals.upd]
  have hloc7'' : s7.locals 7 = some (.int ⟨64, false⟩ (ziAddTerm bLimbs i + carry)) := by simp [s7, s6, Locals.upd]
  have hloc0'' : s7.locals 0 = some (Val.ptr tsblk 0) := by simp [s7, s6, Locals.upd]; exact hloc0
  have hloc4'' : s7.locals 4 = some (.int ⟨64, false⟩ i) := by simp [s7, s6, Locals.upd]; exact hloc4
  have hro7 : s7.ro = false := by show s.ro = false; exact hro
  -- store target
  have hloadPtr7 : EvE LimbGen.prog s7 (.load .ptr (.field (.var 0) 0)) (.ptr tarr 0) :=
    evVPointer s7 0 tsblk tarr (n + 1) hnaz _hTarbound hloc0''
  have hidx7 : EvE LimbGen.prog s7
      (.index (.load .ptr (.field (.var 0) 0)) (.var 4) 4) (.ptr tarr (i * 4)) := by
    apply EvE.index hloadPtr7 (EvE.var hloc4'')
    simp only [s7, s6, u64, Bool.false_eq_true, if_false]
    show ptrAddN _ _ _ = _
    simp only [ptrAddN, hmemTarr]
    rw [if_pos (by
      show 0 + i * 4 ≤ (limbBytes (ziMixedPrefix aLimbs bLimbs i ++ List.replicate (n + 1 - i) 0)).length
      rw [limbBytes_length, List.length_append, List.length_replicate, ziMixedPrefix_length]
      omega)]
    rw [show 0 + i * 4 = i * 4 from Nat.zero_add _]
  have hval7 : EvE LimbGen.prog s7 ziMixedStoreVal
      (.int ⟨32, false⟩ (ziMixedLimb aLimbs bLimbs i carry)) := by
    show EvE LimbGen.prog s7 (.cast ⟨32, false⟩ (.bin .sub (some ⟨64, false⟩) (.var 6) (.var 7))) _
    have hval : EvE LimbGen.prog s7 (.bin .sub (some ⟨64, false⟩) (.var 6) (.var 7))
        (.int ⟨64, false⟩ (if ziAddTerm bLimbs i + carry ≤ ziAddTerm aLimbs i then
            ziAddTerm aLimbs i - (ziAddTerm bLimbs i + carry) else ziAddTerm aLimbs i + 2 ^ 64 - (ziAddTerm bLimbs i + carry))) :=
      EvE.bin (EvE.var hloc6'') (EvE.var hloc7'')
        (evSubVal (ziAddTerm aLimbs i) (ziAddTerm bLimbs i + carry))
    have hcast := evCastSub (ziAddTerm aLimbs i) (ziAddTerm bLimbs i + carry) hxv' hyv'
    have heyc : ziMixedLimb aLimbs bLimbs i carry =
        (if ziAddTerm aLimbs i ≥ ziAddTerm bLimbs i + carry then
          ziAddTerm aLimbs i - (ziAddTerm bLimbs i + carry)
          else ziAddTerm aLimbs i + 2 ^ 32 - (ziAddTerm bLimbs i + carry)) := rfl
    exact EvE.cast hval hcast
  have hlimbbound : i < (ziMixedPrefix aLimbs bLimbs i ++ List.replicate (n + 1 - i) 0).length := by
    rw [List.length_append, List.length_replicate, ziMixedPrefix_length]; omega
  have hstore : ExS LimbGen.prog s7
      (.store (.int ⟨32, false⟩) ziMixedStoreIdx ziMixedStoreVal) .normal
      { s7 with mem := s7.mem.upd tarr (limbBytes (ziMixedPrefix aLimbs bLimbs (i + 1) ++
          List.replicate (n - i) 0)) } := by
    have hstore' := store_limb s7.mem tarr (ziMixedPrefix aLimbs bLimbs i ++ List.replicate (n + 1 - i) 0) i
      (ziMixedLimb aLimbs bLimbs i carry) hmemTarr hlimbbound
    have hpre1 := ziMixedPrefix_set aLimbs bLimbs n i carry (by omega) hcarryEq
    rw [hpre1] at hstore'
    have hro8 : s7.ro = false := hro7
    have hidx7' : EvE LimbGen.prog s7 (.index (.load .ptr (.field (.var 0) 0)) (.var 4) 4)
        (.ptr tarr (4 * i)) := by
      rw [Nat.mul_comm]; exact hidx7
    exact ExS.store hidx7' hval7 hro8 hstore'
  let s8 : State := { s7 with mem := s7.mem.upd tarr (limbBytes (ziMixedPrefix aLimbs bLimbs (i + 1) ++
          List.replicate (n - i) 0)) }
  have hl6s : s8.locals 6 = some (.int ⟨64, false⟩ (ziAddTerm aLimbs i)) := by simp [s8, s7, s6, Locals.upd]
  have hl7s : s8.locals 7 = some (.int ⟨64, false⟩ (ziAddTerm bLimbs i + carry)) := by simp [s8, s7, s6, Locals.upd]
  have hltval : EvE LimbGen.prog s8 (.bin .lt (some ⟨64, false⟩) (.var 6) (.var 7))
      (.int ⟨32, true⟩ (if decide (ziAddTerm aLimbs i < ziAddTerm bLimbs i + carry) then 1 else 0)) :=
    EvE.bin (EvE.var hl6s) (EvE.var hl7s) (by rfl)
  have hborrow : EvE LimbGen.prog s8
      (.cast ⟨64, false⟩ (.bin .lt (some ⟨64, false⟩) (.var 6) (.var 7)))
      (.int ⟨64, false⟩ (ziMixedBorrow aLimbs bLimbs i carry)) := by
    by_cases h : ziAddTerm aLimbs i < ziAddTerm bLimbs i + carry
    · have hltval : EvE LimbGen.prog s8
          (.bin .lt (some ⟨64, false⟩) (.var 6) (.var 7))
          (boolVal (decide (ziAddTerm aLimbs i < ziAddTerm bLimbs i + carry))) :=
        EvE.bin (EvE.var hl6s) (EvE.var hl7s) (by rfl)
      have hcast : evalCast ⟨64, false⟩
          (boolVal (decide (ziAddTerm aLimbs i < ziAddTerm bLimbs i + carry))) =
          .ok (.int ⟨64, false⟩ 1) := by
        rw [decide_eq_true_iff.mpr h]
        rfl
      simp only [ziMixedBorrow, if_pos h]
      exact EvE.cast hltval hcast
    · have hltval : EvE LimbGen.prog s8
          (.bin .lt (some ⟨64, false⟩) (.var 6) (.var 7))
          (boolVal (decide (ziAddTerm aLimbs i < ziAddTerm bLimbs i + carry))) :=
        EvE.bin (EvE.var hl6s) (EvE.var hl7s) (by rfl)
      have hcast : evalCast ⟨64, false⟩
          (boolVal (decide (ziAddTerm aLimbs i < ziAddTerm bLimbs i + carry))) =
          .ok (.int ⟨64, false⟩ 0) := by
        rw [decide_eq_false_iff_not.mpr h]
        rfl
      simp only [ziMixedBorrow, if_neg h]
      exact EvE.cast hltval hcast
  let s9 : State := { s8 with locals := s8.locals.upd 5 (.int ⟨64, false⟩ (ziMixedBorrow aLimbs bLimbs i carry)) }
  have hset5 : ExS LimbGen.prog s8 ziMixedSetBorrow .normal s9 := by
    show ExS LimbGen.prog s8 (.set 5 (.cast ⟨64, false⟩ (.bin .lt (some ⟨64, false⟩) (.var 6) (.var 7)))) .normal s9
    exact ExS.set hborrow
  have hbody : ExS LimbGen.prog s
      (.ite (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 3))
        (.seq (.seq (.set 6 ziMixedXvSet) (.set 7 ziMixedYvExpr))
          (.seq (.store (.int ⟨32, false⟩) ziMixedStoreIdx ziMixedStoreVal) ziMixedSetBorrow))
        .brk)
      .normal s9 := by
    have hout4 : EvE LimbGen.prog s (.var 4) (.int ⟨64, false⟩ i) := EvE.var hloc4
    have hout3 : EvE LimbGen.prog s (.var 3) (.int ⟨64, false⟩ n) := EvE.var hloc3
    have hlt_ev : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 3))
        (boolVal (decide (i < n))) := EvE.bin hout4 hout3 (by rfl)
    have htrue : truthy (boolVal (decide (i < n))) = .ok true := by
      have hd : decide (i < n) = true := decide_eq_true_iff.mpr hi
      rw [hd]; rfl
    have hseq : ExS LimbGen.prog s
        (.seq (.seq (.set 6 ziMixedXvSet) (.set 7 ziMixedYvExpr))
          (.seq (.store (.int ⟨32, false⟩) ziMixedStoreIdx ziMixedStoreVal) ziMixedSetBorrow))
        .normal s9 :=
      ExS.seq (ExS.seq hset6 hset7) (ExS.seq hstore hset5)
    exact ExS.ite hlt_ev htrue hseq
  let s10 : State := { s9 with locals := s9.locals.upd 4 (.int ⟨64, false⟩ (i + 1)) }
  have hstep : ExS LimbGen.prog s9 ziMixedStep .normal s10 := by
    show ExS LimbGen.prog s9
      (.set 4 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.const (.int ⟨64, false⟩ 1)))))
      .normal s10
    exact ExS.set (evVar4Increment s9 i (by omega) (by
      simp [s9, s8, s7, s6, Locals.upd]; exact hloc4))
  refine ⟨s9, s10, hbody, hstep, ?_⟩
  have hborrow' : ziMixedBorrow aLimbs bLimbs i carry ≤ 1 := by
    unfold ziMixedBorrow
    split <;> omega
  have hborrowEq : ziMixedBorrow aLimbs bLimbs i carry = ziMixedBorrowPrefix aLimbs bLimbs (i + 1) := by
    simp only [ziMixedBorrowPrefix]
    rw [← hcarryEq]
  have hl5ff : s10.locals 5 = some (.int ⟨64, false⟩ (ziMixedBorrow aLimbs bLimbs i carry)) := by
    simp [s10, s9, s8, s7, s6, Locals.upd]
  have hl4ff : s10.locals 4 = some (.int ⟨64, false⟩ (i + 1)) := by
    simp [s10, s9, s8, s7, s6, Locals.upd]
  refine ⟨by omega, by omega, hn64, hLen64, hLen64B, hborrow', by simp [s10, s9, s8, s7, s6]; exact hro,
      hna, hnb, hlla, hllb, hborrowEq,
      by simp [s10, s9, s8, s7, s6, Locals.upd, hloc0],
      by simp [s10, s9, s8, s7, s6, Locals.upd, hloc1],
      by simp [s10, s9, s8, s7, s6, Locals.upd, hloc2],
      by simp [s10, s9, s8, s7, s6, Locals.upd, hloc3],
      hl4ff,
      hl5ff,
      (show s10.mem tsblk = s.mem tsblk from by
        simp only [s10, s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : tsblk ≠ tarr)]).trans hnaz,
      (show s10.mem asblk = s.mem asblk from by
        simp only [s10, s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : asblk ≠ tarr)]).trans hastruct,
      (show s10.mem bsblk = s.mem bsblk from by
        simp only [s10, s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : bsblk ≠ tarr)]).trans hbstruct,
      (show s10.mem aarr = s.mem aarr from by
        simp only [s10, s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : aarr ≠ tarr)]).trans haLimbs,
      (show s10.mem barr = s.mem barr from by
        simp only [s10, s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : barr ≠ tarr)]).trans hbLimbs,
      (show s10.mem tarr = some (limbBytes (ziMixedPrefix aLimbs bLimbs (i + 1) ++
          List.replicate (n + 1 - (i + 1)) 0)) from by
        simp [s10, s9, s8, s7, s6, Mem.upd_same]),
      _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
      _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩

/-- `k`-fold unrolling of the mixed loop. -/
theorem ziMixed_loop_aux (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n : Nat) :
    ∀ (k : Nat) (s : State) (i carry : Nat), k = n - i →
      ziMixedLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry s →
      ∃ sf, ExS Tess.C.LimbGen.prog s Tess.C.LimbGen.zi_add_mixed_loop0 .normal sf ∧
        ziMixedLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n n
          (ziMixedBorrowPrefix aLimbs bLimbs n) sf := by
  intro k
  induction k with
  | zero =>
      intro s i carry heq hInv
      rcases hInv with ⟨hle, hlt64, hn64, hLen64, hLen64B, hcarry, hro, hna, hnb, hlla, hllb, hcarryEq,
        hloc0, hloc1, hloc2, hloc3, hloc4, hloc5,
        hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
        _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
        _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩
      have hnn : i = n := by omega
      subst hnn
      have hout4 : EvE Tess.C.LimbGen.prog s (.var 4) (.int ⟨64, false⟩ i) := EvE.var hloc4
      have hout3 : EvE Tess.C.LimbGen.prog s (.var 3) (.int ⟨64, false⟩ i) := EvE.var hloc3
      have hcond : EvE Tess.C.LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 3))
          (boolVal (decide (i < i))) := EvE.bin hout4 hout3 (by rfl)
      have hfalse : truthy (boolVal (decide (i < i))) = .ok false := by
        have hd : decide (i < i) = false := by simp
        rw [hd]; rfl
      refine ⟨s, ?_, ?_⟩
      · rw [ziMixedLoop_ast]
        exact ExS.loop_brk (ExS.ite hcond hfalse ExS.brk)
      · exact ⟨hle, hlt64, hlt64, hLen64, hLen64B,
          by rw [← hcarryEq]; exact hcarry,
          hro, hna, hnb, hlla, hllb, rfl, hloc0, hloc1, hloc2, hloc3, hloc4,
          by rw [← hcarryEq]; exact hloc5,
          hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
          _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
          _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩
  | succ k ih =>
      intro s i carry heq hInv
      have hi' : i < n := by omega
      obtain ⟨s1, s2, hbody, hstep, hinv2⟩ := ziMixed_iCell tsblk tarr asblk aarr bsblk barr
        aLimbs bLimbs aLen bLen n i carry hInv hi'
      obtain ⟨sf, hl, hfin⟩ := ih s2 (i + 1) (ziMixedBorrow aLimbs bLimbs i carry) (by omega) hinv2
      refine ⟨sf, ?_, hfin⟩
      · rw [ziMixedLoop_ast]
        exact ExS.loop_next hbody (Or.inl rfl) hstep hl

/-- The mixed/borrow digit loop refinement: running the translated loop from a
well-formed `n`-limb state yields the final borrow flag and the destination limbs. -/
theorem ziMixed_loop_impl (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n i carry : Nat)
    (hInv : ziMixedLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry s) :
    ∃ sf, ExS Tess.C.LimbGen.prog s Tess.C.LimbGen.zi_add_mixed_loop0 .normal sf ∧
      ziMixedLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n n
        (ziMixedBorrowPrefix aLimbs bLimbs n) sf :=
  ziMixed_loop_aux tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n
    (n - i) s i carry rfl hInv

end Tess.C
