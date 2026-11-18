/-
  Refinement proofs for the limb-summation kernels `zi_add_equisign` and
  `zi_add_mixed` in `lib/tess/src/exact.c`, as translated by c2lean into
  `Tess/C/LimbGen.lean`. The loops sweep from least significant limb to most
  significant, accumulating in 64 bits.

  Claims are about the translated MiniC programs, arbitrary memories
  containing the `zi` struct/array blocks and one writable block for the
  destination limb array with capacity at least n (+1 for equisign's overflow
  limb). No claim is made about the C allocator, `norm`, `move`, `zi_add`, or
  error handling; the C budget checks are outside this refinement.
-/
import Obj.C.Hoare
import Obj.C.Splice
import Tess.C.LimbGen
import Tess.C.ZiMem
import Tess.C.Acmp

namespace Tess.C
open Obj.C

/-- Limb extraction for source arrays with explicit bounds. -/
def ziAddTerm (limbs : List Nat) (i : Nat) : Nat :=
  if h : i < limbs.length then limbs[i]'h else 0

/-- Little-endian positional sum: carry + left limb + right limb, deferred to
arbitrary precision (no wrap). -/
def ziAddStep (aLimbs bLimbs : List Nat) (i carry : Nat) : Nat :=
  ziAddTerm aLimbs i + ziAddTerm bLimbs i + carry

/-- Low 32 bits of the positional sum: the limb written to the result. -/
def ziAddLimb (aLimbs bLimbs : List Nat) (i carry : Nat) : Nat :=
  (ziAddStep aLimbs bLimbs i carry) % 2 ^ 32

/-- Carry out of a positional sum. -/
def ziAddCarry (aLimbs bLimbs : List Nat) (i carry : Nat) : Nat :=
  (ziAddStep aLimbs bLimbs i carry) / 2 ^ 32

/-- Carry after `k` positions. -/
def ziAddCarryPrefix (aLimbs bLimbs : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ziAddCarry aLimbs bLimbs k (ziAddCarryPrefix aLimbs bLimbs k)

/-- Result limbs after `k` positions, low to high. -/
def ziAddPrefix (aLimbs bLimbs : List Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => ziAddPrefix aLimbs bLimbs k ++
      [ziAddLimb aLimbs bLimbs k (ziAddCarryPrefix aLimbs bLimbs k)]

theorem ziAddTerm_bound (aLimbs : List Nat) (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32)
    (i : Nat) : ziAddTerm aLimbs i < 2 ^ 32 := by
  unfold ziAddTerm
  split
  · next h => exact hlla _ (List.getElem_mem h)
  · omega

/-- Carry after `i` positions is at most one when the inputs are limbs. -/
theorem ziAddCarryPrefix_bound (aLimbs bLimbs : List Nat)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (i : Nat) : ziAddCarryPrefix aLimbs bLimbs i ≤ 1 := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hA := ziAddTerm_bound aLimbs hlla k
      have hB := ziAddTerm_bound bLimbs hllb k
      simp only [ziAddCarryPrefix, ziAddCarry, ziAddStep]
      omega

/-- Simulation relation for the `zi_add_equisign` sweep. -/
def ziAddEquiLoopInv (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n i carry : Nat)
    (s : State) : Prop :=
  i ≤ n ∧ i < 18446744073709551616 ∧ n < 18446744073709551616 ∧
    aLen < 18446744073709551616 ∧ bLen < 18446744073709551616 ∧ carry ≤ 1 ∧
    s.ro = false ∧
    aLimbs.length = aLen ∧ bLimbs.length = bLen ∧
    (∀ x ∈ aLimbs, x < 2 ^ 32) ∧ (∀ x ∈ bLimbs, x < 2 ^ 32) ∧
    carry = ziAddCarryPrefix aLimbs bLimbs i ∧
    s.locals 0 = some (.ptr tsblk 0) ∧ s.locals 1 = some (.ptr asblk 0) ∧
    s.locals 2 = some (.ptr bsblk 0) ∧ s.locals 3 = some (.int ⟨64, false⟩ n) ∧
    s.locals 4 = some (.int ⟨64, false⟩ i) ∧ s.locals 5 = some (.int ⟨64, false⟩ carry) ∧
    s.mem tsblk = some (ziBlock tarr (n + 1) 1) ∧ s.mem asblk = some (ziBlock aarr aLen 1) ∧
    s.mem bsblk = some (ziBlock barr bLen 1) ∧
    s.mem aarr = some (limbBytes aLimbs) ∧ s.mem barr = some (limbBytes bLimbs) ∧
    (s.mem tarr = some (limbBytes ((ziAddPrefix aLimbs bLimbs i) ++
      (List.replicate (n + 1 - i) 0)))) ∧
    tsblk < 4294967296 ∧ tarr < 4294967296 ∧ asblk < 4294967296 ∧
    aarr < 4294967296 ∧ bsblk < 4294967296 ∧ barr < 4294967296 ∧
    tarr ≠ tsblk ∧ tarr ≠ asblk ∧ tarr ≠ bsblk ∧ tarr ≠ aarr ∧ tarr ≠ barr

/-- Load the `n` field of a `zi` struct in local `v` as u64 (`n % 2^64`). -/
theorem evZiN (s : State) (v : Nat) (zb vblk vblkValLen : Nat)
    (hm : s.mem zb = some (ziBlock vblk vblkValLen 1))
    (hb : vblk < 4294967296)
    (hl : s.locals v = some (.ptr zb 0)) :
    EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var v) 8)) (.int ⟨64, false⟩ (vblkValLen % 2 ^ 64)) := by
  have hfield : EvE LimbGen.prog s (.field (.var v) 8) (.ptr zb 8) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  exact EvE.load hfield (load_u64_at s.mem zb (ziBlock vblk vblkValLen 1) 8 vblkValLen
    hm (by simp [ziBlock_length]) (by simp [ziBlock, encodeLE_length]))

/-- Conditional limb extraction in the kernel: evaluate the
`if (i < z->n) limbs[i] else 0` expression against memory. -/
theorem evAddTermCond (s : State) (select : Nat) (zb vblk : Nat)
    (limbs : List Nat) (i : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length 1)) (hb : vblk < 4294967296)
    (hl : s.locals select = some (.ptr zb 0))
    (hl2 : s.locals 4 = some (.int ⟨64, false⟩ i))
    (hlm : s.mem vblk = some (limbBytes limbs))
    (hlla : ∀ x ∈ limbs, x < 2 ^ 32) (hi : i < 18446744073709551616)
    (nBound : limbs.length < 18446744073709551616) :
    EvE LimbGen.prog s
      (.cast ⟨64, false⟩
        (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                 (.load (.int ⟨64, false⟩) (.field (.var select) 8)))
               (.load (.int ⟨32, false⟩)
                  (.index (.load .ptr (.field (.var select) 0)) (.var 4) 4))
               (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      (.int ⟨64, false⟩ (ziAddTerm limbs i)) := by
  have hloadN : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var select) 8))
      (.int ⟨64, false⟩ (limbs.length % 2 ^ 64)) :=
    evZiN s select zb vblk limbs.length hm hb hl
  have hlen64 : limbs.length < 18446744073709551616 := nBound
  have hlt : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4)
        (.load (.int ⟨64, false⟩) (.field (.var select) 8))) (boolVal (decide (i < limbs.length))) := by
    show EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4)
        (.load (.int ⟨64, false⟩) (.field (.var select) 8))) (boolVal (decide (i < limbs.length)))
    refine EvE.bin (EvE.var hl2) hloadN ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus,
      Nat.mod_eq_of_lt hlen64]
  by_cases hh : i < limbs.length
  · have htrue : truthy (boolVal (decide (i < limbs.length))) = .ok true := by
      have hd : decide (i < limbs.length) = true := by simp [decide_eq_true_iff, hh]
      rw [hd]; rfl
    have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var select) 0)) (.ptr vblk 0) :=
      evVPointer s select zb vblk limbs.length hm hb hl
    have hb : vblk < 4294967296 := hb
    have hidx4 : i * 4 ≤ (limbBytes limbs).length := by
      rw [limbBytes_length]; omega
    have hidx : EvE LimbGen.prog s
        (.index (.load .ptr (.field (.var select) 0)) (.var 4) 4)
        (.ptr vblk (i * 4)) := by
      apply EvE.index hloadPtr (EvE.var hl2)
      show ptrAddN s.mem (.ptr vblk 0) (i * 4) = _
      simp [ptrAddN, hlm, hidx4]
    have hload : EvE LimbGen.prog s
        (.load (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var select) 0)) (.var 4) 4))
        (.int ⟨32, false⟩ (limbs[i]'hh)) := by
      have hload' := load_limb s.mem vblk limbs i hlm hh
      rw [Nat.mod_eq_of_lt (hlla _ (List.getElem_mem hh))] at hload'
      have heq : 4 * i = i * 4 := by ac_rfl
      rw [heq] at hload'
      exact EvE.load hidx hload' 
    have hcond : EvE LimbGen.prog s
        (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                 (.load (.int ⟨64, false⟩) (.field (.var select) 8)))
               (.load (.int ⟨32, false⟩)
                  (.index (.load .ptr (.field (.var select) 0)) (.var 4) 4))
               (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
        (.int ⟨32, false⟩ (limbs[i]'hh)) :=
      EvE.cond hlt htrue hload
    have hcast : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ (limbs[i]'hh)) = .ok (.int ⟨64, false⟩ (limbs[i]'hh)) := by
      have hle := hlla _ (List.getElem_mem hh)
      simp [evalCast, IntTy.modulus]
      omega
    have hzi : ziAddTerm limbs i = limbs[i]'hh := by
      simp [ziAddTerm, hh]
    rw [hzi]
    exact EvE.cast hcond hcast
  · have hfalse : truthy (boolVal (decide (i < limbs.length))) = .ok false := by
      have hd : decide (i < limbs.length) = false := by
        rw [decide_eq_false]; exact hh
      rw [hd]; rfl
    have hcast0 : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 0) = .ok (.int ⟨32, false⟩ 0) := by
      rfl
    have hconst : EvE LimbGen.prog s
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))
        (.int ⟨32, false⟩ 0) := by
      exact EvE.cast (EvE.const _) hcast0
    have hcond : EvE LimbGen.prog s
        (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                 (.load (.int ⟨64, false⟩) (.field (.var select) 8)))
               (.load (.int ⟨32, false⟩)
                  (.index (.load .ptr (.field (.var select) 0)) (.var 4) 4))
               (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
        (.int ⟨32, false⟩ 0) :=
      EvE.cond hlt hfalse hconst
    have hcast : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 0) = .ok (.int ⟨64, false⟩ 0) := by
      rfl
    have hzi : ziAddTerm limbs i = 0 := by
      simp [ziAddTerm, hh]
    rw [hzi]
    exact EvE.cast hcond hcast


/-- Cast of the limb-sum value into the destination limb. -/
theorem evalCast_u64_u32 (x : Nat) :
    evalCast ⟨32, false⟩ (.int ⟨64, false⟩ x) = .ok (.int ⟨32, false⟩ (x % 2 ^ 32)) := by
  simp [evalCast, IntTy.modulus]

/-- Logical shift right by 32 of a bounded value. -/
theorem ev_shr32 (x : Nat) :
    evalBin .shr (some ⟨64, false⟩) (.int ⟨64, false⟩ x) (.int ⟨32, true⟩ 32) =
    .ok (.int ⟨64, false⟩ (x / 2 ^ 32)) := rfl

/-- Bound on the 64-bit wrap for sums of bounded values. -/
theorem add_u64_bound (a b : Nat) (h : a + b < 18446744073709551616) :
    evalBin .add (some ⟨64, false⟩) (.int ⟨64, false⟩ a) (.int ⟨64, false⟩ b) =
    .ok (.int ⟨64, false⟩ (a + b)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus, Nat.mod_eq_of_lt h]

/-- Unsigned subtract of two u64 values in the limb sweeps: accepts the two
cases (borrow vs no-borrow) as one expression with a case analysis. -/
theorem sub_u64_bound (a b : Nat) :
    evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ a) (.int ⟨64, false⟩ b) =
    .ok (.int ⟨64, false⟩ (if b ≤ a then a - b else a + 18446744073709551616 - b)) := rfl

-- The two case formulae are definitional; the borrow logic chooses which
-- branch applies at each limb position.


theorem ziAddPrefix_length (aLimbs bLimbs : List Nat) (k : Nat) :
    (ziAddPrefix aLimbs bLimbs k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ziAddPrefix, ih]

theorem ziAddPrefix_append (aLimbs bLimbs : List Nat) (i k : Nat) :
    ziAddPrefix aLimbs bLimbs (i + k) =
      ziAddPrefix aLimbs bLimbs i ++ (List.range k).map (fun j =>
        ziAddLimb aLimbs bLimbs (i + j) (ziAddCarryPrefix aLimbs bLimbs (i + j))) := by
  induction k with
  | zero => simp [ziAddPrefix]
  | succ k ih =>
      have hrange : List.range (k + 1) = List.range k ++ [k] := List.range_succ
      show ziAddPrefix aLimbs bLimbs (i + (k + 1)) =
        ziAddPrefix aLimbs bLimbs i ++ ((List.range (k + 1)).map (fun j =>
          ziAddLimb aLimbs bLimbs (i + j) (ziAddCarryPrefix aLimbs bLimbs (i + j))))
      rw [hrange, List.map_append, List.map_singleton]
      simp [ziAddPrefix, ih]

theorem evVar4Increment (s : State) (i : Nat) (hbound : i + 1 < 18446744073709551616)
    (h : s.locals 4 = some (.int ⟨64, false⟩ i)) :
    EvE LimbGen.prog s (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
        (.const (.int ⟨64, false⟩ 1)))) (.int ⟨64, false⟩ (i + 1)) := by
  have hbound' : i < 18446744073709551616 := by omega
  have hcast : evalCast ⟨64, false⟩ (.int ⟨64, false⟩ i) = .ok (.int ⟨64, false⟩ i) := by
    simp [evalCast, IntTy.modulus, Nat.mod_eq_of_lt hbound']
  have hadd : evalBin .add (some ⟨64, false⟩) (.int ⟨64, false⟩ i) (.int ⟨64, false⟩ 1) = .ok (.int ⟨64, false⟩ (i + 1)) := by
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus, Nat.mod_eq_of_lt hbound]
  have hincr : evalCast ⟨64, false⟩ (.int ⟨64, false⟩ (i + 1)) = .ok (.int ⟨64, false⟩ (i + 1)) := by
    simp [evalCast, IntTy.modulus, Nat.mod_eq_of_lt hbound]
  exact EvE.cast (EvE.bin (EvE.cast (EvE.var h) hcast) (EvE.const _) hadd) hincr

/-- The vcalc AST as a literal, adapted from the generated `LimbGen`. -/
@[reducible] def ziVCalc : Expr :=
  .bin .add (some ⟨64, false⟩)
    (.bin .add (some ⟨64, false⟩) (.var 5)
      (.cast ⟨64, false⟩ (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
              (.load (.int ⟨32, false⟩)
                 (.index (.load .ptr (.field (.var 1) 0)) (.var 4) 4))
              (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))))
    (.cast ⟨64, false⟩ (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
              (.load (.int ⟨32, false⟩)
                 (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4))
              (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))

/-- The destination limb store index and the store's target value. -/
def ziStoreIdx : Expr := .index (.load .ptr (.field (.var 0) 0)) (.var 4) 4
def ziStoreVal : Expr := .cast ⟨32, false⟩ (.var 6)
def ziSetCarry : Stmt := .set 5 (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32)))

theorem evVCalc (s : State) (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n i carry : Nat)
    (hInv : ziAddEquiLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry s) :
    EvE LimbGen.prog s
      (.bin .add (some ⟨64, false⟩)
        (.bin .add (some ⟨64, false⟩) (.var 5)
          (.cast ⟨64, false⟩ (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                    (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
                  (.load (.int ⟨32, false⟩)
                     (.index (.load .ptr (.field (.var 1) 0)) (.var 4) 4))
                  (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))))
        (.cast ⟨64, false⟩ (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                    (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
                  (.load (.int ⟨32, false⟩)
                     (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4))
                  (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))))
      (.int ⟨64, false⟩ (ziAddStep aLimbs bLimbs i carry)) := by
  obtain ⟨hle, hlt64, hn64, hLen64, hLen64B, hcarry, hro, hna, hnb, hlla, hllb, hcarryEq,
    hloc0, hloc1, hloc2, hloc3, hloc4, hloc5,
    hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
    _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
    _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩ := hInv
  have hi : i < 18446744073709551616 := hlt64
  have nBoundA : aLimbs.length < 18446744073709551616 := by rw [hna]; omega
  have nBoundB : bLimbs.length < 18446744073709551616 := by rw [hnb]; omega
  have hlen64 : aLimbs.length < 18446744073709551616 := nBoundA
  have hlen64b : bLimbs.length < 18446744073709551616 := nBoundB
  have hbca : EvE LimbGen.prog s
      (.cast ⟨64, false⟩ (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                    (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
                  (.load (.int ⟨32, false⟩)
                     (.index (.load .ptr (.field (.var 1) 0)) (.var 4) 4))
                  (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      (.int ⟨64, false⟩ (ziAddTerm aLimbs i)) :=
    evAddTermCond s 1 asblk aarr aLimbs i (by rw [hna]; exact hastruct) _haarrBound hloc1 hloc4
      haLimbs hlla hi (by rw [hna]; omega)
  have hbcb : EvE LimbGen.prog s
      (.cast ⟨64, false⟩ (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                    (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
                  (.load (.int ⟨32, false⟩)
                     (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4))
                  (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      (.int ⟨64, false⟩ (ziAddTerm bLimbs i)) :=
    evAddTermCond s 2 bsblk barr bLimbs i (by rw [hnb]; exact hbstruct) _hbarBound hloc2 hloc4
      hbLimbs hllb hi (by rw [hnb]; omega)
  have hA5 := add_u64_bound carry (ziAddTerm aLimbs i) (by
    have hA := ziAddTerm_bound aLimbs hlla i
    omega)
  have h5termA : EvE LimbGen.prog s
      (.bin .add (some ⟨64, false⟩) (.var 5)
        (.cast ⟨64, false⟩ (.cond (.bin .lt (some ⟨64, false⟩) (.var 4)
                      (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
                    (.load (.int ⟨32, false⟩)
                       (.index (.load .ptr (.field (.var 1) 0)) (.var 4) 4))
                    (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))))
      (.int ⟨64, false⟩ (carry + ziAddTerm aLimbs i)) :=
    EvE.bin (EvE.var hloc5) hbca hA5
  have hsumBound : carry + ziAddTerm aLimbs i + ziAddTerm bLimbs i < 18446744073709551616 := by
    have hA := ziAddTerm_bound aLimbs hlla i
    have hB := ziAddTerm_bound bLimbs hllb i
    omega
  have hsum2 := add_u64_bound (carry + ziAddTerm aLimbs i) (ziAddTerm bLimbs i) hsumBound
  have hfinal : carry + ziAddTerm aLimbs i + ziAddTerm bLimbs i =
      ziAddStep aLimbs bLimbs i carry := by
    simp [ziAddStep]
    omega
  rw [← hfinal]
  exact EvE.bin h5termA hbcb hsum2

/-- Set lemma: position `|prefix i|` of `prefix i ++ replicate (n+1-i) 0` is the
head of the replicate, which becomes the just-computed limb plus a shorter
(replicate zero) tail. -/
theorem ziAddPrefix_set (aLimbs bLimbs : List Nat) (n i carry : Nat) (h : i < n)
    (hcarry : carry = ziAddCarryPrefix aLimbs bLimbs i) :
    (ziAddPrefix aLimbs bLimbs i ++ List.replicate (n + 1 - i) 0).set i (ziAddLimb aLimbs bLimbs i carry)
      = ziAddPrefix aLimbs bLimbs (i + 1) ++ List.replicate (n - i) 0 := by
  have hlen : (ziAddPrefix aLimbs bLimbs i).length = i := ziAddPrefix_length aLimbs bLimbs i
  rw [List.set_append]
  rw [if_neg (by omega)]
  rw [hlen]
  show ziAddPrefix aLimbs bLimbs i ++
      (List.replicate (n + 1 - i) 0).set (i - i) (ziAddLimb aLimbs bLimbs i carry) =
    ziAddPrefix aLimbs bLimbs (i + 1) ++ List.replicate (n - i) 0
  rw [Nat.sub_self]
  have hne : n + 1 - i = (n - i) + 1 := by omega
  rw [hne, List.replicate_succ, List.set_cons_zero]
  show ziAddPrefix aLimbs bLimbs i ++ (ziAddLimb aLimbs bLimbs i carry ::
      List.replicate (n - i) 0) = _
  simp [ziAddPrefix]
  rw [hcarry]



/-- The loop body AST for `zi_add_equisign_loop0`. -/
def ziEquiBody : Stmt :=
  .ite (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 3))
    (.seq (.set 6 ziVCalc)
      (.seq (.store (.int ⟨32, false⟩) ziStoreIdx ziStoreVal) ziSetCarry))
    .brk

/-- The step statement of the equisign loop. -/
def ziEquiStep : Stmt :=
  .set 4 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
    (.const (.int ⟨64, false⟩ 1))))

/-- One iteration of the equisign sweep: body then step, as the generated
`loop body step` combinator executes them. -/
theorem ziAddEqui_iCell (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n i carry : Nat)
    (hInv : ziAddEquiLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry s)
    (hi : i < n) :
    ∃ s1 s2, ExS LimbGen.prog s ziEquiBody .normal s1 ∧
      ExS LimbGen.prog s1 ziEquiStep .normal s2 ∧
      ziAddEquiLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n (i + 1)
        (ziAddCarry aLimbs bLimbs i carry) s2 := by
  let s6 : State := { s with locals := s.locals.upd 6 (.int ⟨64, false⟩ (ziAddStep aLimbs bLimbs i carry)) }
  have hset6 : ExS LimbGen.prog s (.set 6 ziVCalc) .normal s6 := by
    exact ExS.set (evVCalc s tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry hInv)
  obtain ⟨hle, hlt64, hn64, hLen64, hLen64B, hcarry, hro, hna, hnb, hlla, hllb, hcarryEq,
    hloc0, hloc1, hloc2, hloc3, hloc4, hloc5,
    hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
    _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
    _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩ := hInv
  have hi' : i < 18446744073709551616 := by omega
  have nBoundA : aLimbs.length < 18446744073709551616 := by rw [hna]; exact hLen64
  have nBoundB : bLimbs.length < 18446744073709551616 := by rw [hnb]; exact hLen64B
  have step_def : ziAddTerm aLimbs i + ziAddTerm bLimbs i + carry = ziAddStep aLimbs bLimbs i carry := rfl
  have hvDefeq : ziAddStep aLimbs bLimbs i carry < 18446744073709551616 := by
    rw [← step_def]
    have hA := ziAddTerm_bound aLimbs hlla i
    have hB := ziAddTerm_bound bLimbs hllb i
    omega
  have hvB : ziAddStep aLimbs bLimbs i carry < 2 ^ 33 := by
    rw [← step_def]
    have hA := ziAddTerm_bound aLimbs hlla i
    have hB := ziAddTerm_bound bLimbs hllb i
    omega
  have hvb := hvDefeq
  have hlimb : (ziAddStep aLimbs bLimbs i carry) % 2 ^ 32 < 2 ^ 32 := by
    exact Nat.mod_lt _ (by omega)
  have hloc0' : s6.locals 0 = some (Val.ptr tsblk 0) := by
    simp [s6, Locals.upd]; exact hloc0
  have hloc1' := hloc1
  have hloc4' : s6.locals 4 = some (Val.int ⟨64, false⟩ i) := by
    simp [s6, Locals.upd]; exact hloc4
  have hloc6' : s6.locals 6 = some (Val.int ⟨64, false⟩ (ziAddStep aLimbs bLimbs i carry)) := by
    simp [s6, Locals.upd]
  have hloc01 : s6.locals 1 = some (Val.ptr asblk 0) := by
    simp [s6, Locals.upd]; exact hloc1
  have hloc02 : s6.locals 2 = some (Val.ptr bsblk 0) := by
    simp [s6, Locals.upd]; exact hloc2
  have hloc03 : s6.locals 3 = some (Val.int ⟨64, false⟩ n) := by
    simp [s6, Locals.upd]; exact hloc3
  have hloadPtr : EvE LimbGen.prog s6 (.load .ptr (.field (.var 0) 0)) (.ptr tarr 0) :=
    evVPointer s6 0 tsblk tarr (n + 1) hnaz _hTarbound hloc0'
  have hidx : EvE LimbGen.prog s6
      (.index (.load .ptr (.field (.var 0) 0)) (.var 4) 4) (.ptr tarr (i * 4)) := by
    apply EvE.index hloadPtr (EvE.var hloc4')
    simp only [s6, u64, Bool.false_eq_true, if_false]
    show ptrAddN _ _ _ = _
    have hLen : (limbBytes (ziAddPrefix aLimbs bLimbs i ++
        List.replicate (n + 1 - i) 0)).length = 4 * (n + 1) := by
      rw [limbBytes_length, List.length_append, List.length_replicate, ziAddPrefix_length]
      omega
    have hbound : 0 + i * 4 ≤ (limbBytes (ziAddPrefix aLimbs bLimbs i ++
        List.replicate (n + 1 - i) 0)).length := by
      rw [hLen]; omega
    simp only [ptrAddN, hmemTarr, if_pos hbound]
    rw [show 0 + i * 4 = i * 4 from Nat.zero_add _]
  have hstoreVal : EvE LimbGen.prog s6 ziStoreVal (.int ⟨32, false⟩ ((ziAddStep aLimbs bLimbs i carry) % 2 ^ 32)) :=
    EvE.cast (EvE.var hloc6') (evalCast_u64_u32 (ziAddStep aLimbs bLimbs i carry))
  have hlimbbound : i < (ziAddPrefix aLimbs bLimbs i ++ List.replicate (n + 1 - i) 0).length := by
    rw [List.length_append, List.length_replicate, ziAddPrefix_length]; omega
  have hstore : ExS LimbGen.prog s6
      (.store (.int ⟨32, false⟩) ziStoreIdx ziStoreVal) .normal
      { s6 with mem := s6.mem.upd tarr (limbBytes (ziAddPrefix aLimbs bLimbs (i + 1) ++
          List.replicate (n - i) 0)) } := by
    have hstore' := store_limb s6.mem tarr (ziAddPrefix aLimbs bLimbs i ++ List.replicate (n + 1 - i) 0) i
      (ziAddStep aLimbs bLimbs i carry % 2 ^ 32) hmemTarr hlimbbound
    have hpre1 := ziAddPrefix_set aLimbs bLimbs n i carry (by omega) hcarryEq
    unfold ziAddLimb at hpre1
    rw [hpre1] at hstore'
    have hro6 : s6.ro = false := by
      show s.ro = false
      exact hro
    have hidx' : EvE LimbGen.prog s6 (.index (.load .ptr (.field (.var 0) 0)) (.var 4) 4)
        (.ptr tarr (4 * i)) := by
      rw [Nat.mul_comm]; exact hidx
    exact ExS.store hidx' hstoreVal (by simp [s6]; exact hro) hstore'

  let s7 : State := { s6 with mem := s6.mem.upd tarr (limbBytes (ziAddPrefix aLimbs bLimbs (i + 1) ++
          List.replicate (n - i) 0)) }
  let s8 : State := { s7 with locals := s7.locals.upd 5 (.int ⟨64, false⟩ (ziAddCarry aLimbs bLimbs i carry)) }
  have hset5 : ExS LimbGen.prog s7
      ziSetCarry .normal s8 := by
    have hloc6'' : s7.locals 6 = some (.int ⟨64, false⟩ (ziAddStep aLimbs bLimbs i carry)) := by
      simp [s7, s6, Locals.upd]
    have h5 : EvE LimbGen.prog s7
        (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32)))
        (.int ⟨64, false⟩ (ziAddCarry aLimbs bLimbs i carry)) := by
      show EvE LimbGen.prog _ (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32))) _
      apply EvE.bin (EvE.var hloc6'') (EvE.const _)
      show evalBin .shr (some ⟨64, false⟩) (.int ⟨64, false⟩ (ziAddStep aLimbs bLimbs i carry)) (.int ⟨32, true⟩ 32) =
        .ok (.int ⟨64, false⟩ (ziAddCarry aLimbs bLimbs i carry))
      rfl
    exact ExS.set h5
  have hbody : ExS LimbGen.prog s
      (.seq (.set 6 ziVCalc)
        (.seq (.store (.int ⟨32, false⟩) ziStoreIdx ziStoreVal) ziSetCarry))
      .normal s8 :=
    ExS.seq hset6 (ExS.seq hstore hset5)
  have hout4 : EvE LimbGen.prog s (.var 4) (.int ⟨64, false⟩ i) := EvE.var hloc4
  have hout3 : EvE LimbGen.prog s (.var 3) (.int ⟨64, false⟩ n) := EvE.var hloc3
  have hlt_ev : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 3))
      (boolVal (decide (i < n))) := EvE.bin hout4 hout3 (by rfl)
  have htrue : truthy (boolVal (decide (i < n))) = .ok true := by
    have hd : decide (i < n) = true := decide_eq_true_iff.mpr hi
    rw [hd]; rfl
  have hite : ExS LimbGen.prog s
      (.ite (.bin .lt (some ⟨64, false⟩) (.var 4) (.var 3))
        (.seq (.set 6 ziVCalc)
          (.seq (.store (.int ⟨32, false⟩) ziStoreIdx ziStoreVal) ziSetCarry))
        .brk)
      .normal s8 :=
    ExS.ite hlt_ev htrue hbody
  let s2 : State := { s8 with locals := s8.locals.upd 4 (.int ⟨64, false⟩ (i + 1)) }
  refine ⟨s8, s2, hite, ?_, ?_⟩
  · exact ExS.set (evVar4Increment s8 i (by omega) (by
      simp [s8, s7, s6, Locals.upd]; exact hloc4))
  · have hcarryDef : ziAddCarry aLimbs bLimbs i carry =
        ziAddCarryPrefix aLimbs bLimbs (i + 1) := by
      simp [ziAddCarryPrefix]
      rw [← hcarryEq]
    have hcarry' : ziAddCarry aLimbs bLimbs i carry ≤ 1 := by
      rw [hcarryDef]
      exact ziAddCarryPrefix_bound aLimbs bLimbs hlla hllb (i + 1)
    have s2f : s2 = { s8 with locals := s8.locals.upd 4 (.int ⟨64, false⟩ (i + 1)) } := rfl
    have hloc4f : s2.locals 4 = some (.int ⟨64, false⟩ (i + 1)) := by
      simp [s2, s8, s7, s6, Locals.upd]
    have hloc5f : s2.locals 5 = some (.int ⟨64, false⟩ (ziAddCarry aLimbs bLimbs i carry)) := by
      simp [s2, s8, s7, s6, Locals.upd]
    refine ⟨by omega, by omega, hn64, hLen64, hLen64B, hcarry', by simp [s2, s8, s7, s6]; exact hro,
        hna, hnb, hlla, hllb,
        hcarryDef,
        by simp [s2, s8, s7, s6, Locals.upd, hloc0],
        by simp [s2, s8, s7, s6, Locals.upd, hloc1],
        by simp [s2, s8, s7, s6, Locals.upd, hloc2],
        by simp [s2, s8, s7, s6, Locals.upd, hloc3],
        hloc4f,
        hloc5f,
        (show s2.mem tsblk = s.mem tsblk from by
          simp only [s2, s8, s7, s6, Mem.upd_ne _ _ (by omega : tsblk ≠ tarr)]).trans hnaz,
        (show s2.mem asblk = s.mem asblk from by
          simp only [s2, s8, s7, s6, Mem.upd_ne _ _ (by omega : asblk ≠ tarr)]).trans hastruct,
        (show s2.mem bsblk = s.mem bsblk from by
          simp only [s2, s8, s7, s6, Mem.upd_ne _ _ (by omega : bsblk ≠ tarr)]).trans hbstruct,
        (show s2.mem aarr = s.mem aarr from by
          simp only [s2, s8, s7, s6, Mem.upd_ne _ _ (by omega : aarr ≠ tarr)]).trans haLimbs,
        (show s2.mem barr = s.mem barr from by
          simp only [s2, s8, s7, s6, Mem.upd_ne _ _ (by omega : barr ≠ tarr)]).trans hbLimbs,
        (show s2.mem tarr = some (limbBytes (ziAddPrefix aLimbs bLimbs (i + 1) ++
            List.replicate (n + 1 - (i + 1)) 0)) from by
          simp [s2, s8, s7, s6, Mem.upd_same]),
        _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
        _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩

/-- AST of `zi_add_equisign_loop0`: body is the guarded `ite`, step is `.set 4`.
The loop body and step statements are structurally equal to the generated
MiniC program; this theorem exposes the structural equality needed to drive
`ExS.loop_next` over the function's full unrolling. -/
theorem ziEquiLoop_ast : Tess.C.LimbGen.zi_add_equisign_loop0 =
    Stmt.loop ziEquiBody ziEquiStep := by
  rfl

/-- `k`-fold unrolling of the equisign loop. -/
theorem ziAddEqui_loop_aux (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n : Nat) :
    ∀ (k : Nat) (s : State) (i carry : Nat), k = n - i →
      ziAddEquiLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry s →
      ∃ sf, ExS Tess.C.LimbGen.prog s Tess.C.LimbGen.zi_add_equisign_loop0 .normal sf ∧
        ziAddEquiLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n n
          (ziAddCarryPrefix aLimbs bLimbs n) sf := by
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
      · rw [ziEquiLoop_ast]
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
      obtain ⟨s1, s2, hbody, hstep, hinv2⟩ := ziAddEqui_iCell tsblk tarr asblk aarr bsblk barr
        aLimbs bLimbs aLen bLen n i carry hInv hi'
      obtain ⟨sf, hl, hfin⟩ := ih s2 (i + 1) (ziAddCarry aLimbs bLimbs i carry) (by omega) hinv2
      refine ⟨sf, ?_, hfin⟩
      · rw [ziEquiLoop_ast]
        exact ExS.loop_next hbody (Or.inl rfl) hstep hl

/-- `n - i` iterations of the equisign loop, via `ExS.loop_next`. -/
theorem ziAddEqui_loop_impl (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs : List Nat) (aLen bLen n i carry : Nat)
    (hInv : ziAddEquiLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n i carry s) :
    ∃ sf, ExS Tess.C.LimbGen.prog s Tess.C.LimbGen.zi_add_equisign_loop0 .normal sf ∧
      ziAddEquiLoopInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n n
        (ziAddCarryPrefix aLimbs bLimbs n) sf :=
  ziAddEqui_loop_aux tsblk tarr asblk aarr bsblk barr aLimbs bLimbs aLen bLen n
    (n - i) s i carry rfl hInv

end Tess.C
