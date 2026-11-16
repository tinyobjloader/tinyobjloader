/-
  Refinement proof for the `zi_mul_accumulate` kernel in `lib/tess/src/exact.c`,
  as translated by c2lean into `Tess/C/LimbGen.lean`. The kernel is schoolbook
  multiplication: for each outer index `i` at most `a->n`, an inner sweep over
  `j < b->n` accumulates `a[i] * b[j]` into `t[i + j]` via `tess_limb_madd`.

  Claims are about the translated MiniC program; the C allocator, `norm`,
  `move`, `zi_mul` and budget checks are outside the refinement. The
  destination `t` is modeled as a limb block of capacity `aLen + bLen`,
  matching the `make(c, a->n + b->n)` allocation at the C call site. When
  all C budget checks are satisfied, the composed C program performs the
  same store; this proof covers the data path only.
-/
import Obj.C.Hoare
import Obj.C.Splice
import Tess.C.LimbGen
import Tess.C.ZiMem
import Tess.C.Acmp
import Tess.C.ZiAdd
import Tess.C.Arithmetic

namespace Tess.C
open Obj.C

/-- Four 32-bit limbs cannot overflow the uint64 multiply-add helper. -/
theorem mul_overflow (a b c d : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) (hd : d < 2^32) :
    a * b + c + d < 2^64 := by
  have hp : a * b ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  omega

private theorem cast_limb32 (a : Nat) (ha : a < 2^32) :
    evalCast IntTy.u64 (.int IntTy.u32 a) = .ok (.int IntTy.u64 a) := by
  simp [evalCast, IntTy.u32, IntTy.u64, IntTy.modulus,
    Nat.mod_eq_of_lt (show a < 18446744073709551616 by omega)]

private theorem add_u64' (a b : Nat) (h : a + b < 2^64) :
    evalBin .add (some IntTy.u64) (.int IntTy.u64 a) (.int IntTy.u64 b) =
    .ok (.int IntTy.u64 (a + b)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64,
    IntTy.modulus, Nat.mod_eq_of_lt h]

private theorem mul_u64' (a b : Nat) (h : a * b < 2^64) :
    evalBin .mul (some IntTy.u64) (.int IntTy.u64 a) (.int IntTy.u64 b) =
    .ok (.int IntTy.u64 (a * b)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64,
    IntTy.modulus, Nat.mod_eq_of_lt h]

/-- The `tess_limb_madd` function as translated in `Tess.C.LimbGen` evaluates
exactly as the unbounded `a * b + c + d` value (limb-bounded inputs). -/
theorem limb_madd_refines_lm (s : State) (a b c d : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) (hd : d < 2^32)
    (l0 : s.locals 0 = some (.int IntTy.u32 a))
    (l1 : s.locals 1 = some (.int IntTy.u32 b))
    (l2 : s.locals 2 = some (.int IntTy.u32 c))
    (l3 : s.locals 3 = some (.int IntTy.u32 d)) :
    ExS LimbGen.prog s LimbGen.tess_limb_madd.body
      (.ret (some (.int IntTy.u64 (a * b + c + d)))) s := by
  have bound := mul_overflow a b c d ha hb hc hd
  have ea := EvE.cast (EvE.var (p := LimbGen.prog) l0) (cast_limb32 a ha)
  have eb := EvE.cast (EvE.var (p := LimbGen.prog) l1) (cast_limb32 b hb)
  have ec := EvE.cast (EvE.var (p := LimbGen.prog) l2) (cast_limb32 c hc)
  have ed := EvE.cast (EvE.var (p := LimbGen.prog) l3) (cast_limb32 d hd)
  have ep := EvE.bin ea eb (mul_u64' a b (by omega))
  have es := EvE.bin ep ec (add_u64' (a * b) c (by omega))
  exact ExS.ret (EvE.bin es ed (add_u64' (a * b + c) d bound))

/-- Evaluation of the `.call 0` used inside zi_mul_accumulate_loop0, on a
well-formed state, reduces to the madd body in a fresh frame. -/
theorem limb_madd_call (s : State) (a b c d : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) (hd : d < 2^32)
    (hargs : EvArgs LimbGen.prog s
      [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
       (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
       (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
       (.cast ⟨32, false⟩ (.var 5))]
      [Val.int IntTy.u32 a, Val.int IntTy.u32 b, Val.int IntTy.u32 c, Val.int IntTy.u32 d]) :
    EvE LimbGen.prog s
      (.call 0 [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
       (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
       (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
       (.cast ⟨32, false⟩ (.var 5))])
      (.int IntTy.u64 (a * b + c + d)) := by
  let frame : State :=
    ⟨frameLocals LimbGen.tess_limb_madd.params
      ([Val.int IntTy.u32 a, Val.int IntTy.u32 b, Val.int IntTy.u32 c, Val.int IntTy.u32 d] : List Val),
     s.mem, true⟩
  have l0 : frame.locals 0 = some (.int IntTy.u32 a) := rfl
  have l1 : frame.locals 1 = some (.int IntTy.u32 b) := rfl
  have l2 : frame.locals 2 = some (.int IntTy.u32 c) := rfl
  have l3 : frame.locals 3 = some (.int IntTy.u32 d) := rfl
  have hbody := limb_madd_refines_lm frame a b c d ha hb hc hd l0 l1 l2 l3
  have hprog0 : LimbGen.prog 0 = some LimbGen.tess_limb_madd := rfl
  have hlen : LimbGen.tess_limb_madd.params.length =
      [Val.int IntTy.u32 a, Val.int IntTy.u32 b, Val.int IntTy.u32 c, Val.int IntTy.u32 d].length := by
    rfl
  exact EvE.call hargs hprog0 hlen hbody

/-- One accumulate step of the inner loop: positional low digit (wrap) and carry. -/
def ziMulAccStep (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (j : Nat) (carry : Nat) :
    List Nat × Nat :=
  (t.set (i + j)
     ((ziAddTerm aLimbs i * ziAddTerm bLimbs j + (t[i + j]?).getD 0 + carry) % 2 ^ 32),
   (ziAddTerm aLimbs i * ziAddTerm bLimbs j + (t[i + j]?).getD 0 + carry) / 2 ^ 32)

/-- `j`-th row prefix: the low digits stored by the first `k` inner iterations. -/
def ziMulAcc (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (carry : Nat) :
    Nat → List Nat × Nat
  | 0 => (t, carry)
  | j + 1 =>
      ziMulAccStep aLimbs bLimbs i (ziMulAcc aLimbs bLimbs i t carry j).1 j
        (ziMulAcc aLimbs bLimbs i t carry j).2

/-- Every member of `l.set k v` is either `v` or a member of `l`. -/
theorem set_mem_of_eq (l : List Nat) (k v x : Nat) (hx : x ∈ l.set k v) : x = v ∨ x ∈ l := by
  induction l generalizing k with
  | nil => simp at hx
  | cons y ys ih =>
      cases k with
      | zero =>
          have : (y :: ys).set 0 v = v :: ys := rfl
          rw [this] at hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ h)
      | succ k =>
          have : (y :: ys).set (k + 1) v = y :: ys.set k v := rfl
          rw [this] at hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
          · rcases ih k h with rfl | hin
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem _ hin)

/-- Bound is preserved by `List.set`. -/
theorem set_bound_of_forall (l : List Nat) (k v : Nat) (hv : v < 2 ^ 32)
    (ht : ∀ x ∈ l, x < 2 ^ 32) : ∀ x ∈ l.set k v, x < 2 ^ 32 := by
  intro x hx
  rcases set_mem_of_eq l k v x hx with rfl | hin
  · exact hv
  · exact ht x hin

theorem ziMulAccStep_bound_mem (aLimbs bLimbs : List Nat) (i j : Nat) (t : List Nat) (carry : Nat)
    (ht : ∀ x ∈ t, x < 2 ^ 32) :
    ∀ x ∈ (ziMulAccStep aLimbs bLimbs i t j carry).1, x < 2 ^ 32 := by
  intro x hx
  unfold ziMulAccStep at hx
  exact set_bound_of_forall t (i + j) _ (Nat.mod_lt _ (by omega)) ht x hx

theorem ziMulAccStep_carry_bound (aLimbs bLimbs : List Nat) (i j : Nat) (t : List Nat) (carry : Nat)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (ht : ∀ x ∈ t, x < 2 ^ 32) (hcarry : carry < 2 ^ 32) :
    (ziMulAccStep aLimbs bLimbs i t j carry).2 < 2 ^ 32 := by
  unfold ziMulAccStep
  simp
  have hav := ziAddTerm_bound aLimbs hlla i
  have hbv := ziAddTerm_bound bLimbs hllb j
  have htv : (t[i + j]?).getD 0 ≤ 4294967295 := by
    cases h : t[i + j]? with
    | none => decide
    | some x =>
        rw [List.getElem?_eq_some_iff] at h
        obtain ⟨h1, h2⟩ := h
        have hmem : x ∈ t := h2 ▸ List.getElem_mem h1
        have := ht x hmem
        simp only [Option.getD_some]
        omega
  have hbp : ziAddTerm aLimbs i * ziAddTerm bLimbs j ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hv : ziAddTerm aLimbs i * ziAddTerm bLimbs j + (t[i + j]?).getD 0 + carry < 2 ^ 64 := by
    omega
  have hdiv := hv
  omega

theorem ziMulAcc_invariants (aLimbs bLimbs : List Nat) (i : Nat)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (j : Nat) (t : List Nat) (carry : Nat) (ht : ∀ x ∈ t, x < 2 ^ 32) (hcarry : carry < 2 ^ 32) :
    (∀ x ∈ (ziMulAcc aLimbs bLimbs i t carry j).1, x < 2 ^ 32) ∧
      (ziMulAcc aLimbs bLimbs i t carry j).2 < 2 ^ 32 := by
  induction j generalizing t carry with
  | zero => exact ⟨ht, hcarry⟩
  | succ j ih =>
      obtain ⟨hmem, hcarrybound⟩ := ih t carry ht hcarry
      exact ⟨ziMulAccStep_bound_mem aLimbs bLimbs i j (ziMulAcc aLimbs bLimbs i t carry j).1
          (ziMulAcc aLimbs bLimbs i t carry j).2 hmem,
        ziMulAccStep_carry_bound aLimbs bLimbs i j
          (ziMulAcc aLimbs bLimbs i t carry j).1 (ziMulAcc aLimbs bLimbs i t carry j).2
          hlla hllb hmem hcarrybound⟩

theorem ziMulAcc_mem_bound (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (carry : Nat)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (ht : ∀ x ∈ t, x < 2 ^ 32) (hcarry : carry < 2 ^ 32) (j : Nat) :
    ∀ x ∈ (ziMulAcc aLimbs bLimbs i t carry j).1, x < 2 ^ 32 :=
  (ziMulAcc_invariants aLimbs bLimbs i hlla hllb j t carry ht hcarry).1

theorem ziMulAcc_carry_bound (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (carry : Nat)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (ht : ∀ x ∈ t, x < 2 ^ 32) (hcarry : carry < 2 ^ 32) (j : Nat) :
    (ziMulAcc aLimbs bLimbs i t carry j).2 < 2 ^ 32 :=
  (ziMulAcc_invariants aLimbs bLimbs i hlla hllb j t carry ht hcarry).2

theorem ziMulAcc_length (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (carry : Nat) (j : Nat) :
    (ziMulAcc aLimbs bLimbs i t carry j).1.length = t.length := by
  induction j generalizing t carry with
  | zero => rfl
  | succ j ih => simp [ziMulAcc, ziMulAccStep, List.length_set, ih]

/-- The index expression used by `.index ... (.var 4) 4` for t (with i + j). -/
theorem evMulAddIndex (s : State) (a b : Nat) (ha : s.locals 3 = some (.int ⟨64, false⟩ a))
    (hb : s.locals 4 = some (.int ⟨64, false⟩ b))
    (hbound : a + b < 18446744073709551616) :
    EvE LimbGen.prog s (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4))
      (.int ⟨64, false⟩ (a + b)) :=
  EvE.bin (EvE.var ha) (EvE.var hb) (by
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus, Nat.mod_eq_of_lt hbound])

/-- Simulation relation for one row of schoolbook multiplication: after `j`
positions of row `i`, `t` holds the partial accumulation with carry `k_j`,
and locals 3..6 bind to `i`, `j`, `k_j`. -/
def ziMulInnerInv (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i j : Nat)
    (s : State) : Prop :=
  i < aLen ∧ j ≤ bLen ∧ j < 18446744073709551616 ∧ i < 18446744073709551616 ∧
    aLen < 18446744073709551616 ∧ bLen < 18446744073709551616 ∧
    aLimbs.length = aLen ∧ bLimbs.length = bLen ∧ t0.length = aLen + bLen ∧
    t0.length < 18446744073709551616 ∧
    (∀ x ∈ aLimbs, x < 2 ^ 32) ∧ (∀ x ∈ bLimbs, x < 2 ^ 32) ∧ (∀ x ∈ t0, x < 2 ^ 32) ∧
    s.ro = false ∧
    s.locals 0 = some (.ptr tsblk 0) ∧ s.locals 1 = some (.ptr asblk 0) ∧
    s.locals 2 = some (.ptr bsblk 0) ∧ s.locals 3 = some (.int ⟨64, false⟩ i) ∧
    s.locals 4 = some (.int ⟨64, false⟩ j) ∧
    s.locals 5 = some (.int ⟨64, false⟩ (ziMulAcc aLimbs bLimbs i t0 0 j).2) ∧
    s.mem tsblk = some (ziBlock tarr (aLen + bLen) 1) ∧ s.mem asblk = some (ziBlock aarr aLen 1) ∧
    s.mem bsblk = some (ziBlock barr bLen 1) ∧
    s.mem aarr = some (limbBytes aLimbs) ∧ s.mem barr = some (limbBytes bLimbs) ∧
    (s.mem tarr = some (limbBytes (ziMulAcc aLimbs bLimbs i t0 0 j).1)) ∧
    tsblk < 4294967296 ∧ tarr < 4294967296 ∧ asblk < 4294967296 ∧
    aarr < 4294967296 ∧ bsblk < 4294967296 ∧ barr < 4294967296 ∧
    tarr ≠ tsblk ∧ tarr ≠ asblk ∧ tarr ≠ bsblk ∧ tarr ≠ aarr ∧ tarr ≠ barr

/-- Limb load for the a/b struct arrays at index `i` bounded by the zi length. -/
theorem evMulLimbLoad (s : State) (select vidx : Nat) (zb vblk : Nat)
    (limbs : List Nat) (idx : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length 1)) (hb : vblk < 4294967296)
    (hl : s.locals select = some (.ptr zb 0))
    (hl2 : s.locals vidx = some (.int ⟨64, false⟩ idx))
    (hlm : s.mem vblk = some (limbBytes limbs)) (hi : idx < limbs.length)
    (hlla : ∀ x ∈ limbs, x < 2 ^ 32) :
    EvE LimbGen.prog s (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var select) 0)) (.var vidx) 4))
      (.int ⟨32, false⟩ (limbs[idx]'hi)) := by
  have hfield : EvE LimbGen.prog s (.field (.var select) 0) (.ptr zb 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var select) 0)) (.ptr vblk 0) :=
    EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length 1 hm hb)
  have hbound : 0 + idx * 4 ≤ (limbBytes limbs).length := by
    rw [limbBytes_length]; omega
  have hidx : EvE LimbGen.prog s
      (.index (.load .ptr (.field (.var select) 0)) (.var vidx) 4)
      (.ptr vblk (idx * 4)) := by
    apply EvE.index hloadPtr (EvE.var hl2)
    simp only [u64, Bool.false_eq_true, if_false]
    show ptrAddN _ _ _ = _
    simp only [ptrAddN, hlm, if_pos hbound]
    rw [show 0 + idx * 4 = idx * 4 from Nat.zero_add _]
  have hload' := load_limb s.mem vblk limbs idx hlm hi
  rw [Nat.mod_eq_of_lt (hlla _ (List.getElem_mem hi)), Nat.mul_comm] at hload'
  exact EvE.load hidx hload'

/-- The destination limb at index `i + j`, out of ziMulAcc. -/
theorem evMulTLimbLoad (s : State) (tsblk tarr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i j : Nat)
    (hm : s.mem tsblk = some (ziBlock tarr (aLen + bLen) 1)) (hb : tarr < 4294967296)
    (hl : s.locals 0 = some (.ptr tsblk 0))
    (hl3 : s.locals 3 = some (.int ⟨64, false⟩ i)) (hl4 : s.locals 4 = some (.int ⟨64, false⟩ j))
    (hlm : s.mem tarr = some (limbBytes ((ziMulAcc aLimbs bLimbs i t0 0 j).1)))
    (hi : i < aLen) (hbj : j < bLen) (hlenT : t0.length = aLen + bLen)
    (hav : aLimbs.length = aLen) (hbv : bLimbs.length = bLen)
    (hLen64 : aLen < 18446744073709551616) (hLen64B : bLen < 18446744073709551616)
    (hLenT64 : t0.length < 18446744073709551616)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (ht0 : ∀ x ∈ t0, x < 2 ^ 32)
    (hijbnd : i + j < (ziMulAcc aLimbs bLimbs i t0 0 j).1.length) :
    EvE LimbGen.prog s (.load (.int ⟨32, false⟩)
        (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4))
      (.int ⟨32, false⟩ ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]'hijbnd)) := by
  have hlv := ziMulAcc_mem_bound aLimbs bLimbs i t0 0 hlla hllb ht0 (by decide) j
    ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]'hijbnd) (List.getElem_mem hijbnd)
  have hfield : EvE LimbGen.prog s (.field (.var 0) 0) (.ptr tsblk 0) :=
    EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
  have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var 0) 0)) (.ptr tarr 0) :=
    EvE.load hfield (load_ziBlock_v s.mem tsblk tarr (aLen + bLen) 1 hm hb)
  have hbound64 : i + j < 18446744073709551616 := by omega
  have h3v : EvE LimbGen.prog s (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4))
      (.int ⟨64, false⟩ (i + j)) :=
    evMulAddIndex s i j hl3 hl4 hbound64
  have hbound : 0 + (i + j) * 4 ≤ (limbBytes ((ziMulAcc aLimbs bLimbs i t0 0 j).1)).length := by
    rw [limbBytes_length, ziMulAcc_length]; omega
  have hidx : EvE LimbGen.prog s
      (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)
      (.ptr tarr ((i + j) * 4)) := by
    apply EvE.index hloadPtr h3v
    simp only [u64, Bool.false_eq_true, if_false]
    show ptrAddN _ _ _ = _
    simp only [ptrAddN, hlm, if_pos hbound]
    rw [show 0 + (i + j) * 4 = (i + j) * 4 from Nat.zero_add _]
  have hload' := load_limb s.mem tarr ((ziMulAcc aLimbs bLimbs i t0 0 j).1) (i + j) hlm hijbnd
  rw [Nat.mod_eq_of_lt hlv, Nat.mul_comm] at hload'
  exact EvE.load hidx hload'

/-- The k argument: locals 5 is the accumulated carry, cast to u32 limb. -/
theorem evMulKCast (s : State) (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i j : Nat)
    (hInv : ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i j s) :
    EvE LimbGen.prog s (.cast ⟨32, false⟩ (.var 5))
      (.int ⟨32, false⟩ (ziMulAcc aLimbs bLimbs i t0 0 j).2) := by
  obtain ⟨_, _, _, _, _, _, hna, hnb, _, _, hlla, hllb, ht0, _, _, _, _, _, _, hloc5,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hInv
  have hcarry := ziMulAcc_carry_bound aLimbs bLimbs i t0 0 hlla hllb ht0 (by decide) j
  exact EvE.cast (EvE.var hloc5) (by
    simp [evalCast, IntTy.u32, IntTy.u64, IntTy.modulus, Nat.mod_eq_of_lt hcarry])

/-- The madd call inside the inner loop: value is the schoolbook product limbs
`.int IntTy.u64 (av*bv + tl + k)`. -/
theorem ziMul_call (s : State) (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i j : Nat)
    (hInv : ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i j s)
    (hi : j < bLen) (hb64 : bLen < 18446744073709551616)
    (hLen64 : aLen < 18446744073709551616)
    (hijbnd : i + j < (ziMulAcc aLimbs bLimbs i t0 0 j).1.length) :
    EvE LimbGen.prog s
      (.call 0
        [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
         (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
         (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
            (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
         (.cast ⟨32, false⟩ (.var 5))])
      (.int IntTy.u64
        (ziAddTerm aLimbs i * ziAddTerm bLimbs j +
          ((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hijbnd +
          (ziMulAcc aLimbs bLimbs i t0 0 j).2)) := by
  have hKInv := hInv
  obtain ⟨iBd, _, _, _, _, _, hna, hnb, ht0Len, ht0LenW64, hlla, hllb, ht0,
    hro, hloc0, hloc1, hloc2, hloc3, hloc4, hloc5,
    hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
    _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
    _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩ := hInv
  have hna64 : i < aLimbs.length := by rw [hna]; omega
  have hnb64 : j < bLimbs.length := by rw [hnb]; omega
  have hims : ziAddTerm aLimbs i = aLimbs[i]'hna64 := by simp [ziAddTerm, hna64]
  have hjms : ziAddTerm bLimbs j = bLimbs[j]'hnb64 := by simp [ziAddTerm, hnb64]
  have hlim := ziMulAcc_mem_bound aLimbs bLimbs i t0 0 hlla hllb ht0 (by decide) j
    (((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hijbnd) (List.getElem_mem hijbnd)
  have hcarry := ziMulAcc_carry_bound aLimbs bLimbs i t0 0 hlla hllb ht0 (by decide) j
  have hloadA : EvE LimbGen.prog s
      (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4))
      (.int ⟨32, false⟩ (ziAddTerm aLimbs i)) := by
    rw [hims]
    have hm : s.mem asblk = some (ziBlock aarr aLimbs.length 1) := by rw [hna]; exact hastruct
    exact evMulLimbLoad s 1 3 asblk aarr aLimbs i hm _haarrBound hloc1 hloc3 haLimbs hna64 hlla
  have hloadB : EvE LimbGen.prog s
      (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4))
      (.int ⟨32, false⟩ (ziAddTerm bLimbs j)) := by
    rw [hjms]
    have hm : s.mem bsblk = some (ziBlock barr bLimbs.length 1) := by rw [hnb]; exact hbstruct
    exact evMulLimbLoad s 2 4 bsblk barr bLimbs j hm _hbarBound hloc2 hloc4 hbLimbs hnb64 hllb
  have hloadT : EvE LimbGen.prog s
      (.load (.int ⟨32, false⟩)
        (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4))
      (.int ⟨32, false⟩ ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]'hijbnd)) :=
    evMulTLimbLoad s tsblk tarr aLimbs bLimbs t0 aLen bLen i j hnaz _hTarbound hloc0
      hloc3 hloc4 hmemTarr iBd hi ht0Len hna hnb hLen64 hb64 ht0LenW64 hlla hllb ht0 hijbnd
  have hcastK : EvE LimbGen.prog s (.cast ⟨32, false⟩ (.var 5))
      (.int ⟨32, false⟩ (ziMulAcc aLimbs bLimbs i t0 0 j).2) :=
    evMulKCast s tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i j hKInv
  have hargs : EvArgs LimbGen.prog s
      [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
       (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
       (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
         (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
       (.cast ⟨32, false⟩ (.var 5))]
      [(.int IntTy.u32 (ziAddTerm aLimbs i)),
       (.int IntTy.u32 (ziAddTerm bLimbs j)),
       (.int IntTy.u32 ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]'hijbnd)),
       (.int IntTy.u32 (ziMulAcc aLimbs bLimbs i t0 0 j).2)] :=
    EvArgs.cons hloadA (EvArgs.cons hloadB (EvArgs.cons hloadT (EvArgs.cons hcastK EvArgs.nil)))
  let args : List Val :=
    [Val.int IntTy.u32 (ziAddTerm aLimbs i), Val.int IntTy.u32 (ziAddTerm bLimbs j),
     Val.int IntTy.u32 ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]'hijbnd),
     Val.int IntTy.u32 (ziMulAcc aLimbs bLimbs i t0 0 j).2]
  let frame : State :=
    ⟨frameLocals LimbGen.tess_limb_madd.params args, s.mem, true⟩
  have l0 : frame.locals 0 = some (Val.int IntTy.u32 (ziAddTerm aLimbs i)) := rfl
  have l1 : frame.locals 1 = some (Val.int IntTy.u32 (ziAddTerm bLimbs j)) := rfl
  have l2 : frame.locals 2 = some (Val.int IntTy.u32 ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]'hijbnd)) := rfl
  have l3 : frame.locals 3 = some (Val.int IntTy.u32 (ziMulAcc aLimbs bLimbs i t0 0 j).2) := rfl
  have hbody := limb_madd_refines_lm frame
    (ziAddTerm aLimbs i) (ziAddTerm bLimbs j)
    ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]'hijbnd) (ziMulAcc aLimbs bLimbs i t0 0 j).2
    (ziAddTerm_bound aLimbs hlla i)
    (ziAddTerm_bound bLimbs hllb j)
    hlim
    hcarry l0 l1 l2 l3
  have hprog0 : LimbGen.prog 0 = some LimbGen.tess_limb_madd := rfl
  have hlen : LimbGen.tess_limb_madd.params.length = args.length := by
    rfl
  exact EvE.call hargs hprog0 hlen hbody

/-- Load aLimb[i]: the `if (i < x->n) a->v[i] else 0` expression with the counter in local `vidx`. -/
theorem evMulTermCond (s : State) (select vidx : Nat) (zb vblk : Nat)
    (limbs : List Nat) (idx : Nat)
    (hm : s.mem zb = some (ziBlock vblk limbs.length 1)) (hb : vblk < 4294967296)
    (hl : s.locals select = some (.ptr zb 0))
    (hl2 : s.locals vidx = some (.int ⟨64, false⟩ idx))
    (hlm : s.mem vblk = some (limbBytes limbs))
    (hlla : ∀ x ∈ limbs, x < 2 ^ 32) (hi : idx < 18446744073709551616)
    (nBound : limbs.length < 18446744073709551616) :
    EvE LimbGen.prog s
      (.cast ⟨64, false⟩
        (.cond (.bin .lt (some ⟨64, false⟩) (.var vidx)
                 (.load (.int ⟨64, false⟩) (.field (.var select) 8)))
               (.load (.int ⟨32, false⟩)
                  (.index (.load .ptr (.field (.var select) 0)) (.var vidx) 4))
               (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      (.int ⟨64, false⟩ (ziAddTerm limbs idx)) := by
  have hloadN : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var select) 8))
      (.int ⟨64, false⟩ (limbs.length % 2 ^ 64)) :=
    evZiN s select zb vblk limbs.length hm hb hl
  have hlen64 : limbs.length < 18446744073709551616 := nBound
  have hlt : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var vidx)
        (.load (.int ⟨64, false⟩) (.field (.var select) 8))) (boolVal (decide (idx < limbs.length))) := by
    refine EvE.bin (EvE.var hl2) hloadN ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus,
      Nat.mod_eq_of_lt hlen64]
  by_cases hh : idx < limbs.length
  · have htrue : truthy (boolVal (decide (idx < limbs.length))) = .ok true := by
      have hd : decide (idx < limbs.length) = true := by simp [decide_eq_true_iff, hh]
      rw [hd]; rfl
    have hfield : EvE LimbGen.prog s (.field (.var select) 0) (.ptr zb 0) :=
      EvE.field (EvE.var hl) (by simp [ptrAddN, hm, ziBlock_length])
    have hloadPtr : EvE LimbGen.prog s (.load .ptr (.field (.var select) 0)) (.ptr vblk 0) :=
      EvE.load hfield (load_ziBlock_v s.mem zb vblk limbs.length 1 hm hb)
    have hidx4 : idx * 4 ≤ (limbBytes limbs).length := by
      rw [limbBytes_length]; omega
    have hidx : EvE LimbGen.prog s
        (.index (.load .ptr (.field (.var select) 0)) (.var vidx) 4)
        (.ptr vblk (idx * 4)) := by
      apply EvE.index hloadPtr (EvE.var hl2)
      simp only [u64, Bool.false_eq_true, if_false]
      show ptrAddN _ _ _ = _
      have hbound : 0 + idx * 4 ≤ (limbBytes limbs).length := by
        rw [limbBytes_length]; omega
      simp only [ptrAddN, hlm]
      rw [if_pos hbound]
      rw [show 0 + idx * 4 = idx * 4 from Nat.zero_add _]
    have hload : EvE LimbGen.prog s
        (.load (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var select) 0)) (.var vidx) 4))
        (.int ⟨32, false⟩ (limbs[idx]'hh)) := by
      have hload' := load_limb s.mem vblk limbs idx hlm hh
      rw [Nat.mod_eq_of_lt (hlla _ (List.getElem_mem hh)), Nat.mul_comm] at hload'
      exact EvE.load hidx hload'
    have hcond : EvE LimbGen.prog s
        (.cond (.bin .lt (some ⟨64, false⟩) (.var vidx)
                 (.load (.int ⟨64, false⟩) (.field (.var select) 8)))
               (.load (.int ⟨32, false⟩)
                  (.index (.load .ptr (.field (.var select) 0)) (.var vidx) 4))
               (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
        (.int ⟨32, false⟩ (limbs[idx]'hh)) :=
      EvE.cond hlt htrue hload
    have hcast : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ (limbs[idx]'hh)) =
        .ok (.int ⟨64, false⟩ (limbs[idx]'hh)) := by
      have hll := hlla _ (List.getElem_mem hh)
      simp [evalCast, IntTy.modulus]
      omega
    have hzi : ziAddTerm limbs idx = limbs[idx]'hh := by simp [ziAddTerm, hh]
    rw [hzi]
    exact EvE.cast hcond hcast
  · have hfalse : truthy (boolVal (decide (idx < limbs.length))) = .ok false := by
      rw [decide_eq_false_iff_not.mpr hh]; rfl
    have hcast0 : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 0) = .ok (.int ⟨32, false⟩ 0) := rfl
    have hconst : EvE LimbGen.prog s
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))
        (.int ⟨32, false⟩ 0) := by
      exact EvE.cast (EvE.const _) hcast0
    have hcond : EvE LimbGen.prog s
        (.cond (.bin .lt (some ⟨64, false⟩) (.var vidx)
                 (.load (.int ⟨64, false⟩) (.field (.var select) 8)))
               (.load (.int ⟨32, false⟩)
                  (.index (.load .ptr (.field (.var select) 0)) (.var vidx) 4))
               (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
        (.int ⟨32, false⟩ 0) :=
      EvE.cond hlt hfalse hconst
    have hcast : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 0) = .ok (.int ⟨64, false⟩ 0) := rfl
    have hzi : ziAddTerm limbs idx = 0 := by
      simp [ziAddTerm, hh]
    rw [hzi]
    exact EvE.cast hcond hcast

/-- The zi_mul_accumulate_loop0 inner body AST, exposed for the loop proofs. -/
def ziMulInnerBody : Stmt :=
  .ite (.bin .lt (some ⟨64, false⟩) (.var 4)
    (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
    (.seq (.set 6 (.call 0
        [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
         (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
         (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
            (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
         (.cast ⟨32, false⟩ (.var 5))]))
      (.seq (.store (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)
          (.cast ⟨32, false⟩ (.var 6)))
        (.set 5 (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32))))))
    .brk

/-- The zi_mul_accumulate_loop0 step statement. -/
def ziMulInnerStep : Stmt :=
  .set 4 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
    (.const (.int ⟨64, false⟩ 1))))

theorem ziMulInnerLoop_ast : Tess.C.LimbGen.zi_mul_accumulate_loop0 =
    Stmt.loop ziMulInnerBody ziMulInnerStep := by
  rfl

/-- The low half of a schoolbook accumulate step, for direct correspondence. -/
theorem ziMulAccStep_def (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (j : Nat) (carry : Nat) :
    ziMulAccStep aLimbs bLimbs i t j carry =
      (t.set (i + j)
        ((ziAddTerm aLimbs i * ziAddTerm bLimbs j + (t[i + j]?).getD 0 + carry) % 2 ^ 32),
       (ziAddTerm aLimbs i * ziAddTerm bLimbs j + (t[i + j]?).getD 0 + carry) / 2 ^ 32) := rfl

theorem ziMulAcc_succ (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (carry : Nat) (j : Nat) :
    ziMulAcc aLimbs bLimbs i t carry (j + 1) =
      ziMulAccStep aLimbs bLimbs i (ziMulAcc aLimbs bLimbs i t carry j).1 j
        (ziMulAcc aLimbs bLimbs i t carry j).2 := rfl

theorem ziMulAcc_zero (aLimbs bLimbs : List Nat) (i : Nat) (t : List Nat) (carry : Nat) :
    ziMulAcc aLimbs bLimbs i t carry 0 = (t, carry) := rfl

/-- One iteration of the zi_mul_accumulate inner loop: the `ite` taken branch. -/
theorem ziMul_iCell (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i j : Nat)
    (hInv : ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i j s)
    (hi : j < bLen) (hb64 : bLen < 18446744073709551616)
    (hLen64 : aLen < 18446744073709551616)
    (hjnd : i + j < (ziMulAcc aLimbs bLimbs i t0 0 j).1.length) :
    ∃ s1 s2, ExS LimbGen.prog s ziMulInnerBody .normal s1 ∧
      ExS LimbGen.prog s1 ziMulInnerStep .normal s2 ∧
      ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i (j + 1) s2 := by
  have hKInv := hInv
  obtain ⟨iBd, _, _, _, _, _, hna, hnb, ht0Len, ht0LenW64, hlla, hllb, ht0,
    hro, hloc0, hloc1, hloc2, hloc3, hloc4, hloc5,
    hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
    _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
    _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩ := hInv
  have hna64 : i < aLimbs.length := by rw [hna]; omega
  have hnb64 : j < bLimbs.length := by rw [hnb]; omega
  have hims : ziAddTerm aLimbs i = aLimbs[i]'hna64 := by simp [ziAddTerm, hna64]
  have hjms : ziAddTerm bLimbs j = bLimbs[j]'hnb64 := by simp [ziAddTerm, hnb64]
  have hi64 : i < 18446744073709551616 := by omega
  have hj64 : j < 18446744073709551616 := by omega
  have hlim := ziMulAcc_mem_bound aLimbs bLimbs i t0 0 hlla hllb ht0 (by decide) j
    (((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hjnd) (List.getElem_mem hjnd)
  have hcarry := ziMulAcc_carry_bound aLimbs bLimbs i t0 0 hlla hllb ht0 (by decide) j
  have hav := ziAddTerm_bound aLimbs hlla i
  have hbv := ziAddTerm_bound bLimbs hllb j
  have hvbound : ziAddTerm aLimbs i * ziAddTerm bLimbs j +
      ((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hjnd + (ziMulAcc aLimbs bLimbs i t0 0 j).2 < 2 ^ 64 := by
    have hbp : ziAddTerm aLimbs i * ziAddTerm bLimbs j ≤ 4294967295 * 4294967295 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  let v : Nat := ziAddTerm aLimbs i * ziAddTerm bLimbs j +
      (((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hjnd) +
      (ziMulAcc aLimbs bLimbs i t0 0 j).2
  have hv64 : v < 2 ^ 64 := hvbound
  let s6 : State := { s with locals := s.locals.upd 6 (.int IntTy.u64 v) }
  have hset6 : ExS LimbGen.prog s (.set 6 (.call 0
        [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
         (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
         (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
            (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
         (.cast ⟨32, false⟩ (.var 5))])) .normal s6 := by
    have hcall : EvE LimbGen.prog s
        (.call 0
          [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
           (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
           (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
             (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
           (.cast ⟨32, false⟩ (.var 5))])
        (.int IntTy.u64 v) := by
      show EvE LimbGen.prog s
        (.call 0
          [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
           (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
           (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
             (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
           (.cast ⟨32, false⟩ (.var 5))])
        (.int IntTy.u64 ((ziAddTerm aLimbs i * ziAddTerm bLimbs j) + (((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hjnd) + (ziMulAcc aLimbs bLimbs i t0 0 j).2))
      exact ziMul_call s tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i j hKInv
        hi hb64 hLen64 hjnd
    exact ExS.set hcall
  have hl6' : s6.locals 6 = some (.int IntTy.u64 v) := by simp [s6, Locals.upd]
  have hl4' : s6.locals 4 = some (.int ⟨64, false⟩ j) := by simp [s6, Locals.upd]; exact hloc4
  have hl5' : s6.locals 5 = some (.int ⟨64, false⟩ (ziMulAcc aLimbs bLimbs i t0 0 j).2) := by simp [s6, Locals.upd]; exact hloc5
  have hl0' : s6.locals 0 = some (Val.ptr tsblk 0) := by simp [s6, Locals.upd]; exact hloc0
  have hl1' : s6.locals 1 = some (Val.ptr asblk 0) := by simp [s6, Locals.upd]; exact hloc1
  have hl2' : s6.locals 2 = some (Val.ptr bsblk 0) := by simp [s6, Locals.upd]; exact hloc2
  have hl3' : s6.locals 3 = some (Val.int ⟨64, false⟩ i) := by simp [s6, Locals.upd]; exact hloc3
  have hgetElem : ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]?).getD 0 =
      ((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hjnd := by
    rw [List.getElem?_eq_getElem hjnd]; rfl
  have hocc : ziMulAcc aLimbs bLimbs i t0 0 (j + 1) =
      ziMulAccStep aLimbs bLimbs i (ziMulAcc aLimbs bLimbs i t0 0 j).1 j
        (ziMulAcc aLimbs bLimbs i t0 0 j).2 := rfl


  have hbound64 : i + j < 18446744073709551616 := by
    rw [← ziMulAcc_length aLimbs bLimbs i t0 0 j] at ht0LenW64
    omega
  have hloadPtr6 : EvE LimbGen.prog s6 (.load .ptr (.field (.var 0) 0)) (.ptr tarr 0) := by
    have hloc0'' : s6.locals 0 = some (Val.ptr tsblk 0) := hl0'
    exact evVPointer s6 0 tsblk tarr (aLen + bLen) hnaz _hTarbound hloc0''
  have h3v : EvE LimbGen.prog s6 (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4))
      (.int ⟨64, false⟩ (i + j)) := by
    apply EvE.bin (EvE.var hl3') (EvE.var hl4') (by
      simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus, Nat.mod_eq_of_lt hbound64])
  have hidx6 : EvE LimbGen.prog s6
      (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)
      (.ptr tarr ((i + j) * 4)) := by
    apply EvE.index hloadPtr6 h3v
    simp only [s6, u64, Bool.false_eq_true, if_false]
    show ptrAddN _ _ _ = _
    have hbound : 0 + (i + j) * 4 ≤ (limbBytes ((ziMulAcc aLimbs bLimbs i t0 0 j).1)).length := by
      rw [limbBytes_length, ziMulAcc_length]; omega
    simp only [ptrAddN, hmemTarr, if_pos hbound]
    rw [show 0 + (i + j) * 4 = (i + j) * 4 from Nat.zero_add _]
  have hstoreVal : EvE LimbGen.prog s6 (.cast ⟨32, false⟩ (.var 6))
      (.int ⟨32, false⟩ (v % 2 ^ 32)) := by
    have hloc6' : s6.locals 6 = some (.int IntTy.u64 v) := hl6'
    exact EvE.cast (EvE.var hloc6') (evalCast_u64_u32 v)
  have hlim_mem : i + j < ((ziMulAcc aLimbs bLimbs i t0 0 j).1).length := by
    rw [ziMulAcc_length]; omega
  have hro6 : s6.ro = false := by show s.ro = false; exact hro
  have hstore : ExS LimbGen.prog s6
      (.store (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)
        (.cast ⟨32, false⟩ (.var 6))) .normal
      { s6 with mem := s6.mem.upd tarr (limbBytes ((ziMulAcc aLimbs bLimbs i t0 0 j).1.set (i + j) (v % 2 ^ 32))) } := by
    have hidx6' : EvE LimbGen.prog s6 (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)
        (.ptr tarr (4 * (i + j))) := by
      rw [Nat.mul_comm]; exact hidx6
    have hstore' := store_limb s6.mem tarr (ziMulAcc aLimbs bLimbs i t0 0 j).1 (i + j) (v % 2 ^ 32) hmemTarr hlim_mem
    exact ExS.store hidx6' hstoreVal hro6 hstore'
  let s7 : State := { s6 with mem := s6.mem.upd tarr (limbBytes ((ziMulAcc aLimbs bLimbs i t0 0 j).1.set (i + j) (v % 2 ^ 32))) }
  have hl6'' : s7.locals 6 = some (.int IntTy.u64 v) := by simp [s7, s6, Locals.upd]
  have hset5 : ExS LimbGen.prog s7 (.set 5 (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32))))
      .normal { s7 with locals := s7.locals.upd 5 (.int IntTy.u64 (v / 2 ^ 32)) } := by
    have h5 : EvE LimbGen.prog s7
        (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32)))
        (.int IntTy.u64 (v / 2 ^ 32)) := by
      show EvE LimbGen.prog s7 (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32))) _
      apply EvE.bin (EvE.var hl6'') (EvE.const _)
      rfl
    exact ExS.set h5
  let s8 : State := { s7 with locals := s7.locals.upd 5 (.int IntTy.u64 (v / 2 ^ 32)) }
  let s9 : State := { s8 with locals := s8.locals.upd 4 (.int ⟨64, false⟩ (j + 1)) }
  have hocc : ziMulAcc aLimbs bLimbs i t0 0 (j + 1) =
      ziMulAccStep aLimbs bLimbs i (ziMulAcc aLimbs bLimbs i t0 0 j).1 j
        (ziMulAcc aLimbs bLimbs i t0 0 j).2 := rfl
  have hgot : ((ziMulAcc aLimbs bLimbs i t0 0 j).1[i + j]?).getD 0 =
      ((ziMulAcc aLimbs bLimbs i t0 0 j).1)[i + j]'hjnd := by
    rw [List.getElem?_eq_getElem hjnd]; rfl
  have hocc2 : ziMulAccStep aLimbs bLimbs i ((ziMulAcc aLimbs bLimbs i t0 0 j).1) j
        (ziMulAcc aLimbs bLimbs i t0 0 j).2 =
      (((ziMulAcc aLimbs bLimbs i t0 0 j).1).set (i + j) (v % 2 ^ 32), v / 2 ^ 32) := by
    simp only [ziMulAccStep, hgot]
    rfl
  have hout4 : EvE LimbGen.prog s (.var 4) (.int ⟨64, false⟩ j) := EvE.var hloc4
  have hout3 : EvE LimbGen.prog s (.var 3) (.int ⟨64, false⟩ i) := EvE.var hloc3
  have hloadN : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 2) 8))
      (.int ⟨64, false⟩ (bLimbs.length % 2 ^ 64)) := by
    have hm : s.mem bsblk = some (ziBlock barr bLimbs.length 1) := by rw [hnb]; exact hbstruct
    exact evZiN s 2 bsblk barr bLimbs.length hm _hbarBound hloc2
  have hlt_ev : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4)
        (.load (.int ⟨64, false⟩) (.field (.var 2) 8))) (boolVal (decide (j < bLimbs.length))) := by
    apply EvE.bin hout4 hloadN (by
      show evalBin .lt (some ⟨64, false⟩) (.int ⟨64, false⟩ j) (.int ⟨64, false⟩ (bLimbs.length % 2 ^ 64)) =
        .ok (boolVal (decide (j < bLimbs.length)))
      rw [Nat.mod_eq_of_lt (by omega : bLimbs.length < 18446744073709551616), hnb]
      rfl)
  have htrue : truthy (boolVal (decide (j < bLimbs.length))) = .ok true := by
    have hd : decide (j < bLimbs.length) = true := by
      have hjl : j < bLimbs.length := by rw [hnb]; exact hi
      exact decide_eq_true_iff.mpr hjl
    rw [hd]; rfl
  have hseq : ExS LimbGen.prog s
      (.seq (.set 6 (.call 0
          [(.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 1) 0)) (.var 3) 4)),
           (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 2) 0)) (.var 4) 4)),
           (.load (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0))
              (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)),
           (.cast ⟨32, false⟩ (.var 5))]))
        (.seq (.store (.int ⟨32, false⟩) (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3) (.var 4)) 4)
            (.cast ⟨32, false⟩ (.var 6)))
          (.set 5 (.bin .shr (some ⟨64, false⟩) (.var 6) (.const (.int ⟨32, true⟩ 32))))))
      .normal s8 :=
    ExS.seq hset6 (ExS.seq hstore hset5)
  have hbody : ExS LimbGen.prog s ziMulInnerBody .normal s8 :=
    ExS.ite hlt_ev htrue hseq
  have hbound8 : i + (j + 1) < 18446744073709551616 := by omega
  have hstep : ExS LimbGen.prog s8 ziMulInnerStep .normal s9 := by
    show ExS LimbGen.prog s8
      (.set 4 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
        (.const (.int ⟨64, false⟩ 1))))) .normal s9
    exact ExS.set (evVar4Increment s8 j (by omega) (by
      simp [s9, s8, s7, s6, Locals.upd]; exact hloc4))
  refine ⟨s8, s9, hbody, hstep, ?_⟩
  have hTarAlign : s9.mem tarr = some (limbBytes ((ziMulAcc aLimbs bLimbs i t0 0 (j + 1)).1)) := by
    rw [hocc, hocc2]
    simp [s9, s8, s7, s6, Mem.upd_same]
  have hloc5ff : s9.locals 5 = some (.int ⟨64, false⟩ (ziMulAcc aLimbs bLimbs i t0 0 (j + 1)).2) := by
    have hocc2' : (ziMulAccStep aLimbs bLimbs i ((ziMulAcc aLimbs bLimbs i t0 0 j).1) j
        (ziMulAcc aLimbs bLimbs i t0 0 j).2).2 = v / 2 ^ 32 := by
      simp only [ziMulAccStep, hgot]
      rfl
    simp only [s9, s8, s7, s6, Locals.upd, ziMulAcc, hocc, hocc2']
    rfl
  have hloc4ff : s9.locals 4 = some (.int ⟨64, false⟩ (j + 1)) := by
    simp [s9, s8, Locals.upd]
  refine ⟨by omega, by omega, by omega, hi64, hLen64, hb64, hna, hnb, ht0Len, ht0LenW64, hlla, hllb, ht0,
      by simp [s9, s8, s7, s6]; exact hro,
      by simp [s9, s8, s7, s6, Locals.upd, hloc0],
      by simp [s9, s8, s7, s6, Locals.upd, hloc1],
      by simp [s9, s8, s7, s6, Locals.upd, hloc2],
      by simp [s9, s8, s7, s6, Locals.upd, hloc3],
      hloc4ff,
      hloc5ff,
      (show s9.mem tsblk = s.mem tsblk from by
        simp only [s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : tsblk ≠ tarr)]).trans hnaz,
      (show s9.mem asblk = s.mem asblk from by
        simp only [s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : asblk ≠ tarr)]).trans hastruct,
      (show s9.mem bsblk = s.mem bsblk from by
        simp only [s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : bsblk ≠ tarr)]).trans hbstruct,
      (show s9.mem aarr = s.mem aarr from by
        simp only [s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : aarr ≠ tarr)]).trans haLimbs,
      (show s9.mem barr = s.mem barr from by
        simp only [s9, s8, s7, s6, Mem.upd_ne _ _ (by omega : barr ≠ tarr)]).trans hbLimbs,
      hTarAlign,
      _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
      _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩

/-- The i-fold nested row accumulator chain: for row k, apply the dependent
accumulate of a length-`bLen` row starting from `k`'s current accumulator, then
write the overflow limb at position `k + bLen`.  The list ends up all limbs. -/
def ziMulRows (aLimbs bLimbs : List Nat) (t0 : List Nat) : Nat → List Nat
  | 0 => t0
  | k + 1 =>
      let acc := ziMulAcc aLimbs bLimbs k (ziMulRows aLimbs bLimbs t0 k) 0 bLimbs.length
      acc.1.set (k + bLimbs.length) (acc.2 % 2 ^ 32)

theorem ziMulRows_length (aLimbs bLimbs t0 : List Nat) (k : Nat) :
    (ziMulRows aLimbs bLimbs t0 k).length = t0.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [ziMulRows, ziMulAcc_length, List.length_set, ih]

theorem ziMulRows_mem_bound (aLimbs bLimbs t0 : List Nat)
    (hlla : ∀ x ∈ aLimbs, x < 2 ^ 32) (hllb : ∀ x ∈ bLimbs, x < 2 ^ 32)
    (ht0 : ∀ x ∈ t0, x < 2 ^ 32)
    (i : Nat) :
    ∀ x ∈ ziMulRows aLimbs bLimbs t0 i, x < 2 ^ 32 := by
  induction i with
  | zero => exact ht0
  | succ k ih =>
      simp only [ziMulRows]
      have hmem := ziMulAcc_mem_bound aLimbs bLimbs k (ziMulRows aLimbs bLimbs t0 k) 0 hlla hllb ih (by decide) bLimbs.length
      have hbound : (ziMulAcc aLimbs bLimbs k (ziMulRows aLimbs bLimbs t0 k) 0 bLimbs.length).2 < 2 ^ 32 :=
        ziMulAcc_carry_bound aLimbs bLimbs k (ziMulRows aLimbs bLimbs t0 k) 0 hlla hllb ih (by decide) bLimbs.length
      exact set_bound_of_forall _ _ _ (Nat.mod_lt _ (by omega)) hmem

/-- The outer AST: row `i < a->n` body. -/
def ziMulOuterBody : Stmt :=
  .ite (.bin .lt (some ⟨64, false⟩) (.var 3)
    (.load (.int ⟨64, false⟩) (.field (.var 1) 8)))
    (.seq (.set 5 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))
      (.seq (.seq (.set 4 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) Tess.C.LimbGen.zi_mul_accumulate_loop0)
        (.store (.int ⟨32, false⟩)
          (.index (.load .ptr (.field (.var 0) 0)) (.bin .add (some ⟨64, false⟩) (.var 3)
            (.load (.int ⟨64, false⟩) (.field (.var 2) 8))) 4)
          (.cast ⟨32, false⟩ (.var 5)))))
    .brk

/-- The outer step: locals 3 := locals 3 + 1, u32 -> u64 cast. -/
def ziMulOuterStep : Stmt :=
  .set 3 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
    (.const (.int ⟨64, false⟩ 1))))

theorem ziMulOuterLoop_ast : Tess.C.LimbGen.zi_mul_accumulate_loop1 =
    Stmt.loop ziMulOuterBody ziMulOuterStep := by
  rfl

theorem ziMulFunc_ast : Tess.C.LimbGen.zi_mul_accumulate.body =
    Stmt.seq (Stmt.set 3 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))
      Tess.C.LimbGen.zi_mul_accumulate_loop1 := rfl

/-- Simulation relation for the rows of schoolbook multiplication. -/
def ziMulOuterInv (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i : Nat)
    (s : State) : Prop :=
  i ≤ aLen ∧ i < 18446744073709551616 ∧ aLen < 18446744073709551616 ∧
    bLen < 18446744073709551616 ∧ t0.length = aLen + bLen ∧
    t0.length < 18446744073709551616 ∧
    aLimbs.length = aLen ∧ bLimbs.length = bLen ∧
    (∀ x ∈ aLimbs, x < 2 ^ 32) ∧ (∀ x ∈ bLimbs, x < 2 ^ 32) ∧ (∀ x ∈ t0, x < 2 ^ 32) ∧
    s.ro = false ∧
    s.locals 3 = some (.int ⟨64, false⟩ i) ∧
    s.locals 0 = some (.ptr tsblk 0) ∧ s.locals 1 = some (.ptr asblk 0) ∧
    s.locals 2 = some (.ptr bsblk 0) ∧
    s.mem tsblk = some (ziBlock tarr (aLen + bLen) 1) ∧ s.mem asblk = some (ziBlock aarr aLen 1) ∧
    s.mem bsblk = some (ziBlock barr bLen 1) ∧
    s.mem aarr = some (limbBytes aLimbs) ∧ s.mem barr = some (limbBytes bLimbs) ∧
    (s.mem tarr = some (limbBytes (ziMulRows aLimbs bLimbs t0 i))) ∧
    tsblk < 4294967296 ∧ tarr < 4294967296 ∧ asblk < 4294967296 ∧
    aarr < 4294967296 ∧ bsblk < 4294967296 ∧ barr < 4294967296 ∧
    tarr ≠ tsblk ∧ tarr ≠ asblk ∧ tarr ≠ bsblk ∧ tarr ≠ aarr ∧ tarr ≠ barr

/-- `k`-fold unrolling of the inner `zi_mul_accumulate_loop0` loop. -/
theorem ziMul_inner_loop_aux (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i : Nat) :
    ∀ (k : Nat) (s : State) (j : Nat), k = bLen - j →
      ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i j s →
      ∃ sf, ExS LimbGen.prog s Tess.C.LimbGen.zi_mul_accumulate_loop0 .normal sf ∧
        ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i bLen sf := by
  intro k
  induction k with
  | zero =>
      intro s j heq hInv
      rcases hInv with ⟨hle, _, _, _, _, _, hna, hnb, ht0Len, ht0LenW64, hlla, hllb, hllmem, hro, hloc0, hloc1,
        hloc2, hloc3, hloc4, hloc5, hnaz, hastruct, hbstruct, haLimbs, hbLimbs, hmemTarr,
        _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound, _hbsblkBound, _hbarBound,
        _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩
      have hnn : j = bLen := by omega
      have hb : bLimbs.length = j := by rw [hnb]; omega
      have bMod : bLimbs.length % 2 ^ 64 = j := by
        rw [Nat.mod_eq_of_lt (by omega : bLimbs.length < 18446744073709551616)]; exact hb
      have hout4 : EvE LimbGen.prog s (.var 4) (.int ⟨64, false⟩ j) := EvE.var hloc4
      have hout3 : EvE LimbGen.prog s (.load (.int ⟨64, false⟩) (.field (.var 2) 8))
          (.int ⟨64, false⟩ (bLimbs.length % 2 ^ 64)) := by
        have hm : s.mem bsblk = some (ziBlock barr bLimbs.length 1) := by rw [hnb]; exact hbstruct
        exact evZiN s 2 bsblk barr bLimbs.length hm _hbarBound hloc2
      have hlt_ev : EvE LimbGen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4)
            (.load (.int ⟨64, false⟩) (.field (.var 2) 8))) (boolVal (decide (j < j))) := by
        apply EvE.bin hout4 hout3 (by rw [bMod]; rfl)
      have hfalse : truthy (boolVal (decide (j < j))) = .ok false := by
        rw [show decide (j < j) = false from by simp]; rfl
      refine ⟨s, ?_, ?_⟩
      · rw [ziMulInnerLoop_ast]
        exact ExS.loop_brk (ExS.ite hlt_ev hfalse ExS.brk)
      · subst hnn
        exact ⟨hle, Nat.le_refl _, by omega, by omega, by omega, by omega, hna, hnb, ht0Len, ht0LenW64, hlla, hllb,
          hllmem, hro, hloc0, hloc1, hloc2, hloc3, hloc4, hloc5, hnaz, hastruct, hbstruct,
          haLimbs, hbLimbs, hmemTarr, _hTsblkBound, _hTarbound, _hAsblkBound, _haarrBound,
          _hbsblkBound, _hbarBound, _hneTsblk, _hneAsblk, _hneBsblk, _hneAarr, _hneBarr⟩
  | succ k ih =>
      intro s j heq hInv
      have hi' : j < bLen := by omega
      have hKInv := hInv
      obtain ⟨_, _, _, _, hLen64, hbf64, _, _, ht0Len, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hInv
      have hb64 : bLen < 18446744073709551616 := hbf64
      have hLen64' : aLen < 18446744073709551616 := hLen64
      obtain ⟨s1, s2, hbody, hstep, hinv2⟩ := ziMul_iCell tsblk tarr asblk aarr bsblk barr
        aLimbs bLimbs t0 aLen bLen i j hKInv hi' hb64 hLen64' (by
          rw [ziMulAcc_length]; omega)
      obtain ⟨sf, hl, hfin⟩ := ih s2 (j + 1) (by omega) hinv2
      refine ⟨sf, ?_, hfin⟩
      · rw [ziMulInnerLoop_ast]
        exact ExS.loop_next hbody (Or.inl rfl) hstep hl

/-- The inner zi_mul_accumulate_loop0 refinement, dispatched to the unroll. -/
theorem ziMul_inner_loop_impl (tsblk tarr asblk aarr bsblk barr : Nat)
    (aLimbs bLimbs t0 : List Nat) (aLen bLen i j : Nat)
    (hInv : ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i j s) :
    ∃ sf, ExS LimbGen.prog s Tess.C.LimbGen.zi_mul_accumulate_loop0 .normal sf ∧
      ziMulInnerInv tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i bLen sf :=
  ziMul_inner_loop_aux tsblk tarr asblk aarr bsblk barr aLimbs bLimbs t0 aLen bLen i
    (bLen - j) s j rfl hInv

end Tess.C
