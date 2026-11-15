import Obj.C.Proofs.ObjDabs
namespace Obj.C.Proofs
open Obj.C Obj

/-! ### `tobj_tess_scale2d` support lemmas

`tobj_tess_scale2d(p2d, n)` returns the largest `|p2d[k]|` over `k < 2n`,
starting from `0.0`.  This file proves the bit-level pieces the loop needs:

* negation never changes whether a pattern is NaN (`f64IsNaN_negBits`), hence
  `dabsBits` of a finite value is finite -- so the loop's `>` guards are
  plain key comparisons and never fail;
* `f64Max` is the pure `max` the guards implement, with its two case lemmas;
* `evalBin_f64_gt` evaluates the guard.

The remaining step -- the loop invariant `m = foldl f64Max 0 (|p2d|)` -- is
not asserted here; it is the next piece of work.
-/
/-! ### Negation and NaN -/

theorem xor63_mod52 (a : Nat) : (a ^^^ 2 ^ 63) % 2 ^ 52 = a % 2 ^ 52 := by
  rw [Nat.xor_mod_two_pow, show (2 : Nat) ^ 63 % 2 ^ 52 = 0 from by decide]
  simp

theorem xor63_div52_mod11 (a : Nat) :
    (a ^^^ 2 ^ 63) / 2 ^ 52 % 2 ^ 11 = a / 2 ^ 52 % 2 ^ 11 := by
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow,
    show (2 : Nat) ^ 63 / 2 ^ 52 = 2 ^ 11 from by decide,
    show (2 : Nat) ^ 11 % 2 ^ 11 = 0 from by decide]
  simp

/-- Flipping the sign bit leaves both the exponent field and the mantissa
    alone, so it cannot create or destroy a NaN. -/
theorem f64IsNaN_negBits (a : Nat) : f64IsNaN (F64.negBits a) = f64IsNaN a := by
  unfold F64.negBits F64.p2 f64IsNaN
  rw [xor63_div52_mod11, xor63_mod52]

/-- Bit-level `max` on doubles, as implemented by the loop's `>` guards.
    NaN inputs cannot occur here (`dabsBits_finite`). -/
def f64Max (a b : Nat) : Nat :=
  if (!f64IsNaN a && !f64IsNaN b && decide (f64Key a < f64Key b)) then b else a

/-- `f64Max` of two finite values is finite. -/
theorem f64Max_finite (a b : Nat) (ha : f64IsNaN a = false) (hb : f64IsNaN b = false) :
    f64IsNaN (f64Max a b) = false := by
  unfold f64Max
  split
  · exact hb
  · exact ha

/-- `max` returns its left argument when it is not smaller. -/
theorem f64Max_eq_left (a b : Nat) (h : ¬ f64Key a < f64Key b) : f64Max a b = a := by
  unfold f64Max
  rw [if_neg]
  intro hc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  exact h (decide_eq_true_eq.mp hc.2)

/-- `max` returns its right argument when the left is finite, the right is
    finite, and the right key is strictly larger. -/
theorem f64Max_eq_right (a b : Nat) (ha : f64IsNaN a = false) (hb : f64IsNaN b = false)
    (h : f64Key a < f64Key b) : f64Max a b = b := by
  unfold f64Max
  rw [if_pos]
  simp [ha, hb, h]

/-- `dabs` of a finite pattern is finite: it only flips the sign bit. -/
theorem dabsBits_finite (a : Nat) (h : f64IsNaN a = false) :
    f64IsNaN (dabsBits a) = false := by
  unfold dabsBits
  split
  · rw [f64IsNaN_negBits]; exact h
  · exact h

/-- The loop guard `x > m` is a plain key comparison on finite values. -/
theorem evalBin_f64_gt (a b : Nat) :
    evalBin .gt none (.f64 a) (.f64 b) =
      .ok (boolVal (!f64IsNaN a && !f64IsNaN b && decide (f64Key a > f64Key b))) := by
  simp [evalBin, isPtr, evalBinInt, binF64]


/-! ### Index and cast arithmetic for `p2d[2i]`, `p2d[2i+1]` -/

theorem cast_u32_two : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 2) = .ok (.int ⟨32, false⟩ 2) := by
  simp [evalCast, IntTy.toInt, IntTy.wrap, IntTy.modulus]

theorem cast_u32_one : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 1) = .ok (.int ⟨32, false⟩ 1) := by
  simp [evalCast, IntTy.toInt, IntTy.wrap, IntTy.modulus]

theorem cast_u32_zero : evalCast ⟨32, false⟩ (.int ⟨32, true⟩ 0) = .ok (.int ⟨32, false⟩ 0) := by
  simp [evalCast, IntTy.toInt, IntTy.wrap, IntTy.modulus]

theorem mul_u32_mod (a b : Nat) :
    evalBin .mul (some ⟨32, false⟩) (.int ⟨32, false⟩ a) (.int ⟨32, false⟩ b)
      = .ok (.int ⟨32, false⟩ ((a * b) % 4294967296)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus, Res.bind]

theorem add_u32_mod (a b : Nat) :
    evalBin .add (some ⟨32, false⟩) (.int ⟨32, false⟩ a) (.int ⟨32, false⟩ b)
      = .ok (.int ⟨32, false⟩ ((a + b) % 4294967296)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus, Res.bind]

theorem mul_u32 (a b : Nat) (h : a * b < 4294967296) :
    evalBin .mul (some ⟨32, false⟩) (.int ⟨32, false⟩ a) (.int ⟨32, false⟩ b)
      = .ok (.int ⟨32, false⟩ (a * b)) := by
  rw [mul_u32_mod, Nat.mod_eq_of_lt h]

theorem add_u32 (a b : Nat) (h : a + b < 4294967296) :
    evalBin .add (some ⟨32, false⟩) (.int ⟨32, false⟩ a) (.int ⟨32, false⟩ b)
      = .ok (.int ⟨32, false⟩ (a + b)) := by
  rw [add_u32_mod, Nat.mod_eq_of_lt h]

theorem lt_u32 (a b : Nat) :
    evalBin .lt (some ⟨32, false⟩) (.int ⟨32, false⟩ a) (.int ⟨32, false⟩ b)
      = .ok (boolVal (decide (a < b))) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.modulus, Res.bind]

/-- `ptrAddN` at an in-bounds offset returns the expected pointer. -/
theorem ptrAddN_ok (s : State) (b : Nat) (blk : Block) (k : Nat)
    (hm : s.mem b = some blk) (hk : k ≤ blk.length) :
    ptrAddN s.mem (.ptr b 0) k = .ok (.ptr b k) := by
  simp [ptrAddN, hm, hk]

/-- `p[2*i]` as a `double*` subscript: offset `16*i` bytes. -/
theorem index_mul2 (s : State) (b : Nat) (blk : Block) (i : Nat)
    (hv : EvE Gen.prog s (.var 0) (.ptr b 0)) (hm : s.mem b = some blk)
    (hi : EvE Gen.prog s (.var 3) (.int ⟨32, false⟩ i))
    (hmul : 2 * i < 4294967296) (h2i : 16 * i ≤ blk.length) :
    EvE Gen.prog s (.index (.var 0)
      (.bin .mul (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2)))
        (.var 3)) 8) (.ptr b (16 * i)) :=
  EvE.index hv
    (EvE.bin (EvE.cast (EvE.const _) cast_u32_two) hi (mul_u32 2 i hmul))
    (by
      show (if IntTy.signed IntTy.u32 = true then _ else ptrAddN s.mem (.ptr b 0) (2 * i * 8))
        = .ok (.ptr b (16 * i))
      rw [show IntTy.signed IntTy.u32 = false from rfl, if_neg (by decide),
        ptrAddN_ok s b blk (2 * i * 8) hm (by omega), show 2 * i * 8 = 16 * i from by omega])

/-- `p[2*i+1]` as a `double*` subscript: offset `16*i+8` bytes. -/
theorem index_mul2_add1 (s : State) (b : Nat) (blk : Block) (i : Nat)
    (hv : EvE Gen.prog s (.var 0) (.ptr b 0)) (hm : s.mem b = some blk)
    (hi : EvE Gen.prog s (.var 3) (.int ⟨32, false⟩ i))
    (hmul : 2 * i < 4294967296) (hadd : 2 * i + 1 < 4294967296)
    (h2i : 16 * i + 8 ≤ blk.length) :
    EvE Gen.prog s (.index (.var 0)
      (.bin .add (some ⟨32, false⟩)
        (.bin .mul (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2)))
          (.var 3))
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) 8) (.ptr b (16 * i + 8)) :=
  EvE.index hv
    (EvE.bin (EvE.bin (EvE.cast (EvE.const _) cast_u32_two) hi (mul_u32 2 i hmul))
      (EvE.cast (EvE.const _) cast_u32_one) (add_u32 _ _ hadd))
    (by
      show (if IntTy.signed IntTy.u32 = true then _ else ptrAddN s.mem (.ptr b 0) ((2 * i + 1) * 8))
        = .ok (.ptr b (16 * i + 8))
      rw [show IntTy.signed IntTy.u32 = false from rfl, if_neg (by decide),
        ptrAddN_ok s b blk ((2 * i + 1) * 8) hm (by omega),
        show (2 * i + 1) * 8 = 16 * i + 8 from by omega])

/-- Any in-bounds 8-byte window of a block reads back as *some* `double`.
    This is what lets the loop body be reasoned about without naming the
    array's contents up front. -/
theorem load_f64_exists (m : Mem) (b : Nat) (blk : Block) (o : Nat)
    (hm : m b = some blk) (ho : o + 8 ≤ blk.length) :
    ∃ bits, load m .f64 (.ptr b o) = .ok (.f64 bits) := by
  refine ⟨decodeLE ((blk.drop o).take 8), ?_⟩
  have hrb : readBytes m b o 8 = .ok ((blk.drop o).take 8) := by
    simp only [readBytes, hm]
    rw [if_pos ho]
  have hsz : Ty.size .f64 = 8 := rfl
  simp only [load, hsz, hrb, Res.bind_eq, Res.bind_ok]
  rfl

/-! ### The loop body -/

/-- The C guard `if (x > m) m = x;` implements `m := f64Max m x` on finite
    values: the code reads `x > m` where `f64Max` asks `m < x`. -/
theorem f64Max_guard (mx m : Nat) (hmx : f64IsNaN mx = false) (hm : f64IsNaN m = false) :
    f64Max m mx =
      (if (!f64IsNaN mx && !f64IsNaN m && decide (f64Key mx > f64Key m)) then mx else m) := by
  unfold f64Max
  congr 1
  simp [hm, hmx, decide_eq_decide]

/-- One `if (x > m) m = x;` statement, updating local 2. -/
theorem scaleMaxStep (s : State) (mx m : Nat) (hmx : f64IsNaN mx = false)
    (hm : f64IsNaN m = false)
    (l2 : s.locals 2 = some (.f64 m)) (l4 : s.locals 4 = some (.f64 mx)) :
    ∃ s1, ExS Gen.prog s
      (.ite (.bin .gt none (.var 4) (.var 2)) (.set 2 (.var 4)) .skip) .normal s1 ∧
      s1.locals 2 = some (.f64 (f64Max m mx)) := by
  by_cases h : (!f64IsNaN mx && !f64IsNaN m && decide (f64Key mx > f64Key m)) = true
  · have hg : EvE Gen.prog s (.bin .gt none (.var 4) (.var 2)) (boolVal true) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l4) (EvE.var l2) (evalBin_f64_gt mx m)
      rwa [h] at this
    refine ⟨{ s with locals := s.locals.upd 2 (.f64 mx) },
      ExS.ite (p := Gen.prog) hg (bc := true) (truthy_boolVal true) (ExS.set (p := Gen.prog) (EvE.var l4)), ?_⟩
    rw [show f64Max m mx = mx from by
      rw [f64Max_guard mx m hmx hm, h]; rfl]
    simp [Locals.upd]
  · have hf : (!f64IsNaN mx && !f64IsNaN m && decide (f64Key mx > f64Key m)) = false := by
      simpa using h
    have hg : EvE Gen.prog s (.bin .gt none (.var 4) (.var 2)) (boolVal false) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l4) (EvE.var l2) (evalBin_f64_gt mx m)
      rwa [hf] at this
    refine ⟨s, ExS.ite (p := Gen.prog) hg (bc := false) (truthy_boolVal false) (ExS.skip (p := Gen.prog)), ?_⟩
    rw [show f64Max m mx = m from by
      rw [f64Max_guard mx m hmx hm, hf]; rfl]
    exact l2

/-- A `tobj_dabs` call on a loaded `double`.  The callee frame is read-only,
    so the caller must be writable (`s.ro = false`), as in every other call. -/
theorem dabs_call (s : State) (b : Nat) (off : Nat) (x : Nat) (ex : Expr)
    (he : EvE Gen.prog s ex (.ptr b off)) (hx : load s.mem .f64 (.ptr b off) = .ok (.f64 x))
    (hro : s.ro = false) :
    EvE Gen.prog s (.call 41 [.load .f64 ex]) (.f64 (dabsBits x)) := by
  have hbody := tobj_dabs_refines s.mem x true
  exact EvE.call (p := Gen.prog) (EvArgs.cons (EvE.load he hx) EvArgs.nil)
    (f := 41) (fn := Gen.tobj_dabs) rfl (by simp [Gen.tobj_dabs]) hbody

/-! ### The loop body -/

/-- `p2d` subscript `[2*i]`. -/
def scaleIdx0 : Expr := .index (.var 0)
  (.bin .mul (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2))) (.var 3)) 8

/-- `p2d` subscript `[2*i + 1]`. -/
def scaleIdx1 : Expr := .index (.var 0)
  (.bin .add (some ⟨32, false⟩)
    (.bin .mul (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2))) (.var 3))
    (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) 8

/-- The body of the `tobj_tess_scale2d` loop. -/
def scaleBody : Stmt :=
  (.seq (.set 4 (.call 41 [.load .f64 scaleIdx0]))
    (.seq (.set 5 (.call 41 [.load .f64 scaleIdx1]))
      (.seq (.ite (.bin .gt none (.var 4) (.var 2)) (.set 2 (.var 4)) .skip)
        (.ite (.bin .gt none (.var 5) (.var 2)) (.set 2 (.var 5)) .skip))))

/-- The factored body is definitionally the generated loop body. -/
theorem scale_loop_ast : Gen.tobj_tess_scale2d_loop0 =
    .loop (.ite (.bin .lt (some ⟨32, false⟩) (.var 3) (.var 1)) scaleBody .brk)
      (.set 3 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩)
        (.cast ⟨32, false⟩ (.var 3)) (.const (.int ⟨32, false⟩ 1))))) := rfl

/-- Set a local to a `dabs` call on `p2d[k]`, given the load. -/
theorem dabs_set_exs (s : State) (b : Nat) (off : Nat) (x : Nat) (v : Nat) (e : Expr)
    (he : EvE Gen.prog s e (.ptr b off)) (hx : load s.mem .f64 (.ptr b off) = .ok (.f64 x))
    (hro : s.ro = false) :
    ExS Gen.prog s (.set v (.call 41 [.load .f64 e])) .normal
      { s with locals := s.locals.upd v (.f64 (dabsBits x)) } :=
  ExS.set (p := Gen.prog) (s := s) (i := v) (e := .call 41 [.load .f64 e])
    (dabs_call s b off x e he hx hro)

/-- The array local survives updating a different local. -/
theorem locals0_upd (s : State) (b : Nat) (v : Nat) (val : Val) (hv : v ≠ 0)
    (h : s.locals 0 = some (.ptr b 0)) :
    { s with locals := s.locals.upd v val }.locals 0 = some (.ptr b 0) := by
  show (if (0 : Nat) = v then some val else s.locals 0) = _
  rw [if_neg (Ne.symm hv), h]

/-- `scaleMaxStep` changes only local 2, so local 5 is preserved. -/
theorem scaleMaxStep_locals5 (s : State) (mx m my : Nat)
    (hmx : f64IsNaN mx = false) (hm : f64IsNaN m = false)
    (l2 : s.locals 2 = some (.f64 m)) (l4 : s.locals 4 = some (.f64 mx))
    (l5 : s.locals 5 = some (.f64 my)) :
    ∃ s1, ExS Gen.prog s
      (.ite (.bin .gt none (.var 4) (.var 2)) (.set 2 (.var 4)) .skip) .normal s1 ∧
      s1.locals 2 = some (.f64 (f64Max m mx)) ∧ s1.locals 5 = some (.f64 my) := by
  by_cases h : (!f64IsNaN mx && !f64IsNaN m && decide (f64Key mx > f64Key m)) = true
  · have hg : EvE Gen.prog s (.bin .gt none (.var 4) (.var 2)) (boolVal true) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l4) (EvE.var l2) (evalBin_f64_gt mx m)
      rwa [h] at this
    refine ⟨{ s with locals := s.locals.upd 2 (.f64 mx) },
      ExS.ite (p := Gen.prog) hg (bc := true) (truthy_boolVal true)
        (ExS.set (p := Gen.prog) (EvE.var l4)), ?_, ?_⟩
    · rw [show f64Max m mx = mx from by rw [f64Max_guard mx m hmx hm, h]; rfl]
      simp [Locals.upd]
    · show (if (5 : Nat) = 2 then some (Val.f64 mx) else s.locals 5) = _
      rw [if_neg (by omega)]; exact l5
  · have hf : (!f64IsNaN mx && !f64IsNaN m && decide (f64Key mx > f64Key m)) = false := by
      simpa using h
    have hg : EvE Gen.prog s (.bin .gt none (.var 4) (.var 2)) (boolVal false) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l4) (EvE.var l2) (evalBin_f64_gt mx m)
      rwa [hf] at this
    refine ⟨s, ExS.ite (p := Gen.prog) hg (bc := false) (truthy_boolVal false)
      (ExS.skip (p := Gen.prog)), ?_, l5⟩
    rw [show f64Max m mx = m from by rw [f64Max_guard mx m hmx hm, hf]; rfl]
    exact l2

/-- The second `if` of the loop body (guarding on local 5).  Split out from
    `scaleMaxStep` only because the generated code guards `x > m` with `x` in
    local 5 here. -/
theorem scaleMaxStep_5 (s : State) (my m : Nat)
    (hmy : f64IsNaN my = false) (hm : f64IsNaN m = false)
    (l2 : s.locals 2 = some (.f64 m)) (l5 : s.locals 5 = some (.f64 my)) :
    ∃ s1, ExS Gen.prog s
      (.ite (.bin .gt none (.var 5) (.var 2)) (.set 2 (.var 5)) .skip) .normal s1 ∧
      s1.locals 2 = some (.f64 (f64Max m my)) := by
  by_cases h : (!f64IsNaN my && !f64IsNaN m && decide (f64Key my > f64Key m)) = true
  · have hg : EvE Gen.prog s (.bin .gt none (.var 5) (.var 2)) (boolVal true) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l5) (EvE.var l2) (evalBin_f64_gt my m)
      rwa [h] at this
    refine ⟨{ s with locals := s.locals.upd 2 (.f64 my) },
      ExS.ite (p := Gen.prog) hg (bc := true) (truthy_boolVal true)
        (ExS.set (p := Gen.prog) (EvE.var l5)), ?_⟩
    rw [show f64Max m my = my from by rw [f64Max_guard my m hmy hm, h]; rfl]
    simp [Locals.upd]
  · have hf : (!f64IsNaN my && !f64IsNaN m && decide (f64Key my > f64Key m)) = false := by
      simpa using h
    have hg : EvE Gen.prog s (.bin .gt none (.var 5) (.var 2)) (boolVal false) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l5) (EvE.var l2) (evalBin_f64_gt my m)
      rwa [hf] at this
    refine ⟨s, ExS.ite (p := Gen.prog) hg (bc := false) (truthy_boolVal false)
      (ExS.skip (p := Gen.prog)), ?_⟩
    rw [show f64Max m my = m from by rw [f64Max_guard my m hmy hm, hf]; rfl]
    exact l2

theorem scaleMaxStep_untouched (s : State) (mx m : Nat) (hmx : f64IsNaN mx = false)
    (hm : f64IsNaN m = false)
    (l2 : s.locals 2 = some (.f64 m)) (l4 : s.locals 4 = some (.f64 mx)) :
    ∃ s1, ExS Gen.prog s
      (.ite (.bin .gt none (.var 4) (.var 2)) (.set 2 (.var 4)) .skip) .normal s1 ∧
      s1.locals 2 = some (.f64 (f64Max m mx)) ∧
      (∀ j, j ≠ 2 → s1.locals j = s.locals j) ∧ s1.mem = s.mem ∧ s1.ro = s.ro := by
  by_cases h : (!f64IsNaN mx && !f64IsNaN m && decide (f64Key mx > f64Key m)) = true
  · have hg : EvE Gen.prog s (.bin .gt none (.var 4) (.var 2)) (boolVal true) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l4) (EvE.var l2) (evalBin_f64_gt mx m)
      rwa [h] at this
    refine ⟨{ s with locals := s.locals.upd 2 (.f64 mx) },
      ExS.ite (p := Gen.prog) hg (bc := true) (truthy_boolVal true)
        (ExS.set (p := Gen.prog) (EvE.var l4)), ?_, ?_, rfl, rfl⟩
    · rw [show f64Max m mx = mx from by rw [f64Max_guard mx m hmx hm, h]; rfl]
      simp [Locals.upd]
    · intro j hj
      show (if j = 2 then some (Val.f64 mx) else s.locals j) = s.locals j
      rw [if_neg hj]
  · have hf : (!f64IsNaN mx && !f64IsNaN m && decide (f64Key mx > f64Key m)) = false := by
      simpa using h
    have hg : EvE Gen.prog s (.bin .gt none (.var 4) (.var 2)) (boolVal false) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l4) (EvE.var l2) (evalBin_f64_gt mx m)
      rwa [hf] at this
    refine ⟨s, ExS.ite (p := Gen.prog) hg (bc := false) (truthy_boolVal false)
      (ExS.skip (p := Gen.prog)), ?_, fun _ _ => rfl, rfl, rfl⟩
    rw [show f64Max m mx = m from by rw [f64Max_guard mx m hmx hm, hf]; rfl]
    exact l2

theorem scaleMaxStep5_untouched (s : State) (my m : Nat) (hmy : f64IsNaN my = false)
    (hm : f64IsNaN m = false)
    (l2 : s.locals 2 = some (.f64 m)) (l5 : s.locals 5 = some (.f64 my)) :
    ∃ s1, ExS Gen.prog s
      (.ite (.bin .gt none (.var 5) (.var 2)) (.set 2 (.var 5)) .skip) .normal s1 ∧
      s1.locals 2 = some (.f64 (f64Max m my)) ∧
      (∀ j, j ≠ 2 → s1.locals j = s.locals j) ∧ s1.mem = s.mem ∧ s1.ro = s.ro := by
  by_cases h : (!f64IsNaN my && !f64IsNaN m && decide (f64Key my > f64Key m)) = true
  · have hg : EvE Gen.prog s (.bin .gt none (.var 5) (.var 2)) (boolVal true) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l5) (EvE.var l2) (evalBin_f64_gt my m)
      rwa [h] at this
    refine ⟨{ s with locals := s.locals.upd 2 (.f64 my) },
      ExS.ite (p := Gen.prog) hg (bc := true) (truthy_boolVal true)
        (ExS.set (p := Gen.prog) (EvE.var l5)), ?_, ?_, rfl, rfl⟩
    · rw [show f64Max m my = my from by rw [f64Max_guard my m hmy hm, h]; rfl]
      simp [Locals.upd]
    · intro j hj
      show (if j = 2 then some (Val.f64 my) else s.locals j) = s.locals j
      rw [if_neg hj]
  · have hf : (!f64IsNaN my && !f64IsNaN m && decide (f64Key my > f64Key m)) = false := by
      simpa using h
    have hg : EvE Gen.prog s (.bin .gt none (.var 5) (.var 2)) (boolVal false) := by
      have := EvE.bin (p := Gen.prog) (EvE.var l5) (EvE.var l2) (evalBin_f64_gt my m)
      rwa [hf] at this
    refine ⟨s, ExS.ite (p := Gen.prog) hg (bc := false) (truthy_boolVal false)
      (ExS.skip (p := Gen.prog)), ?_, fun _ _ => rfl, rfl, rfl⟩
    rw [show f64Max m my = m from by rw [f64Max_guard my m hmy hm, hf]; rfl]
    exact l2

/-- **`scaleBody_exs`** — one iteration of the `tobj_tess_scale2d` loop.
    The two array slots are given as loads; the body takes their `dabs` into
    locals 4/5 and folds both into the running maximum in local 2. -/
theorem scaleBody_exs (s : State) (b : Nat) (blk : Block) (i m x0 y0 : Nat)
    (l0 : s.locals 0 = some (.ptr b 0)) (hmb : s.mem b = some blk)
    (l3 : s.locals 3 = some (.int ⟨32, false⟩ i))
    (hmul : 2 * i < 4294967296) (hadd : 2 * i + 1 < 4294967296)
    (h2i : 16 * i ≤ blk.length) (h2i1 : 16 * i + 8 ≤ blk.length)
    (hx0 : load s.mem .f64 (.ptr b (16 * i)) = .ok (.f64 x0))
    (hy0 : load s.mem .f64 (.ptr b (16 * i + 8)) = .ok (.f64 y0))
    (hro : s.ro = false) (l2 : s.locals 2 = some (.f64 m))
    (hmfin : f64IsNaN m = false)
    (hxfin : f64IsNaN (dabsBits x0) = false) (hyfin : f64IsNaN (dabsBits y0) = false) :
    ∃ s', ExS Gen.prog s scaleBody .normal s' ∧
      s'.locals 2 = some (.f64 (f64Max (f64Max m (dabsBits x0)) (dabsBits y0))) ∧
      (∀ j, j ≠ 2 → j ≠ 4 → j ≠ 5 → s'.locals j = s.locals j) ∧
      s'.mem = s.mem ∧ s'.ro = s.ro := by
  let sA : State := { s with locals := s.locals.upd 4 (.f64 (dabsBits x0)) }
  have hidx0 : EvE Gen.prog s scaleIdx0 (.ptr b (16 * i)) :=
    index_mul2 s b blk i (EvE.var l0) hmb (EvE.var l3) hmul h2i
  have hset4 : ExS Gen.prog s (.set 4 (.call 41 [.load .f64 scaleIdx0])) .normal sA :=
    dabs_set_exs s b (16 * i) x0 4 scaleIdx0 hidx0 hx0 hro
  let sB : State := { sA with locals := sA.locals.upd 5 (.f64 (dabsBits y0)) }
  have l0A : sA.locals 0 = some (.ptr b 0) := locals0_upd s b 4 _ (by omega) l0
  have l3A : sA.locals 3 = some (.int ⟨32, false⟩ i) := by
    show (if (3 : Nat) = 4 then some (Val.f64 (dabsBits x0)) else s.locals 3) = _
    rw [if_neg (by omega)]; exact l3
  have hidx1 : EvE Gen.prog sA scaleIdx1 (.ptr b (16 * i + 8)) :=
    index_mul2_add1 sA b blk i (EvE.var l0A) hmb (EvE.var l3A) hmul hadd h2i1
  have hset5 : ExS Gen.prog sA (.set 5 (.call 41 [.load .f64 scaleIdx1])) .normal sB :=
    dabs_set_exs sA b (16 * i + 8) y0 5 scaleIdx1 hidx1 hy0 hro
  have l2A : sA.locals 2 = some (.f64 m) := by
    show (if (2 : Nat) = 4 then some (Val.f64 (dabsBits x0)) else s.locals 2) = _
    rw [if_neg (by omega)]; exact l2
  have l4B : sB.locals 4 = some (.f64 (dabsBits x0)) := by
    show (if (4 : Nat) = 5 then some (Val.f64 (dabsBits y0)) else sA.locals 4) = _
    rw [if_neg (by omega)]
    show (if (4 : Nat) = 4 then some (Val.f64 (dabsBits x0)) else s.locals 4) = _
    rw [if_pos rfl]
  have l5B : sB.locals 5 = some (.f64 (dabsBits y0)) := by
    show (if (5 : Nat) = 5 then some (Val.f64 (dabsBits y0)) else sA.locals 5) = _
    rw [if_pos rfl]
  obtain ⟨sC, hmax1, l2C, hC, hmC, hroC⟩ :=
    scaleMaxStep_untouched sB (dabsBits x0) m hxfin hmfin l2A l4B
  have l5C : sC.locals 5 = some (.f64 (dabsBits y0)) := by
    rw [hC 5 (by omega)]; exact l5B
  obtain ⟨sD, hmax2, l2D, hD, hmD, hroD⟩ :=
    scaleMaxStep5_untouched sC (dabsBits y0) (f64Max m (dabsBits x0)) hyfin
      (f64Max_finite m (dabsBits x0) hmfin hxfin) l2C l5C
  refine ⟨sD, ?_, ?_, ?_, ?_⟩
  · unfold scaleBody
    exact ExS.seq (p := Gen.prog) hset4
      (ExS.seq (p := Gen.prog) hset5 (ExS.seq (p := Gen.prog) hmax1 hmax2))
  · exact l2D
  · intro j hj2 hj4 hj5
    -- sD agrees with sC on j, sC with sB, sB with sA, sA with s
    rw [hD j hj2]
    rw [hC j hj2]
    show (if j = 5 then some (Val.f64 (dabsBits y0)) else sA.locals j) = s.locals j
    rw [if_neg hj5]
    show (if j = 4 then some (Val.f64 (dabsBits x0)) else s.locals j) = s.locals j
    rw [if_neg hj4]
  · exact ⟨by rw [hmD, hmC], by rw [hroD, hroC]⟩


/-! ### The pure scan -/

/-- One iteration of the pure scan: fold `|x|`, `|y|` of index `i` into `m`. -/
def foldStep (g : Nat → Nat × Nat) (m i : Nat) : Nat :=
  f64Max (f64Max m (dabsBits (g i).1)) (dabsBits (g i).2)

/-- The pure result of scanning indices `0 .. n-1`. -/
def scaleFold (g : Nat → Nat × Nat) (m0 : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (foldStep g) m0

theorem foldStep_finite (g : Nat → Nat × Nat) (m i : Nat)
    (hm : f64IsNaN m = false) (hx : f64IsNaN (dabsBits (g i).1) = false)
    (hy : f64IsNaN (dabsBits (g i).2) = false) :
    f64IsNaN (foldStep g m i) = false := by
  unfold foldStep
  exact f64Max_finite _ _ (f64Max_finite _ _ hm hx) hy

theorem foldl_finite (g : Nat → Nat × Nat) (xs : List Nat) (m0 : Nat)
    (hm : f64IsNaN m0 = false)
    (hx : ∀ i, f64IsNaN (dabsBits (g i).1) = false)
    (hy : ∀ i, f64IsNaN (dabsBits (g i).2) = false) :
    f64IsNaN (xs.foldl (foldStep g) m0) = false := by
  induction xs generalizing m0 with
  | nil => simpa using hm
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih _ (foldStep_finite g m0 i hm (hx i) (hy i))

theorem scaleFold_succ (g : Nat → Nat × Nat) (m0 k : Nat) :
    scaleFold g m0 (k+1) = foldStep g (scaleFold g m0 k) k := by
  unfold scaleFold
  rw [List.range_succ, List.foldl_append]; rfl

theorem scaleFold_finite (g : Nat → Nat × Nat) (m0 n : Nat)
    (hm : f64IsNaN m0 = false)
    (hx : ∀ i, f64IsNaN (dabsBits (g i).1) = false)
    (hy : ∀ i, f64IsNaN (dabsBits (g i).2) = false) :
    f64IsNaN (scaleFold g m0 n) = false :=
  foldl_finite g (List.range n) m0 hm hx hy


/-! ### The `tobj_tess_scale2d` loop -/

def ScaleInv (s : State) (m : Mem) (g : Nat → Nat × Nat) (n : Nat) (j : Nat) : Prop :=
  j ≤ n ∧ s.locals 0 = some (.ptr 0 0) ∧ s.mem = m ∧
  s.locals 1 = some (.int ⟨32, false⟩ n) ∧
  s.locals 3 = some (.int ⟨32, false⟩ (n - j)) ∧
  s.locals 2 = some (.f64 (scaleFold g 0 (n - j))) ∧ s.ro = false

def ScaleGuard : Expr := .bin .lt (some ⟨32, false⟩) (.var 3) (.var 1)

theorem guard_true (s : State) (n j : Nat)
    (l1 : s.locals 1 = some (.int ⟨32, false⟩ n))
    (l3 : s.locals 3 = some (.int ⟨32, false⟩ (n - j)))
    (hj : 0 < j) (hjle : j ≤ n) :
    EvE Gen.prog s ScaleGuard (boolVal true) := by
  unfold ScaleGuard
  have hlt : n - j < n := by omega
  exact EvE.bin (EvE.var l3) (EvE.var l1) (by rw [lt_u32]; simp [hlt])

theorem guard_false (s : State) (n : Nat)
    (l1 : s.locals 1 = some (.int ⟨32, false⟩ n))
    (l3 : s.locals 3 = some (.int ⟨32, false⟩ (n - 0))) :
    EvE Gen.prog s ScaleGuard (boolVal false) := by
  unfold ScaleGuard
  have h : ¬ n - 0 < n := by omega
  exact EvE.bin (EvE.var l3) (EvE.var l1) (by rw [lt_u32]; simp [h])

theorem cast_u32 (a : Nat) (h : a < 4294967296) :
    evalCast ⟨32, false⟩ (.int ⟨32, false⟩ a) = .ok (.int ⟨32, false⟩ a) := by
  simp [evalCast, IntTy.modulus]; omega

def ScaleStep : Stmt :=
  .set 3 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩)
    (.cast ⟨32, false⟩ (.var 3)) (.const (.int ⟨32, false⟩ 1))))

theorem scaleStep_exs (s : State) (n j : Nat) (hn : n < 2147483648)
    (hjle : j + 1 ≤ n)
    (l3 : s.locals 3 = some (.int ⟨32, false⟩ (n - (j+1)))) :
    ∃ s2, ExS Gen.prog s ScaleStep .normal s2 ∧
      s2.locals 3 = some (.int ⟨32, false⟩ (n - j)) ∧
      (∀ k, k ≠ 3 → s2.locals k = s.locals k) ∧ s2.mem = s.mem ∧ s2.ro = s.ro := by
  have hc : EvE Gen.prog s (.cast ⟨32, false⟩ (.var 3)) (.int ⟨32, false⟩ (n - (j+1))) :=
    EvE.cast (EvE.var l3) (cast_u32 _ (by omega))
  have h1 : EvE Gen.prog s (.const (.int ⟨32, false⟩ 1)) (.int ⟨32, false⟩ 1) := EvE.const _
  have hadd : EvE Gen.prog s (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 3))
      (.const (.int ⟨32, false⟩ 1))) (.int ⟨32, false⟩ (n - (j+1) + 1)) :=
    EvE.bin hc h1 (add_u32 _ _ (by omega))
  have hcast : EvE Gen.prog s (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.var 3)) (.const (.int ⟨32, false⟩ 1))))
      (.int ⟨32, false⟩ (n - (j+1) + 1)) :=
    EvE.cast hadd (cast_u32 _ (by omega))
  refine ⟨{ s with locals := s.locals.upd 3 (.int ⟨32, false⟩ (n - (j+1) + 1)) },
    ExS.set (p := Gen.prog) hcast, ?_, ?_, rfl, rfl⟩
  · show (if (3 : Nat) = 3 then some (Val.int (IntTy.mk 32 false) (n - (j+1) + 1))
      else s.locals 3) = some (Val.int (IntTy.mk 32 false) (n - j))
    rw [if_pos rfl, show n - (j+1) + 1 = n - j from by omega]
  · intro k hk
    show (if k = 3 then some (Val.int (IntTy.mk 32 false) (n - (j+1) + 1)) else s.locals k)
      = s.locals k
    rw [if_neg hk]

/-- **The `tobj_tess_scale2d` loop.**  Running the loop from the state after
    `m = 0.0`, `i = 0` yields `m` equal to the pure fold over indices
    `0 .. n-1`, with memory untouched. -/
theorem scale_loop (g : Nat → Nat × Nat) (m : Mem) (blk : Block) (n : Nat)
    (hn : n < 2147483648)
    (hblk0 : m 0 = some blk) (hlen16 : 16 * n ≤ blk.length)
    (hload : ∀ pos, pos < 16 * n →
      load m .f64 (.ptr 0 pos)
        = .ok (.f64 (if pos % 16 = 0 then (g (pos / 16)).1 else (g (pos / 16)).2)))
    (hx : ∀ i, f64IsNaN (dabsBits (g i).1) = false)
    (hy : ∀ i, f64IsNaN (dabsBits (g i).2) = false)
    (s : State) (h0 : s.locals 0 = some (.ptr 0 0))
    (h1 : s.locals 1 = some (.int ⟨32, false⟩ n))
    (h3 : s.locals 3 = some (.int ⟨32, false⟩ 0))
    (h2 : s.locals 2 = some (.f64 0))
    (hmem : s.mem = m) (hro : s.ro = false) :
    ∃ sf, ExS Gen.prog s Gen.tobj_tess_scale2d_loop0 .normal sf ∧
      sf.locals 2 = some (.f64 (scaleFold g 0 n)) ∧ sf.mem = m := by
  have hfold0 : scaleFold g 0 (n - n) = 0 := by
    unfold scaleFold; rw [show n - n = 0 from by omega]; rfl
  let P : Nat → State → Prop := fun j st => ScaleInv st m g n j
  have hinv0 : P n s := ⟨by omega, h0, hmem, h1, by rw [show n - n = 0 from by omega]; exact h3,
    by rw [hfold0]; exact h2, hro⟩
  have hstep' : ∀ j st, P (j+1) st → ∃ sA sB,
      ExS Gen.prog st (.ite ScaleGuard scaleBody .brk) .normal sA ∧
      ExS Gen.prog sA ScaleStep .normal sB ∧ P j sB := by
    intro j st hs
    obtain ⟨hjle, l0s, hms, l1s, l3s, l2s, hros⟩ := hs
    have hlt : n - (j+1) < n := by omega
    have hguard : EvE Gen.prog st ScaleGuard (boolVal true) :=
      guard_true st n (j+1) l1s l3s (by omega) hjle
    have hpos0 : 16 * (n - (j+1)) < 16 * n := by omega
    have hpos1 : 16 * (n - (j+1)) + 8 < 16 * n := by omega
    have hlx : load m .f64 (.ptr 0 (16 * (n - (j+1)))) = .ok (.f64 (g (n - (j+1))).1) := by
      have h1' : (16 * (n - (j+1))) % 16 = 0 := by omega
      have h2' : (16 * (n - (j+1))) / 16 = n - (j+1) := by omega
      have := hload _ hpos0; rw [h1', h2'] at this; simpa using this
    have hly : load m .f64 (.ptr 0 (16 * (n - (j+1)) + 8)) = .ok (.f64 (g (n - (j+1))).2) := by
      have h1' : (16 * (n - (j+1)) + 8) % 16 = 8 := by omega
      have h2' : (16 * (n - (j+1)) + 8) / 16 = n - (j+1) := by omega
      have := hload _ hpos1; rw [h1', h2'] at this; simpa using this
    have hlxm : load st.mem .f64 (.ptr 0 (16 * (n - (j+1)))) = .ok (.f64 (g (n - (j+1))).1) := by
      rw [hms]; exact hlx
    have hlym : load st.mem .f64 (.ptr 0 (16 * (n - (j+1)) + 8)) = .ok (.f64 (g (n - (j+1))).2) := by
      rw [hms]; exact hly
    have hs0 : st.mem 0 = some blk := by rw [hms]; exact hblk0
    have hb1 : 2 * (n - (j+1)) < 4294967296 := by omega
    have hb2 : 2 * (n - (j+1)) + 1 < 4294967296 := by omega
    have hb3 : 16 * (n - (j+1)) ≤ blk.length := by omega
    have hb4 : 16 * (n - (j+1)) + 8 ≤ blk.length := by omega
    obtain ⟨sA, hbody, l2A, huntA, hmA, hroA⟩ :=
      scaleBody_exs st 0 blk (n - (j+1)) (scaleFold g 0 (n - (j+1)))
        (g (n - (j+1))).1 (g (n - (j+1))).2 l0s hs0 l3s hb1 hb2 hb3 hb4 hlxm hlym hros l2s
        (scaleFold_finite g 0 (n - (j+1)) rfl hx hy) (hx _) (hy _)
    have hif : ExS Gen.prog st (.ite ScaleGuard scaleBody .brk) .normal sA :=
      ExS.ite (p := Gen.prog) hguard (bc := true) (truthy_boolVal true) hbody
    -- increment, from sA: locals 0/1/2 are as in st, local 3 unchanged
    have l0A : sA.locals 0 = some (.ptr 0 0) := by rw [huntA 0 (by omega) (by omega) (by omega)]; exact l0s
    have l1A : sA.locals 1 = some (.int ⟨32, false⟩ n) := by rw [huntA 1 (by omega) (by omega) (by omega)]; exact l1s
    have l3A : sA.locals 3 = some (.int ⟨32, false⟩ (n - (j+1))) := by
      rw [huntA 3 (by omega) (by omega) (by omega)]; exact l3s
    -- `l2A` is the folded value the invariant at `j` wants.
    have l2Post : sA.locals 2 = some (.f64 (scaleFold g 0 (n - j))) := by
      rw [l2A]
      exact congrArg _ (by
        rw [show n - j = n - (j+1) + 1 from by omega, scaleFold_succ]; rfl)
    obtain ⟨sB, hinc, l3B, huntB, hmB, hroB⟩ := scaleStep_exs sA n j hn hjle l3A
    refine ⟨sA, sB, hif, hinc, by
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [huntB 0 (by omega)]; exact l0A
      · rw [hmB]; exact hmA.trans hms
      · rw [huntB 1 (by omega)]; exact l1A
      · exact l3B
      · rw [huntB 2 (by omega)]; exact l2Post
      · rw [hroB, hroA]; exact hros⟩
  have hexit : ∀ st, P 0 st → ∃ s1, ExS Gen.prog st (.ite ScaleGuard scaleBody .brk) .brk s1 ∧
      s1.locals 2 = some (.f64 (scaleFold g 0 n)) ∧ s1.mem = m := by
    intro st hs
    obtain ⟨hjle, l0s, hms, l1s, l3s, l2s, hros⟩ := hs
    have hguard : EvE Gen.prog st ScaleGuard (boolVal false) :=
      guard_false st n l1s (by rw [show n - 0 = n from by omega]; exact l3s)
    refine ⟨st, ExS.ite (p := Gen.prog) hguard (bc := false) (truthy_boolVal false)
      (ExS.brk (p := Gen.prog)), ?_, ?_⟩
    · rw [show n - 0 = n from by omega] at l2s; exact l2s
    · rw [hms]
  exact ExS.loop_decreasing_post (p := Gen.prog)
    (P := P) (Q := fun st => st.locals 2 = some (.f64 (scaleFold g 0 n)) ∧
      st.mem = m)
    (n := n) (s := s) hinv0 hstep' hexit

/-- **`tobj_tess_scale2d` refines the pure scan.**  For a `double[2n]` array in
    block 0 and a description `g` of its entries, the translated function
    returns the fold of `max |x| |y|` over all `n` index pairs, starting from
    `0.0`; the loop never writes memory. -/
theorem tobj_tess_scale2d_refines (m : Mem) (blk : Block) (g : Nat → Nat × Nat)
    (n : Nat) (hn : n < 2147483648)
    (hblk0 : m 0 = some blk) (hlen16 : 16 * n ≤ blk.length)
    (hload : ∀ pos, pos < 16 * n →
      load m .f64 (.ptr 0 pos)
        = .ok (.f64 (if pos % 16 = 0 then (g (pos / 16)).1 else (g (pos / 16)).2)))
    (hx : ∀ i, f64IsNaN (dabsBits (g i).1) = false)
    (hy : ∀ i, f64IsNaN (dabsBits (g i).2) = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.tobj_tess_scale2d.params [.ptr 0 0, .int ⟨32, false⟩ n], m, false⟩
      Gen.tobj_tess_scale2d.body (.ret (some (.f64 (scaleFold g 0 n)))) s' ∧
      s'.mem = m := by
  let s0 : State := ⟨frameLocals Gen.tobj_tess_scale2d.params
    [.ptr 0 0, .int ⟨32, false⟩ n], m, false⟩
  have l0 : s0.locals 0 = some (.ptr 0 0) := by
    simp [s0, frameLocals, Gen.tobj_tess_scale2d, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have l1 : s0.locals 1 = some (.int ⟨32, false⟩ n) := by
    simp [s0, frameLocals, Gen.tobj_tess_scale2d, List.idxOf?, List.findIdx?, List.findIdx?.go]
  -- m = 0.0
  have hset2 : ExS Gen.prog s0 (.set 2 (.const (.f64 0))) .normal
      { s0 with locals := s0.locals.upd 2 (.f64 0) } :=
    ExS.set (p := Gen.prog) (s := s0) (i := 2) (e := .const (.f64 0)) (EvE.const _)
  let s1 : State := { s0 with locals := s0.locals.upd 2 (.f64 0) }
  -- i = 0
  have hset3 : ExS Gen.prog s1
      (.set 3 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s1 with locals := s1.locals.upd 3 (.int ⟨32, false⟩ 0) } := by
    refine ExS.set (p := Gen.prog) (s := s1) (i := 3)
      (e := .cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))) ?_
    exact EvE.cast (EvE.const _) (by simp [evalCast, IntTy.toInt, IntTy.wrap, IntTy.modulus])
  let s2 : State := { s1 with locals := s1.locals.upd 3 (.int ⟨32, false⟩ 0) }
  have l0_2 : s2.locals 0 = some (.ptr 0 0) := by
    show (if (0 : Nat) = 3 then some (Val.int (IntTy.mk 32 false) 0) else s1.locals 0) = _
    rw [if_neg (by omega)]
    show (if (0 : Nat) = 2 then some (Val.f64 0) else s0.locals 0) = _
    rw [if_neg (by omega)]; exact l0
  have l1_2 : s2.locals 1 = some (.int ⟨32, false⟩ n) := by
    show (if (1 : Nat) = 3 then some (Val.int (IntTy.mk 32 false) 0) else s1.locals 1) = _
    rw [if_neg (by omega)]
    show (if (1 : Nat) = 2 then some (Val.f64 0) else s0.locals 1) = _
    rw [if_neg (by omega)]; exact l1
  have l2_2 : s2.locals 2 = some (.f64 0) := by
    show (if (2 : Nat) = 3 then some (Val.int (IntTy.mk 32 false) 0) else s1.locals 2) = _
    rw [if_neg (by omega)]
    show (if (2 : Nat) = 2 then some (Val.f64 0) else s0.locals 2) = _
    rw [if_pos rfl]
  have l3_2 : s2.locals 3 = some (.int ⟨32, false⟩ 0) := by
    show (if (3 : Nat) = 3 then some (Val.int (IntTy.mk 32 false) 0) else s1.locals 3) = _
    rw [if_pos rfl]
  have hloopAst : Gen.tobj_tess_scale2d.body =
      .seq (.set 2 (.const (.f64 0)))
        (.seq (.seq (.set 3 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
          Gen.tobj_tess_scale2d_loop0) (.ret (some (.var 2)))) := rfl
  obtain ⟨sf, hloop, l2f, hmf⟩ := scale_loop g m blk n hn hblk0 hlen16 hload hx hy
    s2 l0_2 l1_2 l3_2 l2_2 rfl rfl
  have hv : EvE Gen.prog sf (.var 2) (.f64 (scaleFold g 0 n)) := EvE.var l2f
  refine ⟨sf, ?_, hmf⟩
  rw [hloopAst]
  -- the translator grouped `set 3` with the loop into one nested `seq`
  have hset3loop : ExS Gen.prog s1
      (.seq (.set 3 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
        Gen.tobj_tess_scale2d_loop0) .normal sf :=
    ExS.seq (p := Gen.prog) hset3 hloop
  exact ExS.seq (p := Gen.prog) hset2
    (ExS.seq (p := Gen.prog) hset3loop (ExS.ret hv))

end Obj.C.Proofs
