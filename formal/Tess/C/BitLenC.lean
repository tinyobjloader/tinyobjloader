/-
  MiniC refinement of the translated `bit_len32` (`lib/tess/src/exact.c`, used by `qr_exponent`): the
  shift-and-count loop returns `Nat.size x`, the bit length of the 32-bit limb.
-/
import Tess.C.QrExponent
import Tess.C.Acmp

namespace Tess.C
open Obj.C

theorem size_div2 (x : Nat) (hx : 0 < x) : Nat.size (x / 2) + 1 = Nat.size x := by
  have h1 : x < 2 ^ Nat.size x := Nat.lt_size_self x
  have hs : 0 < Nat.size x := Nat.size_pos.mpr hx
  apply le_antisymm
  · -- size x ≥ size (x/2) + 1
    have : x / 2 < 2 ^ (Nat.size x - 1) := by
      have : 2 ^ Nat.size x = 2 * 2 ^ (Nat.size x - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have := Nat.size_le.mpr this
    omega
  · have h2 : x / 2 < 2 ^ Nat.size (x / 2) := Nat.lt_size_self _
    have : x < 2 ^ (Nat.size (x / 2) + 1) := by rw [pow_succ]; omega
    exact Nat.size_le.mpr this

theorem evShr1 (x : Nat) (hx : x < 2 ^ 32) :
    evalBin .shr (some ⟨32, false⟩) (.int ⟨32, false⟩ x) (.int ⟨32, true⟩ 1) =
      .ok (.int ⟨32, false⟩ (x / 2)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.modulus]
  simp only [Obj.C.guard, if_true, Res.bind_ok]

theorem bl_loop_ast : LimbGen.bit_len32_loop0 = .loop
    (.ite (.var 0)
      (.seq (.set 1 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
          (.const (.int ⟨32, false⟩ 1)))))
        (.set 0 (.cast ⟨32, false⟩ (.bin .shr (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0))
          (.const (.int ⟨32, true⟩ 1))))))
      .brk) .skip := rfl

theorem bl_loop : ∀ m x k : Nat, Nat.size x = m → x < 2 ^ 32 → k + m < 2 ^ 32 → ∀ s : State,
    s.locals 0 = some (.int ⟨32, false⟩ x) → s.locals 1 = some (.int ⟨32, false⟩ k) →
    ∃ sf, ExS LimbGen.prog s LimbGen.bit_len32_loop0 .normal sf ∧
      sf.locals 1 = some (.int ⟨32, false⟩ (k + m)) := by
  intro m
  induction m with
  | zero =>
      intro x k hm hx hk s l0 l1
      have hx0 : x = 0 := Nat.size_eq_zero.mp hm
      subst hx0
      refine ⟨s, ?_, by simpa using l1⟩
      rw [bl_loop_ast]
      exact ExS.loop_brk (ExS.ite (EvE.var l0) (show truthy (.int ⟨32, false⟩ 0) = .ok false by simp [truthy]) ExS.brk)
  | succ m ih =>
      intro x k hm hx hk s l0 l1
      have hx' : x < 4294967296 := by simpa using hx
      have hxpos : 0 < x := Nat.size_pos.mp (by omega)
      have hdiv := size_div2 x hxpos
      have hv0 : EvE LimbGen.prog s (.var 0) (.int ⟨32, false⟩ x) := EvE.var l0
      have htr : truthy (.int ⟨32, false⟩ x) = .ok true := by simp [truthy]; omega
      have hc1 : EvE LimbGen.prog s (.cast ⟨32, false⟩ (.var 1)) (.int ⟨32, false⟩ k) :=
        EvE.cast (EvE.var l1) (by
          show Res.ok (Val.int ⟨32, false⟩ (k % 4294967296)) = _
          rw [Nat.mod_eq_of_lt (by omega)])
      have hadd : EvE LimbGen.prog s (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
          (.const (.int ⟨32, false⟩ 1))) (.int ⟨32, false⟩ (k + 1)) :=
        EvE.bin hc1 (EvE.const _) (by
          show Res.ok (Val.int ⟨32, false⟩ ((k + 1) % 4294967296)) = _
          rw [Nat.mod_eq_of_lt (by omega)])
      have hset1 := ExS.set (i := 1) (EvE.cast hadd (by
        show Res.ok (Val.int ⟨32, false⟩ ((k + 1) % 4294967296)) = _
        rw [Nat.mod_eq_of_lt (by omega)]))
      set s1 : State := { s with locals := s.locals.upd 1 (.int ⟨32, false⟩ (k + 1)) } with hs1
      have s1_0 : s1.locals 0 = some (.int ⟨32, false⟩ x) := by simpa [hs1, Locals.upd] using l0
      have hc0 : EvE LimbGen.prog s1 (.cast ⟨32, false⟩ (.var 0)) (.int ⟨32, false⟩ x) :=
        EvE.cast (EvE.var s1_0) (by
          show Res.ok (Val.int ⟨32, false⟩ (x % 4294967296)) = _
          rw [Nat.mod_eq_of_lt hx'])
      have hshr : EvE LimbGen.prog s1 (.bin .shr (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0))
          (.const (.int ⟨32, true⟩ 1))) (.int ⟨32, false⟩ (x / 2)) :=
        EvE.bin hc0 (EvE.const _) (evShr1 x hx)
      have hset0 := ExS.set (i := 0) (EvE.cast hshr (by
        show Res.ok (Val.int ⟨32, false⟩ (x / 2 % 4294967296)) = _
        rw [Nat.mod_eq_of_lt (by omega)]))
      set s2 : State := { s1 with locals := s1.locals.upd 0 (.int ⟨32, false⟩ (x / 2)) } with hs2
      have hbody : ExS LimbGen.prog s (.ite (.var 0)
          (.seq (.set 1 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
            (.const (.int ⟨32, false⟩ 1)))))
            (.set 0 (.cast ⟨32, false⟩ (.bin .shr (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0))
              (.const (.int ⟨32, true⟩ 1))))))
          .brk) .normal s2 :=
        ExS.ite hv0 htr (ExS.seq hset1 hset0)
      obtain ⟨sf, hl, hres⟩ := ih (x / 2) (k + 1) (by omega) (by omega) (by omega) s2
        (by simp [hs2, Locals.upd]) (by simpa [hs2, hs1, Locals.upd] using rfl)
      refine ⟨sf, ?_, ?_⟩
      · rw [bl_loop_ast]; rw [bl_loop_ast] at hl
        exact ExS.loop_next hbody (Or.inl rfl) ExS.skip hl
      · rw [hres]; congr 2; omega

/-- `bit_len32` returns `Nat.size x`. -/
theorem bit_len32_refines (x : Nat) (hx : x < 2 ^ 32) (m : Mem) (ro : Bool) (s0 : State)
    (h0 : s0 = ⟨frameLocals LimbGen.bit_len32.params [.int ⟨32, false⟩ x], m, ro⟩) :
    ∃ sf, ExS LimbGen.prog s0 LimbGen.bit_len32.body (.ret (some (.int ⟨32, false⟩ (Nat.size x)))) sf := by
  have l0 : s0.locals 0 = some (.int ⟨32, false⟩ x) := by rw [h0]; rfl
  have hset : ExS LimbGen.prog s0 (.set 1 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s0 with locals := s0.locals.upd 1 (.int ⟨32, false⟩ 0) } :=
    ExS.set (EvE.cast (EvE.const _) rfl)
  have hsz : Nat.size x ≤ 32 := Nat.size_le.mpr (by simpa using hx)
  obtain ⟨sf, hl, hres⟩ := bl_loop (Nat.size x) x 0 rfl hx (by omega)
    { s0 with locals := s0.locals.upd 1 (.int ⟨32, false⟩ 0) }
    (by simpa [Locals.upd] using l0) (by simp [Locals.upd])
  refine ⟨sf, ?_⟩
  unfold LimbGen.bit_len32
  rw [Nat.zero_add] at hres
  show ExS LimbGen.prog s0 (.seq _ (.seq LimbGen.bit_len32_loop0 (.ret (some (.var 1))))) _ sf
  exact ExS.seq hset (ExS.seq hl (ExS.ret (EvE.var hres)))

end Tess.C
