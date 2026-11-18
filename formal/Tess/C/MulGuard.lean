/-
  The size-overflow guard idiom `s && n > SIZE_MAX / s` used by `tx_alloc`, `zi_mul`
  (`a->n > SIZE_MAX / b->n`) and the face-count check of `tg_red_refine` (`oldnf > SIZE_MAX / 4`):
  for `s > 0` it fires exactly when `n * s` exceeds `SIZE_MAX` (`mulGuard_iff`), so when it does not
  fire the unsigned product `n * s` is exact and at most `SIZE_MAX`.
-/
import Mathlib.Tactic.Linarith

namespace Tess.C

theorem mulGuard_iff (M n s : Nat) (hs : 0 < s) : M / s < n ↔ M < n * s := by
  rw [Nat.div_lt_iff_lt_mul hs, Nat.mul_comm]

theorem mulGuard_exact (M n s : Nat) (hs : 0 < s) (h : ¬ M / s < n) : n * s ≤ M := by
  have := (mulGuard_iff M n s hs).not.mp h
  omega

end Tess.C
