/-
  Value-level model of the bisection loop of `qr_sqrt_bounds` (`lib/tess/src/exact.c`): starting from
  `lo = 0` and a `hi` with `a ≤ hi²`, every step keeps `0 ≤ lo ≤ hi` and `lo² ≤ a ≤ hi²`; the interval
  halves each step, and an exact hit collapses it to the point `mid` with `mid² = a`.
  Hence the returned `lower`/`upper` always bracket `√a` (`sqrtRun_inv`).
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Tess.C

/-- One bisection step; `(lo, hi, done)`. -/
def sqrtStep (a : ℚ) (s : ℚ × ℚ × Bool) : ℚ × ℚ × Bool :=
  if s.2.2 then s else
  let mid := (s.1 + s.2.1) / 2
  if mid * mid = a then (mid, mid, true)
  else if mid * mid < a then (mid, s.2.1, false) else (s.1, mid, false)

def sqrtRun (a hi0 : ℚ) : Nat → ℚ × ℚ × Bool
  | 0 => (0, hi0, false)
  | k + 1 => sqrtStep a (sqrtRun a hi0 k)

theorem sqrtRun_inv (a hi0 : ℚ) (ha : 0 ≤ a) (h0 : 0 ≤ hi0) (hhi : a ≤ hi0 * hi0) :
    ∀ k, 0 ≤ (sqrtRun a hi0 k).1 ∧ (sqrtRun a hi0 k).1 ≤ (sqrtRun a hi0 k).2.1 ∧
      (sqrtRun a hi0 k).1 * (sqrtRun a hi0 k).1 ≤ a ∧
      a ≤ (sqrtRun a hi0 k).2.1 * (sqrtRun a hi0 k).2.1 ∧
      ((sqrtRun a hi0 k).2.2 = false →
        (sqrtRun a hi0 k).2.1 - (sqrtRun a hi0 k).1 = hi0 / 2 ^ k) := by
  intro k
  induction k with
  | zero => simp [sqrtRun, ha, h0, hhi]
  | succ k ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      simp only [sqrtRun]
      generalize hs : sqrtRun a hi0 k = s at h1 h2 h3 h4 h5 ⊢
      obtain ⟨lo, hi, d⟩ := s
      simp only [] at h1 h2 h3 h4 h5
      unfold sqrtStep
      cases d
      · simp only [Bool.false_eq_true, if_false]
        by_cases he : (lo + hi) / 2 * ((lo + hi) / 2) = a
        · simp only [he, if_true]
          refine ⟨by linarith, le_rfl, le_rfl, le_rfl, by simp⟩
        · by_cases hl : (lo + hi) / 2 * ((lo + hi) / 2) < a
          · simp only [he, hl, if_true, if_false]
            refine ⟨by linarith, by linarith, hl.le, h4, fun _ => ?_⟩
            have h5' := h5 rfl
            rw [(show hi - (lo + hi) / 2 = (hi - lo) / 2 by ring), h5', pow_succ]; field_simp
          · simp only [he, hl, if_false]
            have hg : a < (lo + hi) / 2 * ((lo + hi) / 2) := lt_of_le_of_ne (not_lt.mp hl) (Ne.symm he)
            refine ⟨h1, by linarith, h3, hg.le, fun _ => ?_⟩
            have h5' := h5 rfl
            rw [(show (lo + hi) / 2 - lo = (hi - lo) / 2 by ring), h5', pow_succ]; field_simp
      · simp only [if_true]
        exact ⟨h1, h2, h3, h4, fun h => by simp at h⟩

end Tess.C
