/-
  Value-level model of `qr_round_dyadic` (`lib/tess/src/exact.c`): after scaling by `2^-step` the value
  `n/d` is rounded half-up with `q = n / d`, `r = n % d`, `q' = q + (2r ≥ d)`. `roundQ_spec`: `q'` is the
  nearest integer, `|n/d - q'| ≤ 1/2`, and `q' = ⌊n/d + 1/2⌋`. Scaling back by `2^step` (an exact
  rational operation) gives a multiple of `2^step` within `2^(step-1)` of the input.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Tess.C

/-- C: quotient, then `+1` when `2 * remainder >= d`. -/
def roundQ (n d : Nat) : Nat := if d ≤ 2 * (n % d) then n / d + 1 else n / d

theorem roundQ_spec (n d : Nat) (hd : 0 < d) :
    ((roundQ n d : Nat) : ℚ) ≤ (n : ℚ) / d + 1 / 2 ∧ (n : ℚ) / d + 1 / 2 < ((roundQ n d : Nat) : ℚ) + 1 ∧
      |(n : ℚ) / d - (roundQ n d : Nat)| ≤ 1 / 2 := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hn : (n : ℚ) = (n / d : Nat) * d + (n % d : Nat) := by
    exact_mod_cast (Nat.div_add_mod' n d).symm
  have hr : (n % d : Nat) < d := Nat.mod_lt _ hd
  have hrq : ((n % d : Nat) : ℚ) < d := by exact_mod_cast hr
  have hr0 : (0 : ℚ) ≤ ((n % d : Nat) : ℚ) := Nat.cast_nonneg _
  have hfrac : (n : ℚ) / d = ((n / d : Nat) : ℚ) + ((n % d : Nat) : ℚ) / d := by
    rw [hn]; field_simp
  unfold roundQ
  by_cases h : d ≤ 2 * (n % d)
  · rw [if_pos h]
    have h2 : (d : ℚ) ≤ 2 * ((n % d : Nat) : ℚ) := by exact_mod_cast h
    have a1 : (1 : ℚ) / 2 ≤ ((n % d : Nat) : ℚ) / d := by
      rw [le_div_iff₀ hdq]; linarith
    have a2 : ((n % d : Nat) : ℚ) / d < 1 := by rw [div_lt_one hdq]; exact hrq
    push_cast
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_le]; constructor <;> linarith
  · rw [if_neg h]
    have h2 : 2 * ((n % d : Nat) : ℚ) < d := by exact_mod_cast (not_le.mp h)
    have a1 : ((n % d : Nat) : ℚ) / d < 1 / 2 := by
      rw [div_lt_iff₀ hdq]; linarith
    have a0 : 0 ≤ ((n % d : Nat) : ℚ) / d := div_nonneg hr0 hdq.le
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_le]; constructor <;> linarith

end Tess.C
