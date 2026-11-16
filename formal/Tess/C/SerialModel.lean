/-
  Value-level model of `serial_add` (`lib/tess/src/certificate.c`), the overflow-safe size accumulator of
  the certificate preflight: it succeeds exactly when `used + count*width ≤ limit` (and `used ≤ limit`),
  and then the unsigned sum cannot wrap because `used + count*width ≤ limit < 2^64`
  (`serialAdd_spec`).
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Tess.C

/-- C `serial_add`: `none` is the `return 0` paths, `some used'` the updated accumulator. -/
def serialAdd (used count width limit : Nat) : Option Nat :=
  if used > limit ∨ (width ≠ 0 ∧ (limit - used) / width < count) then none
  else some (used + count * width)

theorem serialAdd_spec (used count width limit : Nat) :
    (∀ u', serialAdd used count width limit = some u' →
      u' = used + count * width ∧ u' ≤ limit) ∧
    (serialAdd used count width limit = none → ¬ (used ≤ limit ∧ used + count * width ≤ limit)) := by
  unfold serialAdd
  by_cases h : used > limit ∨ (width ≠ 0 ∧ (limit - used) / width < count)
  · rw [if_pos h]
    refine ⟨?_, ?_⟩
    · intro u' hu; cases hu
    intro _
    rintro ⟨h1, h2⟩
    rcases h with h | ⟨hw, hc⟩
    · omega
    · have hwpos : 0 < width := Nat.pos_of_ne_zero hw
      have : count ≤ (limit - used) / width := (Nat.le_div_iff_mul_le hwpos).mpr (by omega)
      omega
  · rw [if_neg h]
    refine ⟨?_, ?_⟩
    swap
    · intro hn; cases hn
    intro u' hu
    have hu' := Option.some.inj hu
    subst hu'
    refine ⟨rfl, ?_⟩
    simp only [not_or, not_lt, not_and, ne_eq, not_not] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hw : width = 0
    · subst hw; simp; omega
    · have hwpos : 0 < width := Nat.pos_of_ne_zero hw
      have := h2 hw
      have : count * width ≤ limit - used := (Nat.le_div_iff_mul_le hwpos).mp this
      omega

end Tess.C
