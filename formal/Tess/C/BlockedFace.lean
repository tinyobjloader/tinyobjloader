/-
  Value-level model of `blocked_face` (`lib/tess/src/remesh.c`): the linear scan returns 1 exactly when
  the face id occurs among the first `n` blocked ids (`blockedFace_spec`), so the refinement loop never
  re-selects a blocked face.
-/
import Mathlib.Tactic.Linarith

namespace Tess.C

/-- The `for (i = 0; i < n; i++) if (blocked[i] == id) return 1; return 0` scan over indices `< n`. -/
def blockedFace (b : Nat → Nat) (id : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => blockedFace b id n || decide (b n = id)

theorem blockedFace_spec (b : Nat → Nat) (id n : Nat) :
    blockedFace b id n = true ↔ ∃ i, i < n ∧ b i = id := by
  induction n with
  | zero => simp [blockedFace]
  | succ n ih =>
      simp only [blockedFace, Bool.or_eq_true, ih, decide_eq_true_eq]
      constructor
      · rintro (⟨i, hi, e⟩ | e)
        · exact ⟨i, by omega, e⟩
        · exact ⟨n, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        by_cases h : i < n
        · exact Or.inl ⟨i, h, e⟩
        · have : i = n := by omega
          subst this; exact Or.inr e

end Tess.C
