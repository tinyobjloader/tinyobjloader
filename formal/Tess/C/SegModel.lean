/-
  Model of `tg_segments`/`on`/`between` (`lib/tess/src/geometry.c`) over exact rationals and its
  equality with the Lean exact specification `Tess.segmentConflict`, whose semantics are proved in
  `IndexedConflict`/`IntersectionCompleteness`. The orientation signs are the `tg_orient` results
  (`PredModel.orient_C_sign`). Model-level only.
-/
import Tess.C.PredModel
import Tess.SegmentConflict
import Mathlib.Tactic.Linarith

namespace Tess.C

/-- C `between`: ordered range test after an `a ≤ b` comparison. -/
def betweenM (a b x : Rat) : Bool :=
  if a ≤ b then decide (a ≤ x ∧ x ≤ b) else decide (b ≤ x ∧ x ≤ a)

theorem betweenM_iff (a b x : Rat) : betweenM a b x = true ↔ between a b x := by
  unfold betweenM between
  by_cases h : a ≤ b
  · simp only [h, if_true, decide_eq_true_eq]
    constructor
    · intro h1; exact Or.inl h1
    · rintro (h1 | ⟨h2, h3⟩)
      · exact h1
      · constructor <;> linarith
  · simp only [h, if_false, decide_eq_true_eq]
    have hb : b < a := lt_of_not_ge h
    constructor
    · intro h1; exact Or.inr h1
    · rintro (⟨h2, h3⟩ | h1)
      · exact absurd (le_trans h2 h3) h
      · exact h1

/-- C `on`: collinear (zero orientation sign) and inside both coordinate ranges. -/
def onM (p q r : Point2) : Bool :=
  decide (qsign (orient p q r) = 0) && betweenM p.x q.x r.x && betweenM p.y q.y r.y

theorem onM_iff (p q r : Point2) : onM p q r = onSegment p q r := by
  unfold onM onSegment collinear
  have e : qsign (orient p q r) = 0 ↔ orient p q r = 0 := by
    unfold qsign
    constructor
    · intro h; by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h1
      · simp [h1, not_lt_of_gt h1] at h
      · simp [h1] at h
    · intro h; simp [h]
  have b1 := betweenM_iff p.x q.x r.x
  have b2 := betweenM_iff p.y q.y r.y
  cases hx : betweenM p.x q.x r.x <;> cases hy : betweenM p.y q.y r.y <;>
    simp_all [decide_eq_true_eq, Bool.and_eq_true]

theorem qsign_mul_neg (u v : Rat) : qsign u * qsign v < 0 ↔ u * v < 0 := by
  rw [← qsign_mul]
  constructor
  · intro h
    by_contra hn
    have hn' : 0 ≤ u * v := not_lt.mp hn
    rcases lt_or_eq_of_le hn' with h1 | h1
    · rw [qsign_pos h1] at h; omega
    · rw [← h1, qsign_zero] at h; omega
  · intro h; rw [qsign_neg h]; omega

theorem onM_zero (p q r : Point2) : onM p q r = true → qsign (orient p q r) = 0 := by
  intro h
  unfold onM at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- `tg_segments`: identical-edge exclusion, strict crossing, and non-shared endpoint contacts. -/
def tgSegmentsM (p q r s : Point2) (a b c d : Nat) : Bool :=
  if (a = c && b = d) || (a = d && b = c) then false
  else
    decide (qsign (orient p q r) * qsign (orient p q s) < 0 ∧
            qsign (orient r s p) * qsign (orient r s q) < 0) ||
    (decide (qsign (orient p q r) = 0 ∧ c ≠ a ∧ c ≠ b) && onM p q r) ||
    (decide (qsign (orient p q s) = 0 ∧ d ≠ a ∧ d ≠ b) && onM p q s) ||
    (decide (qsign (orient r s p) = 0 ∧ a ≠ c ∧ a ≠ d) && onM r s p) ||
    (decide (qsign (orient r s q) = 0 ∧ b ≠ c ∧ b ≠ d) && onM r s q)

theorem guard_redundant (z : Int) (φ : Prop) [Decidable φ] (o : Bool) (hz : o = true → z = 0)
    (hd : Decidable (z = 0 ∧ φ)) :
    (@decide (z = 0 ∧ φ) hd && o) = (decide φ && o) := by
  cases o
  · simp
  · have := hz rfl
    simp [this]

/-- The C segment-contact model equals the Lean exact specification. -/
theorem tgSegmentsM_eq (m : ExactMesh) (a b c d : Nat) :
    tgSegmentsM (m.project a) (m.project b) (m.project c) (m.project d) a b c d =
      segmentConflict m a b c d := by
  unfold tgSegmentsM segmentConflict
  by_cases hid : ((a = c && b = d) || (a = d && b = c)) = true
  · simp only [hid, if_true]
  · simp only [hid, if_false]
    simp only [qsign_mul_neg]
    rw [guard_redundant _ (c ≠ a ∧ c ≠ b) _ (onM_zero _ _ _)]
    rw [guard_redundant _ (d ≠ a ∧ d ≠ b) _ (onM_zero _ _ _)]
    rw [guard_redundant _ (a ≠ c ∧ a ≠ d) _ (onM_zero _ _ _)]
    rw [guard_redundant _ (b ≠ c ∧ b ≠ d) _ (onM_zero _ _ _)]
    simp only [onM_iff]
    simp only [Bool.false_eq_true, ite_false]
    generalize (decide (orient (m.project a) (m.project b) (m.project c) * orient (m.project a) (m.project b) (m.project d) < 0 ∧
      orient (m.project c) (m.project d) (m.project a) * orient (m.project c) (m.project d) (m.project b) < 0)) = t
    generalize (decide (c ≠ a ∧ c ≠ b) && onSegment (m.project a) (m.project b) (m.project c)) = e1
    generalize (decide (d ≠ a ∧ d ≠ b) && onSegment (m.project a) (m.project b) (m.project d)) = e2
    generalize (decide (a ≠ c ∧ a ≠ d) && onSegment (m.project c) (m.project d) (m.project a)) = e3
    generalize (decide (b ≠ c ∧ b ≠ d) && onSegment (m.project c) (m.project d) (m.project b)) = e4
    cases t <;> cases e1 <;> cases e2 <;> cases e3 <;> cases e4 <;> rfl

end Tess.C
