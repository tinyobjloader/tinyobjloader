import Tess.TriangleContains
import Tess.SegmentSoundness
import Tess.PredicateGeometry
import Tess.RealTopology

noncomputable section
namespace Tess
open RealGeometry

theorem orient_sum (a b c p : Point2) :
    orient a b p + orient b c p + orient c a p = orient a b c := by
  dsimp only [orient]
  ring

theorem orient_swap (a b c : Point2) : orient b a c = -orient a b c := by
  dsimp only [orient]
  ring

/-- Nondegenerate positively oriented faces have the positive halfplane branch
inside the no-mixed-sign test. -/
theorem contains2_iff_closedTriangle_of_pos (a b c p : Point2)
    (positive : 0 < orient a b c) :
    contains2 a b c p = true ↔
      realPoint2 p ∈ closedTriangle (realPoint2 a) (realPoint2 b) (realPoint2 c) := by
  have sum := orient_sum a b c p
  constructor
  · intro checked
    simp only [contains2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at checked
    cases checked with
    | inl nonnegative =>
        simp only [closedTriangle, Set.mem_ofPred_eq]
        rw [orient_realPoint2, orient_realPoint2, orient_realPoint2]
        refine ⟨?_, ?_, ?_⟩
        · exact_mod_cast nonnegative.1.1
        · exact_mod_cast nonnegative.1.2
        · exact_mod_cast nonnegative.2
    | inr nonpositive =>
        have total : 0 ≤ orient a b p + orient b c p + orient c a p := by linarith
        rw [sum] at total
        linarith
  · intro member
    simp only [closedTriangle, Set.mem_ofPred_eq, orient_realPoint2] at member
    have h1 : 0 ≤ orient a b p := by exact_mod_cast member.1
    have h2 : 0 ≤ orient b c p := by exact_mod_cast member.2.1
    have h3 : 0 ≤ orient c a p := by exact_mod_cast member.2.2
    simp [contains2, h1, h2, h3]

/-- Nondegenerate negatively oriented faces use the reversed triangle order and
the nonpositive halfplane branch. -/
theorem contains2_iff_closedTriangle_of_neg (a b c p : Point2)
    (negative : orient a b c < 0) :
    contains2 a b c p = true ↔
      realPoint2 p ∈ closedTriangle (realPoint2 a) (realPoint2 c) (realPoint2 b) := by
  have sum := orient_sum a b c p
  constructor
  · intro checked
    simp only [contains2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at checked
    cases checked with
    | inl nonnegative =>
        have total : 0 ≤ orient a b p + orient b c p + orient c a p := by linarith
        rw [sum] at total
        linarith
    | inr nonpositive =>
        simp only [closedTriangle, Set.mem_ofPred_eq]
        rw [orient_realPoint2, orient_realPoint2, orient_realPoint2]
        have h1 : 0 ≤ orient a c p := by
          have swap := orient_swap c a p
          linarith
        have h2 : 0 ≤ orient c b p := by
          have swap := orient_swap b c p
          linarith
        have h3 : 0 ≤ orient b a p := by
          have swap := orient_swap a b p
          linarith
        refine ⟨?_, ?_, ?_⟩
        · exact_mod_cast h1
        · exact_mod_cast h2
        · exact_mod_cast h3
  · intro member
    simp only [closedTriangle, Set.mem_ofPred_eq, orient_realPoint2] at member
    have m1 : 0 ≤ orient a c p := by exact_mod_cast member.1
    have m2 : 0 ≤ orient c b p := by exact_mod_cast member.2.1
    have m3 : 0 ≤ orient b a p := by exact_mod_cast member.2.2
    have n1 : orient a b p ≤ 0 := by
      have swap := orient_swap b a p
      linarith
    have n2 : orient b c p ≤ 0 := by
      have swap := orient_swap c b p
      linarith
    have n3 : orient c a p ≤ 0 := by
      have swap := orient_swap a c p
      linarith
    simp [contains2, n1, n2, n3]

#print axioms orient_sum
#print axioms contains2_iff_closedTriangle_of_pos
#print axioms contains2_iff_closedTriangle_of_neg
end Tess
