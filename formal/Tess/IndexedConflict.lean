import Tess.SegmentConflict
import Tess.IntersectionCompleteness

namespace Tess

/-- Indexed conflict is a geometric closed-segment intersection whenever it fires. -/
theorem segmentConflict_closedIntersection (m : ExactMesh) (a b c d : Nat)
    (checked : segmentConflict m a b c d = true) :
    closedIntersection (m.project a) (m.project b) (m.project c) (m.project d) = true := by
  unfold segmentConflict at checked
  dsimp only [] at checked
  split at checked
  · contradiction
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at checked
    rcases checked with ((((hC|hD)|hA)|hB)|cross)
    · exact by simp [closedIntersection, hC.2]
    · exact by simp [closedIntersection, hD.2]
    · exact by simp [closedIntersection, hA.2]
    · exact by simp [closedIntersection, hB.2]
    · exact by simp [closedIntersection, cross.1, cross.2]

/-- With no shared vertex indices, the indexed-conflict test is exactly the
ordinary closed geometric intersection test. Valid indices and nondegenerate
edges are stated explicitly; the underlying proof does not rely on projection
disjointness. -/
theorem segmentConflict_iff_closedIntersection (m : ExactMesh) (a b c d : Nat)
    (_validIndices : a<m.points.size ∧ b<m.points.size ∧ c<m.points.size ∧ d<m.points.size)
    (_nondegenerate : m.project a ≠ m.project b ∧ m.project c ≠ m.project d)
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) :
    segmentConflict m a b c d = true ↔
      closedIntersection (m.project a) (m.project b) (m.project c) (m.project d) = true := by
  constructor
  · exact segmentConflict_closedIntersection m a b c d
  · intro geometrically
    unfold segmentConflict
    dsimp only []
    split
    · rename_i same
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at same
      rcases same with h|h
      · exact (hac h.1).elim
      · exact (had h.1).elim
    · simp only [closedIntersection, Bool.or_eq_true, decide_eq_true_eq] at geometrically
      rcases geometrically with ((((hC|hD)|hA)|hB)|cross)
      · have branch : (decide (c≠a ∧ c≠b) && onSegment (m.project a) (m.project b) (m.project c)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨hac.symm, hbc.symm⟩, hC⟩
        rw [branch]
        simp
      · have branch : (decide (d≠a ∧ d≠b) && onSegment (m.project a) (m.project b) (m.project d)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨had.symm, hbd.symm⟩, hD⟩
        rw [branch]
        simp
      · have branch : (decide (a≠c ∧ a≠d) && onSegment (m.project c) (m.project d) (m.project a)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨hac, had⟩, hA⟩
        rw [branch]
        simp
      · have branch : (decide (b≠c ∧ b≠d) && onSegment (m.project c) (m.project d) (m.project b)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨hbc, hbd⟩, hB⟩
        rw [branch]
        simp
      · have branch : decide (orient (m.project a) (m.project b) (m.project c) *
            orient (m.project a) (m.project b) (m.project d) < 0 ∧
            orient (m.project c) (m.project d) (m.project a) *
            orient (m.project c) (m.project d) (m.project b) < 0) = true := by
          rw [decide_eq_true_eq]
          exact cross
        rw [branch]
        simp

/-- An unmodified edge, in either orientation, is an expected shared simplex and
never an indexed conflict. Geometric coordinates for distinct IDs can still be
flagged by the membership branches. -/
theorem segmentConflict_same_unordered (m : ExactMesh) (a b c d : Nat)
    (same : (a=c∧b=d) ∨ (a=d∧b=c)) :
    segmentConflict m a b c d = false := by
  rcases same with h|h
  · simp [segmentConflict, h.1, h.2]
  · simp [segmentConflict, h.1, h.2]

/-- If the two indexed edges share only `a=c`, the remaining indexed conflict is
precisely an unexpected endpoint contact beyond that common vertex. Proper
crossing is impossible there because both supporting lines contain that shared
vertex. This covers collinear overlap beyond a shared endpoint. -/
theorem segmentConflict_shared_head (m : ExactMesh) (a b d : Nat)
    (_nondegenerate : m.project a ≠ m.project b ∧ m.project a ≠ m.project d)
    (distinct : a≠b ∧ a≠d ∧ b≠d) :
    segmentConflict m a b a d =
      (onSegment (m.project a) (m.project b) (m.project d) ||
       onSegment (m.project a) (m.project d) (m.project b)) := by
  have leftZero : orient (m.project a) (m.project b) (m.project a)=0 := by
    dsimp [orient]
    ring
  have rightZero : orient (m.project a) (m.project d) (m.project a)=0 := by
    dsimp [orient]
    ring
  simp [segmentConflict, distinct.1, distinct.2.1, distinct.2.2,
    distinct.1.symm, distinct.2.1.symm, distinct.2.2.symm, leftZero, rightZero]

#print axioms segmentConflict_closedIntersection
#print axioms segmentConflict_iff_closedIntersection
#print axioms segmentConflict_same_unordered

#print axioms segmentConflict_shared_head
end Tess
