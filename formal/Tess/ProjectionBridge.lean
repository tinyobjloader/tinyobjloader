import Tess.Projection
import Tess.TriangleContainsBridge

namespace Tess

/-- A nonzero clockwise projected face uses the positive-orientation theorem. -/
theorem containsProject_of_pos (axis : Nat) (a b c p : Point3)
    (positive :
      0 < orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c)) :
    containsProject axis a b c p = true ↔
      realPoint2 (projectPoint3 axis p) ∈
        RealGeometry.closedTriangle
          (realPoint2 (projectPoint3 axis a))
          (realPoint2 (projectPoint3 axis b))
          (realPoint2 (projectPoint3 axis c)) := by
  exact contains2_iff_closedTriangle_of_pos _ _ _ _ positive

/-- A nonzero counterclockwise or clockwise projected face uses the reversed
edge order, covering both projected face orientations. -/
theorem containsProject_of_neg (axis : Nat) (a b c p : Point3)
    (negative :
      orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) < 0) :
    containsProject axis a b c p = true ↔
      realPoint2 (projectPoint3 axis p) ∈
        RealGeometry.closedTriangle
          (realPoint2 (projectPoint3 axis a))
          (realPoint2 (projectPoint3 axis c))
          (realPoint2 (projectPoint3 axis b)) := by
  exact contains2_iff_closedTriangle_of_neg _ _ _ _ negative

#print axioms containsProject_of_pos
#print axioms containsProject_of_neg
end Tess
