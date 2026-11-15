import Tess.Certificate
import Tess.TriangleContains

namespace Tess

/-- Project a 3D point to the auditor's cyclically rotated plane
`(axis + 1) mod 3`, `(axis + 2) mod 3`. -/
def projectPoint3 (axis : Nat) (p : Point3) : Point2 :=
  ⟨p.coord ((axis + 1) % 3), p.coord ((axis + 2) % 3)⟩

/-- No-mixed-sign projected containment, exactly the geometric half of the
3D auditor's `contains` test after a nondegenerate projected face is chosen. -/
def containsProject (axis : Nat) (a b c p : Point3) : Bool :=
  contains2 (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c)
    (projectPoint3 axis p)
end Tess
