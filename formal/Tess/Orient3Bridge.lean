import Tess.Orient3
import Tess.Check
import Tess.SegmentSoundness

noncomputable section
namespace Tess

def realOrient3 (a b c d : Point3) : ℝ :=
  let ax := ((a.x : Rat) : ℝ)-((d.x : Rat) : ℝ); let ay := ((a.y : Rat) : ℝ)-((d.y : Rat) : ℝ); let az := ((a.z : Rat) : ℝ)-((d.z : Rat) : ℝ)
  let bx := ((b.x : Rat) : ℝ)-((d.x : Rat) : ℝ); let byy := ((b.y : Rat) : ℝ)-((d.y : Rat) : ℝ); let bz := ((b.z : Rat) : ℝ)-((d.z : Rat) : ℝ)
  let cx := ((c.x : Rat) : ℝ)-((d.x : Rat) : ℝ); let cy := ((c.y : Rat) : ℝ)-((d.y : Rat) : ℝ); let cz := ((c.z : Rat) : ℝ)-((d.z : Rat) : ℝ)
  ax*(byy*cz-bz*cy) - ay*(bx*cz-bz*cx) + az*(bx*cy-byy*cx)

/-- The executable exact 3D orientation is the exact cast of the real determinant. -/
theorem orient3_cast (a b c d : Point3) :
    ((orient3 a b c d : Rat) : ℝ) = realOrient3 a b c d := by
  simp only [realOrient3]
  dsimp only [orient3]
  push_cast
  ring

/-- Coplanarity is linear dependence of the translated vectors. It is defined
for degenerate triples as well; no noncollinearity hypothesis is required. -/
def Coplanar (a b c d : Point3) : Prop := realOrient3 a b c d = 0

theorem orient3_zero_iff_coplanar (a b c d : Point3) :
    orient3 a b c d = 0 ↔ Coplanar a b c d := by
  constructor
  · intro h
    show realOrient3 a b c d = 0
    rw [← orient3_cast a b c d, h]
    simp
  · intro h
    have hReal : realOrient3 a b c d = 0 := h
    rw [← orient3_cast a b c d] at hReal
    exact_mod_cast hReal

/-- The exact 3D orientation has the same row order as `planeValue`. -/
theorem planeValue_eq_orient3 (m : ExactMesh) (f : Face) (p : Point3) :
    planeValue m f p = orient3 (m.point f.a) (m.point f.b) (m.point f.c) p := by
  dsimp only [planeValue, orient3, ExactMesh.point, Point3.coord]

theorem planeValue_zero_iff_coplanar (m : ExactMesh) (f : Face) (p : Point3) :
    planeValue m f p = 0 ↔
      Coplanar (m.point f.a) (m.point f.b) (m.point f.c) p := by
  rw [planeValue_eq_orient3, orient3_zero_iff_coplanar]

#print axioms planeValue_eq_orient3
#print axioms orient3_zero_iff_coplanar
#print axioms planeValue_zero_iff_coplanar
end Tess
