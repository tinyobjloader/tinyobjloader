import Tess.CertificateCoverage
import Tess.Barycentric
noncomputable section
namespace Tess
open RealGeometry

def squaredDistance (a b : Point2) : Rat := (a.x-b.x)^2+(a.y-b.y)^2

theorem incircle_circle_identity (a b c d center : Point2) (radiusSquared : Rat) :
    incircleDet a b c d=orient a b c*(radiusSquared-squaredDistance d center) +
      orient b c d*(squaredDistance a center-radiusSquared) +
      orient c a d*(squaredDistance b center-radiusSquared) +
      orient a b d*(squaredDistance c center-radiusSquared) := by
  simp only [incircleDet,orient,squaredDistance]
  ring

/-- The orientation-correct determinant is positive exactly inside a circle
through the three noncollinear sites. Radius is specified by its square. -/
theorem illegalDelaunay_circle (a b c d center : Point2) (radiusSquared : Rat)
    (noncollinear : orient a b c≠0)
    (ha : squaredDistance a center=radiusSquared)
    (hb : squaredDistance b center=radiusSquared)
    (hc : squaredDistance c center=radiusSquared) :
    illegalDelaunay a b c d=true ↔ squaredDistance d center<radiusSquared := by
  have identity : incircleDet a b c d*orient a b c=
      (orient a b c)^2*(radiusSquared-squaredDistance d center) := by
    rw [incircle_circle_identity a b c d center radiusSquared,ha,hb,hc]
    ring
  simp only [illegalDelaunay,decide_eq_true_eq,identity]
  have positive : 0<(orient a b c)^2 := sq_pos_of_ne_zero noncollinear
  rw [mul_pos_iff_of_pos_left positive]
  exact sub_pos

def realPoint2 (p : Point2) : P2 := ((p.x : ℝ),(p.y : ℝ))

theorem orient_realPoint2 (a b c : Point2) :
    RealGeometry.orient (realPoint2 a) (realPoint2 b) (realPoint2 c)=(orient a b c : ℝ) := by
  simp only [realPoint2,RealGeometry.orient,orient]
  push_cast
  rfl

/-- Exact triangle point classification includes the closed boundary. -/
theorem inside_iff_closedTriangle (m : ExactMesh) (f : Face) (p : Point2) :
    inside m f p=true ↔ realPoint2 p∈closedTriangle (realPoint m f.a) (realPoint m f.b) (realPoint m f.c) := by
  simp only [inside,Face.edges,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true]
  simp only [Bool.false_eq_true,ite_false,decide_eq_true_eq]
  change (0≤orient (m.project f.a) (m.project f.b) p ∧
    0≤orient (m.project f.b) (m.project f.c) p ∧ 0≤orient (m.project f.c) (m.project f.a) p) ↔ _
  simp only [closedTriangle,Set.mem_setOf_eq]
  have cast (a b : Nat) : RealGeometry.orient (realPoint m a) (realPoint m b) (realPoint2 p)=
      (orient (m.project a) (m.project b) p : ℝ) := orient_realPoint2 _ _ _
  rw [cast,cast,cast]
  norm_cast

#print axioms illegalDelaunay_circle
#print axioms inside_iff_closedTriangle
end Tess
