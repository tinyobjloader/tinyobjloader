import Tess.Plane
import Tess.SegmentSoundness
import Tess.Orient3Bridge

namespace Tess

/-- Plane value is affine along a rational 3D segment. -/
theorem planeValue_segment3Point (m : ExactMesh) (f : Face)
    (a b : Point3) (t : Rat) :
    planeValue m f (segment3Point a b t) =
      (1 - t) * planeValue m f a + t * planeValue m f b := by
  dsimp only [planeValue, segment3Point]
  ring

/-- A strict plane crossing supplies its exact rational interpolation parameter
and an exact zero on the supporting plane. The parameter is nondegenerate
because endpoint signs are strict and opposite. -/
theorem planeCut_spec (m : ExactMesh) (f : Face) (x y : Nat)
    (checked : planeCut m f x y = some p) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧
      p = segment3Point (m.point x) (m.point y) t ∧
      planeValue m f p = 0 := by
  let dx := planeValue m f (m.point x)
  let dy := planeValue m f (m.point y)
  by_cases opposite : dx * dy < 0
  · have bounds := segment_cross_parameter dx dy opposite
    let t : Rat := dx / (dx - dy)
    have planeZero : (1 - t) * dx + t * dy = 0 := by
      have multiplied : t * (dx - dy) = dx := div_mul_cancel₀ _ bounds.1
      linear_combination -multiplied
    have point : planeCutPoint m x y t =
        segment3Point (m.point x) (m.point y) t := rfl
    simp [planeCut, dx, dy, opposite] at checked
    cases checked
    refine ⟨t, bounds.2.1, bounds.2.2, rfl, ?_⟩
    dsimp only [planeCutPoint]
    rw [planeValue_segment3Point, planeZero]
  · simp [planeCut, dx, dy, opposite] at checked

/-- A strict plane cut lies exactly on the face plane, expressed as real coplanarity. -/
theorem planeCut_spec_coplanar (m : ExactMesh) (f : Face) (x y : Nat)
    (checked : planeCut m f x y = some p) :
    Coplanar (m.point f.a) (m.point f.b) (m.point f.c) p := by
  obtain ⟨_t, _tlo, _thi, _rfl, hplane⟩ := planeCut_spec m f x y checked
  rw [planeValue_eq_orient3] at hplane
  exact (orient3_zero_iff_coplanar _ _ _ _).mp hplane

/-- A false branch means the endpoint plane signs were not strict opposites. -/
theorem planeCut_none_of_not_opposite (m : ExactMesh) (f : Face) (x y : Nat)
    (notOpposite : ¬ planeValue m f (m.point x) * planeValue m f (m.point y) < 0) :
    planeCut m f x y = none := by
  simp [planeCut, notOpposite]

#print axioms planeValue_segment3Point
#print axioms planeCut_spec
#print axioms planeCut_spec_coplanar
#print axioms planeCut_none_of_not_opposite
end Tess
