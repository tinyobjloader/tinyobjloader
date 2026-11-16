import Tess.PairAuditBridge
import Tess.NoncoplanarComplete

namespace Tess
namespace PairAudit

/-- Accepted noncoplanar pairs without shared vertex IDs, in general position (no vertex of
either face on the other's plane), have disjoint closed triangles in 3D (rational points). -/
theorem accepted_noncoplanar_gp_disjoint (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = [])
    (hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (hok : pairOk m fa fb = true)
    (gpA : orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) ≠ 0 ∧
           orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) ≠ 0 ∧
           orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) ≠ 0)
    (gpB : orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) ≠ 0 ∧
           orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) ≠ 0 ∧
           orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) ≠ 0) :
    ¬ ∃ p : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p ∧
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
  have h := pairOk_noncoplanar_disjoint m fa fb pa pb hpa hpb hd hnc
  rw [hok] at h
  have hc : noncoplanarTrianglesConflict (m.point fa.a) (m.point fa.b) (m.point fa.c)
      (m.point fb.a) (m.point fb.b) (m.point fb.c) = false := by
    cases hh : noncoplanarTrianglesConflict (m.point fa.a) (m.point fa.b) (m.point fa.c)
      (m.point fb.a) (m.point fb.b) (m.point fb.c)
    · rfl
    · rw [hh] at h; simp at h
  exact noncoplanar_gp_disjoint _ _ _ _ _ _ pa pb hpa hpb gpA gpB hc

end PairAudit
end Tess
