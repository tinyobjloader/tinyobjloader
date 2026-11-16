import Tess.PairAuditBridge
import Tess.InPlane

namespace Tess
namespace PairAudit

/-- An accepted pair of noncoplanar faces without shared vertex IDs has disjoint closed triangles
(rational points). No general-position assumption: vertices on the other plane and edges lying in
the other plane are handled. -/
theorem accepted_noncoplanar_disjoint (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = [])
    (hnc' : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0))
    (hok : pairOk m fa fb = true) :
    ¬ ∃ p : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p ∧
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
  have hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true := by
    intro h
    apply hnc'
    simp only [List.range_succ, List.range_zero, List.nil_append, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, facePoint, planeValue_eq_orient3] at h
    simp only [Nat.reduceEqDiff, if_true, if_false, ite_true, ite_false, decide_eq_true_eq,
      Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have h := pairOk_noncoplanar_disjoint m fa fb pa pb hpa hpb hd hnc
  rw [hok] at h
  have hc : noncoplanarTrianglesConflict (m.point fa.a) (m.point fa.b) (m.point fa.c)
      (m.point fb.a) (m.point fb.b) (m.point fb.c) = false := by
    cases hh : noncoplanarTrianglesConflict (m.point fa.a) (m.point fa.b) (m.point fa.c)
      (m.point fb.a) (m.point fb.b) (m.point fb.c)
    · rfl
    · rw [hh] at h; simp at h
  exact noncoplanar_disjoint_complete _ _ _ _ _ _ pa pb hpa hpb hnc' hc

end PairAudit
end Tess
