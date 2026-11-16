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

/-- Weaker hypotheses: faces need only be noncoplanar and no edge of `fa` may lie in the plane of
`fb` (vertices on the other plane are allowed). -/
theorem accepted_noncoplanar_edgefree_disjoint (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = [])
    (hnc' : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0))
    (hok : pairOk m fa fb = true)
    (hedge : ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = 0) ∧
             ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = 0) ∧
             ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = 0)) :
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
  exact noncoplanar_edgefree_disjoint _ _ _ _ _ _ pa pb hpa hpb hnc' hedge hc

/-- Accepted noncoplanar pairs without shared vertex IDs have disjoint triangles unless an edge of
each face lies in the other face's plane (the remaining degenerate configuration). -/
theorem accepted_noncoplanar_either_disjoint (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = [])
    (hnc' : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0))
    (hnc'' : ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = 0))
    (hok : pairOk m fa fb = true)
    (hfree : (¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = 0 ∧
                 orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = 0) ∧
              ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = 0 ∧
                 orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = 0) ∧
              ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = 0 ∧
                 orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = 0)) ∨
             (¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
                 orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0) ∧
              ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
                 orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0) ∧
              ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0 ∧
                 orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0))) :
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
  exact noncoplanar_disjoint_either _ _ _ _ _ _ pa pb hpa hpb hnc' hnc'' hfree hc

end PairAudit
end Tess
