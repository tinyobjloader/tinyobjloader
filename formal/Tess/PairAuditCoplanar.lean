import Tess.PairAuditBridge
import Tess.IndexedConflict

namespace Tess
namespace PairAudit

theorem ids_ne_of_common_nil (fa fb : Face) (h : commonIds fa fb = []) (i j : Nat) (hi : i < 3) (hj : j < 3) :
    faceId fa i ≠ faceId fb j := by
  unfold commonIds at h
  simp only [List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff, List.mem_range] at h
  have := h i hi j hj
  simpa using this

/-- Accepted coplanar pairs without shared vertex IDs: no vertex of either face lies in the
other projected closed triangle, and no projected edge of one face closed-intersects an
edge of the other (indices valid, projected edges nondegenerate). -/
theorem coplanar_disjoint_accepted (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = [])
    (hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (hok : pairOk m fa fb = true)
    (hidx : ∀ k, k < 3 → faceId fa k < m.points.size ∧ faceId fb k < m.points.size)
    (hnd : ∀ k, k < 3 →
      (withAxis m pa).project (faceId fa k) ≠ (withAxis m pa).project (faceId fa ((k + 1) % 3)) ∧
      (withAxis m pa).project (faceId fb k) ≠ (withAxis m pa).project (faceId fb ((k + 1) % 3))) :
    (∀ k, k < 3 → containsPt m fb pa (facePoint m fa k) = false) ∧
    (∀ k, k < 3 → containsPt m fa pa (facePoint m fb k) = false) ∧
    (∀ k l, k < 3 → l < 3 →
      closedIntersection ((withAxis m pa).project (faceId fa k))
        ((withAxis m pa).project (faceId fa ((k + 1) % 3)))
        ((withAxis m pa).project (faceId fb l))
        ((withAxis m pa).project (faceId fb ((l + 1) % 3))) = false) := by
  unfold pairOk at hok
  rw [hpa, hpb] at hok
  simp only [hcop, if_true, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff] at hok
  obtain ⟨⟨hpts, hsegs⟩, hshared⟩ := hok
  have hnc : ∀ x : Point3, allowed m fa fb x = false := allowed_of_disjoint m fa fb hd
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have := (hpts k hk).1
    simp only [hnc, Bool.not_false, Bool.and_true, Bool.not_eq_true'] at this
    simpa using this
  · intro k hk
    have := (hpts k hk).2
    simp only [hnc, Bool.not_false, Bool.and_true, Bool.not_eq_true'] at this
    simpa using this
  · intro k l hk hl
    have hseg := hsegs k hk l hl
    by_contra hne
    have hci : closedIntersection ((withAxis m pa).project (faceId fa k))
        ((withAxis m pa).project (faceId fa ((k + 1) % 3)))
        ((withAxis m pa).project (faceId fb l))
        ((withAxis m pa).project (faceId fb ((l + 1) % 3))) = true := by simpa using hne
    have hv1 := hidx k hk
    have hv2 := hidx ((k + 1) % 3) (Nat.mod_lt _ (by norm_num))
    have hv3 := hidx l hl
    have hv4 := hidx ((l + 1) % 3) (Nat.mod_lt _ (by norm_num))
    have hnd1 := hnd k hk
    have hnd2 := hnd l hl
    have key := (segmentConflict_iff_closedIntersection (withAxis m pa) (faceId fa k) (faceId fa ((k + 1) % 3))
      (faceId fb l) (faceId fb ((l + 1) % 3))
      ⟨hv1.1, hv2.1, hv3.2, hv4.2⟩ ⟨hnd1.1, hnd2.2⟩
      (ids_ne_of_common_nil fa fb hd _ _ hk hl)
      (ids_ne_of_common_nil fa fb hd _ _ hk (Nat.mod_lt _ (by norm_num)))
      (ids_ne_of_common_nil fa fb hd _ _ (Nat.mod_lt _ (by norm_num)) hl)
      (ids_ne_of_common_nil fa fb hd _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)))).mpr hci
    rw [hseg] at key
    exact absurd key (by decide)

end PairAudit
end Tess
