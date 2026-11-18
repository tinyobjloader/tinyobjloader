import Tess.PairAudit
import Tess.Orient3Bridge

namespace Tess
namespace PairAudit

/-- Boolean core: strict-cut flags imply both endpoints off the plane. -/
theorem cyclic_bool : ∀ (z0 z1 z2 q01 q12 q20 k0 k1 k2 t01 t12 t20 : Bool),
    (q01 = true → z0 = false ∧ z1 = false) → (q12 = true → z1 = false ∧ z2 = false) →
    (q20 = true → z2 = false ∧ z0 = false) →
    (((!(z0 && k0)) && (!(z1 && k1)) && (if q01 then !t01 else true)) &&
    ((!(z1 && k1)) && (!(z2 && k2)) && (if q12 then !t12 else true)) &&
    ((!(z2 && k2)) && (!(z0 && k0)) && (if q20 then !t20 else true))) =
    (!((if z0 then k0 else if z1 then k1 else if q01 then t01 else false) ||
      (if z1 then k1 else if z2 then k2 else if q12 then t12 else false) ||
      (if z2 then k2 else if z0 then k0 else if q20 then t20 else false))) := by
  intro z0 z1 z2 q01 q12 q20 k0 k1 k2 t01 t12 t20
  cases z0 <;> cases z1 <;> cases z2 <;> cases q01 <;> cases q12 <;> cases q20 <;>
    cases k0 <;> cases k1 <;> cases k2 <;> cases t01 <;> cases t12 <;> cases t20 <;> decide


theorem allowed_of_disjoint (m : ExactMesh) (fa fb : Face) (hd : commonIds fa fb = []) (p : Point3) :
    allowed m fa fb p = false := by
  unfold allowed
  rw [hd]; simp

theorem edgesAgainst_eq (m : ExactMesh) (fa fb : Face) (pb : Nat)
    (hpb : projAxis m fb = some pb) (hd : commonIds fa fb = []) :
    edgesAgainst m fa fb pb =
      !(edgeAgainstTriangle (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) (m.point fa.b) ||
        edgeAgainstTriangle (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) (m.point fa.c) ||
        edgeAgainstTriangle (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) (m.point fa.a)) := by
  have hc : ∀ p, containsPt m fb pb p =
      containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p
    unfold containsPt containsNondegenerate
    unfold projAxis at hpb
    rw [hpb]
  have hpv : ∀ p, planeValue m fb p = pointPlaneValue (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p; rw [planeValue_eq_orient3]; rfl
  unfold edgesAgainst edgeAgainstTriangle
  simp only [allowed_of_disjoint m fa fb hd, hc, hpv, Bool.not_false, Bool.and_true, faceId,
    List.range_succ, List.range_zero, List.nil_append, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  simp only [Nat.reduceMod, Nat.reduceAdd, Nat.zero_add, show (0:Nat) = 0 from rfl, show ¬ (1:Nat) = 0 by decide,
    show ¬ (2:Nat) = 0 by decide, show ¬ (2:Nat) = 1 by decide, show (1:Nat) = 1 from rfl, if_true, if_false,
    ite_true, ite_false, Bool.and_true]
  generalize pointPlaneValue (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = d0
  generalize pointPlaneValue (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = d1
  generalize pointPlaneValue (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = d2
  have hq : ∀ x y : Rat, decide (x * y < 0) = true → decide (x = 0) = false ∧ decide (y = 0) = false := by
    intro x y h
    have h' := of_decide_eq_true h
    constructor <;> simp only [decide_eq_false_iff_not] <;> intro e <;> subst e <;> simp at h'
  have := cyclic_bool (decide (d0 = 0)) (decide (d1 = 0)) (decide (d2 = 0))
    (decide (d0 * d1 < 0)) (decide (d1 * d2 < 0)) (decide (d2 * d0 < 0))
    (containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a))
    (containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b))
    (containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c))
    (containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c)
      (segment3Point (m.point fa.a) (m.point fa.b) (d0 / (d0 - d1))))
    (containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c)
      (segment3Point (m.point fa.b) (m.point fa.c) (d1 / (d1 - d2))))
    (containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c)
      (segment3Point (m.point fa.c) (m.point fa.a) (d2 / (d2 - d0))))
    (hq d0 d1) (hq d1 d2) (hq d2 d0)
  simpa only [decide_eq_true_eq] using this

theorem commonIds_swap_nil (fa fb : Face) (h : commonIds fa fb = []) : commonIds fb fa = [] := by
  unfold commonIds at *
  simp only [List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff, List.mem_range] at h ⊢
  intro i hi j hj
  have := h j hj i hi
  simp only [ite_eq_right_iff, reduceCtorEq, imp_false] at this ⊢
  intro e; exact this e.symm

/-- Without shared vertices, a noncoplanar pair is accepted by the auditor exactly
when the already-proved exact contact predicate reports no contact. -/
theorem pairOk_noncoplanar_disjoint (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = [])
    (hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true) :
    pairOk m fa fb =
      !noncoplanarTrianglesConflict (m.point fa.a) (m.point fa.b) (m.point fa.c)
        (m.point fb.a) (m.point fb.b) (m.point fb.c) := by
  have hA : firstProjectionAxis (m.point fa.a) (m.point fa.b) (m.point fa.c) = some pa := hpa
  have hB : firstProjectionAxis (m.point fb.a) (m.point fb.b) (m.point fb.c) = some pb := hpb
  have hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = false := by
    cases h : (List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)
    · rfl
    · exact absurd h hnc
  unfold pairOk noncoplanarTrianglesConflict
  rw [hpa, hpb, hA, hB]
  simp only [hcop, Bool.false_eq_true, if_false]
  rw [if_neg (by
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    apply hnc
    simp only [List.range_succ, List.range_zero, List.nil_append, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, facePoint, planeValue_eq_orient3]
    simp only [Nat.reduceEqDiff, if_true, if_false, ite_true, ite_false, decide_eq_true_eq, Bool.and_eq_true]
    exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩)]
  rw [edgesAgainst_eq m fa fb pb hpb hd, edgesAgainst_eq m fb fa pa hpa (commonIds_swap_nil fa fb hd)]
  rw [Bool.not_or, Bool.not_or]
  simp only [Bool.not_or, Bool.not_and, Bool.not_not, Bool.or_assoc, Bool.and_assoc]

end PairAudit
end Tess
