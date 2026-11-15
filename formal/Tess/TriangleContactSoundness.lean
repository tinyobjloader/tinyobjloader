import Tess.TriangleContact
import Tess.PlaneCutBridge
import Tess.ProjectionBridge

namespace Tess

/-- Rational 3D closed-segment membership. -/
def RationalSegment3 (a b p : Point3) : Prop :=
  ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p = segment3Point a b t

/-- The 3D orientation determinant is affine along a segment. This follows by
expansion and is the fact used by both the plane-cut proof and the executable
edge-contact predicate. -/
theorem orient3_segment (a b c x y : Point3) (t : Rat) :
    orient3 a b c (segment3Point x y t) =
      (1 - t) * orient3 a b c x + t * orient3 a b c y := by
  dsimp only [orient3, segment3Point]
  ring

/-- Every direct edge/plane-contact result is an exact rational point of the
source edge, lies on the target plane and is recognized by projected target
containment. Degenerate target faces are not silently converted into contacts. -/
theorem edgeAgainst_sound (a b c x y : Point3)
    (checked : edgeAgainstTriangle a b c x y = true) :
    ∃ p : Point3, RationalSegment3 x y p ∧
      pointPlaneValue a b c p = 0 ∧
      containsNondegenerate a b c p = true := by
  by_cases dxZero : pointPlaneValue a b c x = 0
  · simp [edgeAgainstTriangle, dxZero] at checked
    refine ⟨x, ?_, dxZero, checked⟩
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    simp [segment3Point]
  · by_cases dyZero : pointPlaneValue a b c y = 0
    · simp [edgeAgainstTriangle, dxZero, dyZero] at checked
      refine ⟨y, ?_, dyZero, checked⟩
      refine ⟨1, by norm_num, by norm_num, ?_⟩
      cases x; cases y; simp [segment3Point]
    · by_cases opposite : pointPlaneValue a b c x * pointPlaneValue a b c y < 0
      · have bounds := segment_cross_parameter
          (pointPlaneValue a b c x) (pointPlaneValue a b c y) opposite
        let t : Rat := pointPlaneValue a b c x /
          (pointPlaneValue a b c x - pointPlaneValue a b c y)
        let p : Point3 := segment3Point x y t
        have checked := checked
        simp [edgeAgainstTriangle, dxZero, dyZero, opposite] at checked
        have planeZero : (1 - t) * pointPlaneValue a b c x +
            t * pointPlaneValue a b c y = 0 := by
          have multiplied :
              t * (pointPlaneValue a b c x - pointPlaneValue a b c y) =
                pointPlaneValue a b c x := div_mul_cancel₀ _ bounds.1
          linear_combination -multiplied
        have affine : pointPlaneValue a b c p =
            (1 - t) * pointPlaneValue a b c x +
              t * pointPlaneValue a b c y := by
          dsimp only [pointPlaneValue, p]
          exact orient3_segment a b c x y t
        exact ⟨p, ⟨t, bounds.2.1, bounds.2.2, rfl⟩,
          by rw [affine, planeZero], checked⟩
      · simp [edgeAgainstTriangle, dxZero, dyZero, opposite] at checked

#print axioms orient3_segment
#print axioms edgeAgainst_sound

/-- A successful target-containment decision carries a certified nonzero projection axis. -/
theorem containsNondegenerate_spec (a b c p : Point3)
    (checked : containsNondegenerate a b c p = true) :
    ∃ axis : Nat,
      orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) ≠ 0 ∧
      containsProject axis a b c p = true := by
  unfold containsNondegenerate at checked
  cases haxis : firstProjectionAxis a b c with
  | none => simp [haxis] at checked
  | some axis =>
      simp [haxis] at checked
      unfold firstProjectionAxis at haxis
      split at haxis <;> rename_i axisCondition
      · cases haxis
        exact ⟨0, axisCondition, checked⟩
      · split at haxis <;> rename_i secondCondition
        · cases haxis
          exact ⟨1, secondCondition, checked⟩
        · split at haxis <;> rename_i thirdCondition
          · cases haxis
            exact ⟨2, thirdCondition, checked⟩
          · cases haxis

#print axioms containsNondegenerate_spec

/-- Witness returned by a direct edge-to-triangle contact test. -/
def EdgeContact (a b c x y : Point3) : Prop :=
  ∃ p : Point3, RationalSegment3 x y p ∧
    pointPlaneValue a b c p = 0 ∧
    containsNondegenerate a b c p = true

/-- Every true noncoplanar-contact decision has a direct witness. The source
edge is the first triangle's edge in the first three branches, and the second
triangle's edge in the remaining three. -/
theorem noncoplanarTrianglesConflict_sound (a b c d e f : Point3)
    (checked : noncoplanarTrianglesConflict a b c d e f = true) :
    EdgeContact d e f a b ∨ EdgeContact d e f b c ∨ EdgeContact d e f c a ∨
    EdgeContact a b c d e ∨ EdgeContact a b c e f ∨ EdgeContact a b c f d := by
  simp only [noncoplanarTrianglesConflict] at checked
  split at checked
  · rename_i firstAxis secondAxis
    by_cases coplanar : pointPlaneValue a b c d = 0 &&
      pointPlaneValue a b c e = 0 && pointPlaneValue a b c f = 0
    · simp [coplanar] at checked
    · simp [coplanar] at checked
      rcases checked with (((((h1|h2)|h3)|h4)|h5)|h6)
      · exact Or.inl (edgeAgainst_sound d e f a b h1)
      · exact Or.inr (Or.inl (edgeAgainst_sound d e f b c h2))
      · exact Or.inr (Or.inr (Or.inl (edgeAgainst_sound d e f c a h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (edgeAgainst_sound a b c d e h4))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (edgeAgainst_sound a b c e f h5)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (edgeAgainst_sound a b c f d h6)))))
  · contradiction

#print axioms noncoplanarTrianglesConflict_sound

/-- Successful nondegenerate target containment witnesses real closed-triangle membership on the selected projection. -/
theorem containsNondegenerate_member (a b c p : Point3)
    (checked : containsNondegenerate a b c p = true) :
    ∃ axis : Nat,
      (0 < orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) ∧
        realPoint2 (projectPoint3 axis p) ∈
          RealGeometry.closedTriangle
            (realPoint2 (projectPoint3 axis a))
            (realPoint2 (projectPoint3 axis b))
            (realPoint2 (projectPoint3 axis c))) ∨
      (orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) < 0 ∧
        realPoint2 (projectPoint3 axis p) ∈
          RealGeometry.closedTriangle
            (realPoint2 (projectPoint3 axis a))
            (realPoint2 (projectPoint3 axis c))
            (realPoint2 (projectPoint3 axis b))) := by
  obtain ⟨axis, nondegenerate, checked⟩ := containsNondegenerate_spec a b c p checked
  rcases lt_or_gt_of_ne nondegenerate with negative | positive
  · exact ⟨axis, Or.inr ⟨negative,
      (containsProject_of_neg axis a b c p negative).mp checked⟩⟩
  · exact ⟨axis, Or.inl ⟨positive,
      (containsProject_of_pos axis a b c p positive).mp checked⟩⟩

/-- Edge contact with target closed-triangle membership, in the selected 3D projection. -/
theorem edgeAgainst_member (a b c x y : Point3)
    (checked : edgeAgainstTriangle a b c x y = true) :
    ∃ p : Point3, ∃ axis : Nat, RationalSegment3 x y p ∧
      pointPlaneValue a b c p = 0 ∧
      ((0 < orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) ∧
          realPoint2 (projectPoint3 axis p) ∈
            RealGeometry.closedTriangle
              (realPoint2 (projectPoint3 axis a))
              (realPoint2 (projectPoint3 axis b))
              (realPoint2 (projectPoint3 axis c))) ∨
       (orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) < 0 ∧
          realPoint2 (projectPoint3 axis p) ∈
            RealGeometry.closedTriangle
              (realPoint2 (projectPoint3 axis a))
              (realPoint2 (projectPoint3 axis c))
              (realPoint2 (projectPoint3 axis b)))) := by
  obtain ⟨p, segment, planeZero, contains⟩ := edgeAgainst_sound a b c x y checked
  obtain ⟨axis, member⟩ := containsNondegenerate_member a b c p contains
  exact ⟨p, axis, segment, planeZero, member⟩

#print axioms containsNondegenerate_member
#print axioms edgeAgainst_member

/-- Full witness for a direct noncoplanar edge-to-triangle contact, including
real projected triangle membership. -/
def EdgeMember (a b c x y : Point3) : Prop :=
  ∃ p : Point3, ∃ axis : Nat, RationalSegment3 x y p ∧
    pointPlaneValue a b c p = 0 ∧
    ((0 < orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) ∧
        realPoint2 (projectPoint3 axis p) ∈
          RealGeometry.closedTriangle
            (realPoint2 (projectPoint3 axis a))
            (realPoint2 (projectPoint3 axis b))
            (realPoint2 (projectPoint3 axis c))) ∨
     (orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) < 0 ∧
        realPoint2 (projectPoint3 axis p) ∈
          RealGeometry.closedTriangle
            (realPoint2 (projectPoint3 axis a))
            (realPoint2 (projectPoint3 axis c))
            (realPoint2 (projectPoint3 axis b))))

/-- Every true noncoplanar-contact decision has a full geometric witness. -/
theorem noncoplanarTrianglesConflict_member (a b c d e f : Point3)
    (checked : noncoplanarTrianglesConflict a b c d e f = true) :
    EdgeMember d e f a b ∨ EdgeMember d e f b c ∨ EdgeMember d e f c a ∨
    EdgeMember a b c d e ∨ EdgeMember a b c e f ∨ EdgeMember a b c f d := by
  simp only [noncoplanarTrianglesConflict] at checked
  split at checked
  · rename_i firstAxis secondAxis
    by_cases coplanar : pointPlaneValue a b c d = 0 &&
      pointPlaneValue a b c e = 0 && pointPlaneValue a b c f = 0
    · simp [coplanar] at checked
    · simp [coplanar] at checked
      rcases checked with (((((h1|h2)|h3)|h4)|h5)|h6)
      · exact Or.inl (edgeAgainst_member d e f a b h1)
      · exact Or.inr (Or.inl (edgeAgainst_member d e f b c h2))
      · exact Or.inr (Or.inr (Or.inl (edgeAgainst_member d e f c a h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (edgeAgainst_member a b c d e h4))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (edgeAgainst_member a b c e f h5)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (edgeAgainst_member a b c f d h6)))))
  · contradiction

#print axioms noncoplanarTrianglesConflict_member

/-- A coplanar edge cut or endpoint found by the direct test is complete whenever
the source edge is not wholly contained in the target plane. -/
theorem edgeAgainst_complete (a b c x y p : Point3)
    (edgePoint : RationalSegment3 x y p)
    (planeZero : pointPlaneValue a b c p = 0)
    (containsP : containsNondegenerate a b c p = true)
    (notBothPlaneZero : ¬ (pointPlaneValue a b c x = 0 ∧
      pointPlaneValue a b c y = 0)) :
    edgeAgainstTriangle a b c x y = true := by
  obtain ⟨t, tLo, tHi, rfl⟩ := edgePoint
  have affine : (1 - t) * pointPlaneValue a b c x +
      t * pointPlaneValue a b c y = 0 := by
    calc
      (1 - t) * pointPlaneValue a b c x + t * pointPlaneValue a b c y =
          pointPlaneValue a b c (segment3Point x y t) := (orient3_segment a b c x y t).symm
      _ = 0 := planeZero
  by_cases dxZero : pointPlaneValue a b c x = 0
  · have dy : pointPlaneValue a b c y ≠ 0 := by
      intro h
      exact notBothPlaneZero ⟨dxZero, h⟩
    have tZero : t = 0 := by
      rw [dxZero] at affine
      simp only [mul_zero, zero_add] at affine
      exact (mul_eq_zero.mp affine).resolve_right dy
    subst tZero
    have containsX : containsNondegenerate a b c (segment3Point x y 0)
        = containsNondegenerate a b c x := by simp [segment3Point]
    rw [containsX] at containsP
    simp [edgeAgainstTriangle, dxZero, containsP]
  · by_cases dyZero : pointPlaneValue a b c y = 0
    · have tOne : t = 1 := by
        rw [dyZero] at affine
        simp only [mul_zero, add_zero] at affine
        have oneT : 1 - t = 0 := (mul_eq_zero.mp affine).resolve_right dxZero
        linarith
      subst tOne
      have containsY : containsNondegenerate a b c (segment3Point x y 1)
          = containsNondegenerate a b c y := by simp [segment3Point]
      rw [containsY] at containsP
      simp [edgeAgainstTriangle, dxZero, dyZero, containsP]
    · have opposite : pointPlaneValue a b c x * pointPlaneValue a b c y < 0 := by
        rcases lt_or_gt_of_ne dxZero with dxNeg | dxPos
        · rcases lt_or_gt_of_ne dyZero with dyNeg | dyPos
          · have term1 : (1 - t) * pointPlaneValue a b c x ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by linarith) dxNeg.le
            have term2 : t * pointPlaneValue a b c y ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos tLo dyNeg.le
            have bothZero : (1 - t) * pointPlaneValue a b c x = 0 ∧
                t * pointPlaneValue a b c y = 0 := by
              refine ⟨?_, ?_⟩ <;> nlinarith [affine]
            have tOne : t = 1 := by
              have zero := bothZero.1
              have oneT : 1 - t = 0 := Or.resolve_right (mul_eq_zero.mp zero) dxZero
              linarith
            have tZero : t = 0 := by
              have zero := bothZero.2
              exact Or.resolve_right (mul_eq_zero.mp zero) (by linarith)
            exact False.elim (by linarith)
          · exact mul_neg_of_neg_of_pos dxNeg dyPos
        · rcases lt_or_gt_of_ne dyZero with dyNeg | dyPos
          · exact mul_neg_of_pos_of_neg dxPos dyNeg
          · have term1 : (1 - t) * pointPlaneValue a b c x ≥ 0 :=
              mul_nonneg (by linarith) dxPos.le
            have term2 : t * pointPlaneValue a b c y ≥ 0 :=
              mul_nonneg tLo dyPos.le
            have bothZero : (1 - t) * pointPlaneValue a b c x = 0 ∧
                t * pointPlaneValue a b c y = 0 := by
              refine ⟨?_, ?_⟩ <;> nlinarith [affine]
            have tOne : t = 1 := by
              have zero := bothZero.1
              have oneT : 1 - t = 0 := Or.resolve_right (mul_eq_zero.mp zero) dxZero
              linarith
            have tZero : t = 0 := by
              have zero := bothZero.2
              exact Or.resolve_right (mul_eq_zero.mp zero) (by linarith)
            exact False.elim (by linarith)
      have denominator : pointPlaneValue a b c x - pointPlaneValue a b c y ≠ 0 := by
        intro same
        have equal : pointPlaneValue a b c x = pointPlaneValue a b c y :=
          sub_eq_zero.mp same
        rw [equal] at opposite
        nlinarith [sq_nonneg (pointPlaneValue a b c y)]
      have tEquals : t = pointPlaneValue a b c x /
          (pointPlaneValue a b c x - pointPlaneValue a b c y) := by
        have relation : t * (pointPlaneValue a b c x - pointPlaneValue a b c y) =
            pointPlaneValue a b c x := by linarith
        exact (eq_div_iff_mul_eq denominator).mpr relation
      change containsNondegenerate a b c (segment3Point x y t) = true at containsP
      rw [tEquals] at containsP
      simp [edgeAgainstTriangle, dxZero, dyZero, opposite, containsP]

#print axioms edgeAgainst_complete
end Tess
