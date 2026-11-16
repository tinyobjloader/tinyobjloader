import Tess.Certificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-! Soundness of the auditor's exact closed AABB broadphase (`lib/tess/src/bounds.c`).
`tg_bounds` records, for each axis, the vertex index holding the minimum and the maximum
coordinate; `tg_boxes_separate` reports separation only on strict inequality
`high_a < low_b` or `high_b < low_a`. We prove that such a pair has no common point of the
closed triangles, so skipping it cannot hide a forbidden contact (strictness also excludes
shared vertices). Model-level statement over exact rationals. -/
namespace Tess

/-- Closed triangle (convex hull of three points) in 3D. -/
def Hull3 (a b c p : Point3) : Prop :=
  ∃ u v w : Rat, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
    p.x = u * a.x + v * b.x + w * c.x ∧ p.y = u * a.y + v * b.y + w * c.y ∧
    p.z = u * a.z + v * b.z + w * c.z

/-- Per-axis extremum witnesses, as recorded by `tg_bounds`. -/
structure AxisExtrema (a b c : Point3) (j : Nat) (lo hi : Point3) : Prop where
  lo_mem : lo = a ∨ lo = b ∨ lo = c
  hi_mem : hi = a ∨ hi = b ∨ hi = c
  lo_le : lo.coord j ≤ a.coord j ∧ lo.coord j ≤ b.coord j ∧ lo.coord j ≤ c.coord j
  hi_ge : a.coord j ≤ hi.coord j ∧ b.coord j ≤ hi.coord j ∧ c.coord j ≤ hi.coord j

theorem hull_coord_le (a b c p hi : Point3) (j : Nat) (hj : j < 3) (h : Hull3 a b c p)
    (ge : a.coord j ≤ hi.coord j ∧ b.coord j ≤ hi.coord j ∧ c.coord j ≤ hi.coord j) :
    p.coord j ≤ hi.coord j := by
  obtain ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩ := h
  have key : ∀ (pa pb pc pp H : Rat), pa ≤ H → pb ≤ H → pc ≤ H →
      pp = u * pa + v * pb + w * pc → pp ≤ H := by
    intro pa pb pc pp H h1 h2 h3 e
    rw [e]
    nlinarith [mul_nonneg hu (sub_nonneg.2 h1), mul_nonneg hv (sub_nonneg.2 h2), mul_nonneg hw (sub_nonneg.2 h3), show H * (u + v + w) = H by rw [hs, mul_one]]
  interval_cases j
  · exact key _ _ _ _ _ ge.1 ge.2.1 ge.2.2 hx
  · exact key _ _ _ _ _ ge.1 ge.2.1 ge.2.2 hy
  · exact key _ _ _ _ _ ge.1 ge.2.1 ge.2.2 hz

theorem hull_coord_ge (a b c p lo : Point3) (j : Nat) (hj : j < 3) (h : Hull3 a b c p)
    (le : lo.coord j ≤ a.coord j ∧ lo.coord j ≤ b.coord j ∧ lo.coord j ≤ c.coord j) :
    lo.coord j ≤ p.coord j := by
  obtain ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩ := h
  have key : ∀ (pa pb pc pp L : Rat), L ≤ pa → L ≤ pb → L ≤ pc →
      pp = u * pa + v * pb + w * pc → L ≤ pp := by
    intro pa pb pc pp L h1 h2 h3 e
    rw [e]
    nlinarith [mul_nonneg hu (sub_nonneg.2 h1), mul_nonneg hv (sub_nonneg.2 h2), mul_nonneg hw (sub_nonneg.2 h3), show L * (u + v + w) = L by rw [hs, mul_one]]
  interval_cases j
  · exact key _ _ _ _ _ le.1 le.2.1 le.2.2 hx
  · exact key _ _ _ _ _ le.1 le.2.1 le.2.2 hy
  · exact key _ _ _ _ _ le.1 le.2.1 le.2.2 hz

/-- A strict gap between the recorded extrema of two triangles on one axis excludes any common
point (and any shared vertex). -/
theorem boxes_separate_disjoint (a b c d e f : Point3) (j : Nat) (hj : j < 3)
    (loA hiA loB hiB : Point3)
    (EA : AxisExtrema a b c j loA hiA) (EB : AxisExtrema d e f j loB hiB)
    (hsep : hiA.coord j < loB.coord j ∨ hiB.coord j < loA.coord j) :
    ¬ ∃ p : Point3, Hull3 a b c p ∧ Hull3 d e f p := by
  rintro ⟨p, h1, h2⟩
  have a1 := hull_coord_le a b c p hiA j hj h1 EA.hi_ge
  have a2 := hull_coord_ge a b c p loA j hj h1 EA.lo_le
  have b1 := hull_coord_le d e f p hiB j hj h2 EB.hi_ge
  have b2 := hull_coord_ge d e f p loB j hj h2 EB.lo_le
  rcases hsep with h | h <;> linarith

end Tess
