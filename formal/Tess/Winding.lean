import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Real geometric foundation for the oriented-boundary coverage argument.
No domain-coverage assumption appears in the triangle winding identity. -/
noncomputable section
namespace Tess.RealGeometry
abbrev P2 := ℝ × ℝ
def orient (a b c : P2) : ℝ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)
def rayDelta (a b side : ℝ) : ℤ :=
  if a<0 ∧ 0<b ∧ 0<side then 1
  else if b<0 ∧ 0<a ∧ side<0 then -1 else 0

theorem triangle_ray_identity (a b c x y z : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : 0 < x+y+z) (hbalance : x*c+y*a+z*b=0) :
    rayDelta a b x + rayDelta b c y + rayDelta c a z =
      if 0<x ∧ 0<y ∧ 0<z then 1 else 0 := by
  have pxc : 0 < |x| * |c| := mul_pos (abs_pos.mpr hx) (abs_pos.mpr hc)
  have pya : 0 < |y| * |a| := mul_pos (abs_pos.mpr hy) (abs_pos.mpr ha)
  have pzb : 0 < |z| * |b| := mul_pos (abs_pos.mpr hz) (abs_pos.mpr hb)
  rcases lt_or_gt_of_ne ha with ha|ha <;>
    rcases lt_or_gt_of_ne hb with hb|hb <;>
    rcases lt_or_gt_of_ne hc with hc|hc <;>
    rcases lt_or_gt_of_ne hx with hx|hx <;>
    rcases lt_or_gt_of_ne hy with hy|hy <;>
    rcases lt_or_gt_of_ne hz with hz|hz <;>
    simp_all [rayDelta, abs_of_neg, abs_of_pos, not_lt_of_ge ha.le, not_lt_of_ge hb.le,
      not_lt_of_ge hc.le, not_lt_of_ge hx.le, not_lt_of_ge hy.le, not_lt_of_ge hz.le] <;> nlinarith

def edgeRay (a b p : P2) : ℤ := rayDelta (a.2-p.2) (b.2-p.2) (orient a b p)
def triangleWinding (a b c p : P2) : ℤ := edgeRay a b p + edgeRay b c p + edgeRay c a p

theorem orient_sum (a b c p : P2) :
    orient a b p + orient b c p + orient c a p = orient a b c := by
  simp only [orient]; ring

theorem orient_height_relation (a b c p : P2) :
    orient a b p * (c.2-p.2) + orient b c p * (a.2-p.2) +
      orient c a p * (b.2-p.2) = 0 := by
  simp only [orient]; ring

/-- A positively oriented triangle contributes its interior indicator away
from the finite arrangement of edge-supporting and vertex-horizontal lines. -/
theorem triangle_winding_indicator (a b c p : P2)
    (positive : 0 < orient a b c)
    (ha : a.2 ≠ p.2) (hb : b.2 ≠ p.2) (hc : c.2 ≠ p.2)
    (hab : orient a b p ≠ 0) (hbc : orient b c p ≠ 0) (hca : orient c a p ≠ 0) :
    triangleWinding a b c p =
      if 0<orient a b p ∧ 0<orient b c p ∧ 0<orient c a p then 1 else 0 := by
  exact triangle_ray_identity (a.2-p.2) (b.2-p.2) (c.2-p.2)
    (orient a b p) (orient b c p) (orient c a p)
    (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb) (sub_ne_zero.mpr hc)
    hab hbc hca (by rw [orient_sum]; exact positive) (orient_height_relation a b c p)

#print axioms triangle_winding_indicator
end Tess.RealGeometry
