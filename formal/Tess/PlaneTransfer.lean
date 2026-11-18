import Tess.BoxSeparation
import Tess.Orient3
import Tess.Projection
import Tess.TriangleExitQ
import Mathlib.Tactic.LinearCombination

/-! Transfer between 3D closed triangles (`Hull3`) and their axis projections (`Tri2`) for
points on the triangle's plane. Reduced to the `z` axis by cyclic coordinate rotation. -/
namespace Tess

/-- Rotate coordinates so that `axis` becomes the last one. -/
def rot (axis : Nat) (p : Point3) : Point3 :=
  ⟨p.coord ((axis + 1) % 3), p.coord ((axis + 2) % 3), p.coord axis⟩

def proj2 (p : Point3) : Point2 := ⟨p.x, p.y⟩

theorem projectPoint3_eq (axis : Nat) (p : Point3) : projectPoint3 axis p = proj2 (rot axis p) := rfl

theorem orient3_rot (axis : Nat) (h : axis < 3) (a b c d : Point3) :
    orient3 (rot axis a) (rot axis b) (rot axis c) (rot axis d) = orient3 a b c d := by
  interval_cases axis <;> simp only [rot, Point3.coord, orient3] <;> norm_num <;> ring

theorem hull3_rot (axis : Nat) (h : axis < 3) (a b c p : Point3) :
    Hull3 (rot axis a) (rot axis b) (rot axis c) (rot axis p) ↔ Hull3 a b c p := by
  unfold Hull3
  interval_cases axis <;> simp only [rot, Point3.coord] <;> norm_num <;>
    constructor <;> rintro ⟨u, v, w, hu, hv, hw, hs, h1, h2, h3⟩ <;> exact ⟨u, v, w, hu, hv, hw, hs, by assumption, by assumption, by assumption⟩

/-- Plane equation in coordinates: `orient3` is the dot product of the normal with `a - p`. -/
theorem orient3_normal (a b c p : Point3) :
    orient3 a b c p =
      ((b.y - a.y) * (c.z - a.z) - (b.z - a.z) * (c.y - a.y)) * (a.x - p.x) +
      ((b.z - a.z) * (c.x - a.x) - (b.x - a.x) * (c.z - a.z)) * (a.y - p.y) +
      ((b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)) * (a.z - p.z) := by
  simp only [orient3]; ring

theorem orient_proj2_hull (a b c : Point3) (u v w : Rat) (hs : u + v + w = 1) (p : Point3)
    (hx : p.x = u * a.x + v * b.x + w * c.x) (hy : p.y = u * a.y + v * b.y + w * c.y) :
    orient (proj2 a) (proj2 b) (proj2 p) = w * orient (proj2 a) (proj2 b) (proj2 c) ∧
    orient (proj2 b) (proj2 c) (proj2 p) = u * orient (proj2 a) (proj2 b) (proj2 c) ∧
    orient (proj2 c) (proj2 a) (proj2 p) = v * orient (proj2 a) (proj2 b) (proj2 c) := by
  have hu : u = 1 - v - w := by linarith
  subst hu
  simp only [orient, proj2, hx, hy]
  refine ⟨by ring, by ring, by ring⟩

theorem hull_tri2 (a b c p : Point3) (h : Hull3 a b c p) :
    Tri2 (proj2 a) (proj2 b) (proj2 c) (proj2 p) := by
  obtain ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩ := h
  obtain ⟨e1, e2, e3⟩ := orient_proj2_hull a b c u v w hs p hx hy
  unfold Tri2
  rw [e1, e2, e3]
  rcases le_total 0 (orient (proj2 a) (proj2 b) (proj2 c)) with hD | hD
  · left; exact ⟨mul_nonneg hw hD, mul_nonneg hu hD, mul_nonneg hv hD⟩
  · right; exact ⟨mul_nonpos_of_nonneg_of_nonpos hw hD, mul_nonpos_of_nonneg_of_nonpos hu hD,
      mul_nonpos_of_nonneg_of_nonpos hv hD⟩

/-- Plane points with equal projections coincide when the normal's `z` component is nonzero. -/
theorem plane_inj (a b c p q : Point3)
    (hn : orient (proj2 a) (proj2 b) (proj2 c) ≠ 0)
    (hp : orient3 a b c p = 0) (hq : orient3 a b c q = 0)
    (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  rw [orient3_normal] at hp hq
  have hz : p.z = q.z := by
    have h0 : (((b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x))) * (q.z - p.z) = 0 := by
      rw [hx, hy] at hp
      linear_combination hp - hq
    have := (mul_eq_zero.mp h0).resolve_left (by simpa [orient, proj2] using hn)
    linarith
  cases p; cases q; simp_all

theorem tri2_hull (a b c p : Point3) (hn : orient (proj2 a) (proj2 b) (proj2 c) ≠ 0)
    (hp : orient3 a b c p = 0) (ht : Tri2 (proj2 a) (proj2 b) (proj2 c) (proj2 p)) :
    Hull3 a b c p := by
  set Δ := orient (proj2 a) (proj2 b) (proj2 c) with hΔ
  have tot := orient_total (proj2 a) (proj2 b) (proj2 c) (proj2 p)
  have bx := bary_x (proj2 a) (proj2 b) (proj2 c) (proj2 p)
  have by_ := bary_y (proj2 a) (proj2 b) (proj2 c) (proj2 p)
  -- weights
  let u := orient (proj2 b) (proj2 c) (proj2 p) / Δ
  let v := orient (proj2 c) (proj2 a) (proj2 p) / Δ
  let w := orient (proj2 a) (proj2 b) (proj2 p) / Δ
  have hu : 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w := by
    unfold Tri2 at ht
    rcases ht with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hpos : 0 < Δ := lt_of_le_of_ne (by linarith) (Ne.symm hn)
      exact ⟨div_nonneg h2 hpos.le, div_nonneg h3 hpos.le, div_nonneg h1 hpos.le⟩
    · have hneg : Δ < 0 := lt_of_le_of_ne (by linarith) hn
      exact ⟨div_nonneg_of_nonpos h2 hneg.le, div_nonneg_of_nonpos h3 hneg.le,
        div_nonneg_of_nonpos h1 hneg.le⟩
  have hs : u + v + w = 1 := by
    show _ / Δ + _ / Δ + _ / Δ = 1
    rw [← add_div, ← add_div]
    have : orient (proj2 b) (proj2 c) (proj2 p) + orient (proj2 c) (proj2 a) (proj2 p) +
        orient (proj2 a) (proj2 b) (proj2 p) = Δ := by linarith
    rw [this, div_self hn]
  -- the combination point
  let q : Point3 := ⟨u * a.x + v * b.x + w * c.x, u * a.y + v * b.y + w * c.y,
    u * a.z + v * b.z + w * c.z⟩
  have hqx : p.x = q.x := by
    show p.x = u * a.x + v * b.x + w * c.x
    show p.x = orient (proj2 b) (proj2 c) (proj2 p) / Δ * a.x + _ / Δ * b.x + _ / Δ * c.x
    field_simp
    rw [hΔ]
    simp only [proj2] at bx ⊢
    linear_combination bx
  have hqy : p.y = q.y := by
    show p.y = u * a.y + v * b.y + w * c.y
    show p.y = orient (proj2 b) (proj2 c) (proj2 p) / Δ * a.y + _ / Δ * b.y + _ / Δ * c.y
    field_simp
    rw [hΔ]
    simp only [proj2] at by_ ⊢
    linear_combination by_
  have hqp : orient3 a b c q = 0 := by
    rw [orient3_normal]
    have e : ∀ (n0 n1 n2 : Rat), True := fun _ _ _ => trivial
    have hu' : u = 1 - v - w := by linarith
    simp only [q]
    rw [hu']
    ring
  have := plane_inj a b c p q hn hp hqp hqx hqy
  rw [this]
  exact ⟨u, v, w, hu.1, hu.2.1, hu.2.2, hs, rfl, rfl, rfl⟩

theorem rot_injective (axis : Nat) (h : axis < 3) (p q : Point3) (e : rot axis p = rot axis q) :
    p = q := by
  interval_cases axis <;> simp only [rot, Point3.coord] at e <;> norm_num at e <;>
    obtain ⟨⟨p1, p2, p3⟩⟩ := p <;> obtain ⟨⟨q1, q2, q3⟩⟩ := q <;> simp_all

theorem hull_tri2_axis (axis : Nat) (h : axis < 3) (a b c p : Point3) (hh : Hull3 a b c p) :
    Tri2 (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) (projectPoint3 axis p) := by
  simp only [projectPoint3_eq]
  exact hull_tri2 _ _ _ _ ((hull3_rot axis h a b c p).mpr hh)

theorem tri2_hull_axis (axis : Nat) (h : axis < 3) (a b c p : Point3)
    (hn : orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) ≠ 0)
    (hp : orient3 a b c p = 0)
    (ht : Tri2 (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c)
      (projectPoint3 axis p)) : Hull3 a b c p := by
  simp only [projectPoint3_eq] at hn ht
  rw [← hull3_rot axis h]
  apply tri2_hull _ _ _ _ hn _ ht
  rw [orient3_rot axis h]; exact hp

theorem plane_inj_axis (axis : Nat) (h : axis < 3) (a b c p q : Point3)
    (hn : orient (projectPoint3 axis a) (projectPoint3 axis b) (projectPoint3 axis c) ≠ 0)
    (hp : orient3 a b c p = 0) (hq : orient3 a b c q = 0)
    (e : projectPoint3 axis p = projectPoint3 axis q) : p = q := by
  simp only [projectPoint3_eq] at hn e
  apply rot_injective axis h
  have hx : (rot axis p).x = (rot axis q).x := by simpa [proj2] using congrArg Point2.x e
  have hy : (rot axis p).y = (rot axis q).y := by simpa [proj2] using congrArg Point2.y e
  apply plane_inj _ _ _ _ _ hn _ _ hx hy
  · rw [orient3_rot axis h]; exact hp
  · rw [orient3_rot axis h]; exact hq

end Tess
