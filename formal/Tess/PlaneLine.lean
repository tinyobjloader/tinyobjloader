import Tess.PlaneTransfer

/-! Points common to two non-parallel planes are collinear: in the axis projection of the first
plane, any three common points have zero projected orientation. Used for the degenerate
configuration where an edge of each triangle lies in the other's plane. -/
namespace Tess

/-- Core `z`-frame statement. `P Q R` lie on both planes; `V` lies on the first plane but not the
second, so the planes are not parallel. -/
theorem collinear_z (a b c d e f P Q R V : Point3)
    (hn : orient (proj2 d) (proj2 e) (proj2 f) ≠ 0)
    (hP1 : orient3 d e f P = 0) (hQ1 : orient3 d e f Q = 0) (hR1 : orient3 d e f R = 0)
    (hP2 : orient3 a b c P = 0) (hQ2 : orient3 a b c Q = 0) (hR2 : orient3 a b c R = 0)
    (hV1 : orient3 d e f V = 0) (hV2 : orient3 a b c V ≠ 0) :
    orient (proj2 P) (proj2 Q) (proj2 R) = 0 := by
  set n0 := (e.y - d.y) * (f.z - d.z) - (e.z - d.z) * (f.y - d.y)
  set n1 := (e.z - d.z) * (f.x - d.x) - (e.x - d.x) * (f.z - d.z)
  set n2 := (e.x - d.x) * (f.y - d.y) - (e.y - d.y) * (f.x - d.x) with hn2
  set m0 := (b.y - a.y) * (c.z - a.z) - (b.z - a.z) * (c.y - a.y)
  set m1 := (b.z - a.z) * (c.x - a.x) - (b.x - a.x) * (c.z - a.z)
  set m2 := (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)
  have hn2ne : n2 ≠ 0 := by simpa [orient, proj2, hn2] using hn
  rw [orient3_normal] at hP1 hQ1 hR1 hP2 hQ2 hR2 hV1 hV2
  set α := m0 * n2 - m2 * n0
  set β := m1 * n2 - m2 * n1
  -- differences relative to P
  have k1 : α * (Q.x - P.x) + β * (Q.y - P.y) = 0 := by
    linear_combination (-n2) * hQ2 + n2 * hP2 + m2 * hQ1 - m2 * hP1
  have k2 : α * (R.x - P.x) + β * (R.y - P.y) = 0 := by
    linear_combination (-n2) * hR2 + n2 * hP2 + m2 * hR1 - m2 * hP1
  have k3 : α * (V.x - P.x) + β * (V.y - P.y) ≠ 0 := by
    intro h
    apply hV2
    have h2 : n2 * (m0 * (a.x - V.x) + m1 * (a.y - V.y) + m2 * (a.z - V.z)) = 0 := by
      linear_combination n2 * hP2 - h - m2 * hP1 + m2 * hV1
    exact (mul_eq_zero.mp h2).resolve_left hn2ne
  have hab : α ≠ 0 ∨ β ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply k3
    rw [hcon.1, hcon.2]; ring
  have c1 : α * (orient (proj2 P) (proj2 Q) (proj2 R)) = 0 := by
    simp only [orient, proj2]
    linear_combination (R.y - P.y) * k1 - (Q.y - P.y) * k2
  have c2 : β * (orient (proj2 P) (proj2 Q) (proj2 R)) = 0 := by
    simp only [orient, proj2]
    linear_combination (Q.x - P.x) * k2 - (R.x - P.x) * k1
  rcases hab with h | h
  · exact (mul_eq_zero.mp c1).resolve_left h
  · exact (mul_eq_zero.mp c2).resolve_left h

theorem collinear_axis (axis : Nat) (h : axis < 3) (a b c d e f P Q R V : Point3)
    (hn : orient (projectPoint3 axis d) (projectPoint3 axis e) (projectPoint3 axis f) ≠ 0)
    (hP1 : orient3 d e f P = 0) (hQ1 : orient3 d e f Q = 0) (hR1 : orient3 d e f R = 0)
    (hP2 : orient3 a b c P = 0) (hQ2 : orient3 a b c Q = 0) (hR2 : orient3 a b c R = 0)
    (hV1 : orient3 d e f V = 0) (hV2 : orient3 a b c V ≠ 0) :
    orient (projectPoint3 axis P) (projectPoint3 axis Q) (projectPoint3 axis R) = 0 := by
  simp only [projectPoint3_eq] at hn ⊢
  apply collinear_z (rot axis a) (rot axis b) (rot axis c) (rot axis d) (rot axis e) (rot axis f)
    _ _ _ (rot axis V) hn
  all_goals first
    | (rw [orient3_rot axis h]; assumption)
    | skip

theorem collinear_param (P Q R : Point2) (hne : P ≠ Q) (h : orient P Q R = 0) :
    ∃ μ : Rat, R = segmentPoint P Q μ := by
  have pt_eq : ∀ p q : Point2, p.x = q.x → p.y = q.y → p = q := by
    intro p q hx hy; cases p; cases q; simp_all
  simp only [orient] at h
  by_cases hx : Q.x - P.x = 0
  · have hy : Q.y - P.y ≠ 0 := by
      intro hy; apply hne; apply pt_eq <;> linarith
    refine ⟨(R.y - P.y) / (Q.y - P.y), pt_eq _ _ ?_ ?_⟩
    · simp only [segmentPoint]
      have : (R.y - P.y) * (Q.x - P.x) = (R.x - P.x) * (Q.y - P.y) := by linarith
      have h3 : (R.x - P.x) * (Q.y - P.y) = 0 := by rw [← this, hx]; ring
      have h4 : R.x - P.x = 0 := (mul_eq_zero.mp h3).resolve_right hy
      rw [hx]; linarith
    · simp only [segmentPoint]; field_simp; ring
  · refine ⟨(R.x - P.x) / (Q.x - P.x), pt_eq _ _ ?_ ?_⟩
    · simp only [segmentPoint]; field_simp; ring
    · simp only [segmentPoint]
      field_simp
      linarith

theorem segment3Point_inj (x y : Point3) (hne : x ≠ y) (t t' : Rat)
    (h : segment3Point x y t = segment3Point x y t') : t = t' := by
  simp only [segment3Point, Point3.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  by_contra hn
  apply hne
  have hd : t - t' ≠ 0 := sub_ne_zero.mpr hn
  have e1 : (t - t') * (y.x - x.x) = 0 := by linarith
  have e2 : (t - t') * (y.y - x.y) = 0 := by linarith
  have e3 : (t - t') * (y.z - x.z) = 0 := by linarith
  have a1 := (mul_eq_zero.mp e1).resolve_left hd
  have a2 := (mul_eq_zero.mp e2).resolve_left hd
  have a3 := (mul_eq_zero.mp e3).resolve_left hd
  cases x; cases y
  simp only [Point3.mk.injEq]
  simp only [] at a1 a2 a3
  exact ⟨by linarith, by linarith, by linarith⟩

end Tess
