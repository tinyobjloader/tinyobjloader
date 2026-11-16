import Tess.InPlane

/-! Triangles sharing a vertex `v`: any common point other than `v` forces a point of one
triangle's opposite edge (not `v`) to lie in the other triangle. A point `p ≠ v` of a triangle
`v a1 a2` lies on a ray from `v` through a point `x` of the opposite edge; two such rays that
coincide put the nearer of the two edge points inside the other triangle. -/
namespace Tess

theorem cone_decomp (v a1 a2 p : Point3) (h : Hull3 v a1 a2 p) (hne : p ≠ v) :
    ∃ x : Point3, (∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ x = segment3Point a1 a2 s) ∧
      ∃ l : Rat, 0 < l ∧ l ≤ 1 ∧ p = segment3Point v x l := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hs, hx, hy, hz⟩ := h
  have hl : 0 < β + γ := by
    by_contra hh
    have hb : β = 0 := by linarith
    have hg : γ = 0 := by linarith
    apply hne
    have ha : α = 1 := by linarith
    subst hb hg ha
    cases p; cases v
    simp only [Point3.mk.injEq] at hx hy hz ⊢
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  refine ⟨segment3Point a1 a2 (γ / (β + γ)), ⟨γ / (β + γ), div_nonneg hγ hl.le,
    (div_le_one hl).mpr (by linarith), rfl⟩, β + γ, hl, by linarith, ?_⟩
  have hαe : α = 1 - (β + γ) := by linarith
  cases p
  simp only [segment3Point, Point3.mk.injEq] at hx hy hz ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hx, hαe]; field_simp; ring
  · rw [hy, hαe]; field_simp; ring
  · rw [hz, hαe]; field_simp; ring

/-- Two coinciding rays from the shared vertex: the nearer edge point lies in the other triangle. -/
theorem shared_vertex_contact (v a1 a2 b1 b2 p : Point3) (hA : Hull3 v a1 a2 p)
    (hB : Hull3 v b1 b2 p) (hne : p ≠ v) :
    (∃ y : Point3, Hull3 v a1 a2 y ∧ (∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ y = segment3Point b1 b2 s) ∧ y ≠ v) ∨
    (∃ x : Point3, Hull3 v b1 b2 x ∧ (∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ x = segment3Point a1 a2 s) ∧ x ≠ v) := by
  obtain ⟨x, ⟨sx, sx0, sx1, hxe⟩, l, l0, l1, hpl⟩ := cone_decomp v a1 a2 p hA hne
  obtain ⟨y, ⟨sy, sy0, sy1, hye⟩, m, m0, m1, hpm⟩ := cone_decomp v b1 b2 p hB hne
  have hxA : Hull3 v a1 a2 x := by
    rw [hxe]
    exact hull3_segment v a1 a2 a1 a2 (hull3_vertex1 _ _ _) (hull3_vertex2 _ _ _) sx sx0 sx1
  have hyB : Hull3 v b1 b2 y := by
    rw [hye]
    exact hull3_segment v b1 b2 b1 b2 (hull3_vertex1 _ _ _) (hull3_vertex2 _ _ _) sy sy0 sy1
  have hvA : Hull3 v a1 a2 v := hull3_vertex0 _ _ _
  have hvB : Hull3 v b1 b2 v := hull3_vertex0 _ _ _
  have hcoord : segment3Point v x l = segment3Point v y m := hpl.symm.trans hpm
  simp only [segment3Point, Point3.mk.injEq] at hcoord
  obtain ⟨c1, c2, c3⟩ := hcoord
  have vec_eq : ∀ (k : Rat) (hk : 0 < k) (u w : Point3), (∀ t : Rat, True) →
      k * (w.x - v.x) = (u.x - v.x) → k * (w.y - v.y) = (u.y - v.y) → k * (w.z - v.z) = (u.z - v.z) →
      u = segment3Point v w k := by
    intro k hk u w _ e1 e2 e3
    cases u; cases w; cases v
    simp only [segment3Point, Point3.mk.injEq] at e1 e2 e3 ⊢
    exact ⟨by linarith, by linarith, by linarith⟩
  rcases le_total l m with hlm | hlm
  · left
    have hk : 0 < l / m := div_pos l0 m0
    have hyv : y = segment3Point v x (l / m) :=
      vec_eq (l / m) hk y x (fun _ => trivial) (by field_simp; linarith) (by field_simp; linarith)
        (by field_simp; linarith)
    refine ⟨y, ?_, ⟨sy, sy0, sy1, hye⟩, ?_⟩
    · rw [hyv]
      exact hull3_segment v a1 a2 v x hvA hxA _ hk.le ((div_le_one m0).mpr hlm)
    · intro hyv0
      apply hne
      rw [hpm, hyv0]; cases v; simp [segment3Point]
  · right
    have hk : 0 < m / l := div_pos m0 l0
    have hxv : x = segment3Point v y (m / l) :=
      vec_eq (m / l) hk x y (fun _ => trivial) (by field_simp; linarith) (by field_simp; linarith)
        (by field_simp; linarith)
    refine ⟨x, ?_, ⟨sx, sx0, sx1, hxe⟩, ?_⟩
    · rw [hxv]
      exact hull3_segment v b1 b2 v y hvB hyB _ hk.le ((div_le_one l0).mpr hlm)
    · intro hxv0
      apply hne
      rw [hpl, hxv0]; cases v; simp [segment3Point]

end Tess
