import Tess.NoncoplanarComplete

/-! Two noncoplanar closed triangles sharing an edge `x y` meet exactly in that edge. This is the
geometric fact behind the auditor's shared-edge allowance for faces meeting at a crease. -/
namespace Tess

theorem shared_edge_intersection (x y u w p : Point3) (hnc : orient3 x y w u ≠ 0) :
    (Hull3 x y u p ∧ Hull3 x y w p) ↔ ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p = segment3Point x y t := by
  constructor
  · rintro ⟨hA, hB⟩
    have hpl : orient3 x y w p = 0 := hull3_plane x y w p hB
    obtain ⟨α, β, γ, hα, hβ, hγ, hs, hx, hy, hz⟩ := hA
    have hαeq : α = 1 - β - γ := by linarith
    have key : orient3 x y w p = γ * orient3 x y w u := by
      rw [orient3_normal x y w p, hx, hy, hz, orient3_normal x y w u, hαeq]
      ring
    have hγ0 : γ = 0 := by
      rw [key] at hpl
      exact (mul_eq_zero.mp hpl).resolve_right hnc
    subst hγ0
    refine ⟨β, hβ, by linarith, ?_⟩
    cases p
    simp only [segment3Point, Point3.mk.injEq]
    simp only [] at hx hy hz
    refine ⟨?_, ?_, ?_⟩ <;> [rw [hx]; rw [hy]; rw [hz]] <;> rw [hαeq] <;> ring
  · rintro ⟨t, t0, t1, rfl⟩
    exact ⟨hull3_segment x y u x y (hull3_vertex0 _ _ _) (hull3_vertex1 _ _ _) t t0 t1,
      hull3_segment x y w x y (hull3_vertex0 _ _ _) (hull3_vertex1 _ _ _) t t0 t1⟩

end Tess
