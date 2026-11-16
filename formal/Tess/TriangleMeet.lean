import Tess.Barycentric
import Tess.Subdivision

/-! Real-plane lemma behind the auditor's coplanar branch: if two closed triangles
meet, then a vertex of one lies in the other or an edge of one meets an edge of the other.
Proof: a segment from a point of a triangle to a point outside exits through an edge
("exit lemma"); applying it first to a vertex of the second triangle and then to an
edge endpoint gives an edge-edge contact. -/
noncomputable section
namespace Tess.RealGeometry
open Set

/-- `orient a b (interpolate p v t)` is the same affine interpolation of the values. -/
theorem orient_interpolate (a b p v : P2) (t : ℝ) :
    orient a b (interpolate p v t) = (1 - t) * orient a b p + t * orient a b v := by
  unfold orient interpolate; ring

/-- Per-edge exit parameter: the first parameter at which the affine value `(1-t)g + t h`
reaches zero when `h < 0`, and `1` (no constraint) otherwise. -/
def tau (g h : ℝ) : ℝ := if h < 0 then g / (g - h) else 1

theorem tau_props (g h : ℝ) (hg : 0 ≤ g) :
    0 ≤ tau g h ∧ tau g h ≤ 1 ∧ (h < 0 → tau g h < 1 ∧ (1 - tau g h) * g + tau g h * h = 0) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ tau g h → 0 ≤ (1 - t) * g + t * h) := by
  unfold tau
  by_cases hh : h < 0
  · simp only [hh, if_true]
    have hd : 0 < g - h := by linarith
    have hq : g / (g - h) * (g - h) = g := div_mul_cancel₀ _ hd.ne'
    refine ⟨div_nonneg hg hd.le, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩
    · rw [div_le_one hd]; linarith
    · rw [div_lt_one hd]; linarith
    · nlinarith
    · intro t ht0 ht1
      nlinarith
  · simp only [hh, if_false]
    refine ⟨zero_le_one, le_rfl, fun h' => h'.elim, ?_⟩
    intro t ht0 ht1
    have hh' : 0 ≤ h := not_lt.mp hh
    nlinarith

theorem exit_params (g0 g1 g2 h0 h1 h2 : ℝ) (p0 : 0 ≤ g0) (p1 : 0 ≤ g1) (p2 : 0 ≤ g2)
    (hv : h0 < 0 ∨ h1 < 0 ∨ h2 < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ (1 - t) * g0 + t * h0 ∧ 0 ≤ (1 - t) * g1 + t * h1 ∧
      0 ≤ (1 - t) * g2 + t * h2 ∧
      ((1 - t) * g0 + t * h0 = 0 ∨ (1 - t) * g1 + t * h1 = 0 ∨ (1 - t) * g2 + t * h2 = 0) := by
  obtain ⟨a0, a1, a2, a3⟩ := tau_props g0 h0 p0
  obtain ⟨b0, b1, b2, b3⟩ := tau_props g1 h1 p1
  obtain ⟨c0, c1, c2, c3⟩ := tau_props g2 h2 p2
  set t := min (tau g0 h0) (min (tau g1 h1) (tau g2 h2)) with ht
  have t0 : 0 ≤ t := le_min a0 (le_min b0 c0)
  have tle0 : t ≤ tau g0 h0 := min_le_left _ _
  have tle1 : t ≤ tau g1 h1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have tle2 : t ≤ tau g2 h2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have t1 : t ≤ 1 := le_trans tle0 a1
  have hlt : t < 1 := by
    rcases hv with h | h | h
    · exact lt_of_le_of_lt tle0 (a2 h).1
    · exact lt_of_le_of_lt tle1 (b2 h).1
    · exact lt_of_le_of_lt tle2 (c2 h).1
  refine ⟨t, t0, t1, a3 t t0 tle0, b3 t t0 tle1, c3 t t0 tle2, ?_⟩
  have hmin : t = tau g0 h0 ∨ t = tau g1 h1 ∨ t = tau g2 h2 := by
    rcases min_choice (tau g0 h0) (min (tau g1 h1) (tau g2 h2)) with h | h
    · left; rw [ht, h]
    · rcases min_choice (tau g1 h1) (tau g2 h2) with h' | h'
      · right; left; rw [ht, h, h']
      · right; right; rw [ht, h, h']
  rcases hmin with h | h | h
  · left
    by_cases hh : h0 < 0
    · rw [h]; exact (a2 hh).2
    · exfalso; have : tau g0 h0 = 1 := by simp [tau, hh]
      linarith
  · right; left
    by_cases hh : h1 < 0
    · rw [h]; exact (b2 hh).2
    · exfalso; have : tau g1 h1 = 1 := by simp [tau, hh]
      linarith
  · right; right
    by_cases hh : h2 < 0
    · rw [h]; exact (c2 hh).2
    · exfalso; have : tau g2 h2 = 1 := by simp [tau, hh]
      linarith

/-- Barycentric coordinates are read off by the edge orientations. -/
theorem orient_edges_combo3 (a b c : P2) (u v w : ℝ) (total : u + v + w = 1) :
    orient a b (combo3 a b c u v w) = w * orient a b c ∧
    orient b c (combo3 a b c u v w) = u * orient a b c ∧
    orient c a (combo3 a b c u v w) = v * orient a b c := by
  have h1 : orient a b a = 0 := by unfold orient; ring
  have h2 : orient a b b = 0 := by unfold orient; ring
  have h3 : orient b c b = 0 := by unfold orient; ring
  have h4 : orient b c c = 0 := by unfold orient; ring
  have h5 : orient c a a = 0 := by unfold orient; ring
  have h6 : orient c a c = 0 := by unfold orient; ring
  have h7 : orient b c a = orient a b c := by unfold orient; ring
  have h8 : orient c a b = orient a b c := by unfold orient; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [orient_combo3 _ _ _ _ _ _ _ _ total, h1, h2]; ring
  · rw [orient_combo3 _ _ _ _ _ _ _ _ total, h3, h4, h7]; ring
  · rw [orient_combo3 _ _ _ _ _ _ _ _ total, h5, h6, h8]; ring

/-- A point of a positive triangle on the line of an edge lies on that edge segment. -/
theorem on_edge (a b c q : P2) (pos : 0 < orient a b c) (hq : q ∈ closedTriangle a b c) :
    (orient a b q = 0 → ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ q = interpolate a b s) ∧
    (orient b c q = 0 → ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ q = interpolate b c s) ∧
    (orient c a q = 0 → ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ q = interpolate c a s) := by
  obtain ⟨u, v, w, hu, hv, hw, total, rfl⟩ := (barycentric a b c q pos).mp hq
  obtain ⟨e1, e2, e3⟩ := orient_edges_combo3 a b c u v w total
  have hD : orient a b c ≠ 0 := pos.ne'
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hw0 : w = 0 := by
      rw [e1] at h; exact (mul_eq_zero.mp h).resolve_right hD
    have hc : u = 1 - v := by linarith
    refine ⟨v, hv, by linarith, ?_⟩
    subst hw0; subst hc
    apply Prod.ext <;> simp only [combo3, interpolate, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  · have hu0 : u = 0 := by
      rw [e2] at h; exact (mul_eq_zero.mp h).resolve_right hD
    have hc : v = 1 - w := by linarith
    refine ⟨w, hw, by linarith, ?_⟩
    subst hu0; subst hc
    apply Prod.ext <;> simp only [combo3, interpolate, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  · have hv0 : v = 0 := by
      rw [e3] at h; exact (mul_eq_zero.mp h).resolve_right hD
    have hc : w = 1 - u := by linarith
    refine ⟨u, hu, by linarith, ?_⟩
    subst hv0; subst hc
    apply Prod.ext <;> simp only [combo3, interpolate, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- Exit lemma at triangle level: the segment from a point of the triangle to an outside point
leaves through an edge. -/
theorem triangle_exit (a b c p v : P2) (pos : 0 < orient a b c) (hp : p ∈ closedTriangle a b c)
    (hv : v ∉ closedTriangle a b c) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ interpolate p v t ∈ closedTriangle a b c ∧
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
        (interpolate p v t = interpolate a b s ∨ interpolate p v t = interpolate b c s ∨
         interpolate p v t = interpolate c a s) := by
  obtain ⟨hp0, hp1, hp2⟩ := hp
  have hneg : orient a b v < 0 ∨ orient b c v < 0 ∨ orient c a v < 0 := by
    by_contra hcon
    push Not at hcon
    exact hv ⟨hcon.1, hcon.2.1, hcon.2.2⟩
  obtain ⟨t, t0, t1, k0, k1, k2, hz⟩ := exit_params _ _ _ _ _ _ hp0 hp1 hp2 hneg
  rw [← orient_interpolate] at k0 k1 k2
  have hq : interpolate p v t ∈ closedTriangle a b c := ⟨k0, k1, k2⟩
  have := on_edge a b c _ pos hq
  refine ⟨t, t0, t1, hq, ?_⟩
  rcases hz with h | h | h
  · obtain ⟨s, s0, s1, e⟩ := this.1 (by rw [orient_interpolate]; exact h); exact ⟨s, s0, s1, Or.inl e⟩
  · obtain ⟨s, s0, s1, e⟩ := this.2.1 (by rw [orient_interpolate]; exact h); exact ⟨s, s0, s1, Or.inr (Or.inl e)⟩
  · obtain ⟨s, s0, s1, e⟩ := this.2.2 (by rw [orient_interpolate]; exact h); exact ⟨s, s0, s1, Or.inr (Or.inr e)⟩

/-- Closed triangles are convex. -/
theorem closedTriangle_interp_mem (a b c p d : P2) (hp : p ∈ closedTriangle a b c)
    (hd : d ∈ closedTriangle a b c) (t : ℝ) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    interpolate p d t ∈ closedTriangle a b c := by
  obtain ⟨p0, p1, p2⟩ := hp
  obtain ⟨d0, d1, d2⟩ := hd
  refine ⟨?_, ?_, ?_⟩ <;> rw [orient_interpolate] <;> nlinarith

/-- `q` lies on one of the three edge segments of triangle `a b c`. -/
def OnEdge (a b c q : P2) : Prop :=
  (∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ q = interpolate a b s) ∨
  (∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ q = interpolate b c s) ∨
  (∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ q = interpolate c a s)

theorem interpolate_sub (x y q q2 : P2) (s mu : ℝ) (hq : q = interpolate x y s)
    (hq2 : q2 = interpolate q x mu) :
    q2 = interpolate x y ((1 - mu) * s) := by
  subst hq hq2
  apply Prod.ext <;> simp only [interpolate] <;> ring

/-- Two positive closed triangles that meet, with no vertex of either in the other, have
meeting edges. -/
theorem triangles_meet_edges (a b c d e f p : P2) (pos1 : 0 < orient a b c) (pos2 : 0 < orient d e f)
    (hp1 : p ∈ closedTriangle a b c) (hp2 : p ∈ closedTriangle d e f)
    (ha : a ∉ closedTriangle d e f) (hb : b ∉ closedTriangle d e f) (hc : c ∉ closedTriangle d e f)
    (hd : d ∉ closedTriangle a b c) :
    ∃ q, OnEdge a b c q ∧ OnEdge d e f q := by
  have hd2 : d ∈ closedTriangle d e f := by
    have e1 : orient d e d = 0 := by unfold orient; ring
    have e2 : orient e f d = orient d e f := by unfold orient; ring
    have e3 : orient f d d = 0 := by unfold orient; ring
    exact ⟨e1.ge, by rw [e2]; exact pos2.le, e3.ge⟩
  obtain ⟨t, t0, t1, hq1, s, s0, s1, hE⟩ := triangle_exit a b c p d pos1 hp1 hd
  have hq2 : interpolate p d t ∈ closedTriangle d e f :=
    closedTriangle_interp_mem d e f p d hp2 hd2 t t0 t1
  -- the first endpoint of the exited edge is a vertex of triangle 1, hence outside triangle 2
  have step : ∀ x y : P2, x ∉ closedTriangle d e f → interpolate p d t = interpolate x y s →
      ∃ q, (∃ s' : ℝ, 0 ≤ s' ∧ s' ≤ 1 ∧ q = interpolate x y s') ∧ OnEdge d e f q := by
    intro x y hx hxy
    obtain ⟨mu, m0, m1, hm, s2, s20, s21, hE2⟩ :=
      triangle_exit d e f (interpolate p d t) x pos2 hq2 hx
    refine ⟨_, ⟨(1 - mu) * s, by nlinarith, by nlinarith, interpolate_sub x y _ _ s mu hxy rfl⟩, ?_⟩
    rcases hE2 with h | h | h
    · exact Or.inl ⟨s2, s20, s21, h⟩
    · exact Or.inr (Or.inl ⟨s2, s20, s21, h⟩)
    · exact Or.inr (Or.inr ⟨s2, s20, s21, h⟩)
  rcases hE with h | h | h
  · obtain ⟨q, hq, hq'⟩ := step a b ha h; exact ⟨q, Or.inl hq, hq'⟩
  · obtain ⟨q, hq, hq'⟩ := step b c hb h; exact ⟨q, Or.inr (Or.inl hq), hq'⟩
  · obtain ⟨q, hq, hq'⟩ := step c a hc h; exact ⟨q, Or.inr (Or.inr hq), hq'⟩

end Tess.RealGeometry
