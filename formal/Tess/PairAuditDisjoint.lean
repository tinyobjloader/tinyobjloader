import Tess.TriangleMeet
import Tess.TriangleContainsBridge
import Tess.IntersectionCompleteness
import Tess.PairAuditCoplanar

noncomputable section
namespace Tess
open RealGeometry

/-- Counterclockwise normalization of a nondegenerate triangle. -/
def norm3 (a b c : Point2) : Point2 × Point2 × Point2 :=
  if 0 < orient a b c then (a, b, c) else (a, c, b)

/-- Real image of a normalized triangle. -/
def triR (a b c : Point2) : Set P2 :=
  closedTriangle (realPoint2 (norm3 a b c).1) (realPoint2 (norm3 a b c).2.1)
    (realPoint2 (norm3 a b c).2.2)

theorem orient_norm3_pos (a b c : Point2) (h : orient a b c ≠ 0) :
    0 < RealGeometry.orient (realPoint2 (norm3 a b c).1) (realPoint2 (norm3 a b c).2.1)
      (realPoint2 (norm3 a b c).2.2) := by
  unfold norm3
  by_cases hp : 0 < orient a b c
  · simp only [hp, if_true]
    rw [orient_realPoint2]; exact_mod_cast hp
  · simp only [hp, if_false]
    rw [orient_realPoint2]
    have hneg : orient a b c < 0 := lt_of_le_of_ne (not_lt.mp hp) h
    have : orient a c b = - orient a b c := by dsimp only [orient]; ring
    rw [this]; exact_mod_cast (neg_pos.mpr hneg)

theorem contains2_triR (a b c p : Point2) (h : orient a b c ≠ 0) :
    contains2 a b c p = true ↔ realPoint2 p ∈ triR a b c := by
  unfold triR norm3
  by_cases hp : 0 < orient a b c
  · simp only [hp, if_true]; exact contains2_iff_closedTriangle_of_pos a b c p hp
  · simp only [hp, if_false]
    exact contains2_iff_closedTriangle_of_neg a b c p (lt_of_le_of_ne (not_lt.mp hp) h)

/-- Closed segment membership, direction-free. -/
def OnSeg (x y q : P2) : Prop := ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ q = interpolate x y s

theorem OnSeg.symm {x y q : P2} (h : OnSeg x y q) : OnSeg y x q := by
  obtain ⟨s, s0, s1, e⟩ := h
  refine ⟨1 - s, by linarith, by linarith, ?_⟩
  rw [e]; apply Prod.ext <;> simp only [interpolate] <;> ring

/-- Edge contact of the normalized triangle is edge contact of the original triangle. -/
theorem onEdge_norm3 (a b c : Point2) (q : P2)
    (h : OnEdge (realPoint2 (norm3 a b c).1) (realPoint2 (norm3 a b c).2.1)
      (realPoint2 (norm3 a b c).2.2) q) :
    OnSeg (realPoint2 a) (realPoint2 b) q ∨ OnSeg (realPoint2 b) (realPoint2 c) q ∨
    OnSeg (realPoint2 c) (realPoint2 a) q := by
  unfold norm3 at h
  by_cases hp : 0 < orient a b c
  · simp only [hp, if_true] at h
    exact h
  · simp only [hp, if_false] at h
    rcases h with h | h | h
    · exact Or.inr (Or.inr (OnSeg.symm h))
    · exact Or.inr (Or.inl (OnSeg.symm h))
    · exact Or.inl (OnSeg.symm h)

def tri3 (a0 a1 a2 : Point2) (k : Nat) : Point2 := if k = 0 then a0 else if k = 1 then a1 else a2

theorem norm3_vertices (a b c : Point2) :
    ((norm3 a b c).1 = a) ∧
    (((norm3 a b c).2.1 = b ∧ (norm3 a b c).2.2 = c) ∨
     ((norm3 a b c).2.1 = c ∧ (norm3 a b c).2.2 = b)) := by
  unfold norm3
  by_cases hp : 0 < orient a b c <;> simp [hp]

/-- Two nondegenerate coplanar projected triangles with no vertex of either in the other and no
pair of closed-intersecting edges have disjoint closed regions. -/
theorem rational_triangles_disjoint (a0 a1 a2 b0 b1 b2 : Point2)
    (hA : orient a0 a1 a2 ≠ 0) (hB : orient b0 b1 b2 ≠ 0)
    (hav : ∀ k, k < 3 → contains2 b0 b1 b2 (tri3 a0 a1 a2 k) = false)
    (hbv : ∀ k, k < 3 → contains2 a0 a1 a2 (tri3 b0 b1 b2 k) = false)
    (he : ∀ k l, k < 3 → l < 3 →
      closedIntersection (tri3 a0 a1 a2 k) (tri3 a0 a1 a2 ((k + 1) % 3))
        (tri3 b0 b1 b2 l) (tri3 b0 b1 b2 ((l + 1) % 3)) = false) :
    ¬ ∃ p : P2, p ∈ triR a0 a1 a2 ∧ p ∈ triR b0 b1 b2 := by
  rintro ⟨p, hp1, hp2⟩
  have notB : ∀ x, (x = a0 ∨ x = a1 ∨ x = a2) → realPoint2 x ∉ triR b0 b1 b2 := by
    intro x hx hmem
    have key : contains2 b0 b1 b2 x = true := (contains2_triR _ _ _ _ hB).mpr hmem
    have e0 : contains2 b0 b1 b2 a0 = false := by simpa [tri3] using hav 0 (by norm_num)
    have e1 : contains2 b0 b1 b2 a1 = false := by simpa [tri3] using hav 1 (by norm_num)
    have e2 : contains2 b0 b1 b2 a2 = false := by simpa [tri3] using hav 2 (by norm_num)
    rcases hx with h | h | h
    · rw [h, e0] at key; exact absurd key (by decide)
    · rw [h, e1] at key; exact absurd key (by decide)
    · rw [h, e2] at key; exact absurd key (by decide)
  have notA0 : realPoint2 b0 ∉ triR a0 a1 a2 := by
    intro hmem
    have key : contains2 a0 a1 a2 b0 = true := (contains2_triR _ _ _ _ hA).mpr hmem
    have e0 : contains2 a0 a1 a2 b0 = false := by simpa [tri3] using hbv 0 (by norm_num)
    rw [e0] at key; exact absurd key (by decide)
  obtain ⟨n1, n23⟩ := norm3_vertices a0 a1 a2
  obtain ⟨m1, m23⟩ := norm3_vertices b0 b1 b2
  have hn1 : realPoint2 (norm3 a0 a1 a2).1 ∉ triR b0 b1 b2 := notB _ (Or.inl n1)
  have hn2 : realPoint2 (norm3 a0 a1 a2).2.1 ∉ triR b0 b1 b2 := by
    apply notB; rcases n23 with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hn3 : realPoint2 (norm3 a0 a1 a2).2.2 ∉ triR b0 b1 b2 := by
    apply notB; rcases n23 with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hm1 : realPoint2 (norm3 b0 b1 b2).1 ∉ triR a0 a1 a2 := by rw [m1]; exact notA0
  obtain ⟨q, hqA, hqB⟩ := triangles_meet_edges _ _ _ _ _ _ p (orient_norm3_pos _ _ _ hA)
    (orient_norm3_pos _ _ _ hB) hp1 hp2 hn1 hn2 hn3 hm1
  have segs := onEdge_norm3 _ _ _ q hqA
  have segs' := onEdge_norm3 _ _ _ q hqB
  have conflict : ∀ k l, k < 3 → l < 3 →
      OnSeg (realPoint2 (tri3 a0 a1 a2 k)) (realPoint2 (tri3 a0 a1 a2 ((k + 1) % 3))) q →
      OnSeg (realPoint2 (tri3 b0 b1 b2 l)) (realPoint2 (tri3 b0 b1 b2 ((l + 1) % 3))) q → False := by
    intro k l hk hl h1 h2
    have := he k l hk hl
    have hx := (closedIntersection_iff_real _ _ _ _).mpr ⟨q, h1, h2⟩
    rw [hx] at this; exact absurd this (by decide)
  rcases segs with s1 | s1 | s1 <;> rcases segs' with s2 | s2 | s2
  · exact conflict 0 0 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 0 1 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 0 2 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 1 0 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 1 1 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 1 2 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 2 0 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 2 1 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)
  · exact conflict 2 2 (by norm_num) (by norm_num) (by simpa [tri3] using s1) (by simpa [tri3] using s2)

theorem projAxis_orient_ne (m : ExactMesh) (f : Face) (pa : Nat) (h : PairAudit.projAxis m f = some pa) :
    orient (projectPoint3 pa (m.point f.a)) (projectPoint3 pa (m.point f.b))
      (projectPoint3 pa (m.point f.c)) ≠ 0 := by
  unfold PairAudit.projAxis firstProjectionAxis at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; assumption
  · split at h
    · simp only [Option.some.injEq] at h; subst h; assumption
    · split at h
      · simp only [Option.some.injEq] at h; subst h; assumption
      · simp at h

/-- Soundness of the coplanar branch (no shared vertex IDs): an accepted pair has disjoint
projected closed triangles. -/
theorem coplanar_disjoint_triangles_disjoint (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : PairAudit.projAxis m fa = some pa) (hpb : PairAudit.projAxis m fb = some pb)
    (hd : PairAudit.commonIds fa fb = [])
    (hcop : ((List.range 3).all fun k => decide (planeValue m fa (PairAudit.facePoint m fb k) = 0)) = true)
    (hok : PairAudit.pairOk m fa fb = true)
    (hidx : ∀ k, k < 3 → PairAudit.faceId fa k < m.points.size ∧ PairAudit.faceId fb k < m.points.size)
    (hnd : ∀ k, k < 3 →
      (PairAudit.withAxis m pa).project (PairAudit.faceId fa k) ≠
        (PairAudit.withAxis m pa).project (PairAudit.faceId fa ((k + 1) % 3)) ∧
      (PairAudit.withAxis m pa).project (PairAudit.faceId fb k) ≠
        (PairAudit.withAxis m pa).project (PairAudit.faceId fb ((k + 1) % 3)))
    (hBnd : orient (projectPoint3 pa (m.point fb.a)) (projectPoint3 pa (m.point fb.b))
      (projectPoint3 pa (m.point fb.c)) ≠ 0) :
    ¬ ∃ p : P2,
      p ∈ triR (projectPoint3 pa (m.point fa.a)) (projectPoint3 pa (m.point fa.b))
            (projectPoint3 pa (m.point fa.c)) ∧
      p ∈ triR (projectPoint3 pa (m.point fb.a)) (projectPoint3 pa (m.point fb.b))
            (projectPoint3 pa (m.point fb.c)) := by
  obtain ⟨hv1, hv2, hseg⟩ := PairAudit.coplanar_disjoint_accepted m fa fb pa pb hpa hpb hd hcop hok hidx hnd
  have hAnd := projAxis_orient_ne m fa pa hpa
  apply rational_triangles_disjoint _ _ _ _ _ _ hAnd hBnd
  · intro k hk
    have := hv1 k hk
    unfold PairAudit.containsPt containsProject at this
    interval_cases k <;> simpa [tri3, PairAudit.facePoint] using this
  · intro k hk
    have := hv2 k hk
    unfold PairAudit.containsPt containsProject at this
    interval_cases k <;> simpa [tri3, PairAudit.facePoint] using this
  · intro k l hk hl
    have := hseg k l hk hl
    interval_cases k <;> interval_cases l <;> exact this

end Tess
