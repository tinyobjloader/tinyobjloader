import Tess.PairAuditCoplanarShared
import Tess.PairAuditAllowed

/-! Coplanar triangles `(X,Y,U)` and `(X,Y,W)` sharing the edge `X Y`: a point of the first triangle
on the open edge `(Y,W)` of the second forces a contact that the auditor rejects. -/
namespace Tess

theorem segmentPoint_comp_end (P Q : Point2) (s t : Rat) :
    segmentPoint (segmentPoint P Q s) Q t = segmentPoint P Q (s + t * (1 - s)) := by
  simp only [segmentPoint]; congr 1 <;> ring

theorem orient_on_edge_ab (a b c : Point2) (s : Rat) :
    orient a b (segmentPoint a b s) = 0 ∧ orient b c (segmentPoint a b s) = (1 - s) * orient a b c ∧
    orient c a (segmentPoint a b s) = s * orient a b c := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [orient, segmentPoint] <;> ring

theorem tri2_cyc (a b c p : Point2) : Tri2 a b c p ↔ Tri2 b c a p := by
  unfold Tri2
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h3, h1⟩
    · exact Or.inr ⟨h2, h3, h1⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h3, h1, h2⟩
    · exact Or.inr ⟨h3, h1, h2⟩

theorem tri2_on_edge_ab (a b c : Point2) (s : Rat) (s0 : 0 ≤ s) (s1 : s ≤ 1) :
    Tri2 a b c (segmentPoint a b s) := by
  obtain ⟨e1, e2, e3⟩ := orient_on_edge_ab a b c s
  unfold Tri2
  rw [e1, e2, e3]
  rcases le_total 0 (orient a b c) with h | h
  · left; exact ⟨le_rfl, mul_nonneg (sub_nonneg.2 s1) h, mul_nonneg s0 h⟩
  · right; exact ⟨le_rfl, mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 s1) h,
      mul_nonpos_of_nonneg_of_nonpos s0 h⟩

theorem tri2_on_edge_bc (a b c : Point2) (s : Rat) (s0 : 0 ≤ s) (s1 : s ≤ 1) :
    Tri2 a b c (segmentPoint b c s) :=
  (tri2_cyc a b c _).mpr (tri2_on_edge_ab b c a s s0 s1)

theorem tri2_on_edge_ca (a b c : Point2) (s : Rat) (s0 : 0 ≤ s) (s1 : s ≤ 1) :
    Tri2 a b c (segmentPoint c a s) :=
  (tri2_cyc a b c _).mpr ((tri2_cyc b c a _).mpr (tri2_on_edge_ab c a b s s0 s1))

/-- A point `r ≠ Y` of the triangle `(X,Y,U)` on the edge `Y W` of the coplanar triangle `(X,Y,W)`,
with `W ∉ (X,Y,U)`, `U ∉ (X,Y,W)` and no contact between the edges `U X` and `Y W`, is impossible. -/
theorem shared_edge_exit (X Y U W r : Point3) (pa : Nat) (hlt : pa < 3)
    (hndA : orient (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa U) ≠ 0)
    (hndB : orient (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa W) ≠ 0)
    (hWA : ¬ Tri2 (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa U) (projectPoint3 pa W))
    (hUB : ¬ Tri2 (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa W) (projectPoint3 pa U))
    (hconf : ¬ ∃ z : Point2, RationalSegment (projectPoint3 pa U) (projectPoint3 pa X) z ∧
      RationalSegment (projectPoint3 pa Y) (projectPoint3 pa W) z)
    (hr : Hull3 X Y U r) (s : Rat) (s0 : 0 ≤ s) (s1 : s ≤ 1) (hrs : r = segment3Point Y W s)
    (hrY : r ≠ Y) : False := by
  have hs : 0 < s := by
    rcases eq_or_lt_of_le s0 with h | h
    · exfalso; apply hrY; rw [hrs, ← h, segment3Point_zero]
    · exact h
  set X' := projectPoint3 pa X
  set Y' := projectPoint3 pa Y
  set U' := projectPoint3 pa U
  set W' := projectPoint3 pa W
  have hr2 : Tri2 X' Y' U' (projectPoint3 pa r) := hull_tri2_axis pa hlt X Y U r hr
  obtain ⟨t, t0, t1, _, s2, s20, s21, hedge⟩ := tri2_exit X' Y' U' (projectPoint3 pa r) W' hndA hr2 hWA
  have hz : segmentPoint (projectPoint3 pa r) W' t = segmentPoint Y' W' (s + t * (1 - s)) := by
    rw [hrs, projectPoint3_segment, segmentPoint_comp_end]
  set σ := s + t * (1 - s) with hσ
  have σ0 : 0 < σ := by nlinarith
  have σ1 : σ ≤ 1 := by nlinarith
  have hYW : Y' ≠ W' := by
    intro h; apply hndB; simp only [orient, h]; ring
  rcases hedge with h | h | h
  · -- z on the shared edge X Y: forces σ = 0
    have e1 := (orient_on_edge_ab X' Y' U' s2).1
    have e2 : orient X' Y' (segmentPoint Y' W' σ) = σ * orient X' Y' W' := by
      simp only [orient, segmentPoint]; ring
    rw [hz] at h
    rw [h] at e2
    rw [e1] at e2
    have : σ * orient X' Y' W' = 0 := e2.symm
    exact hndB ((mul_eq_zero.mp this).resolve_left σ0.ne')
  · -- z on Y U: W or U would lie in the other triangle
    rw [hz] at h
    have hcoord := congrArg Point2.x h
    have hcoord2 := congrArg Point2.y h
    simp only [segmentPoint] at hcoord hcoord2
    have pt_eq : ∀ p q : Point2, p.x = q.x → p.y = q.y → p = q := by
      intro p q hx hy; cases p; cases q; simp_all
    by_cases hs20 : s2 = 0
    · exfalso
      rw [hs20] at hcoord hcoord2
      apply hYW
      apply pt_eq
      · have : σ * (W'.x - Y'.x) = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_left σ0.ne'
        linarith
      · have : σ * (W'.y - Y'.y) = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_left σ0.ne'
        linarith
    · have s2pos : 0 < s2 := lt_of_le_of_ne s20 (Ne.symm hs20)
      rcases le_total (s2 / σ) 1 with hk | hk
      · apply hWA
        have : W' = segmentPoint Y' U' (s2 / σ) := by
          apply pt_eq <;> simp only [segmentPoint] <;> field_simp <;> linarith
        rw [this]
        exact tri2_on_edge_bc _ _ _ _ (div_nonneg s2pos.le σ0.le) hk
      · apply hUB
        have hk' : σ / s2 ≤ 1 := by
          rw [div_le_one s2pos]
          have := (one_le_div σ0).mp hk
          linarith
        have : U' = segmentPoint Y' W' (σ / s2) := by
          apply pt_eq <;> simp only [segmentPoint] <;> field_simp <;> linarith
        rw [this]
        exact tri2_on_edge_bc _ _ _ _ (div_nonneg σ0.le s2pos.le) hk'
  · exact hconf ⟨segmentPoint (projectPoint3 pa r) W' t, ⟨s2, s20, s21, h⟩, ⟨σ, σ0.le, σ1, hz⟩⟩

/-- Geometric core for coplanar faces sharing the edge `X Y`: the common points lie on that edge. -/
theorem coplanar_shared_edge_geom (X Y U W p : Point3) (pa : Nat) (hlt : pa < 3)
    (hndA : orient (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa U) ≠ 0)
    (hndB : orient (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa W) ≠ 0)
    (hWA : ¬ Tri2 (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa U) (projectPoint3 pa W))
    (hUB : ¬ Tri2 (projectPoint3 pa X) (projectPoint3 pa Y) (projectPoint3 pa W) (projectPoint3 pa U))
    (hconf1 : ¬ ∃ z : Point2, RationalSegment (projectPoint3 pa U) (projectPoint3 pa X) z ∧
      RationalSegment (projectPoint3 pa Y) (projectPoint3 pa W) z)
    (hconf2 : ¬ ∃ z : Point2, RationalSegment (projectPoint3 pa W) (projectPoint3 pa X) z ∧
      RationalSegment (projectPoint3 pa Y) (projectPoint3 pa U) z)
    (hA : Hull3 X Y U p) (hB : Hull3 X Y W p) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p = segment3Point X Y t := by
  by_cases hpX : p = X
  · exact ⟨0, le_rfl, by norm_num, by rw [hpX, segment3Point_zero]⟩
  rcases shared_vertex_contact' X Y U Y W p hA hB hpX with
    ⟨r, hrA, ⟨s, s0, s1, hrs⟩, hrX, μ, μ0, μ1, hpμ⟩ | ⟨q, hqB, ⟨s, s0, s1, hqs⟩, hqX, l, l0, l1, hpl⟩
  · by_cases hrY : r = Y
    · exact ⟨μ, μ0.le, μ1, by rw [hpμ, hrY]⟩
    · exact (shared_edge_exit X Y U W r pa hlt hndA hndB hWA hUB hconf1 hrA s s0 s1 hrs hrY).elim
  · by_cases hqY : q = Y
    · exact ⟨l, l0.le, l1, by rw [hpl, hqY]⟩
    · exact (shared_edge_exit X Y W U q pa hlt hndB hndA hUB hWA hconf2 hqB s s0 s1 hqs hqY).elim

namespace PairAudit

/-- Id-level form of the geometric core: the audit facts for the triangles `(ix,iy,iu)` and
`(ix,iy,iw)` give the shared-edge conclusion. -/
theorem coplanar_shared_edge_of_conflicts (m : ExactMesh) (pa : Nat) (hlt : pa < 3)
    (ix iy iu iw : Nat)
    (hidx : ix < m.points.size ∧ iy < m.points.size ∧ iu < m.points.size ∧ iw < m.points.size)
    (hxy : ix ≠ iy) (hxu : ix ≠ iu) (hxw : ix ≠ iw) (hyu : iy ≠ iu) (hyw : iy ≠ iw) (huw : iu ≠ iw)
    (hndA : orient (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iu)) ≠ 0)
    (hndB : orient (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iw)) ≠ 0)
    (hWA : ¬ Tri2 (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iu)) (projectPoint3 pa (m.point iw)))
    (hUB : ¬ Tri2 (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iw)) (projectPoint3 pa (m.point iu)))
    (hc1 : segmentConflict (withAxis m pa) iu ix iy iw = false)
    (hc2 : segmentConflict (withAxis m pa) iw ix iy iu = false)
    (p : Point3) (hA : Hull3 (m.point ix) (m.point iy) (m.point iu) p)
    (hB : Hull3 (m.point ix) (m.point iy) (m.point iw) p) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p = segment3Point (m.point ix) (m.point iy) t := by
  have ptne : ∀ P Q : Point3, orient (projectPoint3 pa P) (projectPoint3 pa Q) (projectPoint3 pa Q) = 0 →
      True := fun _ _ _ => trivial
  have ne_of_orient : ∀ P Q R : Point2, orient P Q R ≠ 0 → P ≠ Q ∧ Q ≠ R ∧ R ≠ P := by
    intro P Q R h
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply h <;> simp only [orient] <;> ring
  obtain ⟨nXY, nYU, nUX⟩ := ne_of_orient _ _ _ hndA
  obtain ⟨_, nYW, nWX⟩ := ne_of_orient _ _ _ hndB
  have mk : ∀ (a b c d : Nat), a < m.points.size → b < m.points.size → c < m.points.size →
      d < m.points.size → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      (withAxis m pa).project a ≠ (withAxis m pa).project b →
      (withAxis m pa).project c ≠ (withAxis m pa).project d →
      segmentConflict (withAxis m pa) a b c d = false →
      ¬ ∃ z : Point2, RationalSegment ((withAxis m pa).project a) ((withAxis m pa).project b) z ∧
        RationalSegment ((withAxis m pa).project c) ((withAxis m pa).project d) z := by
    intro a b c d ha hb hc hd hac had hbc hbd hab hcd hconf ⟨z, hz1, hz2⟩
    have hci : closedIntersection ((withAxis m pa).project a) ((withAxis m pa).project b)
        ((withAxis m pa).project c) ((withAxis m pa).project d) = true :=
      (closedIntersection_iff_rational _ _ _ _).mpr ⟨z, hz1, hz2⟩
    have := (segmentConflict_iff_closedIntersection (withAxis m pa) a b c d ⟨ha, hb, hc, hd⟩
      ⟨hab, hcd⟩ hac had hbc hbd).mpr hci
    rw [hconf] at this; exact absurd this (by decide)
  have hconf1 := mk iu ix iy iw hidx.2.2.1 hidx.1 hidx.2.1 hidx.2.2.2 hyu.symm huw hxy hxw nUX nYW hc1
  have hconf2 := mk iw ix iy iu hidx.2.2.2 hidx.1 hidx.2.1 hidx.2.2.1 hyw.symm huw.symm hxy hxu nWX nYU hc2
  exact coplanar_shared_edge_geom _ _ _ _ p pa hlt hndA hndB hWA hUB hconf1 hconf2 hA hB

theorem orient_swap_ab (a b c : Point2) : orient b a c = - orient a b c := by
  simp only [orient]; ring

theorem onSegment_swap (p q r : Point2) : onSegment p q r = onSegment q p r := by
  have h1 : (orient p q r = 0) ↔ (orient q p r = 0) := by
    rw [orient_swap_ab]; constructor <;> intro h <;> linarith
  have hb : ∀ a b x : Rat, between a b x ↔ between b a x := by
    intro a b x; unfold between; tauto
  have e : decide (orient p q r = 0) = decide (orient q p r = 0) := decide_eq_decide.mpr h1
  have e2 : decide (between p.x q.x r.x ∧ between p.y q.y r.y) =
      decide (between q.x p.x r.x ∧ between q.y p.y r.y) :=
    decide_eq_decide.mpr (and_congr (hb _ _ _) (hb _ _ _))
  unfold onSegment collinear
  rw [e, e2]

theorem segmentConflict_rev1 (m : ExactMesh) (a b c d : Nat) :
    segmentConflict m a b c d = segmentConflict m b a c d := by
  unfold segmentConflict
  have e1 : ((a = c && b = d) || (a = d && b = c)) = true ↔
      ((b = c && a = d) || (b = d && a = c)) = true := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  by_cases hc : ((a = c && b = d) || (a = d && b = c)) = true
  · have hc' : ((b = c && a = d) || (b = d && a = c)) = true := e1.mp hc
    simp only [hc, hc', ite_true]
  · have hc' : ¬ ((b = c && a = d) || (b = d && a = c)) = true := fun h => hc (e1.mpr h)
    simp only [hc, hc', ite_false]
    rw [onSegment_swap (m.project a) (m.project b) (m.project c),
        onSegment_swap (m.project a) (m.project b) (m.project d)]
    have o1 : orient (m.project b) (m.project a) (m.project c) *
        orient (m.project b) (m.project a) (m.project d) =
        orient (m.project a) (m.project b) (m.project c) * orient (m.project a) (m.project b) (m.project d) := by
      rw [orient_swap_ab, orient_swap_ab (m.project a) (m.project b) (m.project d)]; ring
    have o2 : orient (m.project c) (m.project d) (m.project b) *
        orient (m.project c) (m.project d) (m.project a) =
        orient (m.project c) (m.project d) (m.project a) * orient (m.project c) (m.project d) (m.project b) := by ring
    have d1 : decide (c ≠ b ∧ c ≠ a) = decide (c ≠ a ∧ c ≠ b) := decide_eq_decide.mpr and_comm
    have d2 : decide (d ≠ b ∧ d ≠ a) = decide (d ≠ a ∧ d ≠ b) := decide_eq_decide.mpr and_comm
    rw [o1, o2, d1, d2]
    generalize (decide (c ≠ a ∧ c ≠ b) && onSegment (m.project a) (m.project b) (m.project c)) = t1
    generalize (decide (d ≠ a ∧ d ≠ b) && onSegment (m.project a) (m.project b) (m.project d)) = t2
    generalize (decide (a ≠ c ∧ a ≠ d) && onSegment (m.project c) (m.project d) (m.project a)) = t3
    generalize (decide (b ≠ c ∧ b ≠ d) && onSegment (m.project c) (m.project d) (m.project b)) = t4
    generalize (decide (orient (m.project a) (m.project b) (m.project c) *
        orient (m.project a) (m.project b) (m.project d) < 0 ∧
        orient (m.project c) (m.project d) (m.project a) * orient (m.project c) (m.project d) (m.project b) < 0)) = t5
    cases t3 <;> cases t4 <;> cases t5 <;> simp

theorem segmentConflict_rev2 (m : ExactMesh) (a b c d : Nat) :
    segmentConflict m a b c d = segmentConflict m a b d c := by
  rw [segmentConflict_symm, segmentConflict_rev1, ← segmentConflict_symm]

theorem tri2_rot3 (P : Nat → Point2) (j : Nat) (hj : j < 3) (p : Point2) :
    Tri2 (P j) (P ((j + 1) % 3)) (P ((j + 2) % 3)) p ↔ Tri2 (P 0) (P 1) (P 2) p := by
  interval_cases j
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceMod]
    exact (tri2_cyc (P 0) (P 1) (P 2) p).symm
  · simp only [Nat.reduceAdd, Nat.reduceMod]
    exact ((tri2_cyc (P 0) (P 1) (P 2) p).trans (tri2_cyc (P 1) (P 2) (P 0) p)).symm

theorem tri2_swap23 (a b c p : Point2) : Tri2 a b c p ↔ Tri2 a c b p := by
  unfold Tri2
  have h1 := orient_swap_ab a c p
  have h2 := orient_swap_ab b c p
  have h3 := orient_swap_ab c a p
  have h4 := orient_swap_ab a b p
  constructor
  · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
    · right; refine ⟨?_, ?_, ?_⟩ <;> linarith
    · left; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro (⟨x, y, z⟩ | ⟨x, y, z⟩)
    · right; refine ⟨?_, ?_, ?_⟩ <;> linarith
    · left; refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem hull3_swap23 (a b c p : Point3) : Hull3 a b c p ↔ Hull3 a c b p := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩
    exact ⟨u, w, v, hu, hw, hv, by linarith, by rw [hx]; ring, by rw [hy]; ring, by rw [hz]; ring⟩
  · rintro ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩
    exact ⟨u, w, v, hu, hw, hv, by linarith, by rw [hx]; ring, by rw [hy]; ring, by rw [hz]; ring⟩

theorem allowed_false_off_edge (m : ExactMesh) (fa fb : Face) (ix iy : Nat)
    (hd : commonIds fa fb = [ix, iy] ∨ commonIds fa fb = [iy, ix]) (pa : Nat) (P : Point3)
    (hnd : orient (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa P) ≠ 0) : allowed m fa fb P = false := by
  by_contra h
  have hall : allowed m fa fb P = true := by simpa using h
  rcases allowed_sound m fa fb P hall with ⟨id, hid, hP⟩ | ⟨i, j, hij, t, t0, t1, hP⟩
  · apply hnd
    rcases hd with hd | hd <;> rw [hd] at hid <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hid <;>
      rcases hid with rfl | rfl <;> rw [← hP] <;> simp only [orient] <;> ring
  · apply hnd
    have hseg : ∀ (A B : Point3), (A = m.point ix ∧ B = m.point iy) ∨ (A = m.point iy ∧ B = m.point ix) →
        P = segment3Point A B t →
        orient (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy)) (projectPoint3 pa P) = 0 := by
      intro A B hAB hPe
      rw [hPe, projectPoint3_segment, orient_segmentPoint]
      rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [orient] <;> ring
    rcases hd with hd | hd <;> rw [hd] at hij <;> simp only [List.cons.injEq, and_true] at hij <;>
      obtain ⟨rfl, rfl⟩ := hij
    · exact hseg _ _ (Or.inl ⟨rfl, rfl⟩) hP
    · exact hseg _ _ (Or.inr ⟨rfl, rfl⟩) hP

/-- Coplanar faces sharing the edge `ix iy` (listed consecutively in `fa`; `fb` traverses it in either
direction): an accepted pair meets only in that edge. -/
theorem accepted_coplanar_shared_edge (m : ExactMesh) (fa fb : Face) (pa : Nat) (hlt : pa < 3)
    (hpa : projAxis m fa = some pa) (hpb : ∃ pb, projAxis m fb = some pb)
    (ix iy iu iw j l : Nat) (hj : j < 3) (hl : l < 3)
    (hxj : faceId fa j = ix) (hyj : faceId fa ((j + 1) % 3) = iy) (huj : faceId fa ((j + 2) % 3) = iu)
    (hbl : faceId fb l = ix ∧
      ((faceId fb ((l + 1) % 3) = iy ∧ faceId fb ((l + 2) % 3) = iw) ∨
       (faceId fb ((l + 1) % 3) = iw ∧ faceId fb ((l + 2) % 3) = iy)))
    (hd : commonIds fa fb = [ix, iy] ∨ commonIds fa fb = [iy, ix])
    (hxy : ix ≠ iy) (hxu : ix ≠ iu) (hxw : ix ≠ iw) (hyu : iy ≠ iu) (hyw : iy ≠ iw) (huw : iu ≠ iw)
    (hAnd : orient (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iu)) ≠ 0)
    (hBnd : orient (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iw)) ≠ 0)
    (hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (hok : pairOk m fa fb = true)
    (hidx : ∀ k, k < 3 → faceId fa k < m.points.size ∧ faceId fb k < m.points.size)
    (p : Point3)
    (hpA : Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p)
    (hpB : Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p = segment3Point (m.point ix) (m.point iy) t := by
  obtain ⟨pb, hpb'⟩ := hpb
  unfold pairOk at hok
  rw [hpa, hpb'] at hok
  simp only [hcop, if_true, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff] at hok
  obtain ⟨⟨hpts, hsegs⟩, hshared⟩ := hok
  set PA : Nat → Point3 := fun k => m.point (faceId fa k) with hPA
  set PB : Nat → Point3 := fun k => m.point (faceId fb k) with hPB
  have hPA3 : Hull3 (PA 0) (PA 1) (PA 2) p := hpA
  have hPB3 : Hull3 (PB 0) (PB 1) (PB 2) p := hpB
  have jm1 : (j + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have jm2 : (j + 2) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have lm1 : (l + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have lm2 : (l + 2) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have e1 : ((l + 1) % 3 + 1) % 3 = (l + 2) % 3 := by omega
  have e1' : ((l + 2) % 3 + 1) % 3 = l := by omega
  have e2 : ((j + 1) % 3 + 1) % 3 = (j + 2) % 3 := by omega
  have e2' : ((j + 2) % 3 + 1) % 3 = j := by omega
  have hA' : Hull3 (m.point ix) (m.point iy) (m.point iu) p := by
    have := (hull3_rot3 PA j hj p).mpr hPA3
    simp only [hPA, hxj, hyj, huj] at this
    exact this
  have hcA : ∀ P, containsPt m fa pa P ↔
      Tri2 (projectPoint3 pa (PA 0)) (projectPoint3 pa (PA 1)) (projectPoint3 pa (PA 2)) (projectPoint3 pa P) := by
    intro P
    unfold containsPt containsProject
    rw [← contains2_iff_Tri2]
    rfl
  have hcB : ∀ P, containsPt m fb pa P ↔
      Tri2 (projectPoint3 pa (PB 0)) (projectPoint3 pa (PB 1)) (projectPoint3 pa (PB 2)) (projectPoint3 pa P) := by
    intro P
    unfold containsPt containsProject
    rw [← contains2_iff_Tri2]
    rfl
  have hallU := allowed_false_off_edge m fa fb ix iy hd pa (m.point iu) hAnd
  have hallW := allowed_false_off_edge m fa fb ix iy hd pa (m.point iw) hBnd
  have hfp : ∀ (f : Face) (k : Nat), facePoint m f k = m.point (faceId f k) := by
    intro f k; unfold facePoint faceId; rfl
  -- W not in A
  have hWcont : ∀ k, k < 3 → faceId fb k = iw → containsPt m fa pa (m.point iw) = false := by
    intro k hk hkw
    have h := (hpts k hk).2
    rw [hfp, hkw, hallW] at h
    simpa using h
  have hUcont : ∀ k, k < 3 → faceId fa k = iu → containsPt m fb pa (m.point iu) = false := by
    intro k hk hku
    have h := (hpts k hk).1
    rw [hfp, hku, hallU] at h
    simpa using h
  have hWA : ¬ Tri2 (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iu)) (projectPoint3 pa (m.point iw)) := by
    intro h
    have hh := (tri2_rot3 (fun k => projectPoint3 pa (PA k)) j hj _).mp (by
      simpa only [hPA, hxj, hyj, huj] using h)
    have : containsPt m fa pa (m.point iw) = true := (hcA _).mpr hh
    obtain ⟨k, hk, hkw⟩ : ∃ k, k < 3 ∧ faceId fb k = iw := by
      rcases hbl.2 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact ⟨(l + 2) % 3, lm2, h2⟩
      · exact ⟨(l + 1) % 3, lm1, h1⟩
    rw [hWcont k hk hkw] at this; exact absurd this (by decide)
  have hUB : ¬ Tri2 (projectPoint3 pa (m.point ix)) (projectPoint3 pa (m.point iy))
      (projectPoint3 pa (m.point iw)) (projectPoint3 pa (m.point iu)) := by
    intro h
    have hcont : containsPt m fb pa (m.point iu) = true := by
      apply (hcB _).mpr
      apply (tri2_rot3 (fun k => projectPoint3 pa (PB k)) l hl _).mp
      rcases hbl.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [hPB, hbl.1, h1, h2]; exact h
      · simp only [hPB, hbl.1, h1, h2]; exact (tri2_swap23 _ _ _ _).mp h
    rw [hUcont ((j + 2) % 3) jm2 huj] at hcont; exact absurd hcont (by decide)
  have hB' : Hull3 (m.point ix) (m.point iy) (m.point iw) p := by
    have := (hull3_rot3 PB l hl p).mpr hPB3
    rcases hbl.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [hPB, hbl.1, h1, h2] at this; exact this
    · simp only [hPB, hbl.1, h1, h2] at this; exact (hull3_swap23 _ _ _ _).mpr this
  -- conflicts
  have hc1 : segmentConflict (withAxis m pa) iu ix iy iw = false := by
    have base := hsegs ((j + 2) % 3) jm2
    rcases hbl.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := base ((l + 1) % 3) lm1
      rw [e2', huj, hxj, e1, h1, h2] at this; exact this
    · have := base ((l + 1) % 3) lm1
      rw [e2', huj, hxj, e1, h1, h2] at this
      rw [segmentConflict_rev2]; exact this
  have hc2 : segmentConflict (withAxis m pa) iw ix iy iu = false := by
    have base := hsegs ((j + 1) % 3) jm1
    rcases hbl.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := base ((l + 2) % 3) lm2
      rw [e2, hyj, huj, e1', hbl.1, h2] at this
      rw [segmentConflict_symm]; exact this
    · have := base l hl
      rw [e2, hyj, huj, hbl.1, h1] at this
      rw [segmentConflict_symm, segmentConflict_rev2]
      exact this
  have hix : ix < m.points.size := by rw [← hxj]; exact (hidx j hj).1
  have hiy : iy < m.points.size := by rw [← hyj]; exact (hidx _ jm1).1
  have hiu : iu < m.points.size := by rw [← huj]; exact (hidx _ jm2).1
  have hiw : iw < m.points.size := by
    rcases hbl.2 with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [← h2]; exact (hidx _ lm2).2
    · rw [← h1]; exact (hidx _ lm1).2
  exact coplanar_shared_edge_of_conflicts m pa hlt ix iy iu iw ⟨hix, hiy, hiu, hiw⟩ hxy hxu hxw hyu hyw huw
    hAnd hBnd hWA hUB hc1 hc2 p hA' hB'

end PairAudit

end Tess
