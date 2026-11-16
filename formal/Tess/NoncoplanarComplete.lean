import Tess.PlaneTransfer
import Tess.TriangleContact
import Tess.Plane

/-! Completeness of the exact noncoplanar triangle-contact predicate in general position:
if neither triangle has a vertex on the other's plane and `noncoplanarTrianglesConflict` is
false, the closed triangles share no point. (Soundness is `TriangleContactSoundness`.)
Proof: a common point `p` either gives a point of `B ∩ plane A` outside `A` — the exit lemma in
plane `A` then yields an edge point of `A` inside `B`, a strict plane cut flagged by the
predicate — or `B ∩ plane A ⊆ A`, in which case a strict plane cut of an edge of `B` lies in
`A`, again flagged. -/
namespace Tess

theorem hull3_plane (a b c p : Point3) (h : Hull3 a b c p) : orient3 a b c p = 0 := by
  obtain ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩ := h
  rw [orient3_normal, hx, hy, hz]
  have hu' : u = 1 - v - w := by linarith
  subst hu'
  ring

theorem hull3_affine (a b c : Point3) (Y0 Y1 Y2 : Point3) (p : Point3) (h : Hull3 Y0 Y1 Y2 p) :
    ∃ u v w : Rat, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
      orient3 a b c p = u * orient3 a b c Y0 + v * orient3 a b c Y1 + w * orient3 a b c Y2 := by
  obtain ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩ := h
  refine ⟨u, v, w, hu, hv, hw, hs, ?_⟩
  rw [orient3_normal a b c p, hx, hy, hz]
  simp only [orient3_normal a b c Y0, orient3_normal a b c Y1, orient3_normal a b c Y2]
  have hu' : u = 1 - v - w := by linarith
  subst hu'
  ring

theorem hull3_vertex0 (a b c : Point3) : Hull3 a b c a := ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, by norm_num, by ring, by ring, by ring⟩
theorem hull3_vertex1 (a b c : Point3) : Hull3 a b c b := ⟨0, 1, 0, le_rfl, by norm_num, le_rfl, by norm_num, by ring, by ring, by ring⟩
theorem hull3_vertex2 (a b c : Point3) : Hull3 a b c c := ⟨0, 0, 1, le_rfl, le_rfl, by norm_num, by norm_num, by ring, by ring, by ring⟩

theorem hull3_segment (a b c p s : Point3) (hp : Hull3 a b c p) (hs : Hull3 a b c s)
    (t : Rat) (t0 : 0 ≤ t) (t1 : t ≤ 1) : Hull3 a b c (segment3Point p s t) := by
  obtain ⟨u, v, w, hu, hv, hw, hsum, hx, hy, hz⟩ := hp
  obtain ⟨u', v', w', hu', hv', hw', hsum', hx', hy', hz'⟩ := hs
  refine ⟨(1 - t) * u + t * u', (1 - t) * v + t * v', (1 - t) * w + t * w',
    by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_, ?_, ?_⟩
  · simp only [segment3Point, hx, hx']; ring
  · simp only [segment3Point, hy, hy']; ring
  · simp only [segment3Point, hz, hz']; ring

theorem orient3_segment (a b c p s : Point3) (t : Rat) :
    orient3 a b c (segment3Point p s t) = (1 - t) * orient3 a b c p + t * orient3 a b c s := by
  simp only [orient3_normal, segment3Point]; ring

theorem projectPoint3_segment (axis : Nat) (p s : Point3) (t : Rat) :
    projectPoint3 axis (segment3Point p s t) =
      segmentPoint (projectPoint3 axis p) (projectPoint3 axis s) t := by
  unfold projectPoint3 segment3Point segmentPoint Point3.coord
  split_ifs <;> simp_all

theorem firstProjectionAxis_lt (a b c : Point3) (pa : Nat) (h : firstProjectionAxis a b c = some pa) :
    pa < 3 ∧ orient (projectPoint3 pa a) (projectPoint3 pa b) (projectPoint3 pa c) ≠ 0 := by
  unfold firstProjectionAxis at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨by norm_num, by assumption⟩
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨by norm_num, by assumption⟩
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨by norm_num, by assumption⟩
      · simp at h

theorem containsNondegenerate_of_hull (a b c r : Point3) (pa : Nat)
    (h : firstProjectionAxis a b c = some pa) (hr : Hull3 a b c r) :
    containsNondegenerate a b c r = true := by
  unfold containsNondegenerate
  rw [h]
  simp only [containsProject]
  exact (contains2_iff_Tri2 _ _ _ _).mpr (hull_tri2_axis pa (firstProjectionAxis_lt a b c pa h).1 a b c r hr)

/-- A common point of an edge `x y` and the triangle, with both edge endpoints off the plane,
is the strict plane cut and is flagged by `edgeAgainstTriangle`. -/
theorem cut_flag (a b c x y r : Point3) (pa : Nat) (hpa : firstProjectionAxis a b c = some pa)
    (hx : orient3 a b c x ≠ 0) (hy : orient3 a b c y ≠ 0) (hr : Hull3 a b c r)
    (hseg : ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ r = segment3Point x y s) :
    edgeAgainstTriangle a b c x y = true := by
  obtain ⟨s, s0, s1, hs⟩ := hseg
  have hplane := hull3_plane a b c r hr
  rw [hs, orient3_segment] at hplane
  have hxy : orient3 a b c x * orient3 a b c y < 0 := by
    by_contra hnn
    have hnn' : 0 ≤ orient3 a b c x * orient3 a b c y := not_lt.mp hnn
    rcases lt_or_gt_of_ne hx with h1 | h1 <;> rcases lt_or_gt_of_ne hy with h2 | h2
    · rcases le_total s (1/2) with hs2 | hs2
      · nlinarith [mul_nonneg (sub_nonneg.2 s1) (neg_nonneg.2 h1.le), mul_nonneg s0 (neg_nonneg.2 h2.le)]
      · nlinarith [mul_nonneg (sub_nonneg.2 s1) (neg_nonneg.2 h1.le), mul_nonneg s0 (neg_nonneg.2 h2.le)]
    · nlinarith
    · nlinarith
    · rcases le_total s (1/2) with hs2 | hs2
      · nlinarith [mul_nonneg (sub_nonneg.2 s1) h1.le, mul_nonneg s0 h2.le]
      · nlinarith [mul_nonneg (sub_nonneg.2 s1) h1.le, mul_nonneg s0 h2.le]
  have hden : orient3 a b c x - orient3 a b c y ≠ 0 := by
    intro h
    have : orient3 a b c x = orient3 a b c y := by linarith
    rw [this] at hxy; nlinarith [sq_nonneg (orient3 a b c y)]
  have hsval : s = orient3 a b c x / (orient3 a b c x - orient3 a b c y) := by
    field_simp
    linarith
  unfold edgeAgainstTriangle pointPlaneValue
  simp only [hx, hy, if_false, hxy, if_true]
  rw [← hsval, ← hs]
  exact containsNondegenerate_of_hull a b c r pa hpa hr

/-- Edge/triangle contact flag, allowing endpoints on the plane but not the whole edge: a
common point `r` of the edge and the triangle is flagged by `edgeAgainstTriangle`. -/
theorem edge_flag (a b c x y r : Point3) (pa : Nat) (hpa : firstProjectionAxis a b c = some pa)
    (hnot : ¬ (orient3 a b c x = 0 ∧ orient3 a b c y = 0)) (hr : Hull3 a b c r)
    (hseg : ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ r = segment3Point x y s) :
    edgeAgainstTriangle a b c x y = true := by
  by_cases hx : orient3 a b c x = 0
  · have hy : orient3 a b c y ≠ 0 := fun h => hnot ⟨hx, h⟩
    obtain ⟨s, s0, s1, hs⟩ := hseg
    have hplane := hull3_plane a b c r hr
    rw [hs, orient3_segment, hx] at hplane
    have hs0 : s = 0 := by
      have : s * orient3 a b c y = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hy
    have hrx : r = x := by
      rw [hs, hs0]; simp only [segment3Point]; cases x; simp
    unfold edgeAgainstTriangle pointPlaneValue
    simp only [hx, if_true]
    rw [← hrx]
    exact containsNondegenerate_of_hull a b c r pa hpa hr
  · by_cases hy : orient3 a b c y = 0
    · obtain ⟨s, s0, s1, hs⟩ := hseg
      have hplane := hull3_plane a b c r hr
      rw [hs, orient3_segment, hy] at hplane
      have hs1 : s = 1 := by
        have : (1 - s) * orient3 a b c x = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_right hx
        linarith
      have hry : r = y := by
        rw [hs, hs1]; simp only [segment3Point]; cases y; simp
      unfold edgeAgainstTriangle pointPlaneValue
      simp only [hx, hy, if_false, if_true]
      rw [← hry]
      exact containsNondegenerate_of_hull a b c r pa hpa hr
    · exact cut_flag a b c x y r pa hpa hx hy hr hseg

theorem edges_false (a b c d e f : Point3) (pa pb : Nat)
    (hA : firstProjectionAxis a b c = some pa) (hB : firstProjectionAxis d e f = some pb)
    (hgp : orient3 a b c d ≠ 0)
    (hc : noncoplanarTrianglesConflict a b c d e f = false) :
    edgeAgainstTriangle d e f a b = false ∧ edgeAgainstTriangle d e f b c = false ∧
    edgeAgainstTriangle d e f c a = false ∧ edgeAgainstTriangle a b c d e = false ∧
    edgeAgainstTriangle a b c e f = false ∧ edgeAgainstTriangle a b c f d = false := by
  unfold noncoplanarTrianglesConflict at hc
  rw [hA, hB] at hc
  simp only [pointPlaneValue] at hc
  simp only [hgp, decide_false, Bool.false_and, Bool.false_eq_true, ite_false] at hc
  simp only [Bool.or_eq_false_iff] at hc
  exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

theorem orient3_vertex_zero (a b c : Point3) :
    orient3 a b c a = 0 ∧ orient3 a b c b = 0 ∧ orient3 a b c c = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [orient3] <;> ring

/-- Case II of the proof: a strict cut of a `B` edge lies in `A`'s plane and in `B`; if every such
point were in `A`, the predicate would flag it. -/
theorem case2_contra (a b c d e f : Point3) (pa : Nat) (hA : firstProjectionAxis a b c = some pa)
    (hII : ∀ s, Hull3 d e f s → orient3 a b c s = 0 → Hull3 a b c s)
    (x y : Point3) (hx : Hull3 d e f x) (hy : Hull3 d e f y)
    (hx0 : orient3 a b c x ≠ 0) (hy0 : orient3 a b c y ≠ 0)
    (hxy : orient3 a b c x * orient3 a b c y < 0)
    (flag : edgeAgainstTriangle a b c x y = false) : False := by
  set Dx := orient3 a b c x
  set Dy := orient3 a b c y
  have hden : Dx - Dy ≠ 0 := by
    intro h
    have : Dx = Dy := by linarith
    rw [this] at hxy; nlinarith [sq_nonneg Dy]
  have t0 : 0 ≤ Dx / (Dx - Dy) ∧ Dx / (Dx - Dy) ≤ 1 := by
    rcases lt_or_gt_of_ne hx0 with h1 | h1
    · have h2 : 0 < Dy := by nlinarith
      have hd : Dx - Dy < 0 := by linarith
      exact ⟨div_nonneg_of_nonpos h1.le hd.le, (div_le_one_of_neg hd).mpr (by linarith)⟩
    · have h2 : Dy < 0 := by nlinarith
      have hd : 0 < Dx - Dy := by linarith
      exact ⟨div_nonneg h1.le hd.le, (div_le_one hd).mpr (by linarith)⟩
  have hr : Hull3 d e f (segment3Point x y (Dx / (Dx - Dy))) :=
    hull3_segment d e f x y hx hy _ t0.1 t0.2
  have hpl : orient3 a b c (segment3Point x y (Dx / (Dx - Dy))) = 0 := by
    rw [orient3_segment]
    field_simp
    ring
  have hrA := hII _ hr hpl
  have := cut_flag a b c x y _ pa hA hx0 hy0 hrA ⟨_, t0.1, t0.2, rfl⟩
  rw [flag] at this
  exact absurd this (by decide)

theorem weighted_neg (u v w D1 D2 D3 : Rat) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u + v + w = 1) (h1 : D1 < 0) (h2 : D2 < 0) (h3 : D3 < 0) :
    u * D1 + v * D2 + w * D3 < 0 := by
  set M := max (max D1 D2) D3 with hM
  have hMlt : M < 0 := max_lt (max_lt h1 h2) h3
  have a1 : D1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have a2 : D2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have a3 : D3 ≤ M := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left a1 hu, mul_le_mul_of_nonneg_left a2 hv,
    mul_le_mul_of_nonneg_left a3 hw, show M * (u + v + w) = M by rw [hs, mul_one]]

theorem weighted_pos (u v w D1 D2 D3 : Rat) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u + v + w = 1) (h1 : 0 < D1) (h2 : 0 < D2) (h3 : 0 < D3) :
    0 < u * D1 + v * D2 + w * D3 := by
  have := weighted_neg u v w (-D1) (-D2) (-D3) hu hv hw hs (by linarith) (by linarith) (by linarith)
  linarith

theorem noncoplanar_gp_disjoint (a b c d e f : Point3) (pa pb : Nat)
    (hA : firstProjectionAxis a b c = some pa) (hB : firstProjectionAxis d e f = some pb)
    (gpA : orient3 a b c d ≠ 0 ∧ orient3 a b c e ≠ 0 ∧ orient3 a b c f ≠ 0)
    (gpB : orient3 d e f a ≠ 0 ∧ orient3 d e f b ≠ 0 ∧ orient3 d e f c ≠ 0)
    (hc : noncoplanarTrianglesConflict a b c d e f = false) :
    ¬ ∃ p : Point3, Hull3 a b c p ∧ Hull3 d e f p := by
  obtain ⟨E1, E2, E3, E4, E5, E6⟩ := edges_false a b c d e f pa pb hA hB gpA.1 hc
  rintro ⟨p, hpA, hpB⟩
  obtain ⟨hlt, hnd⟩ := firstProjectionAxis_lt a b c pa hA
  by_cases hI : ∃ s, Hull3 d e f s ∧ orient3 a b c s = 0 ∧ ¬ Hull3 a b c s
  · obtain ⟨s, hsB, hsp, hsA⟩ := hI
    have hpp : orient3 a b c p = 0 := hull3_plane a b c p hpA
    have t_p := hull_tri2_axis pa hlt a b c p hpA
    have nt_s : ¬ Tri2 (projectPoint3 pa a) (projectPoint3 pa b) (projectPoint3 pa c)
        (projectPoint3 pa s) := fun h => hsA (tri2_hull_axis pa hlt a b c s hnd hsp h)
    obtain ⟨t, t0, t1, hmem, s', s0, s1, hedge⟩ := tri2_exit _ _ _ _ _ hnd t_p nt_s
    have hqB : Hull3 d e f (segment3Point p s t) := hull3_segment d e f p s hpB hsB t t0 t1
    have hqpl : orient3 a b c (segment3Point p s t) = 0 := by
      rw [orient3_segment, hpp, hsp]; ring
    have hproj := projectPoint3_segment pa p s t
    have vz := orient3_vertex_zero a b c
    have edgeZero : ∀ x y : Point3, orient3 a b c x = 0 → orient3 a b c y = 0 →
        ∀ r : Rat, orient3 a b c (segment3Point x y r) = 0 := by
      intro x y h1 h2 r; rw [orient3_segment, h1, h2]; ring
    rcases hedge with h | h | h
    · have hE : segment3Point p s t = segment3Point a b s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero a b vz.1 vz.2.1 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      have := cut_flag d e f a b _ pb hB gpB.1 gpB.2.1 hqB ⟨s', s0, s1, hE⟩
      rw [E1] at this; exact absurd this (by decide)
    · have hE : segment3Point p s t = segment3Point b c s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero b c vz.2.1 vz.2.2 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      have := cut_flag d e f b c _ pb hB gpB.2.1 gpB.2.2 hqB ⟨s', s0, s1, hE⟩
      rw [E2] at this; exact absurd this (by decide)
    · have hE : segment3Point p s t = segment3Point c a s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero c a vz.2.2 vz.1 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      have := cut_flag d e f c a _ pb hB gpB.2.2 gpB.1 hqB ⟨s', s0, s1, hE⟩
      rw [E3] at this; exact absurd this (by decide)
  · have hII : ∀ s, Hull3 d e f s → orient3 a b c s = 0 → Hull3 a b c s := by
      intro s hs hp0
      by_contra hn
      exact hI ⟨s, hs, hp0, hn⟩
    obtain ⟨u, v, w, hu, hv, hw, hsum, hform⟩ := hull3_affine a b c d e f p hpB
    rw [hull3_plane a b c p hpA] at hform
    have V0 := hull3_vertex0 d e f
    have V1 := hull3_vertex1 d e f
    have V2 := hull3_vertex2 d e f
    have g1 := gpA.1; have g2 := gpA.2.1; have g3 := gpA.2.2
    rcases lt_or_gt_of_ne g1 with h1 | h1 <;> rcases lt_or_gt_of_ne g2 with h2 | h2 <;>
      rcases lt_or_gt_of_ne g3 with h3 | h3
    · have := weighted_neg u v w _ _ _ hu hv hw hsum h1 h2 h3; linarith
    · exact case2_contra a b c d e f pa hA hII e f V1 V2 g2 g3 (by nlinarith) E5
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII e f V1 V2 g2 g3 (by nlinarith) E5
    · have := weighted_pos u v w _ _ _ hu hv hw hsum h1 h2 h3; linarith

/-- A first endpoint on the plane and inside the triangle is flagged regardless of the other end. -/
theorem vertex_flag (a b c x y : Point3) (pa : Nat) (hpa : firstProjectionAxis a b c = some pa)
    (hx : orient3 a b c x = 0) (hxT : Hull3 a b c x) :
    edgeAgainstTriangle a b c x y = true := by
  unfold edgeAgainstTriangle pointPlaneValue
  simp only [hx, if_true]
  exact containsNondegenerate_of_hull a b c x pa hpa hxT

theorem edges_false2 (a b c d e f : Point3) (pa pb : Nat)
    (hA : firstProjectionAxis a b c = some pa) (hB : firstProjectionAxis d e f = some pb)
    (hnc : ¬ (orient3 a b c d = 0 ∧ orient3 a b c e = 0 ∧ orient3 a b c f = 0))
    (hc : noncoplanarTrianglesConflict a b c d e f = false) :
    edgeAgainstTriangle d e f a b = false ∧ edgeAgainstTriangle d e f b c = false ∧
    edgeAgainstTriangle d e f c a = false ∧ edgeAgainstTriangle a b c d e = false ∧
    edgeAgainstTriangle a b c e f = false ∧ edgeAgainstTriangle a b c f d = false := by
  unfold noncoplanarTrianglesConflict at hc
  rw [hA, hB] at hc
  simp only [pointPlaneValue] at hc
  split_ifs at hc with h
  · exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact hnc ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2, of_decide_eq_true h.2⟩
  simp only [Bool.or_eq_false_iff] at hc
  exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

theorem noncoplanar_edgefree_disjoint (a b c d e f : Point3) (pa pb : Nat)
    (hA : firstProjectionAxis a b c = some pa) (hB : firstProjectionAxis d e f = some pb)
    (hnc : ¬ (orient3 a b c d = 0 ∧ orient3 a b c e = 0 ∧ orient3 a b c f = 0))
    (hedge : ¬ (orient3 d e f a = 0 ∧ orient3 d e f b = 0) ∧
             ¬ (orient3 d e f b = 0 ∧ orient3 d e f c = 0) ∧
             ¬ (orient3 d e f c = 0 ∧ orient3 d e f a = 0))
    (hc : noncoplanarTrianglesConflict a b c d e f = false) :
    ¬ ∃ p : Point3, Hull3 a b c p ∧ Hull3 d e f p := by
  obtain ⟨E1, E2, E3, E4, E5, E6⟩ := edges_false2 a b c d e f pa pb hA hB hnc hc
  rintro ⟨p, hpA, hpB⟩
  obtain ⟨hlt, hnd⟩ := firstProjectionAxis_lt a b c pa hA
  by_cases hI : ∃ s, Hull3 d e f s ∧ orient3 a b c s = 0 ∧ ¬ Hull3 a b c s
  · obtain ⟨s, hsB, hsp, hsA⟩ := hI
    have hpp : orient3 a b c p = 0 := hull3_plane a b c p hpA
    have t_p := hull_tri2_axis pa hlt a b c p hpA
    have nt_s : ¬ Tri2 (projectPoint3 pa a) (projectPoint3 pa b) (projectPoint3 pa c)
        (projectPoint3 pa s) := fun h => hsA (tri2_hull_axis pa hlt a b c s hnd hsp h)
    obtain ⟨t, t0, t1, hmem, s', s0, s1, hedge⟩ := tri2_exit _ _ _ _ _ hnd t_p nt_s
    have hqB : Hull3 d e f (segment3Point p s t) := hull3_segment d e f p s hpB hsB t t0 t1
    have hqpl : orient3 a b c (segment3Point p s t) = 0 := by
      rw [orient3_segment, hpp, hsp]; ring
    have hproj := projectPoint3_segment pa p s t
    have vz := orient3_vertex_zero a b c
    have edgeZero : ∀ x y : Point3, orient3 a b c x = 0 → orient3 a b c y = 0 →
        ∀ r : Rat, orient3 a b c (segment3Point x y r) = 0 := by
      intro x y h1 h2 r; rw [orient3_segment, h1, h2]; ring
    rcases hedge with h | h | h
    · have hE : segment3Point p s t = segment3Point a b s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero a b vz.1 vz.2.1 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      have := edge_flag d e f a b _ pb hB hedge.1 hqB ⟨s', s0, s1, hE⟩
      rw [E1] at this; exact absurd this (by decide)
    · have hE : segment3Point p s t = segment3Point b c s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero b c vz.2.1 vz.2.2 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      have := edge_flag d e f b c _ pb hB hedge.2.1 hqB ⟨s', s0, s1, hE⟩
      rw [E2] at this; exact absurd this (by decide)
    · have hE : segment3Point p s t = segment3Point c a s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero c a vz.2.2 vz.1 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      have := edge_flag d e f c a _ pb hB hedge.2.2 hqB ⟨s', s0, s1, hE⟩
      rw [E3] at this; exact absurd this (by decide)
  · have hII : ∀ s, Hull3 d e f s → orient3 a b c s = 0 → Hull3 a b c s := by
      intro s hs hp0
      by_contra hn
      exact hI ⟨s, hs, hp0, hn⟩
    obtain ⟨u, v, w, hu, hv, hw, hsum, hform⟩ := hull3_affine a b c d e f p hpB
    rw [hull3_plane a b c p hpA] at hform
    have V0 := hull3_vertex0 d e f
    have V1 := hull3_vertex1 d e f
    have V2 := hull3_vertex2 d e f
    by_cases z1 : orient3 a b c d = 0
    · have := vertex_flag a b c d e pa hA z1 (hII d V0 z1)
      rw [E4] at this; exact absurd this (by decide)
    by_cases z2 : orient3 a b c e = 0
    · have := vertex_flag a b c e f pa hA z2 (hII e V1 z2)
      rw [E5] at this; exact absurd this (by decide)
    by_cases z3 : orient3 a b c f = 0
    · have := vertex_flag a b c f d pa hA z3 (hII f V2 z3)
      rw [E6] at this; exact absurd this (by decide)
    have g1 := z1; have g2 := z2; have g3 := z3
    rcases lt_or_gt_of_ne g1 with h1 | h1 <;> rcases lt_or_gt_of_ne g2 with h2 | h2 <;>
      rcases lt_or_gt_of_ne g3 with h3 | h3
    · have := weighted_neg u v w _ _ _ hu hv hw hsum h1 h2 h3; linarith
    · exact case2_contra a b c d e f pa hA hII e f V1 V2 g2 g3 (by nlinarith) E5
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII d e V0 V1 g1 g2 (by nlinarith) E4
    · exact case2_contra a b c d e f pa hA hII e f V1 V2 g2 g3 (by nlinarith) E5
    · have := weighted_pos u v w _ _ _ hu hv hw hsum h1 h2 h3; linarith


end Tess
