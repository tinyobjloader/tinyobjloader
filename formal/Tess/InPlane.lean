import Tess.PlaneLine
import Tess.NoncoplanarComplete

namespace Tess

theorem segment3Point_zero (x y : Point3) : segment3Point x y 0 = x := by
  cases x; simp [segment3Point]

theorem segment3Point_one (x y : Point3) : segment3Point x y 1 = y := by
  cases y; cases x; simp [segment3Point]

theorem seg_comp (x y : Point3) (μ ν σ : Rat) :
    segment3Point (segment3Point x y μ) (segment3Point x y ν) σ =
      segment3Point x y (μ + σ * (ν - μ)) := by
  simp only [segment3Point]; congr 1 <;> ring

theorem segment3Point_plane (x y : Point3) (g : Point3 → Rat)
    (hg : ∀ p q t, g (segment3Point p q t) = (1 - t) * g p + t * g q) (hx : g x = 0) (hy : g y = 0)
    (t : Rat) : g (segment3Point x y t) = 0 := by
  rw [hg, hx, hy]; ring

/-- Both triangles' in-plane edges: if the edge `u w` of `S` lies in the plane of `T` and shares a
point with an edge `x y` of `T` that lies in `S`'s plane, with `x, y` outside `S`, then an endpoint
of `u w` lies on the edge `x y`. -/
theorem inplane_resolve (a b c d e f x y u w : Point3) (pb : Nat) (hlt : pb < 3)
    (hnd : orient (projectPoint3 pb d) (projectPoint3 pb e) (projectPoint3 pb f) ≠ 0)
    (hxy : x ≠ y)
    (hx2 : orient3 a b c x = 0) (hy2 : orient3 a b c y = 0)
    (hu2 : orient3 a b c u = 0) (hw2 : orient3 a b c w = 0)
    (hx1 : orient3 d e f x = 0) (hy1 : orient3 d e f y = 0)
    (hu1 : orient3 d e f u = 0) (hw1 : orient3 d e f w = 0)
    (V : Point3) (hV1 : orient3 d e f V = 0) (hV2 : orient3 a b c V ≠ 0)
    (hxS : ¬ Hull3 d e f x) (hyS : ¬ Hull3 d e f y)
    (huS : Hull3 d e f u) (hwS : Hull3 d e f w)
    (ζ σ : Rat) (ζ0 : 0 ≤ ζ) (ζ1 : ζ ≤ 1) (σ0 : 0 ≤ σ) (σ1 : σ ≤ 1)
    (hz : segment3Point x y ζ = segment3Point u w σ) :
    (∃ μ : Rat, 0 ≤ μ ∧ μ ≤ 1 ∧ u = segment3Point x y μ) ∨
    (∃ ν : Rat, 0 ≤ ν ∧ ν ≤ 1 ∧ w = segment3Point x y ν) := by
  have vz := orient3_vertex_zero d e f
  have plane1 : ∀ p q : Point3, orient3 d e f p = 0 → orient3 d e f q = 0 → ∀ t : Rat,
      orient3 d e f (segment3Point p q t) = 0 := by
    intro p q h1 h2 t; rw [orient3_segment, h1, h2]; ring
  -- projected points of x, y differ
  have hproj : projectPoint3 pb x ≠ projectPoint3 pb y := by
    intro h
    exact hxy (plane_inj_axis pb hlt d e f x y hnd hx1 hy1 h)
  have col : ∀ r : Point3, orient3 d e f r = 0 → orient3 a b c r = 0 →
      ∃ μ : Rat, r = segment3Point x y μ := by
    intro r hr1 hr2
    have h0 := collinear_axis pb hlt a b c d e f x y r V hnd hx1 hy1 hr1 hx2 hy2 hr2 hV1 hV2
    obtain ⟨μ, hμ⟩ := collinear_param _ _ _ hproj h0
    refine ⟨μ, plane_inj_axis pb hlt d e f _ _ hnd hr1 (plane1 x y hx1 hy1 μ) ?_⟩
    rw [hμ, projectPoint3_segment]
  obtain ⟨μ, hμ⟩ := col u hu1 hu2
  obtain ⟨ν, hν⟩ := col w hw1 hw2
  have hzeq : segment3Point x y ζ = segment3Point x y (μ + σ * (ν - μ)) := by
    rw [hz, hμ, hν, seg_comp]
  have hζ := segment3Point_inj x y hxy _ _ hzeq
  -- endpoints of the edge `x y` lie outside the segment `u w`
  have notin : ∀ t0 : Rat, ¬ Hull3 d e f (segment3Point x y t0) →
      ¬ ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ μ + s * (ν - μ) = t0 := by
    rintro t0 hn ⟨s, s0, s1, hs⟩
    apply hn
    have : segment3Point x y t0 = segment3Point u w s := by
      rw [hμ, hν, seg_comp, hs]
    rw [this]
    exact hull3_segment d e f u w huS hwS s s0 s1
  by_contra hcon
  push Not at hcon
  obtain ⟨hu', hw'⟩ := hcon
  have n0 := notin 0 (by rw [segment3Point_zero]; exact hxS)
  have n1 := notin 1 (by rw [segment3Point_one]; exact hyS)
  -- 1D argument on the parameters
  have hμo : μ < 0 ∨ 1 < μ := by
    by_contra hh
    exact hu' μ (not_lt.mp (fun h => hh (Or.inl h))) (not_lt.mp (fun h => hh (Or.inr h))) hμ
  have hνo : ν < 0 ∨ 1 < ν := by
    by_contra hh
    exact hw' ν (not_lt.mp (fun h => hh (Or.inl h))) (not_lt.mp (fun h => hh (Or.inr h))) hν
  have crossing : ∀ t0 : Rat, (μ ≤ t0 ∧ t0 ≤ ν) ∨ (ν ≤ t0 ∧ t0 ≤ μ) →
      ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ μ + s * (ν - μ) = t0 := by
    intro t0 h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases eq_or_lt_of_le h1 with h3 | h3
      · exact ⟨0, le_rfl, by norm_num, by rw [← h3]; ring⟩
      · have hd : 0 < ν - μ := by linarith
        refine ⟨(t0 - μ) / (ν - μ), div_nonneg (by linarith) hd.le, ?_, ?_⟩
        · rw [div_le_one hd]; linarith
        · rw [div_mul_cancel₀ _ hd.ne']; ring
    · rcases eq_or_lt_of_le h1 with h3 | h3
      · exact ⟨1, by norm_num, le_rfl, by rw [h3]; ring⟩
      · have hd : ν - μ < 0 := by linarith
        refine ⟨(t0 - μ) / (ν - μ), div_nonneg_of_nonpos (by linarith) hd.le, ?_, ?_⟩
        · rw [div_le_one_of_neg hd]; linarith
        · rw [div_mul_cancel₀ _ hd.ne]; ring
  rcases hμo with h1 | h1 <;> rcases hνo with h2 | h2
  · rcases le_total μ ν with hle | hle
    · nlinarith [mul_nonneg (sub_nonneg.2 σ1) (sub_nonneg.2 hle)]
    · nlinarith [mul_nonneg σ0 (sub_nonneg.2 hle)]
  · exact n0 (crossing 0 (Or.inl ⟨by linarith, by linarith⟩))
  · exact n0 (crossing 0 (Or.inr ⟨by linarith, by linarith⟩))
  · rcases le_total μ ν with hle | hle
    · nlinarith [mul_nonneg σ0 (sub_nonneg.2 hle)]
    · nlinarith [mul_nonneg (sub_nonneg.2 σ1) (sub_nonneg.2 hle)]

/-- Final step of the in-plane configuration: the exit point `z` lies on an edge `u w` of `S` and
on the in-plane edge `x y` of `T`; it is flagged unless `u w` also lies in `T`'s plane, and then an
endpoint of `u w` lies on `x y`. -/
theorem inplane_branch (a b c d e f x y u w : Point3) (pa pb : Nat)
    (hA : firstProjectionAxis a b c = some pa) (hB : firstProjectionAxis d e f = some pb)
    (hxy : x ≠ y) (hxA : Hull3 a b c x) (hyA : Hull3 a b c y)
    (hx2 : orient3 a b c x = 0) (hy2 : orient3 a b c y = 0)
    (hx1 : orient3 d e f x = 0) (hy1 : orient3 d e f y = 0)
    (hxS : ¬ Hull3 d e f x) (hyS : ¬ Hull3 d e f y)
    (huS : Hull3 d e f u) (hwS : Hull3 d e f w)
    (hu1 : orient3 d e f u = 0) (hw1 : orient3 d e f w = 0)
    (hVFu : orient3 a b c u = 0 → ¬ Hull3 a b c u)
    (hVFw : orient3 a b c w = 0 → ¬ Hull3 a b c w)
    (hflag : edgeAgainstTriangle a b c u w = false)
    (V : Point3) (hV1 : orient3 d e f V = 0) (hV2 : orient3 a b c V ≠ 0)
    (ζ σ : Rat) (ζ0 : 0 ≤ ζ) (ζ1 : ζ ≤ 1) (σ0 : 0 ≤ σ) (σ1 : σ ≤ 1)
    (hz : segment3Point x y ζ = segment3Point u w σ) : False := by
  have hzA : Hull3 a b c (segment3Point x y ζ) := hull3_segment a b c x y hxA hyA ζ ζ0 ζ1
  by_cases hboth : orient3 a b c u = 0 ∧ orient3 a b c w = 0
  · obtain ⟨hlt, hnd⟩ := firstProjectionAxis_lt d e f pb hB
    have hres := inplane_resolve a b c d e f x y u w pb hlt hnd hxy hx2 hy2 hboth.1 hboth.2
      hx1 hy1 hu1 hw1 V hV1 hV2 hxS hyS huS hwS ζ σ ζ0 ζ1 σ0 σ1 hz
    rcases hres with ⟨μ, μ0, μ1, hμ⟩ | ⟨ν, ν0, ν1, hν⟩
    · apply hVFu hboth.1
      rw [hμ]; exact hull3_segment a b c x y hxA hyA μ μ0 μ1
    · apply hVFw hboth.2
      rw [hν]; exact hull3_segment a b c x y hxA hyA ν ν0 ν1
  · have := edge_flag a b c u w (segment3Point x y ζ) pa hA hboth hzA ⟨σ, σ0, σ1, hz⟩
    rw [hflag] at this
    exact absurd this (by decide)

/-- Case I of the completeness proof for an edge `x y` of `T` that may lie in `S`'s plane. -/
theorem caseI_edge (a b c d e f x y : Point3) (pa pb : Nat)
    (hA : firstProjectionAxis a b c = some pa) (hB : firstProjectionAxis d e f = some pb)
    (hxy : x ≠ y) (hxA : Hull3 a b c x) (hyA : Hull3 a b c y)
    (hx2 : orient3 a b c x = 0) (hy2 : orient3 a b c y = 0)
    (hflag : edgeAgainstTriangle d e f x y = false)
    (hVFx : orient3 d e f x = 0 → ¬ Hull3 d e f x) (hVFy : orient3 d e f y = 0 → ¬ Hull3 d e f y)
    (hVFd : orient3 a b c d = 0 → ¬ Hull3 a b c d) (hVFe : orient3 a b c e = 0 → ¬ Hull3 a b c e)
    (hVFf : orient3 a b c f = 0 → ¬ Hull3 a b c f)
    (E4 : edgeAgainstTriangle a b c d e = false) (E5 : edgeAgainstTriangle a b c e f = false)
    (E6 : edgeAgainstTriangle a b c f d = false)
    (hnc : ¬ (orient3 a b c d = 0 ∧ orient3 a b c e = 0 ∧ orient3 a b c f = 0))
    (s' : Rat) (s0 : 0 ≤ s') (s1 : s' ≤ 1) (hq : Hull3 d e f (segment3Point x y s')) : False := by
  by_cases hboth : orient3 d e f x = 0 ∧ orient3 d e f y = 0
  · obtain ⟨hlt, hnd⟩ := firstProjectionAxis_lt d e f pb hB
    have hxS := hVFx hboth.1
    have hyS := hVFy hboth.2
    have vz := orient3_vertex_zero d e f
    obtain ⟨V, hV1, hV2⟩ : ∃ V, orient3 d e f V = 0 ∧ orient3 a b c V ≠ 0 := by
      by_cases h1 : orient3 a b c d = 0
      · by_cases h2 : orient3 a b c e = 0
        · exact ⟨f, vz.2.2, fun h3 => hnc ⟨h1, h2, h3⟩⟩
        · exact ⟨e, vz.2.1, h2⟩
      · exact ⟨d, vz.1, h1⟩
    have hqpl := hull3_plane d e f _ hq
    have tq := hull_tri2_axis pb hlt d e f _ hq
    have nx : ¬ Tri2 (projectPoint3 pb d) (projectPoint3 pb e) (projectPoint3 pb f) (projectPoint3 pb x) :=
      fun h => hxS (tri2_hull_axis pb hlt d e f x hnd hboth.1 h)
    obtain ⟨t2, t20, t21, _, s2, s20, s21, hedge⟩ := tri2_exit _ _ _ _ _ hnd tq nx
    have hzpl : orient3 d e f (segment3Point (segment3Point x y s') x t2) = 0 := by
      rw [orient3_segment, hqpl, hboth.1]; ring
    have hzproj := projectPoint3_segment pb (segment3Point x y s') x t2
    have edgeZero : ∀ p q : Point3, orient3 d e f p = 0 → orient3 d e f q = 0 → ∀ r : Rat,
        orient3 d e f (segment3Point p q r) = 0 := by
      intro p q h1 h2 r; rw [orient3_segment, h1, h2]; ring
    have hζ := seg_comp x y s' 0 t2
    rw [segment3Point_zero] at hζ
    have hζ0 : 0 ≤ s' + t2 * (0 - s') := by nlinarith
    have hζ1 : s' + t2 * (0 - s') ≤ 1 := by nlinarith
    rcases hedge with h | h | h
    · have hE : segment3Point (segment3Point x y s') x t2 = segment3Point d e s2 :=
        plane_inj_axis pb hlt d e f _ _ hnd hzpl (edgeZero d e vz.1 vz.2.1 s2)
          (by rw [hzproj, projectPoint3_segment pb d e s2]; exact h)
      exact inplane_branch a b c d e f x y d e pa pb hA hB hxy hxA hyA hx2 hy2 hboth.1 hboth.2 hxS hyS
        (hull3_vertex0 d e f) (hull3_vertex1 d e f) vz.1 vz.2.1 hVFd hVFe E4 V hV1 hV2
        _ s2 hζ0 hζ1 s20 s21 (by rw [← hζ]; exact hE)
    · have hE : segment3Point (segment3Point x y s') x t2 = segment3Point e f s2 :=
        plane_inj_axis pb hlt d e f _ _ hnd hzpl (edgeZero e f vz.2.1 vz.2.2 s2)
          (by rw [hzproj, projectPoint3_segment pb e f s2]; exact h)
      exact inplane_branch a b c d e f x y e f pa pb hA hB hxy hxA hyA hx2 hy2 hboth.1 hboth.2 hxS hyS
        (hull3_vertex1 d e f) (hull3_vertex2 d e f) vz.2.1 vz.2.2 hVFe hVFf E5 V hV1 hV2
        _ s2 hζ0 hζ1 s20 s21 (by rw [← hζ]; exact hE)
    · have hE : segment3Point (segment3Point x y s') x t2 = segment3Point f d s2 :=
        plane_inj_axis pb hlt d e f _ _ hnd hzpl (edgeZero f d vz.2.2 vz.1 s2)
          (by rw [hzproj, projectPoint3_segment pb f d s2]; exact h)
      exact inplane_branch a b c d e f x y f d pa pb hA hB hxy hxA hyA hx2 hy2 hboth.1 hboth.2 hxS hyS
        (hull3_vertex2 d e f) (hull3_vertex0 d e f) vz.2.2 vz.1 hVFf hVFd E6 V hV1 hV2
        _ s2 hζ0 hζ1 s20 s21 (by rw [← hζ]; exact hE)
  · have := edge_flag d e f x y _ pb hB hboth hq ⟨s', s0, s1, rfl⟩
    rw [hflag] at this
    exact absurd this (by decide)

theorem verts_ne (a b c : Point3) (pa : Nat)
    (hnd : orient (projectPoint3 pa a) (projectPoint3 pa b) (projectPoint3 pa c) ≠ 0) :
    a ≠ b ∧ b ≠ c ∧ c ≠ a := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; apply hnd; simp only [orient]; ring
  · rintro rfl; apply hnd; simp only [orient]; ring
  · rintro rfl; apply hnd; simp only [orient]; ring

theorem noncoplanar_disjoint_complete (a b c d e f : Point3) (pa pb : Nat)
    (hA : firstProjectionAxis a b c = some pa) (hB : firstProjectionAxis d e f = some pb)
    (hnc : ¬ (orient3 a b c d = 0 ∧ orient3 a b c e = 0 ∧ orient3 a b c f = 0))
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
    have ne := verts_ne a b c pa hnd
    have VFa : orient3 d e f a = 0 → ¬ Hull3 d e f a :=
      fun h1 h2 => by have := vertex_flag d e f a b pb hB h1 h2; rw [E1] at this; exact absurd this (by decide)
    have VFb : orient3 d e f b = 0 → ¬ Hull3 d e f b :=
      fun h1 h2 => by have := vertex_flag d e f b c pb hB h1 h2; rw [E2] at this; exact absurd this (by decide)
    have VFc : orient3 d e f c = 0 → ¬ Hull3 d e f c :=
      fun h1 h2 => by have := vertex_flag d e f c a pb hB h1 h2; rw [E3] at this; exact absurd this (by decide)
    have VFd : orient3 a b c d = 0 → ¬ Hull3 a b c d :=
      fun h1 h2 => by have := vertex_flag a b c d e pa hA h1 h2; rw [E4] at this; exact absurd this (by decide)
    have VFe : orient3 a b c e = 0 → ¬ Hull3 a b c e :=
      fun h1 h2 => by have := vertex_flag a b c e f pa hA h1 h2; rw [E5] at this; exact absurd this (by decide)
    have VFf : orient3 a b c f = 0 → ¬ Hull3 a b c f :=
      fun h1 h2 => by have := vertex_flag a b c f d pa hA h1 h2; rw [E6] at this; exact absurd this (by decide)
    rcases hedge with h | h | h
    · have hE : segment3Point p s t = segment3Point a b s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero a b vz.1 vz.2.1 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      exact caseI_edge a b c d e f a b pa pb hA hB ne.1 (hull3_vertex0 a b c) (hull3_vertex1 a b c)
        vz.1 vz.2.1 E1 VFa VFb VFd VFe VFf E4 E5 E6 hnc s' s0 s1 (by rw [← hE]; exact hqB)
    · have hE : segment3Point p s t = segment3Point b c s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero b c vz.2.1 vz.2.2 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      exact caseI_edge a b c d e f b c pa pb hA hB ne.2.1 (hull3_vertex1 a b c) (hull3_vertex2 a b c)
        vz.2.1 vz.2.2 E2 VFb VFc VFd VFe VFf E4 E5 E6 hnc s' s0 s1 (by rw [← hE]; exact hqB)
    · have hE : segment3Point p s t = segment3Point c a s' :=
        plane_inj_axis pa hlt a b c _ _ hnd hqpl (edgeZero c a vz.2.2 vz.1 s')
          (by rw [hproj, projectPoint3_segment]; exact h)
      exact caseI_edge a b c d e f c a pa pb hA hB ne.2.2 (hull3_vertex2 a b c) (hull3_vertex0 a b c)
        vz.2.2 vz.1 E3 VFc VFa VFd VFe VFf E4 E5 E6 hnc s' s0 s1 (by rw [← hE]; exact hqB)
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
