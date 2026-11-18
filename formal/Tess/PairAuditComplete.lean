import Tess.PairAuditShared
import Tess.CoplanarSharedEdge
import Tess.PairAuditCoplanar
import Tess.IntersectionCompleteness
import Tess.IndexedConflict
import Tess.SharedEdge

/-! The auditor's rejections are genuine: for faces with no shared vertex IDs, `pairOk = false`
yields an actual common (rational) point of the two closed triangles. Together with the soundness
results this makes the exact pair decision equivalent to disjointness of the closed triangles. -/
namespace Tess
namespace PairAudit

theorem edgesAgainst_false_contact (m : ExactMesh) (fa fb : Face) (pb : Nat)
    (hpb : projAxis m fb = some pb) (hd : commonIds fa fb = [])
    (hfalse : edgesAgainst m fa fb pb = false) :
    ∃ i, i < 3 ∧ ∃ (r : Point3) (s : Rat), 0 ≤ s ∧ s ≤ 1 ∧
      r = segment3Point (m.point (faceId fa i)) (m.point (faceId fa ((i + 1) % 3))) s ∧
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r := by
  have hc : ∀ p, containsPt m fb pb p =
      containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p
    unfold containsPt containsNondegenerate
    unfold projAxis at hpb
    rw [hpb]
  have hpv : ∀ p, planeValue m fb p = orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p; rw [planeValue_eq_orient3]
  obtain ⟨hlt, hnd⟩ := firstProjectionAxis_lt (m.point fb.a) (m.point fb.b) (m.point fb.c) pb hpb
  have hcont : ∀ p, containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) p = true →
      orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p = 0 →
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p h1 h2
    have hpb2 : firstProjectionAxis (m.point fb.a) (m.point fb.b) (m.point fb.c) = some pb := hpb
    unfold containsNondegenerate at h1
    rw [hpb2] at h1
    simp only [containsProject] at h1
    exact tri2_hull_axis pb hlt _ _ _ p hnd h2 ((contains2_iff_Tri2 _ _ _ _).mp h1)
  unfold edgesAgainst at hfalse
  rw [List.all_eq_false] at hfalse
  obtain ⟨i, hi, hbad⟩ := hfalse
  simp only [List.mem_range] at hi
  refine ⟨i, hi, ?_⟩
  have hnall := allowed_of_disjoint m fa fb hd
  simp only [hc, hpv, hnall, Bool.not_false, Bool.and_true] at hbad
  set x := m.point (faceId fa i)
  set y := m.point (faceId fa ((i + 1) % 3))
  set T0 := m.point fb.a; set T1 := m.point fb.b; set T2 := m.point fb.c
  by_cases h1 : (decide (orient3 T0 T1 T2 x = 0) && containsNondegenerate T0 T1 T2 x) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    refine ⟨x, 0, le_rfl, by norm_num, by rw [segment3Point_zero], hcont x h1.2 h1.1⟩
  by_cases h2 : (decide (orient3 T0 T1 T2 y = 0) && containsNondegenerate T0 T1 T2 y) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    refine ⟨y, 1, by norm_num, le_rfl, by rw [segment3Point_one], hcont y h2.2 h2.1⟩
  have h1' : (decide (orient3 T0 T1 T2 x = 0) && containsNondegenerate T0 T1 T2 x) = false := by simpa using h1
  have h2' : (decide (orient3 T0 T1 T2 y = 0) && containsNondegenerate T0 T1 T2 y) = false := by simpa using h2
  have c1t : (!(decide (orient3 T0 T1 T2 x = 0) && containsNondegenerate T0 T1 T2 x)) = true := by
    rw [h1']; rfl
  have c2t : (!(decide (orient3 T0 T1 T2 y = 0) && containsNondegenerate T0 T1 T2 y)) = true := by
    rw [h2']; rfl
  have h3 : ¬ (if orient3 T0 T1 T2 x * orient3 T0 T1 T2 y < 0 then
      !containsNondegenerate T0 T1 T2
        (segment3Point x y (orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y))) else true) = true := by
    intro h
    exact hbad (by rw [Bool.and_eq_true, Bool.and_eq_true]; exact ⟨⟨c1t, c2t⟩, h⟩)
  by_cases hxy : orient3 T0 T1 T2 x * orient3 T0 T1 T2 y < 0
  · rw [if_pos hxy] at h3
    have hcutc : containsNondegenerate T0 T1 T2
        (segment3Point x y (orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y))) = true := by
      by_contra hh
      apply h3
      simp [Bool.not_eq_true] at hh ⊢
      exact hh
    set Dx := orient3 T0 T1 T2 x
    set Dy := orient3 T0 T1 T2 y
    have hden : Dx - Dy ≠ 0 := by
      intro h
      have : Dx = Dy := by linarith
      rw [this] at hxy; nlinarith [sq_nonneg Dy]
    have hx0 : Dx ≠ 0 := by intro h; rw [h] at hxy; simp at hxy
    have t0 : 0 ≤ Dx / (Dx - Dy) ∧ Dx / (Dx - Dy) ≤ 1 := by
      rcases lt_or_gt_of_ne hx0 with h1 | h1
      · have h2 : 0 < Dy := by nlinarith
        have hd : Dx - Dy < 0 := by linarith
        exact ⟨div_nonneg_of_nonpos h1.le hd.le, (div_le_one_of_neg hd).mpr (by linarith)⟩
      · have h2 : Dy < 0 := by nlinarith
        have hd : 0 < Dx - Dy := by linarith
        exact ⟨div_nonneg h1.le hd.le, (div_le_one hd).mpr (by linarith)⟩
    have hpl : orient3 T0 T1 T2 (segment3Point x y (Dx / (Dx - Dy))) = 0 := by
      rw [orient3_segment]
      field_simp
      ring
    exact ⟨_, _, t0.1, t0.2, rfl, hcont _ hcutc hpl⟩
  · rw [if_neg hxy] at h3
    exact absurd rfl h3

theorem edgesAgainst_false_contact' (m : ExactMesh) (fa fb : Face) (pb : Nat)
    (hpb : projAxis m fb = some pb) (hfalse : edgesAgainst m fa fb pb = false) :
    ∃ i, i < 3 ∧ ∃ (r : Point3) (s : Rat), 0 ≤ s ∧ s ≤ 1 ∧
      r = segment3Point (m.point (faceId fa i)) (m.point (faceId fa ((i + 1) % 3))) s ∧
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r ∧ allowed m fa fb r = false := by
  have hc : ∀ p, containsPt m fb pb p =
      containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p
    unfold containsPt containsNondegenerate
    unfold projAxis at hpb
    rw [hpb]
  have hpv : ∀ p, planeValue m fb p = orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p; rw [planeValue_eq_orient3]
  obtain ⟨hlt, hnd⟩ := firstProjectionAxis_lt (m.point fb.a) (m.point fb.b) (m.point fb.c) pb hpb
  have hcont : ∀ p, containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) p = true →
      orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p = 0 →
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p h1 h2
    have hpb2 : firstProjectionAxis (m.point fb.a) (m.point fb.b) (m.point fb.c) = some pb := hpb
    unfold containsNondegenerate at h1
    rw [hpb2] at h1
    simp only [containsProject] at h1
    exact tri2_hull_axis pb hlt _ _ _ p hnd h2 ((contains2_iff_Tri2 _ _ _ _).mp h1)
  unfold edgesAgainst at hfalse
  rw [List.all_eq_false] at hfalse
  obtain ⟨i, hi, hbad⟩ := hfalse
  simp only [List.mem_range] at hi
  refine ⟨i, hi, ?_⟩
  simp only [hc, hpv] at hbad
  set x := m.point (faceId fa i)
  set y := m.point (faceId fa ((i + 1) % 3))
  set T0 := m.point fb.a; set T1 := m.point fb.b; set T2 := m.point fb.c
  by_cases h1 : (decide (orient3 T0 T1 T2 x = 0) && containsNondegenerate T0 T1 T2 x &&
      !allowed m fa fb x) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact ⟨x, 0, le_rfl, by norm_num, by rw [segment3Point_zero], hcont x h1.1.2 h1.1.1, h1.2⟩
  by_cases h2 : (decide (orient3 T0 T1 T2 y = 0) && containsNondegenerate T0 T1 T2 y &&
      !allowed m fa fb y) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h2
    exact ⟨y, 1, by norm_num, le_rfl, by rw [segment3Point_one], hcont y h2.1.2 h2.1.1, h2.2⟩
  have h1' : (decide (orient3 T0 T1 T2 x = 0) && containsNondegenerate T0 T1 T2 x &&
      !allowed m fa fb x) = false := by simpa using h1
  have h2' : (decide (orient3 T0 T1 T2 y = 0) && containsNondegenerate T0 T1 T2 y &&
      !allowed m fa fb y) = false := by simpa using h2
  have c1t : (!(decide (orient3 T0 T1 T2 x = 0) && containsNondegenerate T0 T1 T2 x &&
      !allowed m fa fb x)) = true := by rw [h1']; rfl
  have c2t : (!(decide (orient3 T0 T1 T2 y = 0) && containsNondegenerate T0 T1 T2 y &&
      !allowed m fa fb y)) = true := by rw [h2']; rfl
  have h3 : ¬ (if orient3 T0 T1 T2 x * orient3 T0 T1 T2 y < 0 then
      !(containsNondegenerate T0 T1 T2
        (segment3Point x y (orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y))) &&
        !allowed m fa fb (segment3Point x y (orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y))))
      else true) = true := by
    intro h
    exact hbad (by rw [Bool.and_eq_true, Bool.and_eq_true]; exact ⟨⟨c1t, c2t⟩, h⟩)
  by_cases hxy : orient3 T0 T1 T2 x * orient3 T0 T1 T2 y < 0
  · rw [if_pos hxy] at h3
    have hcc : (containsNondegenerate T0 T1 T2
        (segment3Point x y (orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y))) &&
        !allowed m fa fb (segment3Point x y (orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y)))) = true := by
      by_contra hh
      apply h3
      simp [Bool.not_eq_true] at hh ⊢
      by_cases hco : containsNondegenerate T0 T1 T2
          (segment3Point x y (orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y))) = true
      · exact Or.inr (hh hco)
      · exact Or.inl (by simpa using hco)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcc
    set Dx := orient3 T0 T1 T2 x
    set Dy := orient3 T0 T1 T2 y
    have hden : Dx - Dy ≠ 0 := by
      intro h
      have : Dx = Dy := by linarith
      rw [this] at hxy; nlinarith [sq_nonneg Dy]
    have hx0 : Dx ≠ 0 := by intro h; rw [h] at hxy; simp at hxy
    have t0 : 0 ≤ Dx / (Dx - Dy) ∧ Dx / (Dx - Dy) ≤ 1 := by
      rcases lt_or_gt_of_ne hx0 with h1 | h1
      · have h2 : 0 < Dy := by nlinarith
        have hd : Dx - Dy < 0 := by linarith
        exact ⟨div_nonneg_of_nonpos h1.le hd.le, (div_le_one_of_neg hd).mpr (by linarith)⟩
      · have h2 : Dy < 0 := by nlinarith
        have hd : 0 < Dx - Dy := by linarith
        exact ⟨div_nonneg h1.le hd.le, (div_le_one hd).mpr (by linarith)⟩
    have hpl : orient3 T0 T1 T2 (segment3Point x y (Dx / (Dx - Dy))) = 0 := by
      rw [orient3_segment]
      field_simp
      ring
    exact ⟨_, _, t0.1, t0.2, rfl, hcont _ hcc.1 hpl, hcc.2⟩
  · rw [if_neg hxy] at h3
    exact absurd rfl h3

theorem hull3_face_vertex (m : ExactMesh) (f : Face) (i : Nat) (hi : i < 3) :
    Hull3 (m.point f.a) (m.point f.b) (m.point f.c) (m.point (faceId f i)) := by
  interval_cases i
  · exact hull3_vertex0 _ _ _
  · exact hull3_vertex1 _ _ _
  · exact hull3_vertex2 _ _ _

theorem hull3_face_edge (m : ExactMesh) (f : Face) (i : Nat) (hi : i < 3) (s : Rat) (s0 : 0 ≤ s)
    (s1 : s ≤ 1) :
    Hull3 (m.point f.a) (m.point f.b) (m.point f.c)
      (segment3Point (m.point (faceId f i)) (m.point (faceId f ((i + 1) % 3))) s) :=
  hull3_segment _ _ _ _ _ (hull3_face_vertex m f i hi)
    (hull3_face_vertex m f ((i + 1) % 3) (Nat.mod_lt _ (by norm_num))) s s0 s1

/-- Noncoplanar faces without shared IDs: a rejected pair has a common point. -/
theorem pairOk_false_noncoplanar_common (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = []) (hd' : commonIds fb fa = [])
    (hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (hrej : pairOk m fa fb = false) :
    ∃ p : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p ∧
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
  unfold pairOk at hrej
  rw [hpa, hpb] at hrej
  have hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = false := by
    cases h : (List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)
    · rfl
    · exact absurd h hnc
  simp only [hcop, Bool.false_eq_true, if_false, Bool.and_eq_false_iff] at hrej
  rcases hrej with h | h
  · obtain ⟨i, hi, r, s, s0, s1, hr, hH⟩ := edgesAgainst_false_contact m fa fb pb hpb hd h
    exact ⟨r, by rw [hr]; exact hull3_face_edge m fa i hi s s0 s1, hH⟩
  · obtain ⟨i, hi, r, s, s0, s1, hr, hH⟩ := edgesAgainst_false_contact m fb fa pa hpa hd' h
    exact ⟨r, hH, by rw [hr]; exact hull3_face_edge m fb i hi s s0 s1⟩

theorem sharedCount_zero (fa fb : Face) (hd : commonIds fa fb = []) : sharedCount fa fb = 0 := by
  unfold sharedCount
  have h := ids_ne_of_common_nil fa fb hd
  have z : ∀ k l, k < 3 → l < 3 → (if faceId fa k = faceId fb l then 1 else 0) = 0 := by
    intro k l hk hl
    rw [if_neg (h k l hk hl)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_cons, List.foldl_nil]
  simp [z]

/-- Coplanar faces without shared IDs: a rejected pair has a common point (both faces lie in one plane,
nondegenerate in the projection along `pa`). -/
theorem pairOk_false_coplanar_common (m : ExactMesh) (fa fb : Face) (pa : Nat) (hlt : pa < 3)
    (hpa : projAxis m fa = some pa) (hpb : ∃ pb, projAxis m fb = some pb)
    (hd : commonIds fa fb = [])
    (hAnd : orient (projectPoint3 pa (m.point fa.a)) (projectPoint3 pa (m.point fa.b))
      (projectPoint3 pa (m.point fa.c)) ≠ 0)
    (hBnd : orient (projectPoint3 pa (m.point fb.a)) (projectPoint3 pa (m.point fb.b))
      (projectPoint3 pa (m.point fb.c)) ≠ 0)
    (hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (hcopA : ∀ k, k < 3 → orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point (faceId fa k)) = 0)
    (hcopB : ∀ k, k < 3 → orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point (faceId fb k)) = 0)
    (hrej : pairOk m fa fb = false) :
    ∃ p : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p ∧
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
  obtain ⟨pb, hpb'⟩ := hpb
  unfold pairOk at hrej
  rw [hpa, hpb'] at hrej
  simp only [hcop, if_true] at hrej
  have hshared := sharedCount_zero fa fb hd
  have hnall := allowed_of_disjoint m fa fb hd
  have hcA : ∀ P, containsPt m fa pa P ↔
      Tri2 (projectPoint3 pa (m.point fa.a)) (projectPoint3 pa (m.point fa.b))
        (projectPoint3 pa (m.point fa.c)) (projectPoint3 pa P) := by
    intro P; unfold containsPt containsProject; rw [← contains2_iff_Tri2]
  have hcB : ∀ P, containsPt m fb pa P ↔
      Tri2 (projectPoint3 pa (m.point fb.a)) (projectPoint3 pa (m.point fb.b))
        (projectPoint3 pa (m.point fb.c)) (projectPoint3 pa P) := by
    intro P; unfold containsPt containsProject; rw [← contains2_iff_Tri2]
  have hfp : ∀ (f : Face) (k : Nat), facePoint m f k = m.point (faceId f k) := by
    intro f k; unfold facePoint faceId; rfl
  have h3 : decide (sharedCount fa fb ≠ 3) = true := by rw [hshared]; decide
  rw [h3, Bool.and_true] at hrej
  have hAvert : ∀ k, k < 3 → Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point (faceId fa k)) :=
    fun k hk => hull3_face_vertex m fa k hk
  have hBvert : ∀ k, k < 3 → Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point (faceId fb k)) :=
    fun k hk => hull3_face_vertex m fb k hk
  rw [Bool.and_eq_false_iff] at hrej
  rcases hrej with hpts | hsegs
  · rw [List.all_eq_false] at hpts
    obtain ⟨k, hk, hbad⟩ := hpts
    simp only [List.mem_range] at hk
    simp only [hnall, hfp, Bool.not_false, Bool.and_true] at hbad
    by_cases hA : containsPt m fb pa (m.point (faceId fa k)) = true
    · refine ⟨m.point (faceId fa k), hAvert k hk, ?_⟩
      exact tri2_hull_axis pa hlt _ _ _ _ hBnd (hcopA k hk) ((hcB _).mp hA)
    · have hB : containsPt m fa pa (m.point (faceId fb k)) = true := by
        by_contra hB
        apply hbad
        have hA' : containsPt m fb pa (m.point (faceId fa k)) = false := by simpa using hA
        have hB' : containsPt m fa pa (m.point (faceId fb k)) = false := by simpa using hB
        simp [hA', hB']
      refine ⟨m.point (faceId fb k), ?_, hBvert k hk⟩
      exact tri2_hull_axis pa hlt _ _ _ _ hAnd (hcopB k hk) ((hcA _).mp hB)
  · rw [List.all_eq_false] at hsegs
    obtain ⟨k, hk, hbad⟩ := hsegs
    simp only [List.mem_range] at hk
    rw [Bool.not_eq_true, List.all_eq_false] at hbad
    obtain ⟨l, hl, hbad2⟩ := hbad
    simp only [List.mem_range] at hl
    have hconf : segmentConflict (withAxis m pa) (faceId fa k) (faceId fa ((k + 1) % 3))
        (faceId fb l) (faceId fb ((l + 1) % 3)) = true := by simpa using hbad2
    have hci := segmentConflict_closedIntersection _ _ _ _ _ hconf
    obtain ⟨z, ⟨sA, sA0, sA1, hzA⟩, ⟨sB, sB0, sB1, hzB⟩⟩ := (closedIntersection_iff_rational _ _ _ _).mp hci
    have hkk : (k + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hll : (l + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have pA : orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c)
        (segment3Point (m.point (faceId fa k)) (m.point (faceId fa ((k + 1) % 3))) sA) = 0 := by
      have := hull3_plane _ _ _ _ (hull3_face_edge m fa k hk sA sA0 sA1)
      exact this
    have pB : orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c)
        (segment3Point (m.point (faceId fb l)) (m.point (faceId fb ((l + 1) % 3))) sB) = 0 := by
      rw [orient3_segment, hcopB l hl, hcopB _ hll]; ring
    have heq : segment3Point (m.point (faceId fa k)) (m.point (faceId fa ((k + 1) % 3))) sA =
        segment3Point (m.point (faceId fb l)) (m.point (faceId fb ((l + 1) % 3))) sB := by
      apply plane_inj_axis pa hlt _ _ _ _ _ hAnd pA pB
      rw [projectPoint3_segment, projectPoint3_segment]
      exact hzA.symm.trans hzB
    exact ⟨_, hull3_face_edge m fa k hk sA sA0 sA1, by rw [heq]; exact hull3_face_edge m fb l hl sB sB0 sB1⟩

/-- Noncoplanar faces without shared vertex IDs: the auditor accepts exactly the disjoint pairs. -/
theorem pairOk_iff_disjoint_noncoplanar (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hd : commonIds fa fb = []) (hd' : commonIds fb fa = [])
    (hnc' : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0)) :
    pairOk m fa fb = true ↔
      ¬ ∃ p : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p ∧
        Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
  have hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true := by
    intro h
    apply hnc'
    simp only [List.range_succ, List.range_zero, List.nil_append, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, facePoint, planeValue_eq_orient3] at h
    simp only [Nat.reduceEqDiff, if_true, if_false, ite_true, ite_false, decide_eq_true_eq,
      Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  constructor
  · intro hok
    exact accepted_noncoplanar_disjoint m fa fb pa pb hpa hpb hd hnc' hok
  · intro hdis
    by_contra hrej
    have hrej' : pairOk m fa fb = false := by simpa using hrej
    exact hdis (pairOk_false_noncoplanar_common m fa fb pa pb hpa hpb hd hd' hnc hrej')

theorem between3_param (a b t : Rat) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    between3 a b (a + t * (b - a)) = true := by
  unfold between3
  by_cases h : a ≤ b
  · simp only [h, if_true, decide_eq_true_eq]
    constructor <;> nlinarith
  · simp only [h, if_false, decide_eq_true_eq]
    have : b < a := lt_of_not_ge h
    constructor <;> nlinarith

theorem allowed_of_segment (m : ExactMesh) (fa fb : Face) (i j : Nat) (hd : commonIds fa fb = [i, j])
    (t : Rat) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    allowed m fa fb (segment3Point (m.point i) (m.point j) t) = true := by
  unfold allowed
  rw [hd]
  by_cases hany : [i, j].any (fun id => m.point id == segment3Point (m.point i) (m.point j) t) = true
  · simp only [hany, if_true]
  · simp only [hany, if_false]
    have bx := between3_param (m.point i).x (m.point j).x t t0 t1
    have by_ := between3_param (m.point i).y (m.point j).y t t0 t1
    have bz := between3_param (m.point i).z (m.point j).z t t0 t1
    simp only [Bool.false_eq_true, ite_false]
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨bx, by_⟩, bz⟩
    · exact decide_eq_true (show _ ∧ _ ∧ _ from
        ⟨by simp only [segment3Point]; ring, by simp only [segment3Point]; ring,
         by simp only [segment3Point]; ring⟩)

theorem allowed_of_edge_point (m : ExactMesh) (fa fb : Face) (ix iy : Nat)
    (hd : commonIds fa fb = [ix, iy] ∨ commonIds fa fb = [iy, ix]) (t : Rat) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    allowed m fa fb (segment3Point (m.point ix) (m.point iy) t) = true := by
  rcases hd with hd | hd
  · exact allowed_of_segment m fa fb ix iy hd t t0 t1
  · have := allowed_of_segment m fa fb iy ix hd (1 - t) (by linarith) (by linarith)
    have e : segment3Point (m.point iy) (m.point ix) (1 - t) = segment3Point (m.point ix) (m.point iy) t := by
      simp only [segment3Point]; congr 1 <;> ring
    rw [e] at this; exact this

/-- Noncoplanar faces sharing an edge are accepted: all their common points are on the shared edge,
which `allowed` admits. -/
theorem pairOk_of_shared_edge_noncoplanar (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (ix iy iu iw j l : Nat) (hj : j < 3) (hl : l < 3)
    (hxj : faceId fa j = ix) (hyj : faceId fa ((j + 1) % 3) = iy) (huj : faceId fa ((j + 2) % 3) = iu)
    (hbl : faceId fb l = ix ∧
      ((faceId fb ((l + 1) % 3) = iy ∧ faceId fb ((l + 2) % 3) = iw) ∨
       (faceId fb ((l + 1) % 3) = iw ∧ faceId fb ((l + 2) % 3) = iy)))
    (hd1 : commonIds fa fb = [ix, iy] ∨ commonIds fa fb = [iy, ix])
    (hd2 : commonIds fb fa = [ix, iy] ∨ commonIds fb fa = [iy, ix])
    (hnc' : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0))
    (hW : orient3 (m.point ix) (m.point iy) (m.point iw) (m.point iu) ≠ 0) :
    pairOk m fa fb = true := by
  have hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true := by
    intro h
    apply hnc'
    simp only [List.range_succ, List.range_zero, List.nil_append, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, facePoint, planeValue_eq_orient3] at h
    simp only [Nat.reduceEqDiff, if_true, if_false, ite_true, ite_false, decide_eq_true_eq,
      Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  -- every common point lies on the shared edge
  have common : ∀ r : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) r →
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r →
      ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ r = segment3Point (m.point ix) (m.point iy) t := by
    intro r hrA hrB
    set PA : Nat → Point3 := fun k => m.point (faceId fa k) with hPA
    set PB : Nat → Point3 := fun k => m.point (faceId fb k) with hPB
    have hA' : Hull3 (m.point ix) (m.point iy) (m.point iu) r := by
      have := (hull3_rot3 PA j hj r).mpr hrA
      simp only [hPA, hxj, hyj, huj] at this
      exact this
    have hB' : Hull3 (m.point ix) (m.point iy) (m.point iw) r := by
      have := (hull3_rot3 PB l hl r).mpr hrB
      rcases hbl.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [hPB, hbl.1, h1, h2] at this; exact this
      · simp only [hPB, hbl.1, h1, h2] at this; exact (hull3_swap23 _ _ _ _).mpr this
    exact (shared_edge_intersection _ _ _ _ r hW).mp ⟨hA', hB'⟩
  by_contra hrej
  have hrej' : pairOk m fa fb = false := by simpa using hrej
  unfold pairOk at hrej'
  rw [hpa, hpb] at hrej'
  have hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = false := by
    cases h : (List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)
    · rfl
    · exact absurd h hnc
  simp only [hcop, Bool.false_eq_true, if_false, Bool.and_eq_false_iff] at hrej'
  rcases hrej' with h | h
  · obtain ⟨i, hi, r, s, s0, s1, hr, hH, hal⟩ := edgesAgainst_false_contact' m fa fb pb hpb h
    have hrA : Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) r := by
      rw [hr]; exact hull3_face_edge m fa i hi s s0 s1
    obtain ⟨t, t0, t1, ht⟩ := common r hrA hH
    rw [ht, allowed_of_edge_point m fa fb ix iy hd1 t t0 t1] at hal
    exact absurd hal (by decide)
  · obtain ⟨i, hi, r, s, s0, s1, hr, hH, hal⟩ := edgesAgainst_false_contact' m fb fa pa hpa h
    have hrB : Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r := by
      rw [hr]; exact hull3_face_edge m fb i hi s s0 s1
    obtain ⟨t, t0, t1, ht⟩ := common r hH hrB
    rw [ht, allowed_of_edge_point m fb fa ix iy hd2 t t0 t1] at hal
    exact absurd hal (by decide)

/-- Noncoplanar faces are accepted as soon as every common point is admitted by `allowed` (in both
argument orders). -/
theorem pairOk_of_common_allowed (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (h1 : ∀ r : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) r →
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r → allowed m fa fb r = true)
    (h2 : ∀ r : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) r →
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r → allowed m fb fa r = true) :
    pairOk m fa fb = true := by
  by_contra hrej
  have hrej' : pairOk m fa fb = false := by simpa using hrej
  unfold pairOk at hrej'
  rw [hpa, hpb] at hrej'
  have hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = false := by
    cases h : (List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)
    · rfl
    · exact absurd h hnc
  simp only [hcop, Bool.false_eq_true, if_false, Bool.and_eq_false_iff] at hrej'
  rcases hrej' with h | h
  · obtain ⟨i, hi, r, s, s0, s1, hr, hH, hal⟩ := edgesAgainst_false_contact' m fa fb pb hpb h
    have hrA : Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) r := by
      rw [hr]; exact hull3_face_edge m fa i hi s s0 s1
    rw [h1 r hrA hH] at hal; exact absurd hal (by decide)
  · obtain ⟨i, hi, r, s, s0, s1, hr, hH, hal⟩ := edgesAgainst_false_contact' m fb fa pa hpa h
    have hrB : Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r := by
      rw [hr]; exact hull3_face_edge m fb i hi s s0 s1
    rw [h2 r hH hrB] at hal; exact absurd hal (by decide)

theorem allowed_of_vertex (m : ExactMesh) (fa fb : Face) (vid : Nat) (hd : commonIds fa fb = [vid]) :
    allowed m fa fb (m.point vid) = true := by
  unfold allowed
  rw [hd]
  simp

/-- Noncoplanar faces whose only common point is the single shared vertex are accepted. -/
theorem pairOk_of_shared_vertex_noncoplanar (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb) (vid : Nat)
    (hd1 : commonIds fa fb = [vid]) (hd2 : commonIds fb fa = [vid])
    (hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (honly : ∀ r : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) r →
      Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r → r = m.point vid) :
    pairOk m fa fb = true :=
  pairOk_of_common_allowed m fa fb pa pb hpa hpb hnc
    (fun r hA hB => by rw [honly r hA hB]; exact allowed_of_vertex m fa fb vid hd1)
    (fun r hA hB => by rw [honly r hA hB]; exact allowed_of_vertex m fb fa vid hd2)

/-- Noncoplanar faces sharing exactly one vertex: the auditor accepts exactly when the triangles
meet only at that vertex. -/
theorem pairOk_iff_shared_vertex_noncoplanar (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (vid j l : Nat) (hj : j < 3) (hl : l < 3)
    (hvj : faceId fa j = vid) (hvl : faceId fb l = vid)
    (hd1 : commonIds fa fb = [vid]) (hd2 : commonIds fb fa = [vid])
    (hnc' : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0))
    (hnc'' : ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = 0)) :
    pairOk m fa fb = true ↔
      ∀ r : Point3, Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) r →
        Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r → r = m.point vid := by
  have hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true := by
    intro h
    apply hnc'
    simp only [List.range_succ, List.range_zero, List.nil_append, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, facePoint, planeValue_eq_orient3] at h
    simp only [Nat.reduceEqDiff, if_true, if_false, ite_true, ite_false, decide_eq_true_eq,
      Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  constructor
  · intro hok r hA hB
    exact accepted_shared_vertex_only m fa fb pa pb hpa hpb vid j l hj hl hvj hvl hd1 hd2 hnc' hnc'' hok r hA hB
  · intro honly
    exact pairOk_of_shared_vertex_noncoplanar m fa fb pa pb hpa hpb vid hd1 hd2 hnc honly

end PairAudit
end Tess
