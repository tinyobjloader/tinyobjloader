import Tess.PairAuditNoncoplanarFull
import Tess.SharedVertex

namespace Tess
namespace PairAudit

theorem hull3_cyc (a b c p : Point3) : Hull3 a b c p ↔ Hull3 b c a p := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩
    exact ⟨v, w, u, hv, hw, hu, by linarith, by rw [hx]; ring, by rw [hy]; ring, by rw [hz]; ring⟩
  · rintro ⟨u, v, w, hu, hv, hw, hs, hx, hy, hz⟩
    exact ⟨w, u, v, hw, hu, hv, by linarith, by rw [hx]; ring, by rw [hy]; ring, by rw [hz]; ring⟩

/-- Accepted edge checks: a point of the other triangle on an edge with an endpoint off the
other plane is only allowed if the auditor's `allowed` rule admits it. -/
theorem edgesAgainst_contact (m : ExactMesh) (fa fb : Face) (pb : Nat)
    (hpb : projAxis m fb = some pb) (hacc : edgesAgainst m fa fb pb = true)
    (i : Nat) (hi : i < 3) (r : Point3)
    (hr : Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) r)
    (s : Rat) (s0 : 0 ≤ s) (s1 : s ≤ 1)
    (hseg : r = segment3Point (m.point (faceId fa i)) (m.point (faceId fa ((i + 1) % 3))) s)
    (hnot : ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point (faceId fa i)) = 0 ∧
               orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c)
                 (m.point (faceId fa ((i + 1) % 3))) = 0)) :
    allowed m fa fb r = true := by
  have hc : ∀ p, containsPt m fb pb p =
      containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p
    unfold containsPt containsNondegenerate
    unfold projAxis at hpb
    rw [hpb]
  have hpv : ∀ p, planeValue m fb p = orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p := by
    intro p; rw [planeValue_eq_orient3]
  have hcont : containsNondegenerate (m.point fb.a) (m.point fb.b) (m.point fb.c) r = true := by
    apply containsNondegenerate_of_hull _ _ _ _ pb
    · exact hpb
    · exact hr
  unfold edgesAgainst at hacc
  simp only [List.all_eq_true, List.mem_range] at hacc
  have h := hacc i hi
  simp only [hc, hpv, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set x := m.point (faceId fa i)
  set y := m.point (faceId fa ((i + 1) % 3))
  set T0 := m.point fb.a; set T1 := m.point fb.b; set T2 := m.point fb.c
  have hplane := hull3_plane T0 T1 T2 r hr
  rw [hseg, orient3_segment] at hplane
  by_cases hx : orient3 T0 T1 T2 x = 0
  · have hy : orient3 T0 T1 T2 y ≠ 0 := fun h' => hnot ⟨hx, h'⟩
    rw [hx] at hplane
    have hs0 : s = 0 := by
      have : s * orient3 T0 T1 T2 y = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hy
    have hrx : r = x := by rw [hseg, hs0]; simp only [segment3Point]; cases x; simp
    rw [hrx] at hcont ⊢
    by_contra hn
    have hn' : allowed m fa fb x = false := by simpa using hn
    simp [hx, hcont, hn'] at h1
  · by_cases hy : orient3 T0 T1 T2 y = 0
    · rw [hy] at hplane
      have hs1 : s = 1 := by
        have : (1 - s) * orient3 T0 T1 T2 x = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_right hx
        linarith
      have hry : r = y := by rw [hseg, hs1]; simp only [segment3Point]; cases y; simp
      rw [hry] at hcont ⊢
      by_contra hn
      have hn' : allowed m fa fb y = false := by simpa using hn
      simp [hy, hcont, hn'] at h2
    · have hxy : orient3 T0 T1 T2 x * orient3 T0 T1 T2 y < 0 := by
        by_contra hnn
        have hnn' : 0 ≤ orient3 T0 T1 T2 x * orient3 T0 T1 T2 y := not_lt.mp hnn
        rcases lt_or_gt_of_ne hx with h1 | h1 <;> rcases lt_or_gt_of_ne hy with h2 | h2
        · rcases le_total s (1/2) with hs2 | hs2
          · nlinarith [mul_nonneg (sub_nonneg.2 s1) (neg_nonneg.2 h1.le), mul_nonneg s0 (neg_nonneg.2 h2.le)]
          · nlinarith [mul_nonneg (sub_nonneg.2 s1) (neg_nonneg.2 h1.le), mul_nonneg s0 (neg_nonneg.2 h2.le)]
        · nlinarith
        · nlinarith
        · rcases le_total s (1/2) with hs2 | hs2
          · nlinarith [mul_nonneg (sub_nonneg.2 s1) h1.le, mul_nonneg s0 h2.le]
          · nlinarith [mul_nonneg (sub_nonneg.2 s1) h1.le, mul_nonneg s0 h2.le]
      have hden : orient3 T0 T1 T2 x - orient3 T0 T1 T2 y ≠ 0 := by
        intro h
        have : orient3 T0 T1 T2 x = orient3 T0 T1 T2 y := by linarith
        rw [this] at hxy; nlinarith [sq_nonneg (orient3 T0 T1 T2 y)]
      have hsval : s = orient3 T0 T1 T2 x / (orient3 T0 T1 T2 x - orient3 T0 T1 T2 y) := by
        field_simp
        linarith
      rw [if_pos hxy] at h3
      rw [← hsval, ← hseg] at h3
      by_contra hn
      have hn' : allowed m fa fb r = false := by simpa using hn
      simp [hcont, hn'] at h3

theorem hull3_rot3 (P : Nat → Point3) (j : Nat) (hj : j < 3) (p : Point3) :
    Hull3 (P j) (P ((j + 1) % 3)) (P ((j + 2) % 3)) p ↔ Hull3 (P 0) (P 1) (P 2) p := by
  interval_cases j
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceMod]
    exact (hull3_cyc (P 0) (P 1) (P 2) p).symm
  · simp only [Nat.reduceAdd, Nat.reduceMod]
    exact ((hull3_cyc (P 0) (P 1) (P 2) p).trans (hull3_cyc (P 1) (P 2) (P 0) p)).symm

theorem allowed_single (m : ExactMesh) (fa fb : Face) (vid : Nat) (hd : commonIds fa fb = [vid])
    (r : Point3) (h : allowed m fa fb r = true) : r = m.point vid := by
  by_contra hn
  unfold allowed at h
  rw [hd] at h
  have hn' : ¬ m.point vid = r := fun e => hn e.symm
  simp [hn'] at h

theorem pairOk_noncoplanar_edges (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (hok : pairOk m fa fb = true) :
    edgesAgainst m fa fb pb = true ∧ edgesAgainst m fb fa pa = true := by
  unfold pairOk at hok
  rw [hpa, hpb] at hok
  have hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = false := by
    cases h : (List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)
    · rfl
    · exact absurd h hnc
  simp only [hcop, Bool.false_eq_true, if_false, Bool.and_eq_true] at hok
  exact hok

/-- Noncoplanar faces sharing exactly one vertex: an accepted pair meets only at that vertex. -/
theorem accepted_shared_vertex_only (m : ExactMesh) (fa fb : Face) (pa pb : Nat)
    (hpa : projAxis m fa = some pa) (hpb : projAxis m fb = some pb)
    (vid j l : Nat) (hj : j < 3) (hl : l < 3)
    (hvj : faceId fa j = vid) (hvl : faceId fb l = vid)
    (hd1 : commonIds fa fb = [vid]) (hd2 : commonIds fb fa = [vid])
    (hnc' : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.a) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.b) = 0 ∧
               orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point fb.c) = 0))
    (hnc'' : ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.a) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.b) = 0 ∧
                orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point fa.c) = 0))
    (hok : pairOk m fa fb = true) (p : Point3)
    (hpA : Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p)
    (hpB : Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p) :
    p = m.point vid := by
  have hnc : ¬ ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true := by
    intro h
    apply hnc'
    simp only [List.range_succ, List.range_zero, List.nil_append, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, facePoint, planeValue_eq_orient3] at h
    simp only [Nat.reduceEqDiff, if_true, if_false, ite_true, ite_false, decide_eq_true_eq,
      Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  obtain ⟨hacc1, hacc2⟩ := pairOk_noncoplanar_edges m fa fb pa pb hpa hpb hnc hok
  by_contra hne
  set PA : Nat → Point3 := fun k => m.point (faceId fa k) with hPA
  set PB : Nat → Point3 := fun k => m.point (faceId fb k) with hPB
  have hPA3 : Hull3 (PA 0) (PA 1) (PA 2) p := hpA
  have hPB3 : Hull3 (PB 0) (PB 1) (PB 2) p := hpB
  have hvA : PA j = m.point vid := by simp only [hPA, hvj]
  have hvB : PB l = m.point vid := by simp only [hPB, hvl]
  have hA' := (hull3_rot3 PA j hj p).mpr hPA3
  have hB' := (hull3_rot3 PB l hl p).mpr hPB3
  rw [hvA] at hA'
  rw [hvB] at hB'
  have hne' : p ≠ m.point vid := hne
  rcases shared_vertex_contact _ _ _ _ _ p hA' hB' hne' with
    ⟨y, hyA, ⟨s, s0, s1, hys⟩, hyv⟩ | ⟨x, hxB, ⟨s, s0, s1, hxs⟩, hxv⟩
  · -- `y` lies in A on the edge of B opposite the shared vertex
    have hyA3 : Hull3 (PA 0) (PA 1) (PA 2) y := by
      rw [← hvA] at hyA
      exact (hull3_rot3 PA j hj y).mp hyA
    have hnot : ¬ (orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point (faceId fb ((l + 1) % 3))) = 0 ∧
        orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point (faceId fb (((l + 1) % 3 + 1) % 3))) = 0) := by
      rintro ⟨h1, h2⟩
      apply hnc'
      have vz := orient3_vertex_zero (m.point fa.a) (m.point fa.b) (m.point fa.c)
      have hvz : orient3 (m.point fa.a) (m.point fa.b) (m.point fa.c) (m.point vid) = 0 := by
        rw [← hvA]
        interval_cases j <;> simp only [hPA, faceId] <;> simp_all
      interval_cases l <;> simp only [faceId, hPB] at hvB h1 h2 <;> simp_all
    have e : ((l + 1) % 3 + 1) % 3 = (l + 2) % 3 := by omega
    have hseg' : y = segment3Point (m.point (faceId fb ((l + 1) % 3)))
        (m.point (faceId fb (((l + 1) % 3 + 1) % 3))) s := by
      rw [e]; exact hys
    have hallowed := edgesAgainst_contact m fb fa pa hpa hacc2 ((l + 1) % 3) (Nat.mod_lt _ (by norm_num))
      y hyA3 s s0 s1 hseg' hnot
    have := allowed_single m fb fa vid hd2 y hallowed
    exact hyv (by rw [this])
  · -- `x` lies in B on the edge of A opposite the shared vertex
    have hxB3 : Hull3 (PB 0) (PB 1) (PB 2) x := by
      rw [← hvB] at hxB
      exact (hull3_rot3 PB l hl x).mp hxB
    have hnot : ¬ (orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point (faceId fa ((j + 1) % 3))) = 0 ∧
        orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point (faceId fa (((j + 1) % 3 + 1) % 3))) = 0) := by
      rintro ⟨h1, h2⟩
      apply hnc''
      have vz := orient3_vertex_zero (m.point fb.a) (m.point fb.b) (m.point fb.c)
      have hvz : orient3 (m.point fb.a) (m.point fb.b) (m.point fb.c) (m.point vid) = 0 := by
        rw [← hvB]
        interval_cases l <;> simp only [hPB, faceId] <;> simp_all
      interval_cases j <;> simp only [faceId, hPA] at hvA h1 h2 <;> simp_all
    have e : ((j + 1) % 3 + 1) % 3 = (j + 2) % 3 := by omega
    have hseg' : x = segment3Point (m.point (faceId fa ((j + 1) % 3)))
        (m.point (faceId fa (((j + 1) % 3 + 1) % 3))) s := by
      rw [e]; exact hxs
    have hallowed := edgesAgainst_contact m fa fb pb hpb hacc1 ((j + 1) % 3) (Nat.mod_lt _ (by norm_num))
      x hxB3 s s0 s1 hseg' hnot
    have := allowed_single m fa fb vid hd1 x hallowed
    exact hxv (by rw [this])

end PairAudit
end Tess
