import Tess.PairAuditShared
import Tess.PairAuditCoplanar
import Tess.IntersectionCompleteness

namespace Tess
namespace PairAudit

theorem segmentPoint_comp (P Q : Point2) (s t : Rat) :
    segmentPoint (segmentPoint P Q s) P t = segmentPoint P Q (s + t * (0 - s)) := by
  simp only [segmentPoint]; congr 1 <;> ring

/-- In the coplanar branch, a point of the closed triangle `fa` lying on a segment `ie1 ie2` whose
endpoints are outside `fa` forces an edge-edge conflict (so the pair is rejected). -/
theorem coplanar_contact_false (m : ExactMesh) (fa : Face) (pa : Nat)
    (hlt : pa < 3)
    (hnd2 : orient (projectPoint3 pa (m.point fa.a)) (projectPoint3 pa (m.point fa.b))
      (projectPoint3 pa (m.point fa.c)) ≠ 0) (ie1 ie2 : Nat)
    (hidx : ie1 < m.points.size ∧ ie2 < m.points.size ∧ ∀ k, k < 3 → faceId fa k < m.points.size)
    (hne : (withAxis m pa).project ie1 ≠ (withAxis m pa).project ie2)
    (hnd : ∀ k, k < 3 → (withAxis m pa).project (faceId fa k) ≠
        (withAxis m pa).project (faceId fa ((k + 1) % 3)))
    (hdiff : ∀ k, k < 3 → faceId fa k ≠ ie1 ∧ faceId fa k ≠ ie2)
    (hv1 : containsPt m fa pa (m.point ie1) = false) (hv2 : containsPt m fa pa (m.point ie2) = false)
    (hsegs : ∀ k, k < 3 → segmentConflict (withAxis m pa) (faceId fa k) (faceId fa ((k + 1) % 3))
        ie1 ie2 = false)
    (y : Point3) (hy : Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) y)
    (hyE : ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ y = segment3Point (m.point ie1) (m.point ie2) s) : False := by
  obtain ⟨s, s0, s1, hys⟩ := hyE
  have hcA : ∀ p, containsPt m fa pa p ↔
      Tri2 (projectPoint3 pa (m.point fa.a)) (projectPoint3 pa (m.point fa.b))
        (projectPoint3 pa (m.point fa.c)) (projectPoint3 pa p) := by
    intro p
    unfold containsPt containsProject
    rw [← contains2_iff_Tri2]
  have n1 : ¬ Tri2 (projectPoint3 pa (m.point fa.a)) (projectPoint3 pa (m.point fa.b))
      (projectPoint3 pa (m.point fa.c)) (projectPoint3 pa (m.point ie1)) := by
    intro h; have := (hcA _).mpr h; rw [hv1] at this; exact absurd this (by decide)
  have hy2 := hull_tri2_axis pa hlt _ _ _ y hy
  obtain ⟨t, t0, t1, _, s2, s20, s21, hedge⟩ := tri2_exit _ _ _ _ _ hnd2 hy2 n1
  have hz : segmentPoint (projectPoint3 pa y) (projectPoint3 pa (m.point ie1)) t =
      segmentPoint (projectPoint3 pa (m.point ie1)) (projectPoint3 pa (m.point ie2)) (s + t * (0 - s)) := by
    rw [hys, projectPoint3_segment, segmentPoint_comp]
  have hp0 : 0 ≤ s + t * (0 - s) := by nlinarith
  have hp1 : s + t * (0 - s) ≤ 1 := by nlinarith
  have conclude : ∀ k, k < 3 →
      segmentPoint (projectPoint3 pa y) (projectPoint3 pa (m.point ie1)) t =
        segmentPoint ((withAxis m pa).project (faceId fa k))
          ((withAxis m pa).project (faceId fa ((k + 1) % 3))) s2 → False := by
    intro k hk hk2
    have hci : closedIntersection ((withAxis m pa).project (faceId fa k))
        ((withAxis m pa).project (faceId fa ((k + 1) % 3)))
        ((withAxis m pa).project ie1) ((withAxis m pa).project ie2) = true := by
      rw [closedIntersection_iff_rational]
      exact ⟨_, ⟨s2, s20, s21, hk2⟩, ⟨s + t * (0 - s), hp0, hp1, hz⟩⟩
    have hkk : (k + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have key := (segmentConflict_iff_closedIntersection (withAxis m pa) (faceId fa k)
      (faceId fa ((k + 1) % 3)) ie1 ie2 ⟨(hidx.2.2 k hk), hidx.2.2 _ hkk, hidx.1, hidx.2.1⟩
      ⟨hnd k hk, hne⟩ (hdiff k hk).1 (hdiff k hk).2 (hdiff _ hkk).1 (hdiff _ hkk).2).mpr hci
    rw [hsegs k hk] at key
    exact absurd key (by decide)
  rcases hedge with h | h | h
  · exact conclude 0 (by norm_num) (by
      rw [h]; rfl)
  · exact conclude 1 (by norm_num) (by
      rw [h]; rfl)
  · exact conclude 2 (by norm_num) (by
      rw [h]; rfl)

theorem segmentConflict_symm (m : ExactMesh) (a b c d : Nat) :
    segmentConflict m a b c d = segmentConflict m c d a b := by
  unfold segmentConflict
  have e1 : ((a = c && b = d) || (a = d && b = c)) = true ↔
      ((c = a && d = b) || (c = b && d = a)) = true := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  by_cases hc : ((a = c && b = d) || (a = d && b = c)) = true
  · have hc' : ((c = a && d = b) || (c = b && d = a)) = true := e1.mp hc
    simp only [hc, hc', if_true]
  · have hc' : ¬ ((c = a && d = b) || (c = b && d = a)) = true := fun h => hc (e1.mpr h)
    simp only [hc, hc', if_false]
    simp only [Bool.decide_and]
    generalize (decide (c ≠ a ∧ c ≠ b) && onSegment (m.project a) (m.project b) (m.project c)) = t1
    generalize (decide (d ≠ a ∧ d ≠ b) && onSegment (m.project a) (m.project b) (m.project d)) = t2
    generalize (decide (a ≠ c ∧ a ≠ d) && onSegment (m.project c) (m.project d) (m.project a)) = t3
    generalize (decide (b ≠ c ∧ b ≠ d) && onSegment (m.project c) (m.project d) (m.project b)) = t4
    generalize decide (orient (m.project a) (m.project b) (m.project c) * orient (m.project a) (m.project b) (m.project d) < 0) = t5
    generalize decide (orient (m.project c) (m.project d) (m.project a) * orient (m.project c) (m.project d) (m.project b) < 0) = t6
    cases t1 <;> cases t2 <;> cases t3 <;> cases t4 <;> cases t5 <;> cases t6 <;> rfl

theorem ids_ne_of_single (fa fb : Face) (vid : Nat) (hd : commonIds fa fb = [vid])
    (i k : Nat) (hi : i < 3) (hk : k < 3) (h : faceId fa i = faceId fb k) :
    faceId fa i = vid := by
  unfold commonIds at hd
  have hmem : faceId fa i ∈ ((List.range 3).flatMap fun i => (List.range 3).filterMap fun j =>
      if faceId fa i = faceId fb j then some (faceId fa i) else none) := by
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range]
    exact ⟨i, hi, k, hk, by simp [h]⟩
  rw [hd] at hmem
  simpa using hmem

/-- Coplanar faces sharing exactly one vertex: an accepted pair meets only at that vertex. -/
theorem accepted_coplanar_shared_vertex_only (m : ExactMesh) (fa fb : Face) (pa : Nat)
    (hlt : pa < 3)
    (hAnd : orient (projectPoint3 pa (m.point fa.a)) (projectPoint3 pa (m.point fa.b))
      (projectPoint3 pa (m.point fa.c)) ≠ 0)
    (hBnd : orient (projectPoint3 pa (m.point fb.a)) (projectPoint3 pa (m.point fb.b))
      (projectPoint3 pa (m.point fb.c)) ≠ 0)
    (vid j l : Nat) (hj : j < 3) (hl : l < 3)
    (hvj : faceId fa j = vid) (hvl : faceId fb l = vid)
    (hd1 : commonIds fa fb = [vid]) (hd2 : commonIds fb fa = [vid])
    (hpa : projAxis m fa = some pa)
    (hpb : ∃ pb, projAxis m fb = some pb)
    (hcop : ((List.range 3).all fun k => decide (planeValue m fa (facePoint m fb k) = 0)) = true)
    (hok : pairOk m fa fb = true)
    (hidx : ∀ k, k < 3 → faceId fa k < m.points.size ∧ faceId fb k < m.points.size)
    (hnd : ∀ k, k < 3 →
      (withAxis m pa).project (faceId fa k) ≠ (withAxis m pa).project (faceId fa ((k + 1) % 3)) ∧
      (withAxis m pa).project (faceId fb k) ≠ (withAxis m pa).project (faceId fb ((k + 1) % 3)))
    (p : Point3)
    (hpA : Hull3 (m.point fa.a) (m.point fa.b) (m.point fa.c) p)
    (hpB : Hull3 (m.point fb.a) (m.point fb.b) (m.point fb.c) p) :
    p = m.point vid := by
  obtain ⟨pb, hpb'⟩ := hpb
  unfold pairOk at hok
  rw [hpa, hpb'] at hok
  simp only [hcop, if_true, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff] at hok
  obtain ⟨⟨hpts, hsegs⟩, hshared⟩ := hok
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
  -- distinctness of ids inside a face (from nondegenerate projected edges)
  have idsne : ∀ (f : Face) (hf : ∀ k, k < 3 → (withAxis m pa).project (faceId f k) ≠
      (withAxis m pa).project (faceId f ((k + 1) % 3))) (i k : Nat), i < 3 → k < 3 → i ≠ k →
      faceId f i ≠ faceId f k := by
    intro f hf i k hi hk hik
    have h01 := hf 0 (by norm_num)
    have h12 := hf 1 (by norm_num)
    have h20 := hf 2 (by norm_num)
    simp only [Nat.reduceAdd, Nat.reduceMod] at h01 h12 h20
    have n01 : faceId f 0 ≠ faceId f 1 := fun h => h01 (by rw [h])
    have n12 : faceId f 1 ≠ faceId f 2 := fun h => h12 (by rw [h])
    have n20 : faceId f 2 ≠ faceId f 0 := fun h => h20 (by rw [h])
    interval_cases i <;> interval_cases k <;> first | exact (hik rfl).elim | exact n01 | exact (fun h => n01 h.symm) | exact n12 | exact (fun h => n12 h.symm) | exact n20 | exact (fun h => n20 h.symm)
  have hndA := fun k hk => (hnd k hk).1
  have hndB := fun k hk => (hnd k hk).2
  have ptne : ∀ i i' : Nat, (withAxis m pa).project i ≠ (withAxis m pa).project i' →
      m.point i ≠ m.point i' := by
    intro i i' h e
    exact h (congrArg (fun q : Point3 => (⟨q.coord ((pa + 1) % 3), q.coord ((pa + 2) % 3)⟩ : Point2)) e)
  have e1 : ((l + 1) % 3 + 1) % 3 = (l + 2) % 3 := by omega
  have e2 : ((j + 1) % 3 + 1) % 3 = (j + 2) % 3 := by omega
  have lm1 : (l + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have lm2 : (l + 2) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have jm1 : (j + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have jm2 : (j + 2) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have bdiffA : ∀ k, k < 3 → faceId fa k ≠ faceId fb ((l + 1) % 3) ∧ faceId fa k ≠ faceId fb ((l + 2) % 3) := by
    intro k hk
    constructor
    · intro h
      have hv := ids_ne_of_single fa fb vid hd1 k _ hk lm1 h
      exact idsne fb hndB l ((l + 1) % 3) hl lm1 (by omega) (by rw [hvl, ← hv, h])
    · intro h
      have hv := ids_ne_of_single fa fb vid hd1 k _ hk lm2 h
      exact idsne fb hndB l ((l + 2) % 3) hl lm2 (by omega) (by rw [hvl, ← hv, h])
  have adiffB : ∀ k, k < 3 → faceId fb k ≠ faceId fa ((j + 1) % 3) ∧ faceId fb k ≠ faceId fa ((j + 2) % 3) := by
    intro k hk
    constructor
    · intro h
      have hv := ids_ne_of_single fa fb vid hd1 _ k jm1 hk h.symm
      exact idsne fa hndA j ((j + 1) % 3) hj jm1 (by omega) (by rw [hvj, hv])
    · intro h
      have hv := ids_ne_of_single fa fb vid hd1 _ k jm2 hk h.symm
      exact idsne fa hndA j ((j + 2) % 3) hj jm2 (by omega) (by rw [hvj, hv])
  have notallowed : ∀ x : Point3, x ≠ m.point vid → allowed m fa fb x = false := by
    intro x hx
    by_contra h
    exact hx (allowed_single m fa fb vid hd1 x (by simpa using h))
  -- vertices of B other than the shared one are not inside A, and vice versa
  have bpt1 : m.point (faceId fb ((l + 1) % 3)) ≠ m.point vid := by
    have := ptne _ _ (hndB l hl)
    rw [hvl] at this
    exact fun h => this h.symm
  have bpt2 : m.point (faceId fb ((l + 2) % 3)) ≠ m.point vid := by
    have h0 := hndB ((l + 2) % 3) lm2
    have e3 : ((l + 2) % 3 + 1) % 3 = l := by omega
    rw [e3] at h0
    have := ptne _ _ h0
    rw [hvl] at this
    exact this
  have apt1 : m.point (faceId fa ((j + 1) % 3)) ≠ m.point vid := by
    have := ptne _ _ (hndA j hj)
    rw [hvj] at this
    exact fun h => this h.symm
  have apt2 : m.point (faceId fa ((j + 2) % 3)) ≠ m.point vid := by
    have h0 := hndA ((j + 2) % 3) jm2
    have e3 : ((j + 2) % 3 + 1) % 3 = j := by omega
    rw [e3] at h0
    have := ptne _ _ h0
    rw [hvj] at this
    exact this
  have hBin : ∀ k, k < 3 → m.point (faceId fb k) ≠ m.point vid → containsPt m fa pa (m.point (faceId fb k)) = false := by
    intro k hk hne2
    have h := (hpts k hk).2
    have hal := notallowed (m.point (faceId fb k)) hne2
    rcases h with h | h
    · exact h
    · exfalso; show False
      have : facePoint m fb k = m.point (faceId fb k) := by
        unfold facePoint faceId; rfl
      rw [this, hal] at h
      simp at h
  have hAin : ∀ k, k < 3 → m.point (faceId fa k) ≠ m.point vid → containsPt m fb pa (m.point (faceId fa k)) = false := by
    intro k hk hne2
    have h := (hpts k hk).1
    have hal := notallowed (m.point (faceId fa k)) hne2
    rcases h with h | h
    · have : facePoint m fa k = m.point (faceId fa k) := by
        unfold facePoint faceId; rfl
      rw [this] at h
      exact h
    · exfalso
      have : facePoint m fa k = m.point (faceId fa k) := by
        unfold facePoint faceId; rfl
      rw [this, hal] at h
      simp at h
  have hidxE : ∀ k, k < 3 → faceId fa k < m.points.size := fun k hk => (hidx k hk).1
  have hidxF : ∀ k, k < 3 → faceId fb k < m.points.size := fun k hk => (hidx k hk).2
  rcases shared_vertex_contact _ _ _ _ _ p hA' hB' hne' with
    ⟨y, hyA, ⟨s, s0, s1, hys⟩, hyv⟩ | ⟨x, hxB, ⟨s, s0, s1, hxs⟩, hxv⟩
  · have hyA3 : Hull3 (PA 0) (PA 1) (PA 2) y := by
      rw [← hvA] at hyA
      exact (hull3_rot3 PA j hj y).mp hyA
    have hne2 : (withAxis m pa).project (faceId fb ((l + 1) % 3)) ≠
        (withAxis m pa).project (faceId fb ((l + 2) % 3)) := by
      have := hndB ((l + 1) % 3) lm1
      rw [e1] at this; exact this
    have hsegsE : ∀ k, k < 3 → segmentConflict (withAxis m pa) (faceId fa k) (faceId fa ((k + 1) % 3))
        (faceId fb ((l + 1) % 3)) (faceId fb ((l + 2) % 3)) = false := by
      intro k hk
      have := hsegs k hk ((l + 1) % 3) lm1
      rw [e1] at this; exact this
    exact coplanar_contact_false m fa pa hlt hAnd (faceId fb ((l + 1) % 3)) (faceId fb ((l + 2) % 3))
      ⟨hidxF _ lm1, hidxF _ lm2, hidxE⟩ hne2 hndA bdiffA (hBin _ lm1 bpt1) (hBin _ lm2 bpt2) hsegsE y
      hyA3 ⟨s, s0, s1, hys⟩
  · have hxB3 : Hull3 (PB 0) (PB 1) (PB 2) x := by
      rw [← hvB] at hxB
      exact (hull3_rot3 PB l hl x).mp hxB
    have hne2 : (withAxis m pa).project (faceId fa ((j + 1) % 3)) ≠
        (withAxis m pa).project (faceId fa ((j + 2) % 3)) := by
      have := hndA ((j + 1) % 3) jm1
      rw [e2] at this; exact this
    have hsegsE : ∀ k, k < 3 → segmentConflict (withAxis m pa) (faceId fb k) (faceId fb ((k + 1) % 3))
        (faceId fa ((j + 1) % 3)) (faceId fa ((j + 2) % 3)) = false := by
      intro k hk
      have := hsegs ((j + 1) % 3) jm1 k hk
      rw [e2, segmentConflict_symm] at this; exact this
    exact coplanar_contact_false m fb pa hlt hBnd (faceId fa ((j + 1) % 3)) (faceId fa ((j + 2) % 3))
      ⟨hidxE _ jm1, hidxE _ jm2, hidxF⟩ hne2 hndB adiffB (hAin _ jm1 apt1) (hAin _ jm2 apt2) hsegsE x
      hxB3 ⟨s, s0, s1, hxs⟩

end PairAudit
end Tess
