import Tess.PairAuditRotation

namespace Tess
namespace PairAudit

theorem ratio_mem (C D : Rat) (h : C * D < 0) : 0 < C / (C - D) ∧ C / (C - D) < 1 := by
  rcases lt_trichotomy C 0 with c | c | c
  · have hD : 0 < D := by nlinarith
    have hne : C - D < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg c hne, by rw [div_lt_one_of_neg hne]; linarith⟩
  · rw [c] at h; simp at h
  · have hD : D < 0 := by nlinarith
    have hne : 0 < C - D := by linarith
    exact ⟨div_pos c hne, by rw [div_lt_one hne]; linarith⟩

/-- Two segments in opposite closed half-planes (one strictly positive somewhere) cannot cross
properly. -/
theorem no_cross (G D p q r s : Point2) (hp : 0 ≤ side G D p) (hq : 0 ≤ side G D q)
    (hpq : 0 < side G D p + side G D q) (hr : side G D r ≤ 0) (hs : side G D s ≤ 0) :
    ¬ (orient p q r * orient p q s < 0 ∧ orient r s p * orient r s q < 0) := by
  rintro ⟨h1, h2⟩
  have hAB : orient p q r - orient p q s ≠ 0 := by
    intro h
    have : orient p q r = orient p q s := by linarith
    rw [this] at h1; nlinarith [sq_nonneg (orient p q s)]
  have hrel : orient p q r - orient p q s = orient r s q - orient r s p := by
    unfold orient; ring
  obtain ⟨hu0, hu1⟩ := ratio_mem _ _ h2
  obtain ⟨ht0, ht1⟩ := ratio_mem _ _ h1
  set u := orient r s p / (orient r s p - orient r s q) with hu
  set t := orient p q r / (orient p q r - orient p q s) with ht
  have hCD : orient r s p - orient r s q ≠ 0 := by
    intro h; apply hAB; linarith
  have hx : segmentPoint p q u = segmentPoint r s t := by
    have hden : orient p q r - orient p q s ≠ 0 := hAB
    have hu' : u = -(orient r s p) / (orient p q r - orient p q s) := by
      rw [hu, hrel, ← neg_div_neg_eq]; congr 1 <;> ring
    have ht' : t = orient p q r / (orient p q r - orient p q s) := rfl
    rw [hu', ht']
    unfold segmentPoint
    have hden' : (orient p q r - orient p q s) ≠ 0 := hden
    congr 1
    · field_simp
      unfold orient
      ring
    · field_simp
      unfold orient
      ring
  have g1 := side_seg G D p q u
  have g2 := side_seg G D r s t
  have key : (1 - u) * side G D p + u * side G D q = (1 - t) * side G D r + t * side G D s := by
    rw [← g1, ← g2, hx]
  have lhs : 0 < (1 - u) * side G D p + u * side G D q := by
    rcases lt_or_ge 0 (side G D p) with h | h
    · nlinarith [mul_pos (sub_pos.mpr hu1) h, mul_nonneg hu0.le hq]
    · have hp0 : side G D p = 0 := le_antisymm h hp
      have : 0 < side G D q := by linarith
      nlinarith [mul_pos hu0 this]
  nlinarith [mul_nonneg ht0.le (neg_nonneg.mpr hs), mul_nonneg (sub_pos.mpr ht1).le (neg_nonneg.mpr hr)]


theorem onSeg_pos_strict (G D a b x : Point2) (ha : 0 < side G D a) (hb : 0 < side G D b)
    (hx : side G D x ≤ 0) : ¬ onSegment a b x = true := by
  intro h
  obtain ⟨t, t0, t1, rfl⟩ := onSegment_rational a b x h
  rw [side_seg] at hx
  rcases eq_or_lt_of_le t1 with h | h
  · rw [h] at hx; nlinarith
  · nlinarith [mul_pos (sub_pos.mpr h) ha, mul_nonneg t0 hb.le]

theorem onSeg_neg_strict (G D a b x : Point2) (ha : side G D a < 0) (hb : side G D b < 0)
    (hx : 0 ≤ side G D x) : ¬ onSegment a b x = true := by
  intro h
  obtain ⟨t, t0, t1, rfl⟩ := onSegment_rational a b x h
  rw [side_seg] at hx
  rcases eq_or_lt_of_le t1 with h | h
  · rw [h] at hx; nlinarith
  · nlinarith [mul_pos (sub_pos.mpr h) (neg_pos.mpr ha), mul_nonneg t0 (neg_nonneg.mpr hb.le)]

theorem bary_id (G D a b c x : Point2) :
    orient a b c * side G D x = orient b c x * side G D a + orient c a x * side G D b +
      orient a b x * side G D c := by
  unfold side orient; ring

theorem tri_sum (a b c x : Point2) : orient a b c = orient a b x + orient b c x + orient c a x := by
  unfold orient; ring

theorem contains_pos_false (G D a b c x : Point2) (ha : side G D a ≤ 0) (hb : side G D b ≤ 0)
    (hc : side G D c ≤ 0) (hx : 0 < side G D x) (hA : orient a b c ≠ 0) :
    contains2 a b c x = false := by
  unfold contains2
  have hid := bary_id G D a b c x
  have hs := tri_sum a b c x
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, not_and, not_le]
  rcases lt_trichotomy (orient a b c) 0 with hneg | hzero | hpos
  · constructor
    · by_contra hcon
      simp only [not_or, not_lt] at hcon
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
      linarith
    · by_contra hcon
      simp only [not_or, not_lt] at hcon
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
      have := mul_neg_of_neg_of_pos hneg hx
      nlinarith [mul_nonneg_of_nonpos_of_nonpos h2 ha, mul_nonneg_of_nonpos_of_nonpos h3 hb,
        mul_nonneg_of_nonpos_of_nonpos h1 hc]
  · exact absurd hzero hA
  · constructor
    · by_contra hcon
      simp only [not_or, not_lt] at hcon
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
      have := mul_pos hpos hx
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 ha, mul_nonpos_of_nonneg_of_nonpos h3 hb,
        mul_nonpos_of_nonneg_of_nonpos h1 hc]
    · by_contra hcon
      simp only [not_or, not_lt] at hcon
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
      linarith

section Vertex
variable (ip iq ir is it : Nat) (P Q R S T D : Point2)
  (hd : [ip, iq, ir, is, it].Nodup)
  (gq : 0 < side P D Q) (gr : 0 < side P D R) (gs : side P D S < 0) (gt : side P D T < 0)

theorem side_self (P D : Point2) : side P D P = 0 := by unfold side orient; ring


include hd gq gr gs gt in
theorem vpair_PQ_PS : segC ip iq ip is P Q P S = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D P Q S (sP.ge) (gq.le) (gs)
  have f1 := onSeg_nonpos P D P S Q (sP.le) (gs.le) (gq)
  have fx := no_cross P D P Q P S (sP.ge) (gq.le) (by linarith) (sP.le) (gs.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, fx]

include hd gq gr gs gt in
theorem vpair_PQ_ST : segC ip iq is it P Q S T = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D P Q S (sP.ge) (gq.le) (gs)
  have f1 := onSeg_nonneg P D P Q T (sP.ge) (gq.le) (gt)
  have f2 := onSeg_neg_strict P D S T P (gs) (gt) (by linarith)
  have f3 := onSeg_nonpos P D S T Q (gs.le) (gt.le) (gq)
  have fx := no_cross P D P Q S T (sP.ge) (gq.le) (by linarith) (gs.le) (gt.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, f2, f3, fx]

include hd gq gr gs gt in
theorem vpair_PQ_TP : segC ip iq it ip P Q T P = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D P Q T (sP.ge) (gq.le) (gt)
  have f1 := onSeg_nonpos P D T P Q (gt.le) (sP.le) (gq)
  have fx := no_cross P D P Q T P (sP.ge) (gq.le) (by linarith) (gt.le) (sP.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, fx]

include hd gq gr gs gt in
theorem vpair_QR_PS : segC iq ir ip is Q R P S = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_pos_strict P D Q R P (gq) (gr) (by linarith)
  have f1 := onSeg_nonneg P D Q R S (gq.le) (gr.le) (gs)
  have f2 := onSeg_nonpos P D P S Q (sP.le) (gs.le) (gq)
  have f3 := onSeg_nonpos P D P S R (sP.le) (gs.le) (gr)
  have fx := no_cross P D Q R P S (gq.le) (gr.le) (by linarith) (sP.le) (gs.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, f2, f3, fx]

include hd gq gr gs gt in
theorem vpair_QR_ST : segC iq ir is it Q R S T = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D Q R S (gq.le) (gr.le) (gs)
  have f1 := onSeg_nonneg P D Q R T (gq.le) (gr.le) (gt)
  have f2 := onSeg_nonpos P D S T Q (gs.le) (gt.le) (gq)
  have f3 := onSeg_nonpos P D S T R (gs.le) (gt.le) (gr)
  have fx := no_cross P D Q R S T (gq.le) (gr.le) (by linarith) (gs.le) (gt.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, f2, f3, fx]

include hd gq gr gs gt in
theorem vpair_QR_TP : segC iq ir it ip Q R T P = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D Q R T (gq.le) (gr.le) (gt)
  have f1 := onSeg_pos_strict P D Q R P (gq) (gr) (by linarith)
  have f2 := onSeg_nonpos P D T P Q (gt.le) (sP.le) (gq)
  have f3 := onSeg_nonpos P D T P R (gt.le) (sP.le) (gr)
  have fx := no_cross P D Q R T P (gq.le) (gr.le) (by linarith) (gt.le) (sP.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, f2, f3, fx]

include hd gq gr gs gt in
theorem vpair_RP_PS : segC ir ip ip is R P P S = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D R P S (gr.le) (sP.ge) (gs)
  have f1 := onSeg_nonpos P D P S R (sP.le) (gs.le) (gr)
  have fx := no_cross P D R P P S (gr.le) (sP.ge) (by linarith) (sP.le) (gs.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, fx]

include hd gq gr gs gt in
theorem vpair_RP_ST : segC ir ip is it R P S T = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D R P S (gr.le) (sP.ge) (gs)
  have f1 := onSeg_nonneg P D R P T (gr.le) (sP.ge) (gt)
  have f2 := onSeg_nonpos P D S T R (gs.le) (gt.le) (gr)
  have f3 := onSeg_neg_strict P D S T P (gs) (gt) (by linarith)
  have fx := no_cross P D R P S T (gr.le) (sP.ge) (by linarith) (gs.le) (gt.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, f2, f3, fx]

include hd gq gr gs gt in
theorem vpair_RP_TP : segC ir ip it ip R P T P = false := by
  have sP := side_self P D
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  have f0 := onSeg_nonneg P D R P T (gr.le) (sP.ge) (gt)
  have f1 := onSeg_nonpos P D T P R (gt.le) (sP.le) (gr)
  have fx := no_cross P D R P T P (gr.le) (sP.ge) (by linarith) (gt.le) (sP.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), f0, f1, fx]

end Vertex

theorem side_reflect (G D x : Point2) :
    side G ⟨2 * G.x - D.x, 2 * G.y - D.y⟩ x = - side G D x := by unfold side orient; ring

theorem contains_neg_false (G D a b c x : Point2) (ha : 0 ≤ side G D a) (hb : 0 ≤ side G D b)
    (hc : 0 ≤ side G D c) (hx : side G D x < 0) (hA : orient a b c ≠ 0) :
    contains2 a b c x = false := by
  apply contains_pos_false G ⟨2 * G.x - D.x, 2 * G.y - D.y⟩ a b c x _ _ _ _ hA
  all_goals rw [side_reflect]
  all_goals linarith

theorem commonIds_vertex (ip iq ir is it : Nat) (hd : [ip, iq, ir, is, it].Nodup) :
    commonIds ⟨ip, iq, ir⟩ ⟨ip, is, it⟩ = [ip] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  simp [commonIds, faceId, List.range_succ, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10,
    Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7,
    Ne.symm n8, Ne.symm n9, Ne.symm n10]

theorem sharedCount_vertex (ip iq ir is it : Nat) (hd : [ip, iq, ir, is, it].Nodup) :
    sharedCount ⟨ip, iq, ir⟩ ⟨ip, is, it⟩ = 1 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd
  simp [sharedCount, faceId, List.range_succ, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10,
    Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7,
    Ne.symm n8, Ne.symm n9, Ne.symm n10]

/-- Completeness for coplanar faces `(P,Q,R)` and `(P,S,T)` sharing exactly the vertex `P`, strictly
separated by a line through `P` (`Q,R` strictly on one side, `S,T` strictly on the other). -/
theorem pairOk_vertex_coplanar (m : ExactMesh) (ip iq ir is it pa pb : Nat)
    (hd : [ip, iq, ir, is, it].Nodup)
    (hA : projAxis m ⟨ip, iq, ir⟩ = some pa) (hB : projAxis m ⟨ip, is, it⟩ = some pb)
    (hS : planeValue m ⟨ip, iq, ir⟩ (m.point is) = 0) (hT : planeValue m ⟨ip, iq, ir⟩ (m.point it) = 0)
    (D : Point2)
    (gq : 0 < side ((withAxis m pa).project ip) D ((withAxis m pa).project iq))
    (gr : 0 < side ((withAxis m pa).project ip) D ((withAxis m pa).project ir))
    (gs : side ((withAxis m pa).project ip) D ((withAxis m pa).project is) < 0)
    (gt : side ((withAxis m pa).project ip) D ((withAxis m pa).project it) < 0)
    (hAa : orient ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project ir) ≠ 0)
    (hAb : orient ((withAxis m pa).project ip) ((withAxis m pa).project is)
      ((withAxis m pa).project it) ≠ 0) :
    pairOk m ⟨ip, iq, ir⟩ ⟨ip, is, it⟩ = true := by
  have hd0 := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd0
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10, -⟩ := hd0
  set P := (withAxis m pa).project ip
  set Q := (withAxis m pa).project iq
  set R := (withAxis m pa).project ir
  set S := (withAxis m pa).project is
  set T := (withAxis m pa).project it
  have cQ : containsPt m ⟨ip, is, it⟩ pa (m.point iq) = false :=
    contains_pos_false P D P S T Q (by rw [side_self]) gs.le gt.le gq hAb
  have cR : containsPt m ⟨ip, is, it⟩ pa (m.point ir) = false :=
    contains_pos_false P D P S T R (by rw [side_self]) gs.le gt.le gr hAb
  have cS : containsPt m ⟨ip, iq, ir⟩ pa (m.point is) = false :=
    contains_neg_false P D P Q R S (by rw [side_self]) gq.le gr.le gs hAa
  have cT : containsPt m ⟨ip, iq, ir⟩ pa (m.point it) = false :=
    contains_neg_false P D P Q R T (by rw [side_self]) gq.le gr.le gt hAa
  have cmn := commonIds_vertex ip iq ir is it hd
  have sc := sharedCount_vertex ip iq ir is it hd
  have al : allowed m ⟨ip, iq, ir⟩ ⟨ip, is, it⟩ (m.point ip) = true := by
    unfold allowed; rw [cmn]; simp
  have pa1 := planeValue_a m ⟨ip, iq, ir⟩
  have pb1 := planeValue_b m ⟨ip, iq, ir⟩
  have pc1 := planeValue_c m ⟨ip, iq, ir⟩
  have hcopl : (List.range 3).all (fun k => decide (planeValue m ⟨ip, iq, ir⟩
      (facePoint m ⟨ip, is, it⟩ k) = 0)) = true := by
    simp [List.range_succ, facePoint, hS, hT, pa1]
  unfold pairOk
  rw [hA, hB]
  simp only []
  rw [if_pos hcopl]
  have e1 := vpair_PQ_PS ip iq ir is it P Q R S T D hd gq gr gs gt
  have e2 := vpair_PQ_ST ip iq ir is it P Q R S T D hd gq gr gs gt
  have e3 := vpair_PQ_TP ip iq ir is it P Q R S T D hd gq gr gs gt
  have e4 := vpair_QR_PS ip iq ir is it P Q R S T D hd gq gr gs gt
  have e5 := vpair_QR_ST ip iq ir is it P Q R S T D hd gq gr gs gt
  have e6 := vpair_QR_TP ip iq ir is it P Q R S T D hd gq gr gs gt
  have e7 := vpair_RP_PS ip iq ir is it P Q R S T D hd gq gr gs gt
  have e8 := vpair_RP_ST ip iq ir is it P Q R S T D hd gq gr gs gt
  have e9 := vpair_RP_TP ip iq ir is it P Q R S T D hd gq gr gs gt
  simp [List.range_succ, facePoint, faceId, segmentConflict_eq, cQ, cR, cS, cT, al, sc,
    e1, e2, e3, e4, e5, e6, e7, e8, e9]
  exact ⟨⟨e1, e2, e3⟩, ⟨e4, e5, e6⟩, ⟨e7, e8, e9⟩⟩

/-- The vertex-only acceptance for every cyclic rotation of either face. -/
theorem pairOk_vertex_coplanar_rot (m : ExactMesh) (ip iq ir is it pa pb : Nat)
    (hd : [ip, iq, ir, is, it].Nodup)
    (hA : projAxis m ⟨ip, iq, ir⟩ = some pa) (hB : projAxis m ⟨ip, is, it⟩ = some pb)
    (hS : planeValue m ⟨ip, iq, ir⟩ (m.point is) = 0) (hT : planeValue m ⟨ip, iq, ir⟩ (m.point it) = 0)
    (D : Point2)
    (gq : 0 < side ((withAxis m pa).project ip) D ((withAxis m pa).project iq))
    (gr : 0 < side ((withAxis m pa).project ip) D ((withAxis m pa).project ir))
    (gs : side ((withAxis m pa).project ip) D ((withAxis m pa).project is) < 0)
    (gt : side ((withAxis m pa).project ip) D ((withAxis m pa).project it) < 0)
    (hAa : orient ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project ir) ≠ 0)
    (hAb : orient ((withAxis m pa).project ip) ((withAxis m pa).project is)
      ((withAxis m pa).project it) ≠ 0)
    (fa fb : Face)
    (hfa : fa = ⟨ip, iq, ir⟩ ∨ fa = ⟨iq, ir, ip⟩ ∨ fa = ⟨ir, ip, iq⟩)
    (hfb : fb = ⟨ip, is, it⟩ ∨ fb = ⟨is, it, ip⟩ ∨ fb = ⟨it, ip, is⟩) :
    pairOk m fa fb = true := by
  have base := pairOk_vertex_coplanar m ip iq ir is it pa pb hd hA hB hS hT D gq gr gs gt hAa hAb
  have pP := planeValue_a m ⟨ip, iq, ir⟩
  have pRa : ∀ p, planeValue m ⟨iq, ir, ip⟩ p = planeValue m ⟨ip, iq, ir⟩ p :=
    fun p => planeValue_rot m ip iq ir p
  have pRb : ∀ p, planeValue m ⟨ir, ip, iq⟩ p = planeValue m ⟨ip, iq, ir⟩ p := fun p =>
    (planeValue_rot m iq ir ip p).trans (planeValue_rot m ip iq ir p)
  have cop : ∀ fb', (fb' = ⟨ip, is, it⟩ ∨ fb' = ⟨is, it, ip⟩ ∨ fb' = ⟨it, ip, is⟩) →
      ∀ fa', (fa' = ⟨ip, iq, ir⟩ ∨ fa' = ⟨iq, ir, ip⟩ ∨ fa' = ⟨ir, ip, iq⟩) →
      (List.range 3).all (fun k => decide (planeValue m fa' (facePoint m fb' k) = 0)) = true := by
    intro fb' hb fa' ha
    rcases hb with rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;>
      simp [List.range_succ, facePoint, pRa, pRb, pP, hS, hT]
  have rb : ∀ fb', (fb' = ⟨ip, is, it⟩ ∨ fb' = ⟨is, it, ip⟩ ∨ fb' = ⟨it, ip, is⟩) →
      pairOk m ⟨ip, iq, ir⟩ fb' = true := by
    intro fb' h
    rcases h with rfl | rfl | rfl
    · exact base
    · rw [pairOk_rotB m ⟨ip, iq, ir⟩ ip is it (cop _ (Or.inl rfl) _ (Or.inl rfl))]; exact base
    · have e1 := pairOk_rotB m ⟨ip, iq, ir⟩ is it ip (cop _ (Or.inr (Or.inl rfl)) _ (Or.inl rfl))
      have e2 := pairOk_rotB m ⟨ip, iq, ir⟩ ip is it (cop _ (Or.inl rfl) _ (Or.inl rfl))
      rw [e1, e2]; exact base
  have ra : ∀ fb', (fb' = ⟨ip, is, it⟩ ∨ fb' = ⟨is, it, ip⟩ ∨ fb' = ⟨it, ip, is⟩) →
      pairOk m fa fb' = true := by
    intro fb' hb
    have hb0 := rb fb' hb
    rcases hfa with rfl | rfl | rfl
    · exact hb0
    · rw [pairOk_rotA m ip iq ir fb' (cop fb' hb _ (Or.inl rfl))]; exact hb0
    · have e1 := pairOk_rotA m iq ir ip fb' (cop fb' hb _ (Or.inr (Or.inl rfl)))
      have e2 := pairOk_rotA m ip iq ir fb' (cop fb' hb _ (Or.inl rfl))
      rw [e1, e2]; exact hb0
  exact ra fb hfb

end PairAudit
end Tess
