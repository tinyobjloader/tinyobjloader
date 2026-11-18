import Tess.PairAudit
import Tess.SegmentSoundness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Tess
namespace PairAudit

/-- `segmentConflict` with the projected points abstracted. -/
def segC (a b c d : Nat) (p q r s : Point2) : Bool :=
  if (a=c && b=d) || (a=d && b=c) then false else
  (decide (c≠a ∧ c≠b) && onSegment p q r) ||
  (decide (d≠a ∧ d≠b) && onSegment p q s) ||
  (decide (a≠c ∧ a≠d) && onSegment r s p) ||
  (decide (b≠c ∧ b≠d) && onSegment r s q) ||
  decide (orient p q r * orient p q s < 0 ∧ orient r s p * orient r s q < 0)

theorem segmentConflict_eq (m : ExactMesh) (a b c d : Nat) :
    segmentConflict m a b c d = segC a b c d (m.project a) (m.project b) (m.project c) (m.project d) := rfl

section Halfplane
variable (P Q : Point2)

/-- The signed side of `x` with respect to the directed line `P Q`. -/
def side (x : Point2) : Rat := orient P Q x

theorem side_seg (a b : Point2) (t : Rat) :
    side P Q (segmentPoint a b t) = (1 - t) * side P Q a + t * side P Q b := by
  unfold side orient segmentPoint; ring

theorem onSeg_nonneg (a b x : Point2) (ha : 0 ≤ side P Q a) (hb : 0 ≤ side P Q b)
    (hx : side P Q x < 0) : ¬ onSegment a b x = true := by
  intro h
  obtain ⟨t, t0, t1, rfl⟩ := onSegment_rational a b x h
  rw [side_seg] at hx
  nlinarith

theorem onSeg_nonpos (a b x : Point2) (ha : side P Q a ≤ 0) (hb : side P Q b ≤ 0)
    (hx : 0 < side P Q x) : ¬ onSegment a b x = true := by
  intro h
  obtain ⟨t, t0, t1, rfl⟩ := onSegment_rational a b x h
  rw [side_seg] at hx
  nlinarith

theorem onSeg_end_a (a b x : Point2) (ha : side P Q a = 0) (hb : side P Q b ≠ 0)
    (hx : side P Q x = 0) (h : onSegment a b x = true) : x = a := by
  obtain ⟨t, t0, t1, rfl⟩ := onSegment_rational a b x h
  rw [side_seg, ha] at hx
  have : t = 0 := by
    have : t * side P Q b = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hb
  subst this
  simp [segmentPoint]

theorem onSeg_end_b (a b x : Point2) (ha : side P Q a ≠ 0) (hb : side P Q b = 0)
    (hx : side P Q x = 0) (h : onSegment a b x = true) : x = b := by
  obtain ⟨t, t0, t1, rfl⟩ := onSegment_rational a b x h
  rw [side_seg, hb] at hx
  have : 1 - t = 0 := by
    have : (1 - t) * side P Q a = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h ha
  have ht : t = 1 := by linarith
  subst ht
  simp [segmentPoint]

end Halfplane


section Adjacent
variable (ip iq ir is : Nat) (P Q R S : Point2)
  (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is) (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is)
  (hR : 0 < side P Q R) (hS : side P Q S < 0)

theorem side_P : side P Q P = 0 := by unfold side orient; ring
theorem side_Q : side P Q Q = 0 := by unfold side orient; ring

theorem P_ne_Q (hR : 0 < side P Q R) : P ≠ Q := by
  intro h; subst h; unfold side orient at hR; simp at hR

theorem orient_cyc (a b c : Point2) : orient a b c = orient b c a := by unfold orient; ring
theorem orient_swap (a b c : Point2) : orient a b c = - orient b a c := by unfold orient; ring
theorem four_pt (P Q R S : Point2) :
    side P Q R - side P Q S + orient P R S - orient Q R S = 0 := by unfold side orient; ring

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_QR_PS : segC iq ir ip is Q R P S = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have ha : ¬ onSegment Q R P = true := fun h =>
    hne (onSeg_end_a P Q Q R P sQ (ne_of_gt hR) sP h)
  have hb : ¬ onSegment Q R S = true := onSeg_nonneg P Q Q R S sQ.ge hR.le hS
  have hc : ¬ onSegment P S Q = true := fun h =>
    hne.symm (onSeg_end_a P Q P S Q sP (ne_of_lt hS) sQ h)
  have hd : ¬ onSegment P S R = true := onSeg_nonpos P Q P S R sP.le hS.le hR
  have he : ¬ (orient Q R P * orient Q R S < 0 ∧ orient P S Q * orient P S R < 0) := by
    rintro ⟨c1, c2⟩
    have o1 : orient Q R P = side P Q R := by rw [← orient_cyc]; rfl
    have o2 : orient P S Q = - side P Q S := by
      unfold side orient; ring
    have o3 : orient P S R = - orient P R S := by unfold orient; ring
    rw [o1] at c1; rw [o2, o3] at c2
    have hid := four_pt P Q R S
    have : orient Q R S < 0 := by nlinarith
    have : 0 < orient P R S := by nlinarith
    linarith
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ha, hb, hc, hd, he]


include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_PQ_QP : segC ip iq iq ip P Q Q P = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_PQ_PS : segC ip iq ip is P Q P S = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hb : ¬ onSegment P Q S = true := onSeg_nonneg P Q P Q S sP.ge sQ.ge hS
  have hc : ¬ onSegment P S Q = true := fun h => hne.symm (onSeg_end_a P Q P S Q sP (ne_of_lt hS) sQ h)
  have he : ¬ (orient P Q P * orient P Q S < 0 ∧ orient P S P * orient P S Q < 0) := by
    rintro ⟨c1, -⟩
    have : orient P Q P = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hb, hc, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_PQ_SQ : segC ip iq is iq P Q S Q = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have ha : ¬ onSegment P Q S = true := onSeg_nonneg P Q P Q S sP.ge sQ.ge hS
  have hc : ¬ onSegment S Q P = true := fun h => hne (onSeg_end_b P Q S Q P (ne_of_lt hS) sQ sP h)
  have he : ¬ (orient P Q S * orient P Q Q < 0 ∧ orient S Q P * orient S Q Q < 0) := by
    rintro ⟨c1, -⟩
    have : orient P Q Q = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ha, hc, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_QR_QP : segC iq ir iq ip Q R Q P = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hb : ¬ onSegment Q R P = true := fun h => hne (onSeg_end_a P Q Q R P sQ (ne_of_gt hR) sP h)
  have hc : ¬ onSegment Q P R = true := onSeg_nonpos P Q Q P R sQ.le sP.le hR
  have he : ¬ (orient Q R Q * orient Q R P < 0 ∧ orient Q P Q * orient Q P R < 0) := by
    rintro ⟨c1, -⟩
    have : orient Q R Q = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hb, hc, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_QR_SQ : segC iq ir is iq Q R S Q = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have ha : ¬ onSegment Q R S = true := onSeg_nonneg P Q Q R S sQ.ge hR.le hS
  have hc : ¬ onSegment S Q R = true := onSeg_nonpos P Q S Q R hS.le sQ.le hR
  have he : ¬ (orient Q R S * orient Q R Q < 0 ∧ orient S Q Q * orient S Q R < 0) := by
    rintro ⟨c1, -⟩
    have : orient Q R Q = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ha, hc, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_RP_QP : segC ir ip iq ip R P Q P = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have ha : ¬ onSegment R P Q = true := fun h => hne.symm (onSeg_end_b P Q R P Q (ne_of_gt hR) sP sQ h)
  have hc : ¬ onSegment Q P R = true := onSeg_nonpos P Q Q P R sQ.le sP.le hR
  have he : ¬ (orient R P Q * orient R P P < 0 ∧ orient Q P R * orient Q P P < 0) := by
    rintro ⟨c1, -⟩
    have : orient R P P = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ha, hc, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_RP_PS : segC ir ip ip is R P P S = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hb : ¬ onSegment R P S = true := onSeg_nonneg P Q R P S hR.le sP.ge hS
  have hc : ¬ onSegment P S R = true := onSeg_nonpos P Q P S R sP.le hS.le hR
  have he : ¬ (orient R P P * orient R P S < 0 ∧ orient P S R * orient P S P < 0) := by
    rintro ⟨c1, -⟩
    have : orient R P P = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hb, hc, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem pair_RP_SQ : segC ir ip is iq R P S Q = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have ha : ¬ onSegment R P S = true := onSeg_nonneg P Q R P S hR.le sP.ge hS
  have hb : ¬ onSegment R P Q = true := fun h => hne.symm (onSeg_end_b P Q R P Q (ne_of_gt hR) sP sQ h)
  have hc : ¬ onSegment S Q R = true := onSeg_nonpos P Q S Q R hS.le sQ.le hR
  have hd : ¬ onSegment S Q P = true := fun h => hne (onSeg_end_b P Q S Q P (ne_of_lt hS) sQ sP h)
  have he : ¬ (orient R P S * orient R P Q < 0 ∧ orient S Q R * orient S Q P < 0) := by
    rintro ⟨c1, c2⟩
    have o1 : orient R P Q = side P Q R := by unfold side orient; ring
    have o2 : orient S Q P = - side P Q S := by unfold side orient; ring
    have o3 : orient R P S = - orient P R S := by unfold orient; ring
    have o4 : orient S Q R = orient Q R S := by unfold orient; ring
    rw [o1] at c1; rw [o2] at c2
    have hid := four_pt P Q R S
    have : orient R P S < 0 := by nlinarith
    have : orient S Q R < 0 := by nlinarith
    linarith
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ha, hb, hc, hd, he]

end Adjacent

theorem area_decomp (A B C X : Point2) :
    orient A B X + orient B C X + orient C A X = orient A B C := by unfold orient; ring

theorem contains_R_false (P Q R S : Point2) (hR : 0 < side P Q R) (hS : side P Q S < 0) :
    contains2 Q P S R = false := by
  unfold contains2
  have hd := area_decomp Q P S R
  have o1 : orient Q P R = - side P Q R := by unfold side orient; ring
  have o2 : orient Q P S = - side P Q S := by unfold side orient; ring
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, not_and, not_le]
  constructor
  · left; left; rw [o1]; linarith
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨⟨a, b⟩, c⟩ := hc
    rw [o2] at hd; linarith

theorem contains_S_false (P Q R S : Point2) (hR : 0 < side P Q R) (hS : side P Q S < 0) :
    contains2 P Q R S = false := by
  unfold contains2
  have hd := area_decomp P Q R S
  have o1 : orient P Q S = side P Q S := rfl
  have o2 : orient P Q R = side P Q R := rfl
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, not_and, not_le]
  constructor
  · left; left; rw [o1]; linarith
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨⟨a, b⟩, c⟩ := hc
    rw [o1, o2] at hd; linarith

theorem planeValue_a (m : ExactMesh) (f : Face) : planeValue m f (m.point f.a) = 0 := by
  unfold planeValue; simp only []; ring
theorem planeValue_b (m : ExactMesh) (f : Face) : planeValue m f (m.point f.b) = 0 := by
  unfold planeValue; simp only []; ring
theorem planeValue_c (m : ExactMesh) (f : Face) : planeValue m f (m.point f.c) = 0 := by
  unfold planeValue; simp only []; ring

theorem commonIds_adj (ip iq ir is : Nat) (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is)
    (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is) :
    commonIds ⟨ip, iq, ir⟩ ⟨iq, ip, is⟩ = [ip, iq] := by
  simp [commonIds, faceId, List.range_succ, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm,
    h4.symm, h5.symm, h6.symm]

theorem sharedCount_adj (ip iq ir is : Nat) (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is)
    (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is) :
    sharedCount ⟨ip, iq, ir⟩ ⟨iq, ip, is⟩ = 2 := by
  simp [sharedCount, faceId, List.range_succ, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm,
    h4.symm, h5.symm, h6.symm]

theorem allowed_adj_p (m : ExactMesh) (ip iq ir is : Nat) (h1 : ip ≠ iq) (h2 : ip ≠ ir)
    (h3 : ip ≠ is) (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is) :
    allowed m ⟨ip, iq, ir⟩ ⟨iq, ip, is⟩ (m.point ip) = true ∧
    allowed m ⟨ip, iq, ir⟩ ⟨iq, ip, is⟩ (m.point iq) = true := by
  unfold allowed
  rw [commonIds_adj ip iq ir is h1 h2 h3 h4 h5 h6]
  simp

/-- Completeness for the common valid planar configuration: two coplanar faces `(P,Q,R)` and
`(Q,P,S)` (shared edge traversed in opposite directions) whose third vertices lie strictly on
opposite sides of the shared edge in the projection are accepted. -/
theorem pairOk_adjacent_coplanar (m : ExactMesh) (ip iq ir is pa pb : Nat)
    (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is) (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is)
    (hA : projAxis m ⟨ip, iq, ir⟩ = some pa) (hB : projAxis m ⟨iq, ip, is⟩ = some pb)
    (hcop : planeValue m ⟨ip, iq, ir⟩ (m.point is) = 0)
    (hR : 0 < side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project ir))
    (hS : side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project is) < 0) :
    pairOk m ⟨ip, iq, ir⟩ ⟨iq, ip, is⟩ = true := by
  have hCR := contains_R_false _ _ _ _ hR hS
  have hCS := contains_S_false _ _ _ _ hR hS
  obtain ⟨hal1, hal2⟩ := allowed_adj_p m ip iq ir is h1 h2 h3 h4 h5 h6
  have sc := sharedCount_adj ip iq ir is h1 h2 h3 h4 h5 h6
  have pa1 := planeValue_a m ⟨ip, iq, ir⟩
  have pb1 := planeValue_b m ⟨ip, iq, ir⟩
  unfold pairOk
  rw [hA, hB]
  simp only []
  have hcopl : (List.range 3).all (fun k => decide (planeValue m ⟨ip, iq, ir⟩
      (facePoint m ⟨iq, ip, is⟩ k) = 0)) = true := by
    simp [List.range_succ, facePoint, hcop, pb1, pa1]
  rw [if_pos hcopl]
  have hCR' : containsPt m ⟨iq, ip, is⟩ pa (m.point ir) = false := hCR
  have hCS' : containsPt m ⟨ip, iq, ir⟩ pa (m.point is) = false := hCS
  set P := (withAxis m pa).project ip
  set Q := (withAxis m pa).project iq
  set R := (withAxis m pa).project ir
  set S := (withAxis m pa).project is
  have e1 := pair_PQ_QP ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e2 := pair_PQ_PS ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e3 := pair_PQ_SQ ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e4 := pair_QR_QP ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e5 := pair_QR_PS ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e6 := pair_QR_SQ ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e7 := pair_RP_QP ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e8 := pair_RP_PS ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e9 := pair_RP_SQ ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  simp [List.range_succ, facePoint, faceId, segmentConflict_eq, hCR', hCS', hal1, hal2, sc,
    e1, e2, e3, e4, e5, e6, e7, e8, e9]
  exact ⟨⟨e1, e2, e3⟩, ⟨e4, e5, e6⟩, ⟨e7, e8, e9⟩⟩

end PairAudit
end Tess
