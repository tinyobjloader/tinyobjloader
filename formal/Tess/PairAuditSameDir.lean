import Tess.PairAuditDisjointComplete

namespace Tess
namespace PairAudit

section SameDir
variable (ip iq ir is : Nat) (P Q R S : Point2)
  (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is) (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is)
  (hR : 0 < side P Q R) (hS : side P Q S < 0)

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_PQ_PQ : segC ip iq ip iq P Q P Q = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_PQ_QS : segC ip iq iq is P Q Q S = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hd : ¬ onSegment P Q S = true := onSeg_nonneg P Q P Q S sP.ge sQ.ge hS
  have ha : ¬ onSegment Q S P = true := fun h => hne (onSeg_end_a P Q Q S P sQ (ne_of_lt hS) sP h)
  have he : ¬ (orient P Q Q * orient P Q S < 0 ∧ orient Q S P * orient Q S Q < 0) := by
    rintro ⟨c1, -⟩
    have : orient P Q Q = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hd, ha, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_PQ_SP : segC ip iq is ip P Q S P = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hc : ¬ onSegment P Q S = true := onSeg_nonneg P Q P Q S sP.ge sQ.ge hS
  have hb : ¬ onSegment S P Q = true := fun h => hne.symm (onSeg_end_b P Q S P Q (ne_of_lt hS) sP sQ h)
  have he : ¬ (orient P Q S * orient P Q P < 0 ∧ orient S P P * orient S P Q < 0) := by
    rintro ⟨c1, -⟩
    have : orient P Q P = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hc, hb, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_QR_PQ : segC iq ir ip iq Q R P Q = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hc : ¬ onSegment Q R P = true := fun h => hne (onSeg_end_a P Q Q R P sQ (ne_of_gt hR) sP h)
  have hb : ¬ onSegment P Q R = true := onSeg_nonpos P Q P Q R sP.le sQ.le hR
  have he : ¬ (orient Q R P * orient Q R Q < 0 ∧ orient P Q Q * orient P Q R < 0) := by
    rintro ⟨c1, -⟩
    have : orient Q R Q = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hc, hb, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_QR_QS : segC iq ir iq is Q R Q S = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hd : ¬ onSegment Q R S = true := onSeg_nonneg P Q Q R S sQ.ge hR.le hS
  have hb : ¬ onSegment Q S R = true := onSeg_nonpos P Q Q S R sQ.le hS.le hR
  have he : ¬ (orient Q R Q * orient Q R S < 0 ∧ orient Q S Q * orient Q S R < 0) := by
    rintro ⟨c1, -⟩
    have : orient Q R Q = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hd, hb, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_QR_SP : segC iq ir is ip Q R S P = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hc : ¬ onSegment Q R S = true := onSeg_nonneg P Q Q R S sQ.ge hR.le hS
  have hd : ¬ onSegment Q R P = true := fun h => hne (onSeg_end_a P Q Q R P sQ (ne_of_gt hR) sP h)
  have ha : ¬ onSegment S P Q = true := fun h => hne.symm (onSeg_end_b P Q S P Q (ne_of_lt hS) sP sQ h)
  have hb : ¬ onSegment S P R = true := onSeg_nonpos P Q S P R hS.le sP.le hR
  have he : ¬ (orient Q R S * orient Q R P < 0 ∧ orient S P Q * orient S P R < 0) := by
    rintro ⟨c1, c2⟩
    have o1 : orient Q R P = side P Q R := by unfold side orient; ring
    have o2 : orient S P Q = side P Q S := by unfold side orient; ring
    have o3 : orient S P R = orient P R S := by unfold orient; ring
    rw [o1] at c1; rw [o2] at c2
    have hid := four_pt P Q R S
    have : orient Q R S < 0 := by nlinarith
    have : 0 < orient P R S := by nlinarith
    linarith
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hc, hd, ha, hb, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_RP_PQ : segC ir ip ip iq R P P Q = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hd : ¬ onSegment R P Q = true := fun h => hne.symm (onSeg_end_b P Q R P Q (ne_of_gt hR) sP sQ h)
  have ha : ¬ onSegment P Q R = true := onSeg_nonpos P Q P Q R sP.le sQ.le hR
  have he : ¬ (orient R P P * orient R P Q < 0 ∧ orient P Q R * orient P Q P < 0) := by
    rintro ⟨c1, -⟩
    have : orient R P P = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hd, ha, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_RP_QS : segC ir ip iq is R P Q S = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hc : ¬ onSegment R P Q = true := fun h => hne.symm (onSeg_end_b P Q R P Q (ne_of_gt hR) sP sQ h)
  have hd : ¬ onSegment R P S = true := onSeg_nonneg P Q R P S hR.le sP.ge hS
  have ha : ¬ onSegment Q S R = true := onSeg_nonpos P Q Q S R sQ.le hS.le hR
  have hb : ¬ onSegment Q S P = true := fun h => hne (onSeg_end_a P Q Q S P sQ (ne_of_lt hS) sP h)
  have he : ¬ (orient R P Q * orient R P S < 0 ∧ orient Q S R * orient Q S P < 0) := by
    rintro ⟨c1, c2⟩
    have o1 : orient R P Q = side P Q R := by unfold side orient; ring
    have o2 : orient Q S P = side P Q S := by unfold side orient; ring
    have o3 : orient R P S = - orient P R S := by unfold orient; ring
    have o4 : orient Q S R = - orient Q R S := by unfold orient; ring
    rw [o1] at c1; rw [o2] at c2
    have hid := four_pt P Q R S
    have : orient R P S < 0 := by nlinarith
    have : 0 < orient Q S R := by nlinarith
    linarith
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hc, hd, ha, hb, he]

include h1 h2 h3 h4 h5 h6 hR hS in
theorem sd_RP_SP : segC ir ip is ip R P S P = false := by
  have hne := P_ne_Q P Q R hR
  have sP := side_P P Q
  have sQ := side_Q P Q
  have hc : ¬ onSegment R P S = true := onSeg_nonneg P Q R P S hR.le sP.ge hS
  have ha : ¬ onSegment S P R = true := onSeg_nonpos P Q S P R hS.le sP.le hR
  have he : ¬ (orient R P S * orient R P P < 0 ∧ orient S P R * orient S P P < 0) := by
    rintro ⟨c1, -⟩
    have : orient R P P = 0 := by unfold orient; ring
    rw [this] at c1; simp at c1
  unfold segC
  simp [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hc, ha, he]

end SameDir

theorem contains_R_false' (P Q R S : Point2) (hR : 0 < side P Q R) (hS : side P Q S < 0) :
    contains2 P Q S R = false := by
  unfold contains2
  have hd := area_decomp P Q S R
  have o1 : orient P Q R = side P Q R := rfl
  have o2 : orient P Q S = side P Q S := rfl
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, not_and, not_le]
  constructor
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨⟨a, b⟩, c⟩ := hc
    rw [o2] at hd; linarith
  · left; left; rw [o1]; linarith

theorem commonIds_sd (ip iq ir is : Nat) (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is)
    (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is) :
    commonIds ⟨ip, iq, ir⟩ ⟨ip, iq, is⟩ = [ip, iq] := by
  simp [commonIds, faceId, List.range_succ, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm,
    h4.symm, h5.symm, h6.symm]

theorem sharedCount_sd (ip iq ir is : Nat) (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is)
    (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is) :
    sharedCount ⟨ip, iq, ir⟩ ⟨ip, iq, is⟩ = 2 := by
  simp [sharedCount, faceId, List.range_succ, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm,
    h4.symm, h5.symm, h6.symm]

/-- Same-direction variant: coplanar faces `(P,Q,R)` and `(P,Q,S)` with third vertices strictly on
opposite sides of the shared edge are accepted. -/
theorem pairOk_adjacent_samedir (m : ExactMesh) (ip iq ir is pa pb : Nat)
    (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is) (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is)
    (hA : projAxis m ⟨ip, iq, ir⟩ = some pa) (hB : projAxis m ⟨ip, iq, is⟩ = some pb)
    (hcop : planeValue m ⟨ip, iq, ir⟩ (m.point is) = 0)
    (hR : 0 < side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project ir))
    (hS : side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project is) < 0) :
    pairOk m ⟨ip, iq, ir⟩ ⟨ip, iq, is⟩ = true := by
  have hCR : containsPt m ⟨ip, iq, is⟩ pa (m.point ir) = false := contains_R_false' _ _ _ _ hR hS
  have hCS : containsPt m ⟨ip, iq, ir⟩ pa (m.point is) = false := contains_S_false _ _ _ _ hR hS
  have cmn := commonIds_sd ip iq ir is h1 h2 h3 h4 h5 h6
  have sc := sharedCount_sd ip iq ir is h1 h2 h3 h4 h5 h6
  have hal : allowed m ⟨ip, iq, ir⟩ ⟨ip, iq, is⟩ (m.point ip) = true ∧
      allowed m ⟨ip, iq, ir⟩ ⟨ip, iq, is⟩ (m.point iq) = true := by
    unfold allowed; rw [cmn]; simp
  obtain ⟨hal1, hal2⟩ := hal
  have pa1 := planeValue_a m ⟨ip, iq, ir⟩
  have pb1 := planeValue_b m ⟨ip, iq, ir⟩
  unfold pairOk
  rw [hA, hB]
  simp only []
  have hcopl : (List.range 3).all (fun k => decide (planeValue m ⟨ip, iq, ir⟩
      (facePoint m ⟨ip, iq, is⟩ k) = 0)) = true := by
    simp [List.range_succ, facePoint, hcop, pb1, pa1]
  rw [if_pos hcopl]
  set P := (withAxis m pa).project ip
  set Q := (withAxis m pa).project iq
  set R := (withAxis m pa).project ir
  set S := (withAxis m pa).project is
  have e1 := sd_PQ_PQ ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e2 := sd_PQ_QS ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e3 := sd_PQ_SP ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e4 := sd_QR_PQ ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e5 := sd_QR_QS ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e6 := sd_QR_SP ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e7 := sd_RP_PQ ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e8 := sd_RP_QS ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  have e9 := sd_RP_SP ip iq ir is P Q R S h1 h2 h3 h4 h5 h6 hR hS
  simp [List.range_succ, facePoint, faceId, segmentConflict_eq, hCR, hCS, hal1, hal2, sc]
  exact ⟨⟨e1, e2, e3⟩, ⟨e4, e5, e6⟩, ⟨e7, e8, e9⟩⟩

/-- Same-direction acceptance for every cyclic rotation of either face. -/
theorem pairOk_adjacent_samedir_rot (m : ExactMesh) (ip iq ir is pa pb : Nat)
    (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is) (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is)
    (hA : projAxis m ⟨ip, iq, ir⟩ = some pa) (hB : projAxis m ⟨ip, iq, is⟩ = some pb)
    (hcop : planeValue m ⟨ip, iq, ir⟩ (m.point is) = 0)
    (hR : 0 < side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project ir))
    (hS : side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project is) < 0)
    (fa fb : Face)
    (hfa : fa = ⟨ip, iq, ir⟩ ∨ fa = ⟨iq, ir, ip⟩ ∨ fa = ⟨ir, ip, iq⟩)
    (hfb : fb = ⟨ip, iq, is⟩ ∨ fb = ⟨iq, is, ip⟩ ∨ fb = ⟨is, ip, iq⟩) :
    pairOk m fa fb = true := by
  have base := pairOk_adjacent_samedir m ip iq ir is pa pb h1 h2 h3 h4 h5 h6 hA hB hcop hR hS
  have pP := planeValue_a m ⟨ip, iq, ir⟩
  have pQ := planeValue_b m ⟨ip, iq, ir⟩
  have pRa : ∀ p, planeValue m ⟨iq, ir, ip⟩ p = planeValue m ⟨ip, iq, ir⟩ p :=
    fun p => planeValue_rot m ip iq ir p
  have pRb : ∀ p, planeValue m ⟨ir, ip, iq⟩ p = planeValue m ⟨ip, iq, ir⟩ p := fun p =>
    (planeValue_rot m iq ir ip p).trans (planeValue_rot m ip iq ir p)
  have cop : ∀ fb', (fb' = ⟨ip, iq, is⟩ ∨ fb' = ⟨iq, is, ip⟩ ∨ fb' = ⟨is, ip, iq⟩) →
      ∀ fa', (fa' = ⟨ip, iq, ir⟩ ∨ fa' = ⟨iq, ir, ip⟩ ∨ fa' = ⟨ir, ip, iq⟩) →
      (List.range 3).all (fun k => decide (planeValue m fa' (facePoint m fb' k) = 0)) = true := by
    intro fb' hb fa' ha
    rcases hb with rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;>
      simp [List.range_succ, facePoint, pRa, pRb, pP, pQ, hcop]
  have rb : ∀ fb', (fb' = ⟨ip, iq, is⟩ ∨ fb' = ⟨iq, is, ip⟩ ∨ fb' = ⟨is, ip, iq⟩) →
      pairOk m ⟨ip, iq, ir⟩ fb' = true := by
    intro fb' h
    rcases h with rfl | rfl | rfl
    · exact base
    · rw [pairOk_rotB m ⟨ip, iq, ir⟩ ip iq is (cop _ (Or.inl rfl) _ (Or.inl rfl))]; exact base
    · have e1 := pairOk_rotB m ⟨ip, iq, ir⟩ iq is ip (cop _ (Or.inr (Or.inl rfl)) _ (Or.inl rfl))
      have e2 := pairOk_rotB m ⟨ip, iq, ir⟩ ip iq is (cop _ (Or.inl rfl) _ (Or.inl rfl))
      rw [e1, e2]; exact base
  have ra : ∀ fb', (fb' = ⟨ip, iq, is⟩ ∨ fb' = ⟨iq, is, ip⟩ ∨ fb' = ⟨is, ip, iq⟩) →
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
