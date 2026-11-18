import Tess.PairAuditCoplanarComplete
namespace Tess
namespace PairAudit

theorem projAxis_rot (m : ExactMesh) (a b c : Nat) :
    projAxis m ⟨b, c, a⟩ = projAxis m ⟨a, b, c⟩ := by
  unfold projAxis firstProjectionAxis
  simp only []
  have h : ∀ k, orient (projectPoint3 k (m.point b)) (projectPoint3 k (m.point c)) (projectPoint3 k (m.point a)) =
      orient (projectPoint3 k (m.point a)) (projectPoint3 k (m.point b)) (projectPoint3 k (m.point c)) :=
    fun k => (orient_cyc _ _ _).symm
  simp only [h]

theorem planeValue_rot (m : ExactMesh) (a b c : Nat) (p : Point3) :
    planeValue m ⟨b, c, a⟩ p = planeValue m ⟨a, b, c⟩ p := by
  unfold planeValue; simp only []; ring

theorem contains2_rot (a b c p : Point2) : contains2 b c a p = contains2 a b c p := by
  unfold contains2
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem containsPt_rot (m : ExactMesh) (a b c ax : Nat) (p : Point3) :
    containsPt m ⟨b, c, a⟩ ax p = containsPt m ⟨a, b, c⟩ ax p := by
  unfold containsPt containsProject
  exact contains2_rot _ _ _ _

/-- `allowed` as a function of the list of common ids. -/
def allowedL (m : ExactMesh) (common : List Nat) (p : Point3) : Bool :=
  if common.any (fun id => m.point id == p) then true
  else match common with
    | [i, j] =>
        let x := m.point i; let y := m.point j
        let da := Point3.mk (p.x - x.x) (p.y - x.y) (p.z - x.z)
        let db := Point3.mk (y.x - x.x) (y.y - x.y) (y.z - x.z)
        let box := between3 x.x y.x p.x && between3 x.y y.y p.y && between3 x.z y.z p.z
        let c0 := da.y * db.z - da.z * db.y
        let c1 := da.z * db.x - da.x * db.z
        let c2 := da.x * db.y - da.y * db.x
        box && decide (c0 = 0 ∧ c1 = 0 ∧ c2 = 0)
    | _ => false

theorem allowed_eq (m : ExactMesh) (fa fb : Face) (p : Point3) :
    allowed m fa fb p = allowedL m (commonIds fa fb) p := rfl

theorem between3_comm (x y p : Rat) : between3 x y p = between3 y x p := by
  unfold between3
  by_cases h1 : x ≤ y <;> by_cases h2 : y ≤ x
  · have : x = y := le_antisymm h1 h2
    subst this; simp
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_total x y) (by tauto)

theorem allowedL_swap2 (m : ExactMesh) (i j : Nat) (p : Point3) :
    allowedL m [i, j] p = allowedL m [j, i] p := by
  unfold allowedL
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.false_or]
  by_cases hany : (m.point i == p || m.point j == p) = true
  · have hany' : (m.point j == p || m.point i == p) = true := by rwa [Bool.or_comm]
    simp only [hany, hany', if_true]
  · have hany' : ¬ (m.point j == p || m.point i == p) = true := by rwa [Bool.or_comm]
    simp only [hany, hany', Bool.false_eq_true, if_false]
    simp only [between3_comm (m.point i).x (m.point j).x p.x, between3_comm (m.point i).y (m.point j).y p.y,
      between3_comm (m.point i).z (m.point j).z p.z]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hb, h0, h1, h2⟩
      exact ⟨hb, by nlinarith [h0], by nlinarith [h1], by nlinarith [h2]⟩
    · rintro ⟨hb, h0, h1, h2⟩
      exact ⟨hb, by nlinarith [h0], by nlinarith [h1], by nlinarith [h2]⟩

theorem allowedL_perm (m : ExactMesh) (L L' : List Nat) (p : Point3) (hp : L.Perm L') :
    allowedL m L p = allowedL m L' p := by
  have hlen := hp.length_eq
  have hany : L.any (fun id => m.point id == p) = L'.any (fun id => m.point id == p) := hp.any_eq
  rcases L with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;> rcases L' with _ | ⟨a, _ | ⟨b, _ | ⟨c, t'⟩⟩⟩ <;>
    simp at hlen
  · rfl
  · obtain rfl : x = a := by simpa using hp.eq_singleton
    rfl
  · rcases List.pair_perm.mp hp.symm with h | h
    · cases h; rfl
    · cases h; exact allowedL_swap2 m _ _ p
  · simp only [allowedL, hany]

theorem commonIds_rotA_perm (a b c : Nat) (fb : Face) :
    (commonIds ⟨b, c, a⟩ fb).Perm (commonIds ⟨a, b, c⟩ fb) := by
  unfold commonIds
  simp only [List.range_succ, List.range_zero, List.nil_append, faceId]
  simp
  rw [← List.append_assoc]
  exact List.perm_append_comm

theorem allowed_rotA (m : ExactMesh) (a b c : Nat) (fb : Face) (p : Point3) :
    allowed m ⟨b, c, a⟩ fb p = allowed m ⟨a, b, c⟩ fb p := by
  rw [allowed_eq, allowed_eq]
  exact allowedL_perm m _ _ p (commonIds_rotA_perm a b c fb)

theorem sharedCount_rotA (a b c : Nat) (fb : Face) :
    sharedCount ⟨b, c, a⟩ fb = sharedCount ⟨a, b, c⟩ fb := by
  simp only [sharedCount, List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
    List.foldl_nil, faceId]
  simp
  split_ifs <;> omega

theorem pairOk_rotA (m : ExactMesh) (a b c : Nat) (fb : Face)
    (hcopl : (List.range 3).all (fun k => decide (planeValue m ⟨a, b, c⟩ (facePoint m fb k) = 0)) = true) :
    pairOk m ⟨b, c, a⟩ fb = pairOk m ⟨a, b, c⟩ fb := by
  unfold pairOk
  rw [projAxis_rot]
  rcases hA : projAxis m ⟨a, b, c⟩ with _ | pa
  · simp
  rcases hB : projAxis m fb with _ | pb
  · simp
  simp only []
  simp only [planeValue_rot, containsPt_rot, allowed_rotA, sharedCount_rotA, hcopl, if_true]
  rw [Bool.eq_iff_iff]
  simp [List.range_succ, facePoint, faceId, -Bool.not_eq_true]
  intro _
  apply iff_of_eq
  ac_rfl

theorem perm3 {α : Type} (A B C : List α) : (B ++ (C ++ A)).Perm (A ++ (B ++ C)) := by
  rw [← List.append_assoc]; exact List.perm_append_comm

theorem blockPerm (x a b c : Nat) :
    (List.filterMap (fun j => if x = (if j = 0 then b else if j = 1 then c else a) then some x else none)
      [0, 1, 2]).Perm
    (List.filterMap (fun j => if x = (if j = 0 then a else if j = 1 then b else c) then some x else none)
      [0, 1, 2]) := by
  simp only [List.filterMap_cons, List.filterMap_nil]
  simp only [one_ne_zero, ite_false, ite_true, OfNat.ofNat_ne_zero, Nat.reduceEqDiff]
  split_ifs <;> simp_all

theorem commonIds_rotB_perm (fa : Face) (a b c : Nat) :
    (commonIds fa ⟨b, c, a⟩).Perm (commonIds fa ⟨a, b, c⟩) := by
  unfold commonIds
  simp only [List.range_succ, List.range_zero, List.nil_append, faceId]
  simp
  exact List.Perm.append (blockPerm _ a b c) (List.Perm.append (blockPerm _ a b c) (blockPerm _ a b c))

theorem allowed_rotB (m : ExactMesh) (fa : Face) (a b c : Nat) (p : Point3) :
    allowed m fa ⟨b, c, a⟩ p = allowed m fa ⟨a, b, c⟩ p := by
  rw [allowed_eq, allowed_eq]
  exact allowedL_perm m _ _ p (commonIds_rotB_perm fa a b c)

theorem sharedCount_rotB (fa : Face) (a b c : Nat) :
    sharedCount fa ⟨b, c, a⟩ = sharedCount fa ⟨a, b, c⟩ := by
  simp only [sharedCount, List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
    List.foldl_nil, faceId]
  simp
  split_ifs <;> omega

theorem pairOk_rotB (m : ExactMesh) (fa : Face) (a b c : Nat)
    (hcopl : (List.range 3).all (fun k => decide (planeValue m fa (facePoint m ⟨a, b, c⟩ k) = 0)) = true) :
    pairOk m fa ⟨b, c, a⟩ = pairOk m fa ⟨a, b, c⟩ := by
  have hcopl' : (List.range 3).all (fun k => decide (planeValue m fa (facePoint m ⟨b, c, a⟩ k) = 0)) = true := by
    simp [List.range_succ, facePoint] at hcopl ⊢
    tauto
  unfold pairOk
  rw [projAxis_rot (m := m) a b c]
  rcases hA : projAxis m fa with _ | pa
  · simp
  rcases hB : projAxis m ⟨a, b, c⟩ with _ | pb
  · simp
  simp only []
  simp only [hcopl, hcopl', if_true, containsPt_rot, allowed_rotB, sharedCount_rotB]
  rw [Bool.eq_iff_iff]
  simp [List.range_succ, facePoint, faceId, -Bool.not_eq_true]
  intro _
  apply iff_of_eq
  ac_rfl

/-- Acceptance of valid coplanar adjacent faces for every cyclic rotation of either face. -/
theorem pairOk_adjacent_coplanar_rot (m : ExactMesh) (ip iq ir is pa pb : Nat)
    (h1 : ip ≠ iq) (h2 : ip ≠ ir) (h3 : ip ≠ is) (h4 : iq ≠ ir) (h5 : iq ≠ is) (h6 : ir ≠ is)
    (hA : projAxis m ⟨ip, iq, ir⟩ = some pa) (hB : projAxis m ⟨iq, ip, is⟩ = some pb)
    (hcop : planeValue m ⟨ip, iq, ir⟩ (m.point is) = 0)
    (hR : 0 < side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project ir))
    (hS : side ((withAxis m pa).project ip) ((withAxis m pa).project iq)
      ((withAxis m pa).project is) < 0)
    (fa fb : Face)
    (hfa : fa = ⟨ip, iq, ir⟩ ∨ fa = ⟨iq, ir, ip⟩ ∨ fa = ⟨ir, ip, iq⟩)
    (hfb : fb = ⟨iq, ip, is⟩ ∨ fb = ⟨ip, is, iq⟩ ∨ fb = ⟨is, iq, ip⟩) :
    pairOk m fa fb = true := by
  have base := pairOk_adjacent_coplanar m ip iq ir is pa pb h1 h2 h3 h4 h5 h6 hA hB hcop hR hS
  have pP := planeValue_a m ⟨ip, iq, ir⟩
  have pQ := planeValue_b m ⟨ip, iq, ir⟩
  have pRa : ∀ p, planeValue m ⟨iq, ir, ip⟩ p = planeValue m ⟨ip, iq, ir⟩ p :=
    fun p => planeValue_rot m ip iq ir p
  have pRb : ∀ p, planeValue m ⟨ir, ip, iq⟩ p = planeValue m ⟨ip, iq, ir⟩ p := fun p =>
    (planeValue_rot m iq ir ip p).trans (planeValue_rot m ip iq ir p)
  have cop : ∀ fb', (fb' = ⟨iq, ip, is⟩ ∨ fb' = ⟨ip, is, iq⟩ ∨ fb' = ⟨is, iq, ip⟩) →
      ∀ fa', (fa' = ⟨ip, iq, ir⟩ ∨ fa' = ⟨iq, ir, ip⟩ ∨ fa' = ⟨ir, ip, iq⟩) →
      (List.range 3).all (fun k => decide (planeValue m fa' (facePoint m fb' k) = 0)) = true := by
    intro fb' hb fa' ha
    rcases hb with rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;>
      simp [List.range_succ, facePoint, pRa, pRb, pP, pQ, hcop]
  have rb : ∀ fb', (fb' = ⟨iq, ip, is⟩ ∨ fb' = ⟨ip, is, iq⟩ ∨ fb' = ⟨is, iq, ip⟩) →
      pairOk m ⟨ip, iq, ir⟩ fb' = true := by
    intro fb' h
    rcases h with rfl | rfl | rfl
    · exact base
    · rw [pairOk_rotB m ⟨ip, iq, ir⟩ iq ip is (cop _ (Or.inl rfl) _ (Or.inl rfl))]; exact base
    · have e1 := pairOk_rotB m ⟨ip, iq, ir⟩ ip is iq (cop _ (Or.inr (Or.inl rfl)) _ (Or.inl rfl))
      have e2 := pairOk_rotB m ⟨ip, iq, ir⟩ iq ip is (cop _ (Or.inl rfl) _ (Or.inl rfl))
      rw [e1, e2]; exact base
  have ra : ∀ fb', (fb' = ⟨iq, ip, is⟩ ∨ fb' = ⟨ip, is, iq⟩ ∨ fb' = ⟨is, iq, ip⟩) →
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
