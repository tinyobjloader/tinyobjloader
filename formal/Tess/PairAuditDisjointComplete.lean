import Tess.PairAuditVertexComplete

namespace Tess
namespace PairAudit

section Disjoint
variable (a1 a2 a3 b1 b2 b3 : Nat) (A1 A2 A3 B1 B2 B3 G D : Point2)
  (hd : [a1, a2, a3, b1, b2, b3].Nodup)
  (g1 : 0 < side G D A1) (g2 : 0 < side G D A2) (g3 : 0 < side G D A3)
  (h1 : side G D B1 < 0) (h2 : side G D B2 < 0) (h3 : side G D B3 < 0)

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_00 : segC a1 a2 b1 b2 A1 A2 B1 B2 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A1 A2 B1 (g1) (g2) (by linarith)
  have f1 := onSeg_pos_strict G D A1 A2 B2 (g1) (g2) (by linarith)
  have f2 := onSeg_neg_strict G D B1 B2 A1 (h1) (h2) (by linarith)
  have f3 := onSeg_neg_strict G D B1 B2 A2 (h1) (h2) (by linarith)
  have fx := no_cross G D A1 A2 B1 B2 (g1.le) (g2.le) (by linarith) (h1.le) (h2.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_01 : segC a1 a2 b2 b3 A1 A2 B2 B3 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A1 A2 B2 (g1) (g2) (by linarith)
  have f1 := onSeg_pos_strict G D A1 A2 B3 (g1) (g2) (by linarith)
  have f2 := onSeg_neg_strict G D B2 B3 A1 (h2) (h3) (by linarith)
  have f3 := onSeg_neg_strict G D B2 B3 A2 (h2) (h3) (by linarith)
  have fx := no_cross G D A1 A2 B2 B3 (g1.le) (g2.le) (by linarith) (h2.le) (h3.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_02 : segC a1 a2 b3 b1 A1 A2 B3 B1 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A1 A2 B3 (g1) (g2) (by linarith)
  have f1 := onSeg_pos_strict G D A1 A2 B1 (g1) (g2) (by linarith)
  have f2 := onSeg_neg_strict G D B3 B1 A1 (h3) (h1) (by linarith)
  have f3 := onSeg_neg_strict G D B3 B1 A2 (h3) (h1) (by linarith)
  have fx := no_cross G D A1 A2 B3 B1 (g1.le) (g2.le) (by linarith) (h3.le) (h1.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_10 : segC a2 a3 b1 b2 A2 A3 B1 B2 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A2 A3 B1 (g2) (g3) (by linarith)
  have f1 := onSeg_pos_strict G D A2 A3 B2 (g2) (g3) (by linarith)
  have f2 := onSeg_neg_strict G D B1 B2 A2 (h1) (h2) (by linarith)
  have f3 := onSeg_neg_strict G D B1 B2 A3 (h1) (h2) (by linarith)
  have fx := no_cross G D A2 A3 B1 B2 (g2.le) (g3.le) (by linarith) (h1.le) (h2.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_11 : segC a2 a3 b2 b3 A2 A3 B2 B3 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A2 A3 B2 (g2) (g3) (by linarith)
  have f1 := onSeg_pos_strict G D A2 A3 B3 (g2) (g3) (by linarith)
  have f2 := onSeg_neg_strict G D B2 B3 A2 (h2) (h3) (by linarith)
  have f3 := onSeg_neg_strict G D B2 B3 A3 (h2) (h3) (by linarith)
  have fx := no_cross G D A2 A3 B2 B3 (g2.le) (g3.le) (by linarith) (h2.le) (h3.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_12 : segC a2 a3 b3 b1 A2 A3 B3 B1 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A2 A3 B3 (g2) (g3) (by linarith)
  have f1 := onSeg_pos_strict G D A2 A3 B1 (g2) (g3) (by linarith)
  have f2 := onSeg_neg_strict G D B3 B1 A2 (h3) (h1) (by linarith)
  have f3 := onSeg_neg_strict G D B3 B1 A3 (h3) (h1) (by linarith)
  have fx := no_cross G D A2 A3 B3 B1 (g2.le) (g3.le) (by linarith) (h3.le) (h1.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_20 : segC a3 a1 b1 b2 A3 A1 B1 B2 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A3 A1 B1 (g3) (g1) (by linarith)
  have f1 := onSeg_pos_strict G D A3 A1 B2 (g3) (g1) (by linarith)
  have f2 := onSeg_neg_strict G D B1 B2 A3 (h1) (h2) (by linarith)
  have f3 := onSeg_neg_strict G D B1 B2 A1 (h1) (h2) (by linarith)
  have fx := no_cross G D A3 A1 B1 B2 (g3.le) (g1.le) (by linarith) (h1.le) (h2.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_21 : segC a3 a1 b2 b3 A3 A1 B2 B3 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A3 A1 B2 (g3) (g1) (by linarith)
  have f1 := onSeg_pos_strict G D A3 A1 B3 (g3) (g1) (by linarith)
  have f2 := onSeg_neg_strict G D B2 B3 A3 (h2) (h3) (by linarith)
  have f3 := onSeg_neg_strict G D B2 B3 A1 (h2) (h3) (by linarith)
  have fx := no_cross G D A3 A1 B2 B3 (g3.le) (g1.le) (by linarith) (h2.le) (h3.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

include hd g1 g2 g3 h1 h2 h3 in
theorem dpair_22 : segC a3 a1 b3 b1 A3 A1 B3 B1 = false := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  have f0 := onSeg_pos_strict G D A3 A1 B3 (g3) (g1) (by linarith)
  have f1 := onSeg_pos_strict G D A3 A1 B1 (g3) (g1) (by linarith)
  have f2 := onSeg_neg_strict G D B3 B1 A3 (h3) (h1) (by linarith)
  have f3 := onSeg_neg_strict G D B3 B1 A1 (h3) (h1) (by linarith)
  have fx := no_cross G D A3 A1 B3 B1 (g3.le) (g1.le) (by linarith) (h3.le) (h1.le)
  unfold segC
  simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, (Ne.symm n1), (Ne.symm n2), (Ne.symm n3), (Ne.symm n4), (Ne.symm n5), (Ne.symm n6), (Ne.symm n7), (Ne.symm n8), (Ne.symm n9), (Ne.symm n10), (Ne.symm n11), (Ne.symm n12), (Ne.symm n13), (Ne.symm n14), (Ne.symm n15), f0, f1, f2, f3, fx]

end Disjoint

theorem commonIds_disjoint (a1 a2 a3 b1 b2 b3 : Nat) (hd : [a1, a2, a3, b1, b2, b3].Nodup) :
    commonIds ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ = [] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  simp [commonIds, faceId, List.range_succ, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12,
    n13, n14, n15, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6,
    Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11, Ne.symm n12, Ne.symm n13,
    Ne.symm n14, Ne.symm n15]

theorem sharedCount_disjoint (a1 a2 a3 b1 b2 b3 : Nat) (hd : [a1, a2, a3, b1, b2, b3].Nodup) :
    sharedCount ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ = 0 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨n6, n7, n8, n9⟩, ⟨n10, n11, n12⟩, ⟨n13, n14⟩, n15, -⟩ := hd
  simp [sharedCount, faceId, List.range_succ, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12,
    n13, n14, n15, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6,
    Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11, Ne.symm n12, Ne.symm n13,
    Ne.symm n14, Ne.symm n15]

/-- Completeness for coplanar faces with no shared vertex ids that are strictly separated by a line
in the projection (every pair of disjoint triangles is). -/
theorem pairOk_disjoint_coplanar (m : ExactMesh) (a1 a2 a3 b1 b2 b3 pa pb : Nat)
    (hd : [a1, a2, a3, b1, b2, b3].Nodup)
    (hA : projAxis m ⟨a1, a2, a3⟩ = some pa) (hB : projAxis m ⟨b1, b2, b3⟩ = some pb)
    (c1 : planeValue m ⟨a1, a2, a3⟩ (m.point b1) = 0) (c2 : planeValue m ⟨a1, a2, a3⟩ (m.point b2) = 0)
    (c3 : planeValue m ⟨a1, a2, a3⟩ (m.point b3) = 0) (G D : Point2)
    (g1 : 0 < side G D ((withAxis m pa).project a1)) (g2 : 0 < side G D ((withAxis m pa).project a2))
    (g3 : 0 < side G D ((withAxis m pa).project a3))
    (h1 : side G D ((withAxis m pa).project b1) < 0) (h2 : side G D ((withAxis m pa).project b2) < 0)
    (h3 : side G D ((withAxis m pa).project b3) < 0)
    (hAa : orient ((withAxis m pa).project a1) ((withAxis m pa).project a2)
      ((withAxis m pa).project a3) ≠ 0)
    (hAb : orient ((withAxis m pa).project b1) ((withAxis m pa).project b2)
      ((withAxis m pa).project b3) ≠ 0) :
    pairOk m ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ = true := by
  set A1 := (withAxis m pa).project a1
  set A2 := (withAxis m pa).project a2
  set A3 := (withAxis m pa).project a3
  set B1 := (withAxis m pa).project b1
  set B2 := (withAxis m pa).project b2
  set B3 := (withAxis m pa).project b3
  have cmn := commonIds_disjoint a1 a2 a3 b1 b2 b3 hd
  have sc := sharedCount_disjoint a1 a2 a3 b1 b2 b3 hd
  have al : ∀ p, allowed m ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ p = false := by
    intro p; unfold allowed; rw [cmn]; simp
  have kA : ∀ x, 0 < side G D x → contains2 B1 B2 B3 x = false := fun x hx =>
    contains_pos_false G D B1 B2 B3 x h1.le h2.le h3.le hx hAb
  have kB : ∀ x, side G D x < 0 → contains2 A1 A2 A3 x = false := fun x hx =>
    contains_neg_false G D A1 A2 A3 x g1.le g2.le g3.le hx hAa
  have hcopl : (List.range 3).all (fun k => decide (planeValue m ⟨a1, a2, a3⟩
      (facePoint m ⟨b1, b2, b3⟩ k) = 0)) = true := by
    simp [List.range_succ, facePoint, c1, c2, c3]
  have q1 : containsPt m ⟨b1, b2, b3⟩ pa (m.point a1) = false := kA A1 g1
  have q2 : containsPt m ⟨b1, b2, b3⟩ pa (m.point a2) = false := kA A2 g2
  have q3 : containsPt m ⟨b1, b2, b3⟩ pa (m.point a3) = false := kA A3 g3
  have r1 : containsPt m ⟨a1, a2, a3⟩ pa (m.point b1) = false := kB B1 h1
  have r2 : containsPt m ⟨a1, a2, a3⟩ pa (m.point b2) = false := kB B2 h2
  have r3 : containsPt m ⟨a1, a2, a3⟩ pa (m.point b3) = false := kB B3 h3
  unfold pairOk
  rw [hA, hB]
  simp only []
  rw [if_pos hcopl]
  have e00 := dpair_00 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e01 := dpair_01 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e02 := dpair_02 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e10 := dpair_10 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e11 := dpair_11 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e12 := dpair_12 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e20 := dpair_20 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e21 := dpair_21 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  have e22 := dpair_22 a1 a2 a3 b1 b2 b3 A1 A2 A3 B1 B2 B3 G D hd g1 g2 g3 h1 h2 h3
  simp [List.range_succ, facePoint, faceId, segmentConflict_eq, al, sc, q1, q2, q3, r1, r2, r3]
  exact ⟨⟨e00, e01, e02⟩, ⟨e10, e11, e12⟩, ⟨e20, e21, e22⟩⟩

/-- The disjoint-face acceptance for every cyclic rotation of either face. -/
theorem pairOk_disjoint_coplanar_rot (m : ExactMesh) (a1 a2 a3 b1 b2 b3 pa pb : Nat)
    (hd : [a1, a2, a3, b1, b2, b3].Nodup)
    (hA : projAxis m ⟨a1, a2, a3⟩ = some pa) (hB : projAxis m ⟨b1, b2, b3⟩ = some pb)
    (c1 : planeValue m ⟨a1, a2, a3⟩ (m.point b1) = 0) (c2 : planeValue m ⟨a1, a2, a3⟩ (m.point b2) = 0)
    (c3 : planeValue m ⟨a1, a2, a3⟩ (m.point b3) = 0) (G D : Point2)
    (g1 : 0 < side G D ((withAxis m pa).project a1)) (g2 : 0 < side G D ((withAxis m pa).project a2))
    (g3 : 0 < side G D ((withAxis m pa).project a3))
    (h1 : side G D ((withAxis m pa).project b1) < 0) (h2 : side G D ((withAxis m pa).project b2) < 0)
    (h3 : side G D ((withAxis m pa).project b3) < 0)
    (hAa : orient ((withAxis m pa).project a1) ((withAxis m pa).project a2)
      ((withAxis m pa).project a3) ≠ 0)
    (hAb : orient ((withAxis m pa).project b1) ((withAxis m pa).project b2)
      ((withAxis m pa).project b3) ≠ 0)
    (fa fb : Face)
    (hfa : fa = ⟨a1, a2, a3⟩ ∨ fa = ⟨a2, a3, a1⟩ ∨ fa = ⟨a3, a1, a2⟩)
    (hfb : fb = ⟨b1, b2, b3⟩ ∨ fb = ⟨b2, b3, b1⟩ ∨ fb = ⟨b3, b1, b2⟩) :
    pairOk m fa fb = true := by
  have base := pairOk_disjoint_coplanar m a1 a2 a3 b1 b2 b3 pa pb hd hA hB c1 c2 c3 G D g1 g2 g3
    h1 h2 h3 hAa hAb
  have pRa : ∀ p, planeValue m ⟨a2, a3, a1⟩ p = planeValue m ⟨a1, a2, a3⟩ p :=
    fun p => planeValue_rot m a1 a2 a3 p
  have pRb : ∀ p, planeValue m ⟨a3, a1, a2⟩ p = planeValue m ⟨a1, a2, a3⟩ p := fun p =>
    (planeValue_rot m a2 a3 a1 p).trans (planeValue_rot m a1 a2 a3 p)
  have cop : ∀ fb', (fb' = ⟨b1, b2, b3⟩ ∨ fb' = ⟨b2, b3, b1⟩ ∨ fb' = ⟨b3, b1, b2⟩) →
      ∀ fa', (fa' = ⟨a1, a2, a3⟩ ∨ fa' = ⟨a2, a3, a1⟩ ∨ fa' = ⟨a3, a1, a2⟩) →
      (List.range 3).all (fun k => decide (planeValue m fa' (facePoint m fb' k) = 0)) = true := by
    intro fb' hb fa' ha
    rcases hb with rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;>
      simp [List.range_succ, facePoint, pRa, pRb, c1, c2, c3]
  have rb : ∀ fb', (fb' = ⟨b1, b2, b3⟩ ∨ fb' = ⟨b2, b3, b1⟩ ∨ fb' = ⟨b3, b1, b2⟩) →
      pairOk m ⟨a1, a2, a3⟩ fb' = true := by
    intro fb' h
    rcases h with rfl | rfl | rfl
    · exact base
    · rw [pairOk_rotB m ⟨a1, a2, a3⟩ b1 b2 b3 (cop _ (Or.inl rfl) _ (Or.inl rfl))]; exact base
    · have e1 := pairOk_rotB m ⟨a1, a2, a3⟩ b2 b3 b1 (cop _ (Or.inr (Or.inl rfl)) _ (Or.inl rfl))
      have e2 := pairOk_rotB m ⟨a1, a2, a3⟩ b1 b2 b3 (cop _ (Or.inl rfl) _ (Or.inl rfl))
      rw [e1, e2]; exact base
  have ra : ∀ fb', (fb' = ⟨b1, b2, b3⟩ ∨ fb' = ⟨b2, b3, b1⟩ ∨ fb' = ⟨b3, b1, b2⟩) →
      pairOk m fa fb' = true := by
    intro fb' hb
    have hb0 := rb fb' hb
    rcases hfa with rfl | rfl | rfl
    · exact hb0
    · rw [pairOk_rotA m a1 a2 a3 fb' (cop fb' hb _ (Or.inl rfl))]; exact hb0
    · have e1 := pairOk_rotA m a2 a3 a1 fb' (cop fb' hb _ (Or.inr (Or.inl rfl)))
      have e2 := pairOk_rotA m a1 a2 a3 fb' (cop fb' hb _ (Or.inl rfl))
      rw [e1, e2]; exact hb0
  exact ra fb hfb

end PairAudit
end Tess
