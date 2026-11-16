/-
  Predicate-level models of `lib/tess/src/predicates.c` / `geometry.c`: the
  rational expressions evaluated through `qr_*` (whose models are proved in
  `QrModel`) equal the Lean exact specifications `Tess.orient`,
  `Tess.incircleDet`, `Tess.orient3`, and the sign returned by the C code is the
  mathematical sign. Model-level: the C data flow (matrix fill, allocation,
  budget failure returning no sign) is not refined.
-/
import Tess.C.QrModel
import Tess.Predicates
import Tess.Orient3
import Mathlib.Algebra.Order.Field.Basic

namespace Tess.C

/-- Sign of an exact rational, as returned by `.n.sign` of a reduced `qr`. -/
def qsign (q : Rat) : Int := if 0 < q then 1 else if q < 0 then -1 else 0

/-- `det3` of `predicates.c`: accumulate the three cofactor terms in the same order. -/
def det3Q (m : Nat → Nat → Rat) : Rat :=
  let t := fun j => (m 1 ((j + 1) % 3) * m 2 ((j + 2) % 3) -
                     m 1 ((j + 2) % 3) * m 2 ((j + 1) % 3)) * m 0 j
  ((0 + t 0) + t 1) + t 2

theorem orient2_C_eq (a b c : Point2) :
    (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x) = orient a b c := rfl

/-- The 3x3 matrix `tg_incircle` builds: rows `(x-dx, y-dy, (x-dx)^2+(y-dy)^2)`. -/
def incircleMat (a b c d : Point2) : Nat → Nat → Rat := fun i j =>
  let p := if i = 0 then a else if i = 1 then b else c
  let x := p.x - d.x
  let y := p.y - d.y
  if j = 0 then x else if j = 1 then y else x * x + y * y

theorem det3_incircle (a b c d : Point2) : det3Q (incircleMat a b c d) = incircleDet a b c d := by
  simp only [det3Q, incircleMat, incircleDet]
  norm_num
  ring

def orient3Mat (a b c d : Point3) : Nat → Nat → Rat := fun i j =>
  let p := if i = 0 then a else if i = 1 then b else c
  if j = 0 then p.x - d.x else if j = 1 then p.y - d.y else p.z - d.z

theorem det3_orient3 (a b c d : Point3) : det3Q (orient3Mat a b c d) = orient3 a b c d := by
  simp only [det3Q, orient3Mat, orient3]
  norm_num
  ring

theorem qsign_pos {q : Rat} (h : 0 < q) : qsign q = 1 := by simp [qsign, h]
theorem qsign_neg {q : Rat} (h : q < 0) : qsign q = -1 := by
  simp [qsign, h, not_lt_of_gt h]
theorem qsign_zero : qsign 0 = 0 := by simp [qsign]

theorem qsign_mul (p q : Rat) : qsign (p * q) = qsign p * qsign q := by
  rcases lt_trichotomy p 0 with hp | rfl | hp <;> rcases lt_trichotomy q 0 with hq | rfl | hq
  · rw [qsign_pos (mul_pos_of_neg_of_neg hp hq), qsign_neg hp, qsign_neg hq]; norm_num
  · simp [qsign_zero]
  · rw [qsign_neg (mul_neg_of_neg_of_pos hp hq), qsign_neg hp, qsign_pos hq]; norm_num
  · simp [qsign_zero]
  · simp [qsign_zero]
  · simp [qsign_zero]
  · rw [qsign_neg (mul_neg_of_pos_of_neg hp hq), qsign_pos hp, qsign_neg hq]; norm_num
  · simp [qsign_zero]
  · rw [qsign_pos (mul_pos hp hq), qsign_pos hp, qsign_pos hq]; norm_num

/-- `tg_incircle` returns `sign(det) * sign(orient)`, which is exactly the sign of
the corrected determinant used by `illegalDelaunay`; illegal iff it is positive. -/
theorem incircle_C_sign (a b c d : Point2) :
    qsign (det3Q (incircleMat a b c d)) * qsign (orient a b c) = qsign (incircleDet a b c d * orient a b c) := by
  rw [det3_incircle, qsign_mul]

theorem illegalDelaunay_iff_sign (a b c d : Point2) :
    illegalDelaunay a b c d = true ↔
      qsign (det3Q (incircleMat a b c d)) * qsign (orient a b c) = 1 := by
  rw [incircle_C_sign]
  unfold illegalDelaunay
  simp only [decide_eq_true_eq]
  generalize incircleDet a b c d * orient a b c = z
  constructor
  · intro h; exact qsign_pos h
  · intro h
    by_contra hz
    rcases lt_trichotomy z 0 with h1 | h1 | h1
    · rw [qsign_neg h1] at h; omega
    · rw [h1, qsign_zero] at h; omega
    · exact hz h1

theorem zsign_wf (n : ZiM) (h : n.WF) : n.sign = Int.sign n.val := by
  unfold ZiM.val sval
  rcases h.sign with h0 | h1 | h1
  · rw [h0, h.zero h0]; simp [lv]
  · have hne : n.limbs ≠ [] := by intro e; have := h.nz e; omega
    have hpos : 0 < lv n.limbs := by
      have := lv_normalized_ge n.limbs hne h.norm
      have : 0 < 2 ^ (32 * (n.limbs.length - 1)) := pow_pos (by norm_num) _
      omega
    rw [h1]; simp [Int.sign_eq_one_of_pos (by exact_mod_cast hpos : (0:Int) < lv n.limbs)]
  · have hne : n.limbs ≠ [] := by intro e; have := h.nz e; omega
    have hpos : 0 < lv n.limbs := by
      have := lv_normalized_ge n.limbs hne h.norm
      have : 0 < 2 ^ (32 * (n.limbs.length - 1)) := pow_pos (by norm_num) _
      omega
    rw [h1]; simp [Int.sign_eq_one_of_pos (by exact_mod_cast hpos : (0:Int) < lv n.limbs)]

theorem qsign_qv (p : Int × Int) (hp : 0 < p.2) : qsign (qv p) = Int.sign p.1 := by
  have hd : (0 : Rat) < p.2 := by exact_mod_cast hp
  unfold qv
  rcases lt_trichotomy p.1 0 with h | h | h
  · rw [qsign_neg (div_neg_of_neg_of_pos (by exact_mod_cast h) hd)]; rw [Int.sign_eq_neg_one_of_neg h]
  · rw [h]; simp [qsign_zero]
  · rw [qsign_pos (div_pos (by exact_mod_cast h) hd)]; rw [Int.sign_eq_one_of_pos h]

/-- `tg_orient_q`: sub, sub, sub, sub, mul, mul, sub on canonical coordinates. -/
def orientQM (ax ay bx by_ cx cy : Int × Int) : Int × Int :=
  qrSubM (qrMulM (qrSubM bx ax) (qrSubM cy ay)) (qrMulM (qrSubM by_ ay) (qrSubM cx ax))

theorem orientQM_spec (ax ay bx by_ cx cy : Int × Int)
    (h1 : Canon ax) (h2 : Canon ay) (h3 : Canon bx) (h4 : Canon by_) (h5 : Canon cx) (h6 : Canon cy) :
    Canon (orientQM ax ay bx by_ cx cy) ∧
    qv (orientQM ax ay bx by_ cx cy) =
      orient ⟨qv ax, qv ay⟩ ⟨qv bx, qv by_⟩ ⟨qv cx, qv cy⟩ := by
  obtain ⟨c1, v1⟩ := qrSubM_spec bx ax h3 h1
  obtain ⟨c2, v2⟩ := qrSubM_spec cy ay h6 h2
  obtain ⟨c3, v3⟩ := qrSubM_spec by_ ay h4 h2
  obtain ⟨c4, v4⟩ := qrSubM_spec cx ax h5 h1
  obtain ⟨c5, v5⟩ := qrMulM_spec _ _ c1 c2
  obtain ⟨c6, v6⟩ := qrMulM_spec _ _ c3 c4
  obtain ⟨c7, v7⟩ := qrSubM_spec _ _ c5 c6
  refine ⟨c7, ?_⟩
  unfold orientQM
  rw [v7, v5, v6, v1, v2, v3, v4]
  rfl

/-- The sign `tg_orient_q` returns equals the exact sign of `Tess.orient` of the denoted points. -/
theorem orient_C_sign (ax ay bx by_ cx cy : Int × Int)
    (h1 : Canon ax) (h2 : Canon ay) (h3 : Canon bx) (h4 : Canon by_) (h5 : Canon cx) (h6 : Canon cy) :
    Int.sign (orientQM ax ay bx by_ cx cy).1 =
      qsign (orient ⟨qv ax, qv ay⟩ ⟨qv bx, qv by_⟩ ⟨qv cx, qv cy⟩) := by
  obtain ⟨c, v⟩ := orientQM_spec ax ay bx by_ cx cy h1 h2 h3 h4 h5 h6
  rw [← v, qsign_qv _ c.1]

end Tess.C
