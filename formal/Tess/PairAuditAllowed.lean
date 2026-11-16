import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Tess.PairAudit

namespace Tess
namespace PairAudit

theorem between3_iff (x y p : Rat) (h : between3 x y p = true) :
    (x ≤ p ∧ p ≤ y) ∨ (y ≤ p ∧ p ≤ x) := by
  unfold between3 at h
  split at h
  · left; simpa using h
  · right; simpa using h

/-- One-coordinate parametrization: with `db ≠ 0`, `da` parallel to `db` on this axis and
`p` between `x` and `y` on this axis gives `t ∈ [0,1]` with `p - x = t * db` on this axis. -/
theorem axis_param (x y p : Rat) (hne : y - x ≠ 0) (hb : between3 x y p = true) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p - x = t * (y - x) := by
  have ht : (p - x) / (y - x) * (y - x) = p - x := div_mul_cancel₀ _ hne
  set t := (p - x) / (y - x) with htd
  refine ⟨t, ?_, ?_, ht.symm⟩
  · rcases between3_iff x y p hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hy : 0 < y - x := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      by_contra hn; push_neg at hn; nlinarith
    · have hy : y - x < 0 := lt_of_le_of_ne (by linarith) hne
      by_contra hn; push_neg at hn; nlinarith
  · rcases between3_iff x y p hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hy : 0 < y - x := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      by_contra hn; push_neg at hn; nlinarith
    · have hy : y - x < 0 := lt_of_le_of_ne (by linarith) hne
      by_contra hn; push_neg at hn; nlinarith

theorem between3_eq (x y p : Rat) (h : y - x = 0) (hb : between3 x y p = true) : p - x = 0 := by
  rcases between3_iff x y p hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

theorem allowed_geom (x y p : Point3)
    (bx : between3 x.x y.x p.x = true) (by_ : between3 x.y y.y p.y = true)
    (bz : between3 x.z y.z p.z = true)
    (c0 : (p.y - x.y) * (y.z - x.z) - (p.z - x.z) * (y.y - x.y) = 0)
    (c1 : (p.z - x.z) * (y.x - x.x) - (p.x - x.x) * (y.z - x.z) = 0)
    (c2 : (p.x - x.x) * (y.y - x.y) - (p.y - x.y) * (y.x - x.x) = 0) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p = segment3Point x y t := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  obtain ⟨p1, p2, p3⟩ := p
  simp only [segment3Point, Point3.mk.injEq] at *
  by_cases h1 : y1 - x1 = 0
  · have e1 := between3_eq _ _ _ h1 bx
    by_cases h2 : y2 - x2 = 0
    · have e2 := between3_eq _ _ _ h2 by_
      by_cases h3 : y3 - x3 = 0
      · have e3 := between3_eq _ _ _ h3 bz
        refine ⟨0, le_rfl, by norm_num, ?_, ?_, ?_⟩ <;> linarith
      · obtain ⟨t, t0, t1, ht⟩ := axis_param _ _ _ h3 bz
        refine ⟨t, t0, t1, ?_, ?_, ?_⟩ <;> nlinarith
    · obtain ⟨t, t0, t1, ht⟩ := axis_param _ _ _ h2 by_
      refine ⟨t, t0, t1, ?_, ?_, ?_⟩
      · nlinarith
      · linarith
      · have : (p3 - x3 - t * (y3 - x3)) * (y2 - x2) = 0 := by
          linear_combination (-1) * c0 + (y3 - x3) * ht
        have := (mul_eq_zero.mp this).resolve_right h2
        linarith
  · obtain ⟨t, t0, t1, ht⟩ := axis_param _ _ _ h1 bx
    refine ⟨t, t0, t1, by linarith, ?_, ?_⟩
    · have : (p2 - x2 - t * (y2 - x2)) * (y1 - x1) = 0 := by
        linear_combination (-1) * c2 + (y2 - x2) * ht
      have := (mul_eq_zero.mp this).resolve_right h1
      linarith
    · have : (p3 - x3 - t * (y3 - x3)) * (y1 - x1) = 0 := by
        linear_combination c1 + (y3 - x3) * ht
      have := (mul_eq_zero.mp this).resolve_right h1
      linarith

/-- `allowed` only admits shared vertices and points of the shared edge. -/
theorem allowed_sound (m : ExactMesh) (fa fb : Face) (p : Point3) (h : allowed m fa fb p = true) :
    (∃ id ∈ commonIds fa fb, m.point id = p) ∨
    (∃ i j, commonIds fa fb = [i, j] ∧ ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧
      p = segment3Point (m.point i) (m.point j) t) := by
  unfold allowed at h
  by_cases hv : (commonIds fa fb).any (fun id => m.point id == p) = true
  · left
    obtain ⟨id, hid, he⟩ := List.any_eq_true.mp hv
    exact ⟨id, hid, by simpa using he⟩
  · right
    rw [if_neg hv] at h
    split at h
    · next i j hij =>
        refine ⟨i, j, hij, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨bx, by_⟩, bz⟩, c0, c1, c2⟩ := h
        exact allowed_geom (m.point i) (m.point j) p bx by_ bz (by linarith) (by linarith) (by linarith)
    · simp at h

end PairAudit
end Tess
