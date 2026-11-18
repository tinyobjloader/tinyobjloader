import Tess.SegmentSoundness
import Tess.TriangleContains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Rational-plane exit lemma: a segment from a point of a triangle to a point outside leaves
through an edge. Same argument as `TriangleMeet` (over `ℝ`), restated over `ℚ` with the exact
`Tess.orient`/`contains2`-style membership so that it applies to the executable predicates. -/
namespace Tess

/-- Closed-triangle membership, either orientation (the `contains2` condition). -/
def Tri2 (a b c p : Point2) : Prop :=
  (0 ≤ orient a b p ∧ 0 ≤ orient b c p ∧ 0 ≤ orient c a p) ∨
  (orient a b p ≤ 0 ∧ orient b c p ≤ 0 ∧ orient c a p ≤ 0)

theorem contains2_iff_Tri2 (a b c p : Point2) : contains2 a b c p = true ↔ Tri2 a b c p := by
  unfold contains2 Tri2
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def tauQ (g h : Rat) : Rat := if h < 0 then g / (g - h) else 1

theorem tauQ_props (g h : Rat) (hg : 0 ≤ g) :
    0 ≤ tauQ g h ∧ tauQ g h ≤ 1 ∧ (h < 0 → tauQ g h < 1 ∧ (1 - tauQ g h) * g + tauQ g h * h = 0) ∧
    (∀ t : Rat, 0 ≤ t → t ≤ tauQ g h → 0 ≤ (1 - t) * g + t * h) := by
  unfold tauQ
  by_cases hh : h < 0
  · simp only [hh, if_true]
    have hd : 0 < g - h := by linarith
    have hq : g / (g - h) * (g - h) = g := div_mul_cancel₀ _ hd.ne'
    refine ⟨div_nonneg hg hd.le, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩
    · rw [div_le_one hd]; linarith
    · rw [div_lt_one hd]; linarith
    · nlinarith
    · intro t ht0 ht1
      nlinarith
  · simp only [hh, if_false]
    refine ⟨zero_le_one, le_rfl, fun h' => h'.elim, ?_⟩
    intro t ht0 ht1
    have hh' : 0 ≤ h := not_lt.mp hh
    nlinarith

theorem exit_paramsQ (g0 g1 g2 h0 h1 h2 : Rat) (p0 : 0 ≤ g0) (p1 : 0 ≤ g1) (p2 : 0 ≤ g2)
    (hv : h0 < 0 ∨ h1 < 0 ∨ h2 < 0) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ (1 - t) * g0 + t * h0 ∧ 0 ≤ (1 - t) * g1 + t * h1 ∧
      0 ≤ (1 - t) * g2 + t * h2 ∧
      ((1 - t) * g0 + t * h0 = 0 ∨ (1 - t) * g1 + t * h1 = 0 ∨ (1 - t) * g2 + t * h2 = 0) := by
  obtain ⟨a0, a1, a2, a3⟩ := tauQ_props g0 h0 p0
  obtain ⟨b0, b1, b2, b3⟩ := tauQ_props g1 h1 p1
  obtain ⟨c0, c1, c2, c3⟩ := tauQ_props g2 h2 p2
  set t := min (tauQ g0 h0) (min (tauQ g1 h1) (tauQ g2 h2)) with ht
  have t0 : 0 ≤ t := le_min a0 (le_min b0 c0)
  have tle0 : t ≤ tauQ g0 h0 := min_le_left _ _
  have tle1 : t ≤ tauQ g1 h1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have tle2 : t ≤ tauQ g2 h2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have t1 : t ≤ 1 := le_trans tle0 a1
  have hlt : t < 1 := by
    rcases hv with h | h | h
    · exact lt_of_le_of_lt tle0 (a2 h).1
    · exact lt_of_le_of_lt tle1 (b2 h).1
    · exact lt_of_le_of_lt tle2 (c2 h).1
  refine ⟨t, t0, t1, a3 t t0 tle0, b3 t t0 tle1, c3 t t0 tle2, ?_⟩
  have hmin : t = tauQ g0 h0 ∨ t = tauQ g1 h1 ∨ t = tauQ g2 h2 := by
    rcases min_choice (tauQ g0 h0) (min (tauQ g1 h1) (tauQ g2 h2)) with h | h
    · left; rw [ht, h]
    · rcases min_choice (tauQ g1 h1) (tauQ g2 h2) with h' | h'
      · right; left; rw [ht, h, h']
      · right; right; rw [ht, h, h']
  rcases hmin with h | h | h
  · left
    by_cases hh : h0 < 0
    · rw [h]; exact (a2 hh).2
    · exfalso; have : tauQ g0 h0 = 1 := by simp [tauQ, hh]
      linarith
  · right; left
    by_cases hh : h1 < 0
    · rw [h]; exact (b2 hh).2
    · exfalso; have : tauQ g1 h1 = 1 := by simp [tauQ, hh]
      linarith
  · right; right
    by_cases hh : h2 < 0
    · rw [h]; exact (c2 hh).2
    · exfalso; have : tauQ g2 h2 = 1 := by simp [tauQ, hh]
      linarith

/-- Barycentric identity: `Δ q = α a + β b + γ c` with the edge orientations as weights. -/
theorem bary_x (a b c q : Point2) :
    orient a b c * q.x = orient b c q * a.x + orient c a q * b.x + orient a b q * c.x := by
  simp only [orient]; ring

theorem bary_y (a b c q : Point2) :
    orient a b c * q.y = orient b c q * a.y + orient c a q * b.y + orient a b q * c.y := by
  simp only [orient]; ring

theorem orient_total (a b c q : Point2) :
    orient a b q + orient b c q + orient c a q = orient a b c := by
  simp only [orient]; ring

/-- A point of the (signed-nonnegative) triangle on an edge line lies on that edge segment. -/
theorem on_edgeQ (a b c q : Point2) (σ : Rat) (hΔ : 0 < σ * orient a b c)
    (h1 : 0 ≤ σ * orient a b q) (h2 : 0 ≤ σ * orient b c q) (h3 : 0 ≤ σ * orient c a q) :
    (orient a b q = 0 → ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ q = segmentPoint a b s) ∧
    (orient b c q = 0 → ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ q = segmentPoint b c s) ∧
    (orient c a q = 0 → ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ q = segmentPoint c a s) := by
  have hΔne : orient a b c ≠ 0 := by intro h; rw [h] at hΔ; simp at hΔ
  have tot := orient_total a b c q
  have bx := bary_x a b c q
  have by_ := bary_y a b c q
  have range : ∀ w : Rat, 0 ≤ σ * w → σ * w ≤ σ * orient a b c → 0 ≤ w / orient a b c ∧ w / orient a b c ≤ 1 := by
    intro w hw0 hw1
    have key : w / orient a b c = (σ * w) / (σ * orient a b c) := by
      have hσ : σ ≠ 0 := by rintro rfl; simp at hΔ
      field_simp
    rw [key]
    exact ⟨div_nonneg hw0 hΔ.le, (div_le_one hΔ).mpr hw1⟩
  have tot' : σ * orient a b q + σ * orient b c q + σ * orient c a q = σ * orient a b c := by
    rw [← mul_add, ← mul_add, tot]
  have pt_eq : ∀ p q : Point2, p.x = q.x → p.y = q.y → p = q := by
    intro p q hx hy; cases p; cases q; simp_all
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have z : σ * orient a b q = 0 := by rw [h]; ring
    refine ⟨orient c a q / orient a b c, (range _ h3 (by linarith)).1, (range _ h3 (by linarith)).2, ?_⟩
    apply pt_eq <;> simp only [segmentPoint] <;> field_simp
    · linear_combination bx + a.x * tot + (c.x - a.x) * h
    · linear_combination by_ + a.y * tot + (c.y - a.y) * h
  · have z : σ * orient b c q = 0 := by rw [h]; ring
    refine ⟨orient a b q / orient a b c, (range _ h1 (by linarith)).1, (range _ h1 (by linarith)).2, ?_⟩
    apply pt_eq <;> simp only [segmentPoint] <;> field_simp
    · linear_combination bx + b.x * tot + (a.x - b.x) * h
    · linear_combination by_ + b.y * tot + (a.y - b.y) * h
  · have z : σ * orient c a q = 0 := by rw [h]; ring
    refine ⟨orient b c q / orient a b c, (range _ h2 (by linarith)).1, (range _ h2 (by linarith)).2, ?_⟩
    apply pt_eq <;> simp only [segmentPoint] <;> field_simp
    · linear_combination bx + c.x * tot + (b.x - c.x) * h
    · linear_combination by_ + c.y * tot + (b.y - c.y) * h

theorem tri2_iff (a b c p : Point2) (σ : Rat) (hσ : σ = 1 ∨ σ = -1) (hΔ : 0 < σ * orient a b c) :
    Tri2 a b c p ↔ (0 ≤ σ * orient a b p ∧ 0 ≤ σ * orient b c p ∧ 0 ≤ σ * orient c a p) := by
  have tot := orient_total a b c p
  unfold Tri2
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hΔ ⊢
    constructor
    · rintro (h | h)
      · exact h
      · exfalso; linarith [h.1, h.2.1, h.2.2]
    · intro h; exact Or.inl h
  · constructor
    · rintro (h | h)
      · exfalso; linarith [h.1, h.2.1, h.2.2]
      · refine ⟨?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2]
    · intro h
      right
      refine ⟨?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2]

theorem tri2_exit (a b c p v : Point2) (hnd : orient a b c ≠ 0) (hp : Tri2 a b c p)
    (hv : ¬ Tri2 a b c v) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ Tri2 a b c (segmentPoint p v t) ∧
      ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧
        (segmentPoint p v t = segmentPoint a b s ∨ segmentPoint p v t = segmentPoint b c s ∨
         segmentPoint p v t = segmentPoint c a s) := by
  obtain ⟨σ, hσ, hΔ⟩ : ∃ σ : Rat, (σ = 1 ∨ σ = -1) ∧ 0 < σ * orient a b c := by
    rcases lt_or_gt_of_ne hnd with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  have iff := tri2_iff a b c
  rw [iff p σ hσ hΔ] at hp
  rw [iff v σ hσ hΔ] at hv
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hneg : σ * orient a b v < 0 ∨ σ * orient b c v < 0 ∨ σ * orient c a v < 0 := by
    by_contra hcon
    push Not at hcon
    exact hv ⟨hcon.1, hcon.2.1, hcon.2.2⟩
  obtain ⟨t, t0, t1, k0, k1, k2, hz⟩ := exit_paramsQ _ _ _ _ _ _ hp1 hp2 hp3 hneg
  have e1 : (1 - t) * (σ * orient a b p) + t * (σ * orient a b v) =
      σ * orient a b (segmentPoint p v t) := by rw [orient_segmentPoint]; ring
  have e2 : (1 - t) * (σ * orient b c p) + t * (σ * orient b c v) =
      σ * orient b c (segmentPoint p v t) := by rw [orient_segmentPoint]; ring
  have e3 : (1 - t) * (σ * orient c a p) + t * (σ * orient c a v) =
      σ * orient c a (segmentPoint p v t) := by rw [orient_segmentPoint]; ring
  rw [e1] at k0 hz
  rw [e2] at k1 hz
  rw [e3] at k2 hz
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hΔ
  have mem : Tri2 a b c (segmentPoint p v t) := (tri2_iff _ _ _ _ σ hσ hΔ).mpr ⟨k0, k1, k2⟩
  have edge := on_edgeQ a b c _ σ hΔ k0 k1 k2
  refine ⟨t, t0, t1, mem, ?_⟩
  rcases hz with h | h | h
  · obtain ⟨s, s0, s1, e⟩ := edge.1 ((mul_eq_zero.mp h).resolve_left hσ0)
    exact ⟨s, s0, s1, Or.inl e⟩
  · obtain ⟨s, s0, s1, e⟩ := edge.2.1 ((mul_eq_zero.mp h).resolve_left hσ0)
    exact ⟨s, s0, s1, Or.inr (Or.inl e)⟩
  · obtain ⟨s, s0, s1, e⟩ := edge.2.2 ((mul_eq_zero.mp h).resolve_left hσ0)
    exact ⟨s, s0, s1, Or.inr (Or.inr e)⟩

end Tess
