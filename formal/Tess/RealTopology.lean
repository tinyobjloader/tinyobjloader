import Tess.Winding
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section
namespace Tess.RealGeometry
open Set

def openTriangle (a b c : P2) : Set P2 :=
  {p | 0<orient a b p ∧ 0<orient b c p ∧ 0<orient c a p}
def closedTriangle (a b c : P2) : Set P2 :=
  {p | 0≤orient a b p ∧ 0≤orient b c p ∧ 0≤orient c a p}

theorem continuous_orient (a b : P2) : Continuous (fun p => orient a b p) := by
  unfold orient
  fun_prop

theorem isOpen_openTriangle (a b c : P2) : IsOpen (openTriangle a b c) := by
  exact ((isOpen_lt continuous_const (continuous_orient a b)).inter
    ((isOpen_lt continuous_const (continuous_orient b c)).inter
     (isOpen_lt continuous_const (continuous_orient c a))))

theorem isClosed_closedTriangle (a b c : P2) : IsClosed (closedTriangle a b c) := by
  exact ((isClosed_le continuous_const (continuous_orient a b)).inter
    ((isClosed_le continuous_const (continuous_orient b c)).inter
     (isClosed_le continuous_const (continuous_orient c a))))

theorem orient_affine (a b p q : P2) (s t : ℝ) (h : s+t=1) :
    orient a b (s • p + t • q) = s*orient a b p+t*orient a b q := by
  calc
    _ = s*orient a b p+t*orient a b q+(1-s-t)*orient a b (0,0) := by
      simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    _ = _ := by rw [show 1-s-t=0 by linarith]; ring

def center (a b c : P2) : P2 := ((a.1+b.1+c.1)/3,(a.2+b.2+c.2)/3)

theorem center_inside (a b c : P2) (positive : 0<orient a b c) :
    center a b c ∈ openTriangle a b c := by
  have h1 : orient a b (center a b c) = orient a b c/3 := by unfold orient center; ring
  have h2 : orient b c (center a b c) = orient a b c/3 := by unfold orient center; ring
  have h3 : orient c a (center a b c) = orient a b c/3 := by unfold orient center; ring
  exact ⟨by rw [h1]; positivity,by rw [h2]; positivity,by rw [h3]; positivity⟩

/-- Every point of the closed triangle is a limit of its strictly positive
interior, including edges and vertices. No coverage hypothesis is used. -/
theorem triangle_closure (a b c : P2) (positive : 0<orient a b c) :
    closure (openTriangle a b c) = closedTriangle a b c := by
  apply subset_antisymm
  · exact closure_minimal (fun _ h => ⟨h.1.le,h.2.1.le,h.2.2.le⟩) (isClosed_closedTriangle a b c)
  · intro p hp
    have hc := center_inside a b c positive
    have segmentInside : openSegment ℝ (center a b c) p ⊆ openTriangle a b c := by
      rintro q ⟨s,t,hs,ht,hst,rfl⟩
      change 0<orient a b (s • center a b c + t • p) ∧
        0<orient b c (s • center a b c + t • p) ∧ 0<orient c a (s • center a b c + t • p)
      rw [orient_affine _ _ _ _ _ _ hst,orient_affine _ _ _ _ _ _ hst,orient_affine _ _ _ _ _ _ hst]
      exact ⟨add_pos_of_pos_of_nonneg (mul_pos hs hc.1) (mul_nonneg ht.le hp.1),
        add_pos_of_pos_of_nonneg (mul_pos hs hc.2.1) (mul_nonneg ht.le hp.2.1),
        add_pos_of_pos_of_nonneg (mul_pos hs hc.2.2) (mul_nonneg ht.le hp.2.2)⟩
    exact closure_mono segmentInside (segment_subset_closure_openSegment (right_mem_segment ℝ (center a b c) p))

def affineValue (a b c : ℝ) (p : P2) : ℝ := a*p.1+b*p.2+c

theorem affineComplement_open (a b c : ℝ) : IsOpen {p : P2 | affineValue a b c p ≠ 0} := by
  apply isOpen_ne_fun _ continuous_const
  unfold affineValue
  fun_prop

/-- A nonconstant affine line has open dense complement. The elementary metric
proof makes the finite-arrangement generic-point argument explicit. -/
theorem affineComplement_dense (a b c : ℝ) (nonconstant : a≠0 ∨ b≠0) :
    Dense {p : P2 | affineValue a b c p ≠ 0} := by
  apply Metric.dense_iff.mpr
  intro p ε hε
  by_cases hp : affineValue a b c p ≠ 0
  · exact ⟨p,by simp [Metric.mem_ball,hε],hp⟩
  have hp0 : affineValue a b c p = 0 := not_ne_iff.mp hp
  rcases nonconstant with ha|hb
  · refine ⟨(p.1+ε/2,p.2),?_,?_⟩
    · change dist (p.1+ε/2,p.2) (p.1,p.2) < ε
      rw [dist_prod_same_right,Real.dist_eq]
      have habs : |p.1+ε/2-p.1| = ε/2 := by rw [show p.1+ε/2-p.1=ε/2 by ring,abs_of_pos (by positivity)]
      rw [habs]; linarith
    · change affineValue a b c (p.1+ε/2,p.2) ≠ 0
      have hproduct : a*(ε/2) ≠ 0 := mul_ne_zero ha (ne_of_gt (by positivity))
      unfold affineValue at hp0 ⊢
      dsimp only
      intro hz
      apply hproduct
      nlinarith
  · refine ⟨(p.1,p.2+ε/2),?_,?_⟩
    · change dist (p.1,p.2+ε/2) (p.1,p.2) < ε
      rw [dist_prod_same_left,Real.dist_eq]
      rw [show p.2+ε/2-p.2=ε/2 by ring,abs_of_pos (by positivity)]
      linarith
    · change affineValue a b c (p.1,p.2+ε/2) ≠ 0
      have hproduct : b*(ε/2) ≠ 0 := mul_ne_zero hb (ne_of_gt (by positivity))
      unfold affineValue at hp0 ⊢
      dsimp only
      intro hz
      apply hproduct
      nlinarith

/-- Removing a finite open-dense generic set cannot change the regularized
winding domain. This permits closure to recover edges and vertices. -/
theorem regularized_eq_of_generic (s u g : Set P2) (hu : IsOpen u)
    (hg : IsOpen g) (dense : Dense g) (agree : s ∩ g = u ∩ g) :
    closure (interior s) = closure u := by
  have huInterior : u ∩ g ⊆ interior s :=
    interior_maximal (by rw [← agree]; exact inter_subset_left) (hu.inter hg)
  have hleft : interior s ⊆ closure u := by
    intro p hp
    have hclosure := dense.open_subset_closure_inter isOpen_interior hp
    exact closure_mono (fun q hq => by
      have hm : q ∈ s ∩ g := ⟨interior_subset hq.1,hq.2⟩
      rw [agree] at hm
      exact hm.1) hclosure
  apply subset_antisymm
  · exact closure_minimal hleft isClosed_closure
  · apply closure_minimal _ isClosed_closure
    exact fun p hp => closure_mono huInterior (dense.open_subset_closure_inter hu hp)

#print axioms triangle_closure
#print axioms regularized_eq_of_generic
end Tess.RealGeometry
