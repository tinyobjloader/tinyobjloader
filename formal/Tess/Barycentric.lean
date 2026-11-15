import Tess.RealTopology
import Mathlib.Analysis.Convex.Combination
noncomputable section
namespace Tess.RealGeometry
open Set

def combo3 (a b c : P2) (u v w : ℝ) : P2 := u • a + v • b + w • c

theorem affine_combo3 (A B C : ℝ) (a b c : P2) (u v w : ℝ) (total : u+v+w=1) :
    affineValue A B C (combo3 a b c u v w) =
      u*affineValue A B C a + v*affineValue A B C b + w*affineValue A B C c := by
  unfold affineValue combo3
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  linear_combination -C * total

theorem orient_combo3 (a b c d e : P2) (u v w : ℝ) (total : u+v+w=1) :
    orient d e (combo3 a b c u v w) =
      u*orient d e a+v*orient d e b+w*orient d e c := by
  calc
    _ = u*orient d e a+v*orient d e b+w*orient d e c+(1-u-v-w)*orient d e (0,0) := by
      unfold combo3 orient
      simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
      ring
    _ = _ := by rw [show 1-u-v-w=0 by linarith]; ring

theorem barycentric (a b c p : P2) (positive : 0<orient a b c) :
    p ∈ closedTriangle a b c ↔ ∃ u v w : ℝ, 0≤u ∧ 0≤v ∧ 0≤w ∧ u+v+w=1 ∧ combo3 a b c u v w=p := by
  constructor
  · intro hp
    let D := orient a b c
    have hD : D ≠ 0 := ne_of_gt positive
    refine ⟨orient b c p/D,orient c a p/D,orient a b p/D,
      div_nonneg hp.2.1 positive.le,div_nonneg hp.2.2 positive.le,div_nonneg hp.1 positive.le,?_,?_⟩
    · rw [← add_div,← add_div]
      have hsum : orient b c p+orient c a p+orient a b p=D := by
        have hs := orient_sum a b c p
        dsimp only [D]
        linarith
      rw [hsum,div_self hD]
    · apply Prod.ext <;>
        simp only [combo3,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;>
        dsimp only [D] <;> field_simp [hD] <;> unfold orient <;> ring
  · rintro ⟨u,v,w,hu,hv,hw,total,rfl⟩
    change 0≤orient a b (combo3 a b c u v w) ∧
      0≤orient b c (combo3 a b c u v w) ∧ 0≤orient c a (combo3 a b c u v w)
    rw [orient_combo3 _ _ _ _ _ _ _ _ total,orient_combo3 _ _ _ _ _ _ _ _ total,orient_combo3 _ _ _ _ _ _ _ _ total]
    have h1 : orient a b a=0 := by unfold orient; ring
    have h2 : orient a b b=0 := by unfold orient; ring
    have h3 : orient b c b=0 := by unfold orient; ring
    have h4 : orient b c c=0 := by unfold orient; ring
    have h5 : orient c a a=0 := by unfold orient; ring
    have h6 : orient c a c=0 := by unfold orient; ring
    have h7 : orient b c a=orient a b c := by unfold orient; ring
    have h8 : orient c a b=orient a b c := by unfold orient; ring
    simp only [h1,h2,h3,h4,h5,h6,h7,h8,mul_zero,zero_add,add_zero]
    exact ⟨mul_nonneg hw positive.le,mul_nonneg hu positive.le,mul_nonneg hv positive.le⟩

/-- Convex combinations supported only at common indexed vertices belong to
that indexed simplex, even when some of the three coefficients vanish. -/
theorem combo_mem_hull {s : Set P2} (a b c : P2) (u v w : ℝ)
    (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) (total : u+v+w=1)
    (ha : u≠0 → a∈s) (hb : v≠0 → b∈s) (hc : w≠0 → c∈s) :
    combo3 a b c u v w ∈ convexHull ℝ s := by
  classical
  let weights : Fin 3 → ℝ := ![u,v,w]
  let points : Fin 3 → P2 := ![a,b,c]
  have hnonnegative : ∀ i, 0≤weights i := by intro i; fin_cases i <;> simpa [weights]
  have htotal : ∑ i, weights i = 1 := by simpa [weights,Fin.sum_univ_succ,add_assoc] using total
  have support : ∀ i, weights i≠0 → points i∈s := by
    intro i; fin_cases i <;> simpa [weights,points]
  have existsNonzero : ∃ i, weights i≠0 := by
    by_contra! hzero
    have : ∑ i, weights i=0 := Finset.sum_eq_zero (fun i _ => hzero i)
    linarith
  obtain ⟨chosen,hchosen⟩ := existsNonzero
  let fixed (i : Fin 3) : P2 := if weights i=0 then points chosen else points i
  have fixedMem : ∀ i, fixed i∈s := by
    intro i
    by_cases hi : weights i=0
    · simpa [fixed,hi] using support chosen hchosen
    · simpa [fixed,hi] using support i hi
  have same (i : Fin 3) : weights i • fixed i = weights i • points i := by
    by_cases hi : weights i=0 <;> simp [fixed,hi]
  have represented : ∑ i, weights i • fixed i = combo3 a b c u v w := by
    simp only [same]
    simp [weights,points,combo3,Fin.sum_univ_succ,add_assoc]
  exact mem_convexHull_of_exists_fintype weights fixed hnonnegative htotal fixedMem represented
#print axioms barycentric
#print axioms combo_mem_hull
end Tess.RealGeometry
