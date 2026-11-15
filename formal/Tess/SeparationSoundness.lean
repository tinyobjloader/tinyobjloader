import Tess.CertificateCoverage
import Tess.Barycentric
noncomputable section
namespace Tess.RealGeometry
open Set

def commonSimplex (points : Nat → P2) (a b : Tess.Face) : Set P2 :=
  convexHull ℝ {q | ∃ i ∈ a.ids, i ∈ b.ids ∧ points i=q}
structure SeparationSigns (points : Nat → P2) (a b : Tess.Face) (A B C : ℝ) : Prop where
  nonnegative : ∀ i ∈ a.ids, 0≤affineValue A B C (points i)
  nonpositive : ∀ i ∈ b.ids, affineValue A B C (points i)≤0
  strictLeft : ∀ i ∈ a.ids, i ∉ b.ids → 0<affineValue A B C (points i)
  strictRight : ∀ i ∈ b.ids, i ∉ a.ids → affineValue A B C (points i)<0

theorem closedTriangle_convex (a b c : P2) : Convex ℝ (closedTriangle a b c) := by
  intro p hp q hq u v hu hv total
  change 0≤orient a b (u • p+v • q) ∧ 0≤orient b c (u • p+v • q) ∧ 0≤orient c a (u • p+v • q)
  rw [orient_affine _ _ _ _ _ _ total,orient_affine _ _ _ _ _ _ total,orient_affine _ _ _ _ _ _ total]
  exact ⟨add_nonneg (mul_nonneg hu hp.1) (mul_nonneg hv hq.1),
    add_nonneg (mul_nonneg hu hp.2.1) (mul_nonneg hv hq.2.1),
    add_nonneg (mul_nonneg hu hp.2.2) (mul_nonneg hv hq.2.2)⟩

theorem faceVertex_mem (points : Nat → P2) (a : Tess.Face)
    (positive : 0<orient (points a.a) (points a.b) (points a.c))
    (i : Nat) (hi : i ∈ a.ids) :
    points i ∈ closedTriangle (points a.a) (points a.b) (points a.c) := by
  simp [Tess.Face.ids] at hi
  rcases hi with rfl|rfl|rfl
  · apply (barycentric _ _ _ _ positive).mpr
    exact ⟨1,0,0,by norm_num,by norm_num,by norm_num,by norm_num,by simp [combo3]⟩
  · apply (barycentric _ _ _ _ positive).mpr
    exact ⟨0,1,0,by norm_num,by norm_num,by norm_num,by norm_num,by simp [combo3]⟩
  · apply (barycentric _ _ _ _ positive).mpr
    exact ⟨0,0,1,by norm_num,by norm_num,by norm_num,by norm_num,by simp [combo3]⟩

/-- A separating affine functional forces all weights of noncommon vertices
to vanish at an intersection point. Thus intersection is the shared simplex. -/
theorem separation_intersection (points : Nat → P2) (a b : Tess.Face) (A B C : ℝ)
    (pa : 0<orient (points a.a) (points a.b) (points a.c))
    (pb : 0<orient (points b.a) (points b.b) (points b.c))
    (signs : SeparationSigns points a b A B C) :
    closedTriangle (points a.a) (points a.b) (points a.c) ∩
      closedTriangle (points b.a) (points b.b) (points b.c) = commonSimplex points a b := by
  apply subset_antisymm
  · intro p hp
    obtain ⟨u,v,w,hu,hv,hw,total,repr⟩ := (barycentric _ _ _ _ pa).mp hp.1
    obtain ⟨r,s,t,hr,hs,ht,totalB,reprB⟩ := (barycentric _ _ _ _ pb).mp hp.2
    have ha := signs.nonnegative a.a (by simp [Tess.Face.ids])
    have hb := signs.nonnegative a.b (by simp [Tess.Face.ids])
    have hc := signs.nonnegative a.c (by simp [Tess.Face.ids])
    have hd := signs.nonpositive b.a (by simp [Tess.Face.ids])
    have he := signs.nonpositive b.b (by simp [Tess.Face.ids])
    have hf := signs.nonpositive b.c (by simp [Tess.Face.ids])
    have left : 0≤affineValue A B C p := by
      rw [← repr,affine_combo3 _ _ _ _ _ _ _ _ _ total]
      exact add_nonneg (add_nonneg (mul_nonneg hu ha) (mul_nonneg hv hb)) (mul_nonneg hw hc)
    have right : affineValue A B C p≤0 := by
      rw [← reprB,affine_combo3 _ _ _ _ _ _ _ _ _ totalB]
      exact add_nonpos (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr hd)
        (mul_nonpos_of_nonneg_of_nonpos hs he)) (mul_nonpos_of_nonneg_of_nonpos ht hf)
    have zero : u*affineValue A B C (points a.a)+v*affineValue A B C (points a.b)+
        w*affineValue A B C (points a.c)=0 := by
      rw [← affine_combo3 _ _ _ _ _ _ _ _ _ total,repr]
      exact le_antisymm right left
    have huv := mul_nonneg hu ha
    have hvv := mul_nonneg hv hb
    have hwv := mul_nonneg hw hc
    rw [← repr]
    apply combo_mem_hull _ _ _ _ _ _ hu hv hw total
    · intro nonzero
      refine ⟨a.a,by simp [Tess.Face.ids],?_,rfl⟩
      by_contra absent
      have strict := signs.strictLeft a.a (by simp [Tess.Face.ids]) absent
      have pos := mul_pos (lt_of_le_of_ne hu (Ne.symm nonzero)) strict
      linarith
    · intro nonzero
      refine ⟨a.b,by simp [Tess.Face.ids],?_,rfl⟩
      by_contra absent
      have strict := signs.strictLeft a.b (by simp [Tess.Face.ids]) absent
      have pos := mul_pos (lt_of_le_of_ne hv (Ne.symm nonzero)) strict
      linarith
    · intro nonzero
      refine ⟨a.c,by simp [Tess.Face.ids],?_,rfl⟩
      by_contra absent
      have strict := signs.strictLeft a.c (by simp [Tess.Face.ids]) absent
      have pos := mul_pos (lt_of_le_of_ne hw (Ne.symm nonzero)) strict
      linarith
  · apply convexHull_min
    · rintro p ⟨i,ha,hb,rfl⟩
      exact ⟨faceVertex_mem points a pa i ha,faceVertex_mem points b pb i hb⟩
    · exact (closedTriangle_convex _ _ _).inter (closedTriangle_convex _ _ _)
end Tess.RealGeometry

namespace Tess
open RealGeometry

theorem separator_cast (m : ExactMesh) (line : Separator) (i : Nat) :
    affineValue (line.x : ℝ) (line.y : ℝ) (line.c : ℝ) (realPoint m i) =
      ((line.value (m.project i)) : ℝ) := by
  simp [affineValue,realPoint,Separator.value]

private theorem separator_signs (m : ExactMesh) (a b : Face) (line : Separator)
    (h : separatorValid m a b line = true) :
    SeparationSigns (realPoint m) a b line.x line.y line.c := by
  simp only [separatorValid,Bool.and_eq_true] at h
  have ha : a.ids.all (fun i => if b.ids.contains i then decide (line.value (m.project i)=0)
    else decide (0<line.value (m.project i))) = true := by aesop
  have hb : b.ids.all (fun i => if a.ids.contains i then decide (line.value (m.project i)=0)
    else decide (line.value (m.project i)<0)) = true := by aesop
  constructor
  · intro i hi
    have hv := (List.all_eq_true.mp ha) i hi
    rw [separator_cast]
    by_cases common : i∈b.ids
    · simp [common] at hv
      exact_mod_cast (show (0 : Rat)≤line.value (m.project i) by rw [hv])
    · simp [common] at hv
      exact_mod_cast hv.le
  · intro i hi
    have hv := (List.all_eq_true.mp hb) i hi
    rw [separator_cast]
    by_cases common : i∈a.ids
    · simp [common] at hv
      exact_mod_cast (show line.value (m.project i)≤(0 : Rat) by rw [hv])
    · simp [common] at hv
      exact_mod_cast hv.le
  · intro i hi absent
    have hv := (List.all_eq_true.mp ha) i hi
    simp [absent] at hv
    rw [separator_cast]
    exact_mod_cast hv
  · intro i hi absent
    have hv := (List.all_eq_true.mp hb) i hi
    simp [absent] at hv
    rw [separator_cast]
    exact_mod_cast hv

theorem pairSeparable_sound (m : ExactMesh) (a b : Face)
    (pa : 0<RealGeometry.orient (realPoint m a.a) (realPoint m a.b) (realPoint m a.c))
    (pb : 0<RealGeometry.orient (realPoint m b.a) (realPoint m b.b) (realPoint m b.c))
    (h : pairSeparable m a b = true) :
    closedTriangle (realPoint m a.a) (realPoint m a.b) (realPoint m a.c) ∩
      closedTriangle (realPoint m b.a) (realPoint m b.b) (realPoint m b.c) = commonSimplex (realPoint m) a b := by
  obtain ⟨line,valid⟩ := pairSeparable_witness m a b h
  exact separation_intersection _ a b line.x line.y line.c pa pb (separator_signs m a b line valid)
#print axioms pairSeparable_sound
end Tess
