import Tess.SeparationSoundness
noncomputable section
namespace Tess.RealGeometry
open Set

def affineLift (a b c : P2) (ha hb hc : ℝ) (p : P2) : ℝ :=
  (orient p b c*ha+orient p c a*hb+orient p a b*hc)/orient a b c

def liftCoefficients (a b c : P2) (ha hb hc : ℝ) : ℝ × ℝ × ℝ :=
  (((b.2-c.2)*ha+(c.2-a.2)*hb+(a.2-b.2)*hc)/orient a b c,
   ((c.1-b.1)*ha+(a.1-c.1)*hb+(b.1-a.1)*hc)/orient a b c,
   ((b.1*c.2-b.2*c.1)*ha+(c.1*a.2-c.2*a.1)*hb+(a.1*b.2-a.2*b.1)*hc)/orient a b c)

theorem affineLift_coefficients (a b c : P2) (ha hb hc : ℝ) (p : P2) :
    affineLift a b c ha hb hc p =
      affineValue (liftCoefficients a b c ha hb hc).1 (liftCoefficients a b c ha hb hc).2.1
        (liftCoefficients a b c ha hb hc).2.2 p := by
  unfold affineLift affineValue liftCoefficients
  dsimp only
  simp only [div_eq_mul_inv]
  unfold orient
  ring

theorem continuous_affineLift (a b c : P2) (ha hb hc : ℝ) : Continuous (affineLift a b c ha hb hc) := by
  have eq : affineLift a b c ha hb hc = fun p =>
      affineValue (liftCoefficients a b c ha hb hc).1 (liftCoefficients a b c ha hb hc).2.1
        (liftCoefficients a b c ha hb hc).2.2 p := funext (affineLift_coefficients a b c ha hb hc)
  rw [eq]
  unfold affineValue
  fun_prop

theorem affineLift_combo3 (a b c p q r : P2) (ha hb hc u v w : ℝ) (total : u+v+w=1) :
    affineLift a b c ha hb hc (combo3 p q r u v w) =
      u*affineLift a b c ha hb hc p+v*affineLift a b c ha hb hc q+w*affineLift a b c ha hb hc r := by
  simp only [affineLift_coefficients]
  exact affine_combo3 _ _ _ _ _ _ _ _ _ total

theorem affineLift_vertex_a (a b c : P2) (ha hb hc : ℝ) (h : orient a b c≠0) :
    affineLift a b c ha hb hc a=ha := by
  unfold affineLift
  have h1 : orient a c a=0 := by unfold orient;ring
  have h2 : orient a a b=0 := by unfold orient;ring
  rw [h1,h2]
  simp [mul_div_cancel_left₀ ha h]

theorem affineLift_vertex_b (a b c : P2) (ha hb hc : ℝ) (h : orient a b c≠0) :
    affineLift a b c ha hb hc b=hb := by
  unfold affineLift
  have h1 : orient b b c=0 := by unfold orient;ring
  have h2 : orient b a b=0 := by unfold orient;ring
  have h3 : orient b c a=orient a b c := by unfold orient;ring
  rw [h1,h2,h3]
  simp [mul_div_cancel_left₀ hb h]

theorem affineLift_vertex_c (a b c : P2) (ha hb hc : ℝ) (h : orient a b c≠0) :
    affineLift a b c ha hb hc c=hc := by
  unfold affineLift
  have h1 : orient c b c=0 := by unfold orient;ring
  have h2 : orient c c a=0 := by unfold orient;ring
  have h3 : orient c a b=orient a b c := by unfold orient;ring
  rw [h1,h2,h3]
  simp [mul_div_cancel_left₀ hc h]
end Tess.RealGeometry

namespace Tess
open RealGeometry Set

def faceHeight (m : ExactMesh) (f : Face) : P2 → ℝ :=
  affineLift (realPoint m f.a) (realPoint m f.b) (realPoint m f.c)
    ((m.point f.a).coord m.axis) ((m.point f.b).coord m.axis) ((m.point f.c).coord m.axis)
def faceRegion (m : ExactMesh) (f : Face) : Set P2 :=
  closedTriangle (realPoint m f.a) (realPoint m f.b) (realPoint m f.c)

theorem faceHeight_interpolates (m : ExactMesh) (f : Face)
    (positive : 0<RealGeometry.orient (realPoint m f.a) (realPoint m f.b) (realPoint m f.c))
    (i : Nat) (hi : i∈f.ids) : faceHeight m f (realPoint m i)=((m.point i).coord m.axis : ℝ) := by
  simp [Face.ids] at hi
  rcases hi with rfl|rfl|rfl
  · exact affineLift_vertex_a _ _ _ _ _ _ (ne_of_gt positive)
  · exact affineLift_vertex_b _ _ _ _ _ _ (ne_of_gt positive)
  · exact affineLift_vertex_c _ _ _ _ _ _ (ne_of_gt positive)

theorem agreement_on_commonSimplex (m : ExactMesh) (a b : Face)
    (pa : 0<RealGeometry.orient (realPoint m a.a) (realPoint m a.b) (realPoint m a.c))
    (pb : 0<RealGeometry.orient (realPoint m b.a) (realPoint m b.b) (realPoint m b.c)) :
    commonSimplex (realPoint m) a b ⊆ {p | faceHeight m a p=faceHeight m b p} := by
  apply convexHull_min
  · rintro p ⟨i,ha,hb,rfl⟩
    exact (faceHeight_interpolates m a pa i ha).trans (faceHeight_interpolates m b pb i hb).symm
  · intro p hp q hq u v hu hv total
    change faceHeight m a (u • p+v • q)=faceHeight m b (u • p+v • q)
    have sum : u+v+0=1 := by simpa using total
    have zeroCombo : combo3 p q (0,0) u v 0=u • p+v • q := by simp [combo3]
    rw [← zeroCombo]
    unfold faceHeight
    rw [affineLift_combo3 _ _ _ _ _ _ _ _ _ _ _ _ sum,
        affineLift_combo3 _ _ _ _ _ _ _ _ _ _ _ _ sum]
    change u*faceHeight m a p+v*faceHeight m a q+0*_=u*faceHeight m b p+v*faceHeight m b q+0*_
    rw [hp,hq]
    ring

theorem meshPositive (rings : Array Nat) (m : ExactMesh) {expected : List (Nat × Nat)} (h : meshCheck rings m expected=true) :
    ∀ f∈m.faces, 0<RealGeometry.orient (realPoint m f.a) (realPoint m f.b) (realPoint m f.c) := by
  have hs : m.faces.all (facePositive m)=true := by
    simp only [meshCheck,Bool.and_eq_true] at h
    aesop
  intro f hf
  have hp := (Array.all_eq_true'.mp hs) f hf
  simp only [facePositive,Bool.and_eq_true] at hp
  rw [orient_cast]
  exact_mod_cast positive_sound _ _ _ hp.2

theorem mesh_intersection_sound (rings : Array Nat) (m : ExactMesh) {expected : List (Nat × Nat)} (h : meshCheck rings m expected=true)
    (i j : Nat) (hi : i<m.faces.size) (hj : j < i) :
    faceRegion m m.faces[i] ∩ faceRegion m m.faces[j] = commonSimplex (realPoint m) m.faces[i] m.faces[j] := by
  have hjn : j<m.faces.size := by omega
  have pairs : allN m.faces.size (fun i => allN i fun j => facePair m m.faces[i]! m.faces[j]!)=true := by
    simp only [meshCheck,Bool.and_eq_true] at h; aesop
  simp only [allN,List.all_eq_true,List.mem_range] at pairs
  have pair := pairs i hi j hj
  simp only [getElem!_pos m.faces i hi,getElem!_pos m.faces j hjn,facePair,Bool.and_eq_true] at pair
  have sep : pairSeparable m m.faces[i] m.faces[j]=true := by aesop
  exact pairSeparable_sound m _ _ (meshPositive rings m h _ (Array.getElem_mem hi))
    (meshPositive rings m h _ (Array.getElem_mem hjn)) sep

/-- Heights agree on every face intersection. This is the gluing property
needed for the finite, closed PL graph, proved from actual checker predicates. -/
theorem mesh_height_agreement (rings : Array Nat) (m : ExactMesh) {expected : List (Nat × Nat)} (h : meshCheck rings m expected=true) :
    ∀ a∈m.faces, ∀ b∈m.faces, ∀ p∈faceRegion m a ∩ faceRegion m b,
      faceHeight m a p=faceHeight m b p := by
  have positive := meshPositive rings m h
  have pairs : allN m.faces.size (fun i => allN i fun j => facePair m m.faces[i]! m.faces[j]!)=true := by
    simp only [meshCheck,Bool.and_eq_true] at h
    aesop
  simp only [allN,List.all_eq_true,List.mem_range] at pairs
  have ordered (i j : Nat) (hi : i<m.faces.size) (hj : j < i) :
      ∀ p∈faceRegion m m.faces[i] ∩ faceRegion m m.faces[j],
        faceHeight m m.faces[i] p=faceHeight m m.faces[j] p := by
    have hjn : j<m.faces.size := by omega
    have pair := pairs i hi j hj
    simp only [getElem!_pos m.faces i hi,getElem!_pos m.faces j hjn,facePair,Bool.and_eq_true] at pair
    have sep : pairSeparable m m.faces[i] m.faces[j]=true := by aesop
    have pa := positive m.faces[i] (Array.getElem_mem hi)
    have pb := positive m.faces[j] (Array.getElem_mem hjn)
    intro p hp
    have common := (pairSeparable_sound m _ _ pa pb sep).le hp
    exact agreement_on_commonSimplex m _ _ pa pb common
  intro a ha b hb p hp
  obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp ha
  obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp hb
  rcases lt_trichotomy i j with hij|hij|hij
  · exact (ordered j i hj hij p ⟨hp.2,hp.1⟩).symm
  · subst j; rfl
  · exact ordered i j hi hij p hp
#print axioms mesh_height_agreement
end Tess
