import Tess.AffineBound
import Tess.ReferenceSoundness
noncomputable section
namespace Tess
open RealGeometry Set

def realValue (line : Separator) (p : P2) : ℝ :=
  affineValue (line.x : ℝ) (line.y : ℝ) (line.c : ℝ) p

theorem realValue_add (a b : Separator) (p : P2) :
    realValue (a.add b) p=realValue a p+realValue b p := by
  simp only [realValue,Separator.add,affineValue]; push_cast; ring

theorem realValue_neg (a : Separator) (p : P2) : realValue a.neg p= -realValue a p := by
  simp only [realValue,Separator.neg,affineValue]; push_cast; ring

theorem realValue_scale (a : Separator) (t : Rat) (p : P2) :
    realValue (a.scale t) p=(t : ℝ)*realValue a p := by
  simp only [realValue,Separator.scale,affineValue]; push_cast; ring

theorem coneWitnessValid_sound (a b c target weights : Separator)
    (checked : coneWitnessValid a b c target weights=true) (p : P2)
    (ha : 0≤realValue a p) (hb : 0≤realValue b p) (hc : 0≤realValue c p) :
    0≤realValue target p := by
  simp only [coneWitnessValid,Bool.and_eq_true,decide_eq_true_eq,planesEqual] at checked
  have equality : realValue target p=realValue (combine3 a b c weights) p := by
    simp only [realValue,checked.2.1,checked.2.2.1,checked.2.2.2]
  rw [equality,combine3,realValue_add,realValue_add,realValue_scale,realValue_scale,realValue_scale]
  exact add_nonneg (mul_nonneg (by exact_mod_cast checked.1.1) ha)
    (add_nonneg (mul_nonneg (by exact_mod_cast checked.1.2.1) hb)
      (mul_nonneg (by exact_mod_cast checked.1.2.2) hc))

theorem coneTriple_sound (a b c target : Separator) (checked : coneTriple a b c target=true)
    (p : P2) (ha : 0≤realValue a p) (hb : 0≤realValue b p) (hc : 0≤realValue c p) :
    0≤realValue target p := by
  by_cases zero : detColumns a b c=0
  · simp [coneTriple,zero] at checked
  · have witness : coneWitnessValid a b c target
        ⟨detColumns target b c/detColumns a b c,detColumns a target c/detColumns a b c,
          detColumns a b target/detColumns a b c⟩=true := by
      simpa only [coneTriple,zero,ite_false] using checked
    exact coneWitnessValid_sound _ _ _ _ _ witness p ha hb hc

theorem coneCheck_sound (lines : Array Separator) (target : Separator)
    (checked : coneCheck lines target=true) (p : P2)
    (nonnegative : ∀ line∈lines,0≤realValue line p) : 0≤realValue target p := by
  simp only [coneCheck,List.any_eq_true] at checked
  obtain ⟨k,hk,j,hj,i,hi,checked⟩:=checked
  have hk:=List.mem_range.mp hk
  have hj:=List.mem_range.mp hj
  have hi:=List.mem_range.mp hi
  exact coneTriple_sound _ _ _ _ checked p
    (nonnegative _ (by simpa only [getElem!_pos lines i (show i<lines.size by omega)] using Array.getElem_mem (show i<lines.size by omega)))
    (nonnegative _ (by simpa only [getElem!_pos lines j (show j<lines.size by omega)] using Array.getElem_mem (show j<lines.size by omega)))
    (nonnegative _ (by simpa only [getElem!_pos lines k hk] using Array.getElem_mem hk))

theorem supportingLine_realValue (m : ExactMesh) (a b : Nat) (p : P2) :
    realValue (supportingLine (m.project a) (m.project b)) p=
      RealGeometry.orient (realPoint m a) (realPoint m b) p := by
  simp only [realValue,supportingLine,affineValue,RealGeometry.orient,realPoint]
  push_cast
  ring

theorem halfplanes_nonnegative (seed output : ExactMesh) (a b : Face) (p : P2)
    (ha : p∈faceRegion seed a) (hb : p∈faceRegion output b) :
    ∀ line∈overlayHalfplanes seed a output b,0≤realValue line p := by
  intro line hl
  simp only [overlayHalfplanes,Array.mem_toArray,List.mem_append,List.mem_map,List.mem_singleton] at hl
  rcases hl with (⟨edge,he,rfl⟩|⟨edge,he,rfl⟩)|rfl
  · rw [supportingLine_realValue]
    simp only [Face.edges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl
    · exact ha.1
    · exact ha.2.1
    · exact ha.2.2
  · rw [supportingLine_realValue]
    simp only [Face.edges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2
  · norm_num [realValue,affineValue]

theorem overlayPairBound_sound (seed output : ExactMesh) (a b : Face) (tolerance : Rat)
    (positiveSeed : 0<RealGeometry.orient (realPoint seed a.a) (realPoint seed a.b) (realPoint seed a.c))
    (positiveOutput : 0<RealGeometry.orient (realPoint output b.a) (realPoint output b.b) (realPoint output b.c))
    (checked : overlayPairBound seed a output b tolerance=true) (nonnegative : 0≤tolerance)
    (p : P2) (ha : p∈openTriangle (realPoint seed a.a) (realPoint seed a.b) (realPoint seed a.c))
    (hb : p∈openTriangle (realPoint output b.a) (realPoint output b.b) (realPoint output b.c)) :
    |faceHeight seed a p-faceHeight output b p|≤(tolerance : ℝ) := by
  have ca : p∈faceRegion seed a:=⟨ha.1.le,ha.2.1.le,ha.2.2.le⟩
  have cb : p∈faceRegion output b:=⟨hb.1.le,hb.2.1.le,hb.2.2.le⟩
  simp only [overlayPairBound,Bool.or_eq_true,Bool.and_eq_true] at checked
  rcases checked with (same|separated)|bounds
  · rw [equalPlanes_heights _ _ _ _ same p,sub_self,abs_zero]
    exact_mod_cast nonnegative
  · simp only [noInteriorOverlap,Bool.or_eq_true] at separated
    rcases separated with left|right
    · exact (edgeSeparates_sound _ _ _ _ positiveOutput left p ha cb).elim
    · exact (edgeSeparates_sound _ _ _ _ positiveSeed right p hb ca).elim
  · have low:=coneCheck_sound _ _ bounds.1 p (halfplanes_nonnegative seed output a b p ca cb)
    have high:=coneCheck_sound _ _ bounds.2 p (halfplanes_nonnegative seed output a b p ca cb)
    have delta : realValue (heightDifference seed a output b) p=faceHeight seed a p-faceHeight output b p := by
      rw [heightDifference,realValue_add,realValue_neg]
      exact congrArg₂ (fun x y : ℝ => x-y) (heightPlane_real seed a p) (heightPlane_real output b p)
    have constant : realValue (⟨0,0,tolerance⟩ : Separator) p=(tolerance : ℝ) := by
      simp [realValue,affineValue]
    rw [realValue_add,delta,constant] at low
    rw [realValue_add,realValue_neg,delta,constant] at high
    exact abs_le.mpr ⟨by linarith,by linarith⟩

#print axioms coneCheck_sound
end Tess
