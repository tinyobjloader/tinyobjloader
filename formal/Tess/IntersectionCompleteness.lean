import Tess.SegmentSoundness

noncomputable section
namespace Tess
open RealGeometry

/-- A nondegenerate rational line admits a rational parameter for every rational
collinear point, including points outside the closed segment. -/
theorem collinear_parameter (a b p : Point2) (different : a≠b)
    (col : orient a b p=0) : ∃ t : Rat,p=segmentPoint a b t := by
  by_cases hx : b.x-a.x=0
  · have hy : b.y-a.y≠0 := by
      intro hy
      apply different
      cases a; cases b
      simp only [Point2.mk.injEq]
      constructor <;> dsimp at * <;> linarith
    let t : Rat := (p.y-a.y)/(b.y-a.y)
    have hty : t*(b.y-a.y)=p.y-a.y := div_mul_cancel₀ _ hy
    have px : p.x=a.x := by
      have product : (b.y-a.y)*(p.x-a.x)=0 := by
        dsimp [orient] at col
        rw [hx,zero_mul] at col
        linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left hy)
    refine ⟨t,?_⟩
    cases p; cases a; cases b
    simp only [segmentPoint,Point2.mk.injEq]
    constructor
    · dsimp at hx px
      rw [hx,mul_zero,add_zero]
      exact px
    · dsimp at hty
      linarith
  · let t : Rat := (p.x-a.x)/(b.x-a.x)
    have htx : t*(b.x-a.x)=p.x-a.x := div_mul_cancel₀ _ hx
    have py : p.y=a.y+t*(b.y-a.y) := by
      apply mul_left_cancel₀ hx
      calc (b.x-a.x)*p.y=(b.x-a.x)*a.y+(b.y-a.y)*(p.x-a.x) := by
             dsimp [orient] at col; linarith
           _=(b.x-a.x)*(a.y+t*(b.y-a.y)) := by rw [← htx]; ring
    refine ⟨t,?_⟩
    cases p; cases a; cases b
    simp only [segmentPoint,Point2.mk.injEq]
    constructor <;> dsimp at * <;> linarith

theorem real_segmentPoint (a b : Point2) (t : Rat) :
    realPoint2 (segmentPoint a b t)=interpolate (realPoint2 a) (realPoint2 b) t := by
  simp only [realPoint2,segmentPoint,interpolate]
  push_cast
  rfl

theorem interpolate_comp (a b : P2) (u v t : ℝ) :
    interpolate (interpolate a b u) (interpolate a b v) t=
      interpolate a b (u+t*(v-u)) := by
  ext <;> dsimp [interpolate] <;> ring

theorem interpolate_parameter_unique (a b : Point2) (different : a≠b) (s t : ℝ)
    (equal : interpolate (realPoint2 a) (realPoint2 b) s=
      interpolate (realPoint2 a) (realPoint2 b) t) : s=t := by
  have component (x y : Rat) (h : (x : ℝ)+s*((y : ℝ)-x)=(x : ℝ)+t*((y : ℝ)-x))
      (different : y-x≠0) : s=t := by
    have nonzero : (y : ℝ)-(x : ℝ)≠0 := by exact_mod_cast different
    have product : (s-t)*((y : ℝ)-(x : ℝ))=0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right nonzero)
  by_cases hx : b.x-a.x=0
  · have hy : b.y-a.y≠0 := by
      intro hy
      apply different
      cases a; cases b
      simp only [Point2.mk.injEq]
      constructor <;> dsimp at * <;> linarith
    exact component a.y b.y (congrArg Prod.snd equal) hy
  · exact component a.x b.x (congrArg Prod.fst equal) hx

/-- Affine reparameterization preserves every closed subinterval of a line. -/
theorem parameter_subsegment (a b : Point2) (u v q : Rat) (bounds : between u v q) :
    RationalSegment (segmentPoint a b u) (segmentPoint a b v) (segmentPoint a b q) := by
  have checked : onSegment ⟨u,0⟩ ⟨v,0⟩ ⟨q,0⟩=true := by
    simp only [onSegment,Bool.and_eq_true,collinear,decide_eq_true_eq]
    exact ⟨by simp [orient],bounds,Or.inl ⟨le_rfl,le_rfl⟩⟩
  obtain ⟨t,lo,hi,equal⟩:=onSegment_rational _ _ _ checked
  have coordinate : q=u+t*(v-u) := congrArg Point2.x equal
  refine ⟨t,lo,hi,?_⟩
  rw [coordinate]
  cases a; cases b
  simp only [segmentPoint,Point2.mk.injEq]
  constructor <;> ring

/-- Interpolation never leaves the coordinate interval of its endpoints. -/
theorem real_between_interpolation (u v t : ℝ) (lo : 0≤t) (hi : t≤1) :
    (u≤u+t*(v-u) ∧ u+t*(v-u)≤v) ∨ (v≤u+t*(v-u) ∧ u+t*(v-u)≤u) := by
  rcases le_total u v with forward|reverse
  · left
    constructor <;> nlinarith [mul_nonneg lo (show 0≤v-u by linarith),
      mul_nonneg (show 0≤1-t by linarith) (show 0≤v-u by linarith)]
  · right
    constructor <;> nlinarith [mul_nonneg lo (show 0≤u-v by linarith),
      mul_nonneg (show 0≤1-t by linarith) (show 0≤u-v by linarith)]

/-- Collinear closed intervals can intersect only if an endpoint belongs to
both. No proper-crossing assumption or rationality of the common point is used. -/
theorem collinear_intersection_endpoint (a b c d : Point2) (different : a≠b)
    (colC : orient a b c=0) (colD : orient a b d=0)
    (common : ∃ p : P2,
      (∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 a) (realPoint2 b) t) ∧
      (∃ s : ℝ,0≤s ∧ s≤1 ∧ p=interpolate (realPoint2 c) (realPoint2 d) s)) :
    onSegment a b c=true ∨ onSegment a b d=true ∨ onSegment c d a=true := by
  obtain ⟨u,hc⟩:=collinear_parameter a b c different colC
  obtain ⟨v,hd⟩:=collinear_parameter a b d different colD
  obtain ⟨p,⟨t,tlo,thi,ht⟩,⟨s,slo,shi,hs⟩⟩:=common
  have parameter : t=(u : ℝ)+s*((v : ℝ)-(u : ℝ)) := by
    apply interpolate_parameter_unique a b different
    rw [← ht,hs,hc,hd,real_segmentPoint,real_segmentPoint,interpolate_comp]
  have interval:=real_between_interpolation (u : ℝ) (v : ℝ) s slo shi
  rw [← parameter] at interval
  have atStart (zero : between u v 0) : onSegment c d a=true := by
    have member:=parameter_subsegment a b u v 0 zero
    have original : segmentPoint a b 0=a := by simp [segmentPoint]
    rw [← hc,← hd,original] at member
    exact RationalSegment_onSegment c d a member
  rcases interval with forward|reverse
  · by_cases nonnegative : (0 : ℝ)≤u
    · left
      exact RationalSegment_onSegment a b c ⟨u,by exact_mod_cast nonnegative,
        by exact_mod_cast (show (u : ℝ)≤1 by linarith),hc⟩
    · right; right
      apply atStart
      left
      exact ⟨by exact_mod_cast (show (u : ℝ)≤0 by linarith),
        by exact_mod_cast (show (0 : ℝ)≤v by linarith)⟩
  · by_cases nonnegative : (0 : ℝ)≤v
    · right; left
      exact RationalSegment_onSegment a b d ⟨v,by exact_mod_cast nonnegative,
        by exact_mod_cast (show (v : ℝ)≤1 by linarith),hd⟩
    · right; right
      apply atStart
      right
      exact ⟨by exact_mod_cast (show (v : ℝ)≤0 by linarith),
        by exact_mod_cast (show (0 : ℝ)≤u by linarith)⟩

/-- An affine orientation interpolates exactly along a real segment. -/
theorem real_orient_interpolate (a b c d : Point2) (s : ℝ) :
    RealGeometry.orient (realPoint2 a) (realPoint2 b)
      (interpolate (realPoint2 c) (realPoint2 d) s)=
      (1-s)*(orient a b c : ℝ)+s*(orient a b d : ℝ) := by
  dsimp [RealGeometry.orient,realPoint2,interpolate,orient]
  push_cast
  ring

/-- If closed segments have a common real point and no endpoint contacts,
their endpoints lie strictly on opposite sides of the other supporting line. -/
theorem intersection_strict_sides (a b c d : Point2)
    (common : ∃ p : P2,
      (∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 a) (realPoint2 b) t) ∧
      (∃ s : ℝ,0≤s ∧ s≤1 ∧ p=interpolate (realPoint2 c) (realPoint2 d) s))
    (noC : onSegment a b c=false) (noD : onSegment a b d=false)
    (noA : onSegment c d a=false) :
    orient a b c * orient a b d<0 := by
  obtain ⟨p,⟨t,tlo,thi,ht⟩,⟨s,slo,shi,hs⟩⟩:=common
  have different : a≠b := by
    intro equal
    have hp : p=realPoint2 a := by rw [equal] at ht; simpa [interpolate,equal] using ht
    have member : onSegment c d a=true :=
      (onSegment_iff_real c d a).mpr ⟨s,slo,shi,by rw [← hp]; exact hs⟩
    rw [noA] at member
    contradiction
  have sPositive : 0<s := by
    by_contra notPositive
    have zero : s=0 := by linarith
    have hp : p=realPoint2 c := by simpa [zero,interpolate] using hs
    have member : onSegment a b c=true :=
      (onSegment_iff_real a b c).mpr ⟨t,tlo,thi,by rw [← hp]; exact ht⟩
    rw [noC] at member
    contradiction
  have sBelow : s<1 := by
    by_contra notBelow
    have one : s=1 := by linarith
    have hp : p=realPoint2 d := by simpa [one,interpolate] using hs
    have member : onSegment a b d=true :=
      (onSegment_iff_real a b d).mpr ⟨t,tlo,thi,by rw [← hp]; exact ht⟩
    rw [noD] at member
    contradiction
  have relation : (1-s)*(orient a b c : ℝ)+s*(orient a b d : ℝ)=0 := by
    rw [← real_orient_interpolate,← hs,ht]
    dsimp [RealGeometry.orient,realPoint2,interpolate]
    ring
  have nonzero : orient a b c≠0 := by
    intro colC
    have colDReal : (orient a b d : ℝ)=0 := by
      rw [colC] at relation
      simp only [Rat.cast_zero,mul_zero,zero_add] at relation
      exact (mul_eq_zero.mp relation).resolve_left sPositive.ne'
    have colD : orient a b d=0 := by exact_mod_cast colDReal
    have contact:=collinear_intersection_endpoint a b c d different colC colD
      ⟨p,⟨t,tlo,thi,ht⟩,⟨s,slo,shi,hs⟩⟩
    rcases contact with contact|contact|contact <;> simp_all
  have realNonzero : (orient a b c : ℝ)≠0 := by exact_mod_cast nonzero
  have squarePositive : 0<(orient a b c : ℝ)*(orient a b c : ℝ) := mul_self_pos.mpr realNonzero
  have multiplied:=congrArg (fun x : ℝ => (orient a b c : ℝ)*x) relation
  have identity : s*((orient a b c : ℝ)*(orient a b d : ℝ))=
      -(1-s)*((orient a b c : ℝ)*(orient a b c : ℝ)) := by
    nlinarith only [multiplied]
  have productNegative : s*((orient a b c : ℝ)*(orient a b d : ℝ))<0 := by
    rw [identity]
    exact mul_neg_of_neg_of_pos (by linarith) squarePositive
  have result : (orient a b c : ℝ)*(orient a b d : ℝ)<0 := by
    by_contra bad
    have nonnegative:=mul_nonneg sPositive.le (le_of_not_gt bad)
    exact (not_lt_of_ge nonnegative) productNegative
  exact_mod_cast result

/-- Completeness of the executable closed intersection check with respect to
real segments. Degenerate segments and collinear overlaps need no exceptions. -/
theorem closedIntersection_complete (a b c d : Point2)
    (common : ∃ p : P2,
      (∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 a) (realPoint2 b) t) ∧
      (∃ s : ℝ,0≤s ∧ s≤1 ∧ p=interpolate (realPoint2 c) (realPoint2 d) s)) :
    closedIntersection a b c d=true := by
  by_cases hC : onSegment a b c=true
  · simp [closedIntersection,hC]
  by_cases hD : onSegment a b d=true
  · simp [closedIntersection,hD]
  by_cases hA : onSegment c d a=true
  · simp [closedIntersection,hA]
  by_cases hB : onSegment c d b=true
  · simp [closedIntersection,hB]
  have cFalse : onSegment a b c=false := Bool.eq_false_iff.mpr hC
  have dFalse : onSegment a b d=false := Bool.eq_false_iff.mpr hD
  have aFalse : onSegment c d a=false := Bool.eq_false_iff.mpr hA
  have bFalse : onSegment c d b=false := Bool.eq_false_iff.mpr hB
  have left:=intersection_strict_sides a b c d common cFalse dFalse aFalse
  have swapped : ∃ p : P2,
      (∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 c) (realPoint2 d) t) ∧
      (∃ s : ℝ,0≤s ∧ s≤1 ∧ p=interpolate (realPoint2 a) (realPoint2 b) s) := by
    obtain ⟨p,hp,hq⟩:=common
    exact ⟨p,hq,hp⟩
  have right:=intersection_strict_sides c d a b swapped aFalse bFalse cFalse
  simp [closedIntersection,left,right]

theorem closedIntersection_iff_real (a b c d : Point2) :
    closedIntersection a b c d=true ↔ ∃ p : P2,
      (∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 a) (realPoint2 b) t) ∧
      (∃ s : ℝ,0≤s ∧ s≤1 ∧ p=interpolate (realPoint2 c) (realPoint2 d) s) :=
  ⟨closedIntersection_sound a b c d,closedIntersection_complete a b c d⟩

/-- The executable check also characterizes rational common-point witnesses. -/
theorem closedIntersection_iff_rational (a b c d : Point2) :
    closedIntersection a b c d=true ↔ ∃ p,RationalSegment a b p ∧ RationalSegment c d p := by
  constructor
  · exact closedIntersection_rational a b c d
  · rintro ⟨p,hp,hq⟩
    exact closedIntersection_complete a b c d
      ⟨realPoint2 p,RationalSegment_real a b p hp,RationalSegment_real c d p hq⟩

/-- A false predicate means the real closed segments are disjoint, rather than
merely a failed search for an intersection witness. -/
theorem closedIntersection_false_iff (a b c d : Point2) :
    closedIntersection a b c d=false ↔ ¬∃ p : P2,
      (∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 a) (realPoint2 b) t) ∧
      (∃ s : ℝ,0≤s ∧ s≤1 ∧ p=interpolate (realPoint2 c) (realPoint2 d) s) := by
  constructor
  · intro rejected common
    have accepted:=closedIntersection_complete a b c d common
    rw [rejected] at accepted
    contradiction
  · intro disjoint
    cases result : closedIntersection a b c d with
    | false => rfl
    | true => exact False.elim (disjoint (closedIntersection_sound a b c d result))

#print axioms closedIntersection_iff_rational
#print axioms closedIntersection_false_iff

#print axioms closedIntersection_iff_real

#print axioms collinear_intersection_endpoint

#print axioms parameter_subsegment
end Tess
