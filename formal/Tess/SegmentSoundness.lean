import Tess.PredicateGeometry
import Tess.Subdivision
noncomputable section
namespace Tess
open RealGeometry

def segmentPoint (a b : Point2) (t : Rat) : Point2 :=
  ⟨a.x+t*(b.x-a.x),a.y+t*(b.y-a.y)⟩
def RationalSegment (a b p : Point2) : Prop :=
  ∃ t : Rat,0≤t ∧ t≤1 ∧ p=segmentPoint a b t

theorem ratio_between (a b x : Rat) (different : b-a≠0) (h : between a b x) :
    0≤(x-a)/(b-a) ∧ (x-a)/(b-a)≤1 := by
  rcases lt_or_gt_of_ne different with negative|positive
  · have bounds : b≤x ∧ x≤a := by rcases h with h|h <;> constructor <;> linarith [h.1,h.2]
    exact ⟨div_nonneg_of_nonpos (by linarith [bounds.2]) negative.le,
      (div_le_one_of_neg negative).mpr (by linarith [bounds.1])⟩
  · have bounds : a≤x ∧ x≤b := by rcases h with h|h <;> constructor <;> linarith [h.1,h.2]
    exact ⟨div_nonneg (by linarith [bounds.1]) positive.le,
      (div_le_one positive).mpr (by linarith [bounds.2])⟩

theorem onSegment_rational (a b p : Point2) (checked : onSegment a b p=true) : RationalSegment a b p := by
  obtain ⟨col,xbetween,ybetween⟩:=onSegment_sound a b p checked
  by_cases hx : b.x-a.x=0
  · by_cases hy : b.y-a.y=0
    · have px : p.x=a.x := by rcases xbetween with h|h <;> linarith [h.1,h.2]
      have py : p.y=a.y := by rcases ybetween with h|h <;> linarith [h.1,h.2]
      refine ⟨0,by norm_num,by norm_num,?_⟩
      cases p; cases a; simp_all [segmentPoint]
    · let t:Rat:=(p.y-a.y)/(b.y-a.y)
      have bounds:=ratio_between a.y b.y p.y hy ybetween
      have hty : t*(b.y-a.y)=p.y-a.y:=div_mul_cancel₀ _ hy
      have px : p.x=a.x := by rcases xbetween with h|h <;> linarith [h.1,h.2]
      refine ⟨t,bounds.1,bounds.2,?_⟩
      cases p; cases a; cases b
      simp only [segmentPoint,Point2.mk.injEq]
      constructor <;> dsimp at * <;> nlinarith
  · let t:Rat:=(p.x-a.x)/(b.x-a.x)
    have bounds:=ratio_between a.x b.x p.x hx xbetween
    have htx : t*(b.x-a.x)=p.x-a.x:=div_mul_cancel₀ _ hx
    have py : p.y=a.y+t*(b.y-a.y) := by
      apply mul_left_cancel₀ hx
      calc (b.x-a.x)*p.y=(b.x-a.x)*a.y+(b.y-a.y)*(p.x-a.x) := by
            dsimp [orient] at col; linarith
           _=(b.x-a.x)*(a.y+t*(b.y-a.y)) := by rw [← htx]; ring
    refine ⟨t,bounds.1,bounds.2,?_⟩
    cases p; cases a; cases b
    simp only [segmentPoint,Point2.mk.injEq]
    constructor <;> dsimp at * <;> linarith

theorem segmentPoint_self (a b : Point2) (t : Rat) : orient a b (segmentPoint a b t)=0 := by
  simp only [orient,segmentPoint]; ring

theorem orient_segmentPoint (a b c d : Point2) (t : Rat) :
    orient c d (segmentPoint a b t)=(1-t)*orient c d a+t*orient c d b := by
  simp only [orient,segmentPoint]; ring

theorem segment_cross_parameter (x y : Rat) (opposite : x*y<0) :
    x-y≠0 ∧ 0≤x/(x-y) ∧ x/(x-y)≤1 := by
  have different:x-y≠0:=by intro h; have eq:x=y:=sub_eq_zero.mp h; rw [eq] at opposite; nlinarith [sq_nonneg y]
  have betweenZero : between x y 0 := by
    rcases mul_neg_iff.mp opposite with ⟨hx,hy⟩|⟨hx,hy⟩
    · exact Or.inr ⟨hy.le,hx.le⟩
    · exact Or.inl ⟨hx.le,hy.le⟩
  have bounds:=ratio_between x y 0 (by intro h; apply different; linarith) betweenZero
  have ratio : (0-x)/(y-x)=x/(x-y) := by rw [zero_sub,← neg_sub x y,neg_div_neg_eq]
  rw [ratio] at bounds
  exact ⟨different,bounds⟩

theorem crossing_line_unique (a b c d p q : Point2)
    (different : orient c d a-orient c d b≠0)
    (hap : orient a b p=0) (haq : orient a b q=0)
    (hcp : orient c d p=0) (hcq : orient c d q=0) : p=q := by
  let D:Rat:=(b.x-a.x)*(d.y-c.y)-(b.y-a.y)*(d.x-c.x)
  have identity : orient c d a-orient c d b=D := by dsimp [D,orient]; ring
  have nonzero : D≠0 := by rwa [identity] at different
  have px : D*(p.x-q.x)=0 := by
    dsimp [D,orient] at *
    linear_combination (d.x-c.x)*hap-(d.x-c.x)*haq-(b.x-a.x)*hcp+(b.x-a.x)*hcq
  have py : D*(p.y-q.y)=0 := by
    dsimp [D,orient] at *
    linear_combination (d.y-c.y)*hap-(d.y-c.y)*haq-(b.y-a.y)*hcp+(b.y-a.y)*hcq
  have ex:=sub_eq_zero.mp ((mul_eq_zero.mp px).resolve_left nonzero)
  have ey:=sub_eq_zero.mp ((mul_eq_zero.mp py).resolve_left nonzero)
  cases p; cases q; simp_all

theorem properCrossing_rational (a b c d : Point2)
    (cross : orient a b c*orient a b d<0 ∧ orient c d a*orient c d b<0) :
    ∃ p,RationalSegment a b p ∧ RationalSegment c d p := by
  let x:=orient c d a;let y:=orient c d b
  let u:=orient a b c;let v:=orient a b d
  have xt:=segment_cross_parameter x y cross.2
  have ut:=segment_cross_parameter u v cross.1
  let t:=x/(x-y);let s:=u/(u-v)
  let p:=segmentPoint a b t;let q:=segmentPoint c d s
  have tp:t*(x-y)=x:=div_mul_cancel₀ _ xt.1
  have sp:s*(u-v)=u:=div_mul_cancel₀ _ ut.1
  have hp : orient c d p=0 := by rw [orient_segmentPoint]; change (1-t)*x+t*y=0; nlinarith [tp]
  have hq : orient a b q=0 := by rw [orient_segmentPoint]; change (1-s)*u+s*v=0; nlinarith [sp]
  have equal:p=q:=crossing_line_unique a b c d p q xt.1 (segmentPoint_self a b t) hq hp (segmentPoint_self c d s)
  exact ⟨p,⟨t,xt.2.1,xt.2.2,rfl⟩,⟨s,ut.2.1,ut.2.2,equal⟩⟩

theorem RationalSegment_real (a b p : Point2) (h : RationalSegment a b p) :
    ∃ t : ℝ,0≤t ∧ t≤1 ∧ realPoint2 p=interpolate (realPoint2 a) (realPoint2 b) t := by
  obtain ⟨t,lo,hi,rfl⟩:=h
  refine ⟨(t : ℝ),by exact_mod_cast lo,by exact_mod_cast hi,?_⟩
  simp only [realPoint2,segmentPoint,interpolate]
  push_cast
  rfl

/-- Every accepted intersection has a rational common point, even when it
arises from collinear overlap rather than a proper crossing. -/
theorem closedIntersection_rational (a b c d : Point2)
    (checked : closedIntersection a b c d=true) :
    ∃ p,RationalSegment a b p ∧ RationalSegment c d p := by
  simp only [closedIntersection,Bool.or_eq_true,decide_eq_true_eq] at checked
  have selfStart (a b : Point2):RationalSegment a b a:=⟨0,by norm_num,by norm_num,by simp [segmentPoint]⟩
  have selfEnd (a b : Point2):RationalSegment a b b:=⟨1,by norm_num,by norm_num,by cases a;cases b;simp [segmentPoint]⟩
  have rational : ∃ p,RationalSegment a b p ∧ RationalSegment c d p := by
    rcases checked with (((left|left)|left)|left)|cross
    · exact ⟨c,onSegment_rational _ _ _ left,selfStart c d⟩
    · exact ⟨d,onSegment_rational _ _ _ left,selfEnd c d⟩
    · exact ⟨a,selfStart a b,onSegment_rational _ _ _ left⟩
    · exact ⟨b,selfEnd a b,onSegment_rational _ _ _ left⟩
    · exact properCrossing_rational a b c d cross
  exact rational

/-- Accepted closed intersection supplies a real common segment point. This
includes zero-length segments, endpoints, and collinear interval overlap. -/
theorem closedIntersection_sound (a b c d : Point2) (checked : closedIntersection a b c d=true) :
    ∃ p : P2,(∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 a) (realPoint2 b) t) ∧
      (∃ t : ℝ,0≤t ∧ t≤1 ∧ p=interpolate (realPoint2 c) (realPoint2 d) t) := by
  obtain ⟨p,hp,hq⟩:=closedIntersection_rational a b c d checked
  exact ⟨realPoint2 p,RationalSegment_real a b p hp,RationalSegment_real c d p hq⟩

/-- Every convex parameter gives coordinate-wise closed interval membership. -/
theorem between_interpolation (a b t : Rat) (lo : 0≤t) (hi : t≤1) :
    between a b (a+t*(b-a)) := by
  rcases le_total a b with forward|reverse
  · left
    constructor <;> nlinarith [mul_nonneg lo (show 0≤b-a by linarith),
      mul_nonneg (show 0≤1-t by linarith) (show 0≤b-a by linarith)]
  · right
    constructor <;> nlinarith [mul_nonneg lo (show 0≤a-b by linarith),
      mul_nonneg (show 0≤1-t by linarith) (show 0≤a-b by linarith)]

/-- Completeness of the executable segment-membership check, including a=b. -/
theorem RationalSegment_onSegment (a b p : Point2) (h : RationalSegment a b p) :
    onSegment a b p=true := by
  obtain ⟨t,lo,hi,rfl⟩:=h
  simp only [onSegment,Bool.and_eq_true,collinear,decide_eq_true_eq]
  exact ⟨segmentPoint_self a b t,
    between_interpolation a.x b.x t lo hi,between_interpolation a.y b.y t lo hi⟩

theorem onSegment_iff_rational (a b p : Point2) :
    onSegment a b p=true ↔ RationalSegment a b p :=
  ⟨onSegment_rational a b p,RationalSegment_onSegment a b p⟩

#print axioms onSegment_iff_rational

/-- Exact executable membership is equivalent to real closed-segment membership.
There are no nondegeneracy hypotheses and no tolerance. -/
theorem onSegment_iff_real (a b p : Point2) :
    onSegment a b p=true ↔
      ∃ t : ℝ,0≤t ∧ t≤1 ∧ realPoint2 p=interpolate (realPoint2 a) (realPoint2 b) t := by
  constructor
  · intro checked
    exact RationalSegment_real a b p (onSegment_rational a b p checked)
  · rintro ⟨t,lo,hi,equal⟩
    have coordinateBounds (x y : ℝ) :
        (x≤x+t*(y-x) ∧ x+t*(y-x)≤y) ∨ (y≤x+t*(y-x) ∧ x+t*(y-x)≤x) := by
      rcases le_total x y with forward|reverse
      · left
        constructor <;> nlinarith [mul_nonneg lo (show 0≤y-x by linarith),
          mul_nonneg (show 0≤1-t by linarith) (show 0≤y-x by linarith)]
      · right
        constructor <;> nlinarith [mul_nonneg lo (show 0≤x-y by linarith),
          mul_nonneg (show 0≤1-t by linarith) (show 0≤x-y by linarith)]
    have hx := congrArg Prod.fst equal
    have hy := congrArg Prod.snd equal
    change (p.x : ℝ)=(a.x : ℝ)+t*((b.x : ℝ)-(a.x : ℝ)) at hx
    change (p.y : ℝ)=(a.y : ℝ)+t*((b.y : ℝ)-(a.y : ℝ)) at hy
    have bx := coordinateBounds (a.x : ℝ) (b.x : ℝ)
    have byy := coordinateBounds (a.y : ℝ) (b.y : ℝ)
    rw [← hx] at bx
    rw [← hy] at byy
    have col : (orient a b p : ℝ)=0 := by
      rw [← orient_realPoint2,equal]
      dsimp [RealGeometry.orient,realPoint2,interpolate]
      ring
    simp only [onSegment,Bool.and_eq_true,collinear,decide_eq_true_eq]
    refine ⟨?_,?_,?_⟩
    · exact_mod_cast col
    · unfold between
      exact_mod_cast bx
    · unfold between
      exact_mod_cast byy

#print axioms onSegment_iff_real

#print axioms onSegment_rational
#print axioms closedIntersection_sound
end Tess
